#include <algorithm>
#include <memory>
#include <utility>

#include "opt-sched/Scheduler/bb_spill.h"
#include "opt-sched/Scheduler/config.h"
#include "opt-sched/Scheduler/graph_trans.h"
#include "opt-sched/Scheduler/list_sched.h"
#include "opt-sched/Scheduler/logger.h"
#include "opt-sched/Scheduler/random.h"
#include "opt-sched/Scheduler/reg_alloc.h"
#include "opt-sched/Scheduler/relaxed_sched.h"
#include "opt-sched/Scheduler/sched_region.h"
#include "opt-sched/Scheduler/stats.h"
#include "opt-sched/Scheduler/utilities.h"
#include "opt-sched/Scheduler/aco.h"

extern bool OPTSCHED_gPrintSpills;

using namespace llvm::opt_sched;

SchedRegion::SchedRegion(MachineModel *machMdl, DataDepGraph *dataDepGraph,
                         long rgnNum, int16_t sigHashSize, LB_ALG lbAlg,
                         SchedPriorities hurstcPrirts,
                         SchedPriorities enumPrirts, bool vrfySched,
                         Pruning PruningStrategy, SchedulerType HeurSchedType) {
  machMdl_ = machMdl;
  dataDepGraph_ = dataDepGraph;
  rgnNum_ = rgnNum;
  sigHashSize_ = sigHashSize;
  lbAlg_ = lbAlg;
  hurstcPrirts_ = hurstcPrirts;
  enumPrirts_ = enumPrirts;
  vrfySched_ = vrfySched;
  prune_ = PruningStrategy;
  HeurSchedType_ = HeurSchedType;
  isSecondPass = false;

  totalSimSpills_ = INVALID_VALUE;
  bestCost_ = 0;
  bestSchedLngth_ = 0;
  hurstcCost_ = 0;
  hurstcSchedLngth_ = 0;
  acoScheduleCost_ = 0;
  acoScheduleLength_ = 0;
  enumCrntSched_ = NULL;
  enumBestSched_ = NULL;
  schedLwrBound_ = 0;
  schedUprBound_ = INVALID_VALUE;

  instCnt_ = dataDepGraph_->GetInstCnt();

  needTrnstvClsr_ = false;
}

void SchedRegion::UseFileBounds_() {
  InstCount fileLwrBound, fileUprBound;

  dataDepGraph_->UseFileBounds();
  dataDepGraph_->GetFileSchedBounds(fileLwrBound, fileUprBound);
  assert(fileLwrBound >= schedLwrBound_);
  schedLwrBound_ = fileLwrBound;
}

InstSchedule *SchedRegion::AllocNewSched_() {
  InstSchedule *newSched =
      new InstSchedule(machMdl_, dataDepGraph_, vrfySched_);
  if (newSched == NULL)
    Logger::Fatal("Out of memory.");
  return newSched;
}

void SchedRegion::CmputAbslutUprBound_() {
  abslutSchedUprBound_ = dataDepGraph_->GetAbslutSchedUprBound();
}

// FIXME: Heuristic cost and length is being returned by reference
// which may cause an issue when heuristic is disabled.
FUNC_RESULT SchedRegion::FindOptimalSchedule( //TODO: CHIPPIE: Add helper functions as private functions in the class.
    Milliseconds rgnTimeout, Milliseconds lngthTimeout, bool &isLstOptml,
    InstCount &bestCost, InstCount &bestSchedLngth, InstCount &hurstcCost,
    InstCount &hurstcSchedLngth, InstSchedule *&bestSched, bool filterByPerp,
    const BLOCKS_TO_KEEP blocksToKeep) {
  ConstrainedScheduler *lstSchdulr = NULL;
  ConstrainedScheduler *acoSchdulr = NULL;
  InstSchedule *initialSchedule = NULL;
  InstSchedule *lstSched = NULL;
  InstSchedule *acoSchedule = NULL;
  InstCount initialScheduleLength;
  InstCount initialScheduleCost = 0;
  FUNC_RESULT rslt = RES_SUCCESS;
  Milliseconds hurstcTime = 0;
  Milliseconds boundTime = 0;
  Milliseconds enumTime = 0;
  Milliseconds vrfyTime = 0;
  Milliseconds acoTime = 0;
  Milliseconds acoStart = 0;
  
  enumCrntSched_ = NULL;
  enumBestSched_ = NULL;
  bestSched = bestSched_ = NULL;

  bool acoBeforeEnum = false;
  bool acoAfterEnum = false;

  //TODO: CHIPPIE: Perhaps rename these to match the flag names?
  Config &schedIni = SchedulerOptions::getInstance();
  bool heuristicSchedulerEnabled = schedIni.GetBool("HEUR_ENABLED");
  bool acoSchedulerEnabled = schedIni.GetBool("ACO_ENABLED");
  bool bbSchedulerEnabled = schedIni.GetBool("ENUM_ENABLED");
  if (acoSchedulerEnabled) {
    acoBeforeEnum = schedIni.GetBool("ACO_BEFORE_ENUM");
    acoAfterEnum = schedIni.GetBool("ACO_AFTER_ENUM");
  }

  if (false == heuristicSchedulerEnabled && false == acoBeforeEnum) {
    //Abort if ACO and heuristic algorithms are disabled.
    cout << "TODO: Descriptive error message here saying that there must be at least one of the ACO or Heuristic scheduler enabled before the enumerator.\n";
    return RES_ERROR;
  }

  /*
    * Algorithm run order:
    * 1) Heuristic
    * 2) ACO
    * 3) Branch & Bound
    * 4) ACO (TODO)
    * 
    * Each of these 3 algorithms can be individually disabled, but one of the heuristic or ACO must be enabled. (TODO: CHIPPIE)
    */

  Logger::Info("---------------------------------------------------------------"
               "------------");
  Logger::Info("Processing DAG %s with %d insts and max latency %d.",
               dataDepGraph_->GetDagID(), dataDepGraph_->GetInstCnt(),
               dataDepGraph_->GetMaxLtncy());

  stats::problemSize.Record(dataDepGraph_->GetInstCnt());

  const auto *GraphTransformations = dataDepGraph_->GetGraphTrans();
  if (rgnTimeout > 0 || GraphTransformations->size() > 0 ||
      spillCostFunc_ == SCF_SLIL)
    needTrnstvClsr_ = true;

  rslt = dataDepGraph_->SetupForSchdulng(needTrnstvClsr_);
  if (rslt != RES_SUCCESS) {
    Logger::Info("Invalid input DAG");
    return rslt;
  }

  // Apply graph transformations
  for (auto &GT : *GraphTransformations) {
    rslt = GT->ApplyTrans();

    if (rslt != RES_SUCCESS)
      return rslt;

    // Update graph after each transformation
    rslt = dataDepGraph_->UpdateSetupForSchdulng(needTrnstvClsr_);
    if (rslt != RES_SUCCESS) {
      Logger::Info("Invalid DAG after graph transformations");
      return rslt;
    }
  }

  SetupForSchdulng_();
  CmputAbslutUprBound_();
  schedLwrBound_ = dataDepGraph_->GetSchedLwrBound();

  // We can calculate lower bounds here since it is only dependent
  // on schedLwrBound_
  if (!bbSchedulerEnabled) 
    costLwrBound_ = CmputCostLwrBound();
  else
    CmputLwrBounds_(false);

  // Step #1: Find the heuristic schedule if enabled.
  if (heuristicSchedulerEnabled) {
    cout << "TODO: Heuristic Scheduler is enabled.\n"; //TODO: Remove this debugging line when done.
    Milliseconds hurstcStart = Utilities::GetProcessorTime();
    lstSched = new InstSchedule(machMdl_, dataDepGraph_, vrfySched_);
    if (lstSched == NULL)
      Logger::Fatal("Out of memory.");

    lstSchdulr = AllocHeuristicScheduler_();
    
    rslt = lstSchdulr->FindSchedule(lstSched, this);
   
    if (rslt != RES_SUCCESS) {
      Logger::Info("List scheduling failed");
      delete lstSchdulr;
      delete lstSched;
      return rslt;
    }

    hurstcTime = Utilities::GetProcessorTime() - hurstcStart;
    stats::heuristicTime.Record(hurstcTime);
    if (hurstcTime > 0)
      Logger::Info("Heuristic_Time %d", hurstcTime);
    
    hurstcSchedLngth_ = lstSched->GetCrntLngth(); 
    InstCount hurstcExecCost;
    // Compute cost for Heuristic list scheduler, this must be called before
    // calling GetCost() on the InstSchedule instance.
    CmputNormCost_(lstSched, CCM_DYNMC, hurstcExecCost, true);
    hurstcCost_ = lstSched->GetCost();
    cout << "[CHIPPIE: DEBUG] Right after lstSched->GetCost(): return value was " << hurstcCost_ << "\n";
   
    // This schedule is optimal so ACO will not be run
    // so set bestSched here.
    if (hurstcCost_ == 0) {
      cout << "[CHIPPIE: DEBUG] ***** HEURISTIC SCHEDULE IS OPTIMAL *****\n"; //TODO: CHIPPIE: REMOVE DEBUGGING STATEMENT.
      isLstOptml = true;
      bestSched = bestSched_ = lstSched;
      bestSchedLngth_ = hurstcSchedLngth_;
      bestCost_ = hurstcCost_;
    }
   
    FinishHurstc_(); //TODO: CHIPPIE: Need one for ACO. Will need to also add some new statistic for the ACO counterparts.

    //  #ifdef IS_DEBUG_SOLN_DETAILS_1
    Logger::Info(
        "The list schedule is of length %d and spill cost %d. Tot cost = %d",
        hurstcSchedLngth_, lstSched->GetSpillCost(), hurstcCost_);
    //  #endif

#ifdef IS_DEBUG_PRINT_SCHEDS
    lstSched->Print(Logger::GetLogStream(), "Heuristic");
#endif
#ifdef IS_DEBUG_PRINT_BOUNDS
    dataDepGraph_->PrintLwrBounds(DIR_FRWRD, Logger::GetLogStream(),
                                  "CP Lower Bounds");
#endif
  }

  // Step #2: Use ACO to find a schedule if enabled.
  if (acoBeforeEnum && false == isLstOptml) { //If the Heuristic algorithm already produced the optimal result, don't run ACO or B&B.
    //TODO: CHIPPIE: If ACO's schedule is optimal, set the best schedule to that (and don't run B&B).
    //TODO: CHIPPIE: If neither ACO's or the Heuristic's schedule is optimal, compare ACO's result with the heuristic's and then set the initial_schedule to that.

    cout << "TODO: ACO Scheduler is enabled & running.\n"; //TODO: Remove this debugging line when done.
    acoStart = Utilities::GetProcessorTime();
    acoSchedule = new InstSchedule(machMdl_, dataDepGraph_, vrfySched_);
    if (acoSchedule == NULL)
      Logger::Fatal("Out of memory."); 

    rslt = runACO(acoSchedule, lstSched);
    if (rslt != RES_SUCCESS) {
      Logger::Info("ACO scheduling failed");
      if (lstSchdulr) 
        delete lstSchdulr;
      if (lstSched) 
        delete lstSched;
      delete acoSchdulr;
      delete acoSchedule;
      return rslt;
    }

    acoTime = Utilities::GetProcessorTime() - acoStart;
    stats::acoTime.Record(acoTime);
    if (acoTime > 0)
      Logger::Info("ACO_Time %d", acoTime);

    acoScheduleLength_ = acoSchedule->GetCrntLngth();
    InstCount ACOExecCost;
    // Compute cost for ACO scheduler, this must be called before
    // calling GetCost() on the InstSchedule instance.
    acoScheduleCost_ = acoSchedule->GetCost();
    Logger::Info("[CHIPPIE: DEBUG] Just finished ACO! Here's the ACO schedule cost: %d, and length: %d", acoScheduleCost_, acoScheduleLength_);

    // If ACO is run then that means either:
    // 1.) Heuristic was not run
    // 2.) Heuristic was not optimal
    // In both cases, the current best will be ACO if
    // ACO is optimal so set bestSched here.
    if (acoScheduleCost_ == 0) {
      Logger::Info("[CHIPPIE: DEBUG] ***** ACO SCHEDULE IS OPTIMAL *****"); //TODO: CHIPPIE: REMOVE DEBUGGING STATEMENT.
      isLstOptml  = true;
      bestSched = bestSched_ = acoSchedule;
      bestSchedLngth_ = acoScheduleLength_;
      bestCost_ = acoScheduleCost_;
    }
  }

  // If an optimal schedule was found then it should have already
  // been taken care of when optimality was discovered.
  // Thus we only account for cases where no optimal schedule
  // was found.
  if (!isLstOptml ) {
//There are 3 possible situations:
    // A) ACO was never run. In that case, just use Heuristic and run with its results, into B&B.
    if (!acoBeforeEnum) {
      bestSched = bestSched_ = lstSched;
      bestSchedLngth_ = hurstcSchedLngth_;
      bestCost_ = hurstcCost_;
    }
    // B) Heuristic was never run. In that case, just use ACO and run with its results, into B&B.
    else if (!heuristicSchedulerEnabled) {
      bestSched = bestSched_ = acoSchedule;
      bestSchedLngth_ = acoScheduleLength_;
      bestCost_ = acoScheduleCost_;
    // C) Neither scheduler was optimal. In that case, compare the two schedules and use the one that's better as the input (initialSched) for B&B.      
    } else {
      compareSchedules(lstSched, acoSchedule, bestSched_);
      bestSched = bestSched_;
      bestSchedLngth_ = bestSched_->GetCrntLngth();
      bestCost_ = bestSched_->GetCost();
    }
  }
  // Step #2: Compute the cost upper bound.
  Milliseconds boundStart = Utilities::GetProcessorTime();
  assert(bestSchedLngth_ >= schedLwrBound_);
  assert(schedLwrBound_ <= bestSched_->GetCrntLngth());

  // Only used to calculate upper bounds
  // Was previously used to check for optimality.
  CmputUprBounds_(lstSched, false);
  boundTime = Utilities::GetProcessorTime() - boundStart;
  stats::boundComputationTime.Record(boundTime);

#ifdef IS_DEBUG_PRINT_SCHEDS
  lstSched->Print(Logger::GetLogStream(), "Heuristic");
#endif
#ifdef IS_DEBUG_PRINT_BOUNDS
  dataDepGraph_->PrintLwrBounds(DIR_FRWRD, Logger::GetLogStream(),
                                "CP Lower Bounds");
#endif

  if (rgnTimeout == 0)
    isLstOptml = true; //TODO: CHIPPIE: NOTE: This was a hack to disable B&B before these scheduler enabling flags tasks.

  // (Chris): If the cost function is SLIL, then the list schedule is considered
  // optimal if PERP is 0.
  if (filterByPerp && !isLstOptml && spillCostFunc_ == SCF_SLIL) {
    const InstCount *regPressures = nullptr;
    auto regTypeCount = lstSched->GetPeakRegPressures(regPressures);
    InstCount sumPerp = 0;
    for (int i = 0; i < regTypeCount; ++i) {
      int perp = regPressures[i] - machMdl_->GetPhysRegCnt(i);
      if (perp > 0)
        sumPerp += perp;
    }
    if (sumPerp == 0) {
      isLstOptml = true;
      Logger::Info("Marking SLIL list schedule as optimal due to zero PERP.");
    }
  }

#if defined(IS_DEBUG_SLIL_OPTIMALITY)
  // (Chris): This code prints a statement when a schedule is SLIL-optimal but
  // not PERP-optimal.
  if (spillCostFunc_ == SCF_SLIL && bestCost_ == 0) {
    const InstCount *regPressures = nullptr;
    auto regTypeCount = lstSched->GetPeakRegPressures(regPressures);
    InstCount sumPerp = 0;
    for (int i = 0; i < regTypeCount; ++i) {
      int perp = regPressures[i] - machMdl_->GetPhysRegCnt(i);
      if (perp > 0)
        sumPerp += perp;
    }
    if (sumPerp > 0) {
      Logger::Info("Dag %s is SLIL optimal but not PERP optimal (PERP=%d).",
                   dataDepGraph_->GetDagID(), sumPerp);
    }
  }
#endif
  if (EnableEnum_() == false) {
    delete lstSchdulr;
    return RES_FAIL;
  }
 
#ifdef IS_DEBUG_BOUNDS
  Logger::Info("Sched LB = %d, Sched UB = %d", schedLwrBound_, schedUprBound_);
#endif
 
  initialSchedule = bestSched_;
  initialScheduleCost = bestCost_;
  initialScheduleLength = bestSchedLngth_;
  
// Step #4: Find the optimal schedule if the heuristc was not optimal.
  if (bbSchedulerEnabled) {
    Milliseconds enumStart = Utilities::GetProcessorTime();
    cout << "TODO: BB scheduler is enabled.\n";
    //isLstOptml = false; //TODO: CHIPPIE: Remove this when done debugging. //Yes, this flow works correctly.
    if (false == isLstOptml) { 
      cout << "TODO: Running BB scheduler...\n"; //TODO: CHIPPIE: Remove this when done debugging.
      dataDepGraph_->SetHard(true);
      rslt = Optimize_(enumStart, rgnTimeout, lngthTimeout);
      Milliseconds enumTime = Utilities::GetProcessorTime() - enumStart;
      
      // TODO: Implement one for ACO also. Maybe also Heuristic + ACO? 
      // Priority: Low
      if (hurstcTime > 0) { //TODO: CHIPPIE: This shouldn't use the heuristic time...what should this now use? initialScheduleTime?
        enumTime /= hurstcTime;
        stats::enumerationToHeuristicTimeRatio.Record(enumTime);
      }

      if (bestCost_ < initialScheduleCost) {
        assert(enumBestSched_ != NULL);
        bestSched = bestSched_ = enumBestSched_;
  #ifdef IS_DEBUG_PRINT_SCHEDS
        enumBestSched_->Print(Logger::GetLogStream(), "Optimal");
  #endif
      }
    } else if (rgnTimeout == 0) {
       Logger::Info(
           "Bypassing optimal scheduling due to zero time limit with cost %d",
           bestCost_);
    } else {
       Logger::Info("The initial schedule of length %d and cost %d is optimal.",
                   bestSchedLngth_, bestCost_);
    }

    if (rgnTimeout != 0) {
      bool optimalSchedule = isLstOptml || (rslt == RES_SUCCESS);
       Logger::Info("Best schedule for DAG %s has cost %d and length %d. The "
                   "schedule is %s",
                   dataDepGraph_->GetDagID(), bestCost_, bestSchedLngth_,
                   optimalSchedule ? "optimal" : "not optimal");
    }

#ifdef IS_DEBUG_PRINT_PERP_AT_EACH_STEP
    Logger::Info("Printing PERP at each step in the schedule.");

    int costSum = 0;
    for (int i = 0; i < dataDepGraph_->GetInstCnt(); ++i) {
      Logger::Info("Cycle: %lu Cost: %lu", i, bestSched_->GetSpillCost(i));
      costSum += bestSched_->GetSpillCost(i);
    }
    Logger::Info("Cost Sum: %lu", costSum);
#endif

    if (SchedulerOptions::getInstance().GetString(
            "SIMULATE_REGISTER_ALLOCATION") != "NO") {
      //#ifdef IS_DEBUG
      RegAlloc_(bestSched, initialSchedule);
      //#endif
    }

    enumTime = Utilities::GetProcessorTime() - enumStart;
    stats::enumerationTime.Record(enumTime);
  }

  // Step 5: Run ACO if schedule from enumerator is not optimal
  if (bestCost_ != 0 && acoAfterEnum) {
    Logger::Info("Final cost is not optimal, running ACO.");
    InstSchedule *acoAfterEnumSchedule = new InstSchedule(machMdl_, dataDepGraph_, vrfySched_);
    if (acoAfterEnumSchedule == NULL)
      Logger::Fatal("Out of memory");

    FUNC_RESULT acoRslt = runACO(acoAfterEnumSchedule, bestSched);
    if (acoRslt != RES_SUCCESS) {
      Logger::Info("Running final ACO failed");
      delete acoAfterEnumSchedule;
    }

    InstCount acoAfterEnumCost = acoAfterEnumSchedule->GetCost();
    if (acoAfterEnumCost < bestCost_) {
      InstCount acoAfterEnumLength = acoAfterEnumSchedule->GetCrntLngth();
      InstCount imprvmnt = bestCost_ - acoAfterEnumCost;
      Logger::Info("ACO found better schedule with length=%d, spill cost = %d, tot cost = %d, cost imp=%d.",
                    acoAfterEnumLength, acoAfterEnumSchedule->GetSpillCost(), acoAfterEnumCost, imprvmnt);
      bestSched_ = bestSched = acoAfterEnumSchedule;
      bestCost_ = acoAfterEnumCost;
      bestSchedLngth_ = acoAfterEnumLength;
    } else
      delete acoAfterEnumSchedule;
  }
  
  
  Milliseconds vrfyStart = Utilities::GetProcessorTime();
  if (vrfySched_) {
    bool isValidSchdul = bestSched->Verify(machMdl_, dataDepGraph_);

    if (isValidSchdul == false) {
      stats::invalidSchedules++;
    }
  }

  vrfyTime = Utilities::GetProcessorTime() - vrfyStart;
  stats::verificationTime.Record(vrfyTime);

  // VANG: Is this still needed? It is only used in
  // DataDepGraph::WriteToFile. I don't think we write 
  // to file anymore.
  InstCount finalLwrBound = costLwrBound_;
  InstCount finalUprBound = costLwrBound_ + bestCost_;
  if (rslt == RES_SUCCESS)
    finalLwrBound = finalUprBound;

  dataDepGraph_->SetFinalBounds(finalLwrBound, finalUprBound);
  ///////////////////////////////////////////////////////

  // May need to be updated for ACO running after BB
  FinishOptml_();

  bool tookBest = ChkSchedule_(bestSched, initialSchedule);
  if (tookBest == false) {
    bestCost_ = initialScheduleCost;
    bestSchedLngth_ = initialScheduleLength;
  }

  if (lstSchdulr) {
    delete lstSchdulr;
  }
  if (NULL != lstSched && bestSched != lstSched) {
      delete lstSched;
  }
  if (NULL != acoSchedule && bestSched != acoSchedule) {
    delete acoSchedule;
  }
  if (enumBestSched_ != NULL && bestSched != enumBestSched_)
    delete enumBestSched_;
  if (enumCrntSched_ != NULL)
    delete enumCrntSched_;

  bestCost = bestCost_;
  bestSchedLngth = bestSchedLngth_;
  hurstcCost = hurstcCost_;
  hurstcSchedLngth = hurstcSchedLngth_;
  
  // (Chris): Experimental. Discard the schedule based on sched.ini setting.
  if (spillCostFunc_ == SCF_SLIL) {
    bool optimal = isLstOptml || (rslt == RES_SUCCESS);
    if ((blocksToKeep == BLOCKS_TO_KEEP::ZERO_COST && bestCost != 0) ||
        (blocksToKeep == BLOCKS_TO_KEEP::OPTIMAL && !optimal) ||
        (blocksToKeep == BLOCKS_TO_KEEP::IMPROVED &&
         !(bestCost < initialScheduleCost)) ||									
        (blocksToKeep == BLOCKS_TO_KEEP::IMPROVED_OR_OPTIMAL &&
         !(optimal || bestCost < initialScheduleCost))) {
      delete bestSched;
      bestSched = nullptr;
      return rslt;
    }
  }
  
  // TODO: Update this
  // Priority: Low
#if defined(IS_DEBUG_COMPARE_SLIL_BB) //TODO: CHIPPIE: This block will likewise need to be updated...I note that there are some references to isLstOptml, which will need to be updated if the heuristic scheduler is disabled, and also may need to be changed to account for ACO.
  {
    const auto &status = [&]() {
      switch (rslt) {
      case RES_SUCCESS:
        return "optimal";
      case RES_TIMEOUT:
        return "timeout";
      default:
        return "failed";
      }
    }();
    if (!isLstOptml) { //TODO: CHIPPIE: What to do about this? initialScheduleOptimal?
      Logger::Info("Dag %s %s cost %d time %lld", dataDepGraph_->GetDagID(),
                   status, bestCost_, enumTime);
      Logger::Info("Dag %s %s absolute cost %d time %lld",
                   dataDepGraph_->GetDagID(), status, bestCost_ + costLwrBound_,
                   enumTime);
    }
  }
  {
    if (spillCostFunc_ == SCF_SLIL && rgnTimeout != 0) {
      // costLwrBound_: static lower bound
      // bestCost_: total cost of the best schedule relative to static lower
      // bound

      auto isEnumerated = [&]() { return (!isLstOptml) ? "True" : "False"; }(); //TODO: CHIPPIE: What to do about this? initialScheduleOptimal?

      auto isOptimal = [&]() {
        return (isLstOptml || (rslt == RES_SUCCESS)) ? "True" : "False"; //TODO: CHIPPIE: What to do about this? initialScheduleOptimal?
      }();

      auto isPerpHigherThanHeuristic = [&]() {
        auto getSumPerp = [&](InstSchedule *sched) {
          const InstCount *regPressures = nullptr;
          auto regTypeCount = sched->GetPeakRegPressures(regPressures);
          InstCount sumPerp = 0;
          for (int i = 0; i < regTypeCount; ++i) {
            int perp = regPressures[i] - machMdl_->GetPhysRegCnt(i);
            if (perp > 0)
              sumPerp += perp;
          }
          return sumPerp;
        };

        if (lstSched == bestSched) //TODO: CHIPPIE: What to do about this? Just check against the initial schedule?
          return "False";

        auto heuristicPerp = getSumPerp(lstSched);
        auto bestPerp = getSumPerp(bestSched);

        return (bestPerp > heuristicPerp) ? "True" : "False";
      }();

      Logger::Info("SLIL stats: DAG %s static LB %d gap size %d enumerated %s "
                   "optimal %s PERP higher %s",
                   dataDepGraph_->GetDagID(), costLwrBound_, bestCost_,
                   isEnumerated, isOptimal, isPerpHigherThanHeuristic);
    }
  }
#endif
#if defined(IS_DEBUG_FINAL_SPILL_COST)
  // (Chris): Unconditionally Print out the spill cost of the final schedule.
  // This makes it easy to compare results.
  Logger::Info("Final spill cost is %d for DAG %s.", bestSched_->GetSpillCost(),
               dataDepGraph_->GetDagID());
#endif
#if defined(IS_DEBUG_PRINT_PEAK_FOR_ENUMERATED)
  if (!isLstOptml) {
    InstCount maxSpillCost = 0;
    for (int i = 0; i < dataDepGraph_->GetInstCnt(); ++i) {
      if (bestSched->GetSpillCost(i) > maxSpillCost)
        maxSpillCost = bestSched->GetSpillCost(i);
    }
    Logger::Info("DAG %s PEAK %d", dataDepGraph_->GetDagID(), maxSpillCost);
  }
#endif
  return rslt;
}

FUNC_RESULT SchedRegion::Optimize_(Milliseconds startTime,
                                   Milliseconds rgnTimeout,
                                   Milliseconds lngthTimeout) {
  Enumerator *enumrtr;
  FUNC_RESULT rslt = RES_SUCCESS;

  enumCrntSched_ = AllocNewSched_();
  enumBestSched_ = AllocNewSched_();

  InstCount initCost = bestCost_;
  enumrtr = AllocEnumrtr_(lngthTimeout);
  rslt = Enumerate_(startTime, rgnTimeout, lngthTimeout);

  Milliseconds solnTime = Utilities::GetProcessorTime() - startTime;

#ifdef IS_DEBUG_NODES
  Logger::Info("Examined %lld nodes.", enumrtr->GetNodeCnt());
#endif
  stats::nodeCount.Record(enumrtr->GetNodeCnt());
  stats::solutionTime.Record(solnTime);

  InstCount imprvmnt = initCost - bestCost_;
  if (rslt == RES_SUCCESS) {
    Logger::Info("DAG solved optimally in %lld ms with "
                 "length=%d, spill cost = %d, tot cost = %d, cost imp=%d.",
                 solnTime, bestSchedLngth_, bestSched_->GetSpillCost(),
                 bestCost_, imprvmnt);
    stats::solvedProblemSize.Record(dataDepGraph_->GetInstCnt());
    stats::solutionTimeForSolvedProblems.Record(solnTime);
  } else {
    if (rslt == RES_TIMEOUT) {
      Logger::Info("DAG timed out with "
                   "length=%d, spill cost = %d, tot cost = %d, cost imp=%d.",
                   bestSchedLngth_, bestSched_->GetSpillCost(), bestCost_,
                   imprvmnt);
    }
    stats::unsolvedProblemSize.Record(dataDepGraph_->GetInstCnt());
  }

  return rslt;
}

void SchedRegion::CmputLwrBounds_(bool useFileBounds) {
  RelaxedScheduler *rlxdSchdulr = NULL;
  RelaxedScheduler *rvrsRlxdSchdulr = NULL;
  InstCount rlxdUprBound = dataDepGraph_->GetAbslutSchedUprBound();

  switch (lbAlg_) {
  case LBA_LC:
    rlxdSchdulr = new LC_RelaxedScheduler(dataDepGraph_, machMdl_, rlxdUprBound,
                                          DIR_FRWRD);
    rvrsRlxdSchdulr = new LC_RelaxedScheduler(dataDepGraph_, machMdl_,
                                              rlxdUprBound, DIR_BKWRD);
    break;
  case LBA_RJ:
    rlxdSchdulr = new RJ_RelaxedScheduler(dataDepGraph_, machMdl_, rlxdUprBound,
                                          DIR_FRWRD, RST_STTC);
    rvrsRlxdSchdulr = new RJ_RelaxedScheduler(
        dataDepGraph_, machMdl_, rlxdUprBound, DIR_BKWRD, RST_STTC);
    break;
  }

  if (rlxdSchdulr == NULL || rvrsRlxdSchdulr == NULL) {
    Logger::Fatal("Out of memory.");
  }

  InstCount frwrdLwrBound = 0;
  InstCount bkwrdLwrBound = 0;
  frwrdLwrBound = rlxdSchdulr->FindSchedule();
  bkwrdLwrBound = rvrsRlxdSchdulr->FindSchedule();
  InstCount rlxdLwrBound = std::max(frwrdLwrBound, bkwrdLwrBound);

  assert(rlxdLwrBound >= schedLwrBound_);

  if (rlxdLwrBound > schedLwrBound_)
    schedLwrBound_ = rlxdLwrBound;

#ifdef IS_DEBUG_PRINT_BOUNDS
  dataDepGraph_->PrintLwrBounds(DIR_FRWRD, Logger::GetLogStream(),
                                "Relaxed Forward Lower Bounds");
  dataDepGraph_->PrintLwrBounds(DIR_BKWRD, Logger::GetLogStream(),
                                "Relaxed Backward Lower Bounds");
#endif

  if (useFileBounds)
    UseFileBounds_();

  costLwrBound_ = CmputCostLwrBound();

  delete rlxdSchdulr;
  delete rvrsRlxdSchdulr;
}

//TODO: CHIPPIE: This function needs to not use hurstcCost_? Because what if ACO is happening right now...?
bool SchedRegion::CmputUprBounds_(InstSchedule *schedule, bool useFileBounds) {
  if (useFileBounds) { //TODO: CHIPPIE: Why?
    hurstcCost_ = dataDepGraph_->GetFileCostUprBound();
    hurstcCost_ -= GetCostLwrBound();
  }

  if (bestCost_ == 0) {
    // If the heuristic schedule is optimal, we are done!
    schedUprBound_ = bestSchedLngth_;
    return true;
  } else if (isSecondPass) {
    // In the second pass, the upper bound is the length of the min-RP schedule
    // that was found in the first pass with stalls inserted.
    schedUprBound_ = schedule->GetCrntLngth();
    return false;
  } else {
    CmputSchedUprBound_();
    return false;
  }
}

void SchedRegion::UpdateScheduleCost(InstSchedule *schedule) {
  InstCount crntExecCost;
  CmputNormCost_(schedule, CCM_STTC, crntExecCost, false);
  // no need to return anything as all results can be found in the schedule
}

SPILL_COST_FUNCTION SchedRegion::GetSpillCostFunc() { return spillCostFunc_; }

void SchedRegion::HandlEnumrtrRslt_(FUNC_RESULT rslt, InstCount trgtLngth) {
  switch (rslt) {
  case RES_FAIL:
    //    #ifdef IS_DEBUG_ENUM_ITERS
    Logger::Info("No feasible solution of length %d was found.", trgtLngth);
    //    #endif
    break;
  case RES_SUCCESS:
#ifdef IS_DEBUG_ENUM_ITERS
    Logger::Info("Found a feasible solution of length %d.", trgtLngth);
#endif
    break;
  case RES_TIMEOUT:
    //    #ifdef IS_DEBUG_ENUM_ITERS
    Logger::Info("Enumeration timedout at length %d.", trgtLngth);
    //    #endif
    break;
  case RES_ERROR:
    Logger::Info("The processing of DAG \"%s\" was terminated with an error.",
                 dataDepGraph_->GetDagID(), rgnNum_);
    break;
  case RES_END:
    //    #ifdef IS_DEBUG_ENUM_ITERS
    Logger::Info("Enumeration ended at length %d.", trgtLngth);
    //    #endif
    break;
  }
}

void SchedRegion::RegAlloc_(InstSchedule *&bestSched, InstSchedule *&lstSched) {
  std::unique_ptr<LocalRegAlloc> u_regAllocBest = nullptr;
  std::unique_ptr<LocalRegAlloc> u_regAllocList = nullptr;

  if (SchedulerOptions::getInstance().GetString(
          "SIMULATE_REGISTER_ALLOCATION") == "HEURISTIC" ||
      SchedulerOptions::getInstance().GetString(
          "SIMULATE_REGISTER_ALLOCATION") == "BOTH" ||
      SchedulerOptions::getInstance().GetString(
          "SIMULATE_REGISTER_ALLOCATION") == "TAKE_SCHED_WITH_LEAST_SPILLS") {
    // Simulate register allocation using the heuristic schedule.
    u_regAllocList = std::unique_ptr<LocalRegAlloc>(
        new LocalRegAlloc(lstSched, dataDepGraph_));

    u_regAllocList->SetupForRegAlloc();
    u_regAllocList->AllocRegs();

    std::string id(dataDepGraph_->GetDagID());
    std::string heur_ident(" ***heuristic_schedule***");
    std::string ident(id + heur_ident);

    u_regAllocList->PrintSpillInfo(ident.c_str());
  }
  if (SchedulerOptions::getInstance().GetString(
          "SIMULATE_REGISTER_ALLOCATION") == "BEST" ||
      SchedulerOptions::getInstance().GetString(
          "SIMULATE_REGISTER_ALLOCATION") == "BOTH" ||
      SchedulerOptions::getInstance().GetString(
          "SIMULATE_REGISTER_ALLOCATION") == "TAKE_SCHED_WITH_LEAST_SPILLS") {
    // Simulate register allocation using the best schedule.
    u_regAllocBest = std::unique_ptr<LocalRegAlloc>(
        new LocalRegAlloc(bestSched, dataDepGraph_));

    u_regAllocBest->SetupForRegAlloc();
    u_regAllocBest->AllocRegs();

    u_regAllocBest->PrintSpillInfo(dataDepGraph_->GetDagID());
    totalSimSpills_ = u_regAllocBest->GetCost();
  }

  if (SchedulerOptions::getInstance().GetString(
          "SIMULATE_REGISTER_ALLOCATION") == "TAKE_SCHED_WITH_LEAST_SPILLS")
    if (u_regAllocList->GetCost() < u_regAllocBest->GetCost()) {
      bestSched = lstSched;
#ifdef IS_DEBUG
      Logger::Info(
          "Taking list schedule becuase of less spilling with simulated RA.");
#endif
    }
}

void SchedRegion::InitSecondPass() { isSecondPass = true; }

FUNC_RESULT SchedRegion::runACO(InstSchedule *returnSched, InstSchedule *initSched) {
  InitForSchdulng();
  ACOScheduler *acoSchdulr = new ACOScheduler(dataDepGraph_, machMdl_, abslutSchedUprBound_, hurstcPrirts_, vrfySched_);
  acoSchdulr->setInitialSched(initSched);
  FUNC_RESULT rslt = acoSchdulr->FindSchedule(returnSched, this);
  delete acoSchdulr;
  return rslt;
}

void SchedRegion::compareSchedules(InstSchedule *first, InstSchedule *second, InstSchedule *&third) {
  InstCount firstCost = first->GetCost();
  InstCount secondCost = second->GetCost();

  // Instances where costs are equal, take sched. length into account
  if (firstCost == secondCost) {
    Logger::Info("Both schedule had equal cost. Taking first sched!");
    third = first;
  }
  // First has better cost than second
  else if (firstCost < secondCost) {
    Logger::Info("The first schedule was better than the second!");
    third = first;
  }
  // Second has better cost than First
  else if (firstCost > secondCost) {
    Logger::Info("The second schedule was better than the second!");
    third = second;
  }
 }

