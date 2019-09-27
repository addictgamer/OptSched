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

FUNC_RESULT SchedRegion::FindOptimalSchedule( //TODO: CHIPPIE: Add helper functions as private functions in the class.
    Milliseconds rgnTimeout, Milliseconds lngthTimeout, bool &isLstOptml,
    InstCount &bestCost, InstCount &bestSchedLngth, InstCount &hurstcCost,
    InstCount &hurstcSchedLngth, InstSchedule *&bestSched, bool filterByPerp,
    const BLOCKS_TO_KEEP blocksToKeep) {
  ConstrainedScheduler *lstSchdulr;
  ConstrainedScheduler *acoSchdulr;
  InstSchedule *lstSched = NULL;
  InstSchedule *acoSched = NULL;
  llvm::opt_sched::InstCount ACOScheduleLength; //TODO: CHIPPIE: Initialization value(s)? //TODO: Chippie: What is up with the similarly-named variable in the header file? InstCount acoScheduleLength_; in sched_region.h
  InstCount ACOScheduleCost;
  bool isACOOptimal = false; //TODO: CHIPPIE: Where should this go? Should it become an additional parameter? Why is isLstOptml a reference parameter? Or don't add it as a parameter -- just rename the existing one???
  InstSchedule *initialSched = NULL;
  bool initialScheduleOptimal = false;
  llvm::opt_sched::InstCount initialScheduleLength; //TODO: CHIPPIE: Initialization value(s)?
  FUNC_RESULT rslt = RES_SUCCESS;
  Milliseconds hurstcTime = 0;
  Milliseconds boundTime = 0;
  Milliseconds enumTime = 0;
  Milliseconds vrfyTime = 0;
  Milliseconds acoTime = 0;
  Milliseconds acoStart = 0;
  Milliseconds boundStart;

  enumCrntSched_ = NULL;
  enumBestSched_ = NULL;
  bestSched = bestSched_ = NULL;

  //TODO: CHIPPIE: Perhaps rename these to match the flag?
  bool run_heur_sched = SchedulerOptions::getInstance().GetBool("HEUR_ENABLED");
  bool run_aco_sched = SchedulerOptions::getInstance().GetBool("ACO_ENABLED");
  bool run_bb_sched = SchedulerOptions::getInstance().GetBool("BB_ENABLED");

  if (false == run_heur_sched && false == run_aco_sched) //TODO: CHIPPIE: Return error if ACO & the heuristic are disabled. Don't care about B&B, it may be disabled, or it may not, in any combination. As long as at least one of the heuristic or ACO are enabled.
  {
    //Abort if ACO and heuristic algorithms are disabled.
    cout << "TODO: Descriptive error message here saying that there must be at least one of the ACO or Heuristic scheduler enabled.\n";
    return RES_ERROR;
  }

	/*
	 * Algorithm run order:
	 * 1) Heuristic
	 * 2) ACO
	 * 3) Branch & Bound
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

  if (run_heur_sched) {
    cout << "TODO: Heuristic Scheduler is enabled.\n"; //TODO: Remove this debugging line when done.
    Milliseconds hurstcStart = Utilities::GetProcessorTime();
    lstSched = new InstSchedule(machMdl_, dataDepGraph_, vrfySched_);
    if (lstSched == NULL)
      Logger::Fatal("Out of memory.");

    lstSchdulr = AllocHeuristicScheduler_(); //TODO: CHIPPIE: This one currently calls the heuristic allocator for the ACO scheduler. Need to move that up here, and run ACO anyway, if ACO is enabled...

    // Step #1: Find the heuristic schedule.
    rslt = lstSchdulr->FindSchedule(lstSched, this);

    if (rslt != RES_SUCCESS) {
      Logger::Info("List scheduling failed");
      delete lstSchdulr;
      delete lstSched;
      return rslt;
    }

    //TODO: CHIPPIE: Need to do this both for ACO and the HEURISTIC scheduler? Think so, yes...since ACO will currently run this.
    hurstcTime = Utilities::GetProcessorTime() - hurstcStart;
    stats::heuristicTime.Record(hurstcTime);
    if (hurstcTime > 0)
      Logger::Info("Heuristic_Time %d", hurstcTime);

  #ifdef IS_DEBUG_SLIL_PRINTOUT
    if (OPTSCHED_gPrintSpills) {
      const auto &slilVector = this->GetSLIL_();
      for (int j = 0; j < slilVector.size(); j++) {
        Logger::Info(
            "SLIL after Heuristic Scheduler for dag %s Type %d %s is %d.",
            dataDepGraph_->GetDagID(), j, machMdl_->GetRegTypeName(j).c_str(),
            slilVector[j]);
      }
    }
  #endif

    boundStart = Utilities::GetProcessorTime();
    hurstcSchedLngth_ = lstSched->GetCrntLngth(); //TODO: CHIPPIE: Need to do this both for ACO and the HEURISTIC scheduler.

    //The heuristic is the first schedule to run, so guaranteed to provide the initial values for these variables.
    initialSched = lstSched;
    initialScheduleLength = hurstcSchedLngth_;
    bestSchedLngth_ = hurstcSchedLngth_;
    assert(bestSchedLngth_ >= schedLwrBound_);
    bestSched = bestSched_ = lstSched;

    // Step #2: Compute the lower bounds and cost upper bound.
    if (rgnTimeout == 0) //TODO: CHIPPIE: NOTE: This was a hack to disable B&B before these scheduler enabling flags tasks.
      costLwrBound_ = CmputCostLwrBound();
    else
      CmputLwrBounds_(false); //TODO: CHIPPIE: I highly suspect that this needs to run before the upper bound & is_optimal checks...YUP. Check line 760 of this file.
    assert(schedLwrBound_ <= initialSched->GetCrntLngth());

    //TODO: CHIPPIE: I don't like doing this before checking if it's optimal, in ACO...
    InstCount hurstcExecCost;
    Config &schedIni = SchedulerOptions::getInstance();
    if (!schedIni.GetBool("USE_ACO", false)) { //TODO: CHIPPIE: What does this flag do? Doesn't seem to actually disable ACO...
      CmputNormCost_(lstSched, CCM_DYNMC, hurstcExecCost, true);
    } else {
      CmputNormCost_(lstSched, CCM_STTC, hurstcExecCost, false);
    }
    hurstcCost_ = lstSched->GetCost();
    isLstOptml = CmputUprBounds_(lstSched, false);

    boundTime = Utilities::GetProcessorTime() - boundStart;
    stats::boundComputationTime.Record(boundTime); //TODO: CHIPPIE: Does ACO need this too?

    FinishHurstc_(); //TODO: CHIPPIE: Need one for ACO. Will need to also add some new statistic for the ACO counterparts.

    //  #ifdef IS_DEBUG_SOLN_DETAILS_1
    Logger::Info(
        "The list schedule is of length %d and spill cost %d. Tot cost = %d",
        bestSchedLngth_, lstSched->GetSpillCost(), bestCost_);
    //  #endif

  #ifdef IS_DEBUG_PRINT_SCHEDS
    lstSched->Print(Logger::GetLogStream(), "Heuristic");
  #endif
  #ifdef IS_DEBUG_PRINT_BOUNDS
    dataDepGraph_->PrintLwrBounds(DIR_FRWRD, Logger::GetLogStream(),
                                  "CP Lower Bounds");
  #endif

    if (rgnTimeout == 0) //TODO: CHIPPIE: NOTE: This was a hack to disable B&B before these scheduler enabling flags task.
      isLstOptml = true;

    if (isLstOptml)
    {
      initialScheduleOptimal = true;
      cout << "[CHIPPIE: DEBUG] ***** HEURISTIC SCHEDULE IS OPTIMAL *****\n"; //TODO: CHIPPIE: REMOVE DEBUGGING STATEMENT.
    }

    //TODO: CHIPPIE: Does ACO need this? Don't think so...
    // (Chris): If the cost function is SLIL, then the list schedule is considered
    // optimal if PERP is 0.
    if (filterByPerp && !isLstOptml && spillCostFunc_ == SCF_SLIL) { //TODO: Need to check if heuristic is optimal before ACO. And then check again after ACO.
    //TODO: To determine if the list is optimal, need to do the lower bound between list and aco.
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

  #if defined(IS_DEBUG_SLIL_OPTIMALITY) //TODO: CHIPPIE: Does ACO need this?
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
    if (EnableEnum_() == false) { //TODO: CHIPPIE: Does ACO need this?
      delete lstSchdulr;
      return RES_FAIL;
    }
  }

  // Step #3: Try to find the optimal schedule with ACO if the heuristic was not optimal. //TODO: CHIPPIE: Make it happen.

  cout << " ### BLARG ### \n";
  // LLVM_DEBUG(dbgs() << " *** LLVM_DEBUG BLARG *** \n");
  // Logger::Info(" *** LOGGER INFO BLARG *** \n");

  if (run_aco_sched && false == initialScheduleOptimal) { //TODO: CHIPPIE: If the Heuristic algorithm already produced the optimal result, don't run ACO or B&B.
    //TODO: CHIPPIE: If ACO's schedule is optimal, set the best schedule to that (and don't run B&B).
    //TODO: CHIPPIE: If neither ACO's or the Heuristic's schedule is optimal, compare ACO's result with the heuristic's and then set the initial_schedule to that.

    cout << "TODO: ACO Scheduler is enabled.\n"; //TODO: Remove this debugging line when done.
    acoStart = Utilities::GetProcessorTime();
    acoSched = new InstSchedule(machMdl_, dataDepGraph_, vrfySched_);
    if (acoSched == NULL) {
      Logger::Fatal("Out of memory.");
    }

    acoSchdulr = new ACOScheduler(dataDepGraph_, machMdl_, abslutSchedUprBound_, hurstcPrirts_);

    rslt = acoSchdulr->FindSchedule(acoSched, this);

    if (rslt != RES_SUCCESS) {
      Logger::Info("ACO scheduling failed");
      if (run_heur_sched)
      {
        delete lstSchdulr;
        delete lstSched;
      }
      delete acoSchdulr;
      delete acoSched;
      return rslt;
    }

    acoTime = Utilities::GetProcessorTime() - acoStart;
    stats::acoTime.Record(acoTime);
    if (acoTime > 0) {
      Logger::Info("ACO_Time %d", acoTime);
    }

#ifdef IS_DEBUG_SLIL_PRINTOUT //TODO: CHIPPIE: What is this and is it needed here? (Copied from the Heuristic block)
    if (OPTSCHED_gPrintSpills) {
      const auto &slilVector = this->GetSLIL_();
      for (int j = 0; j < slilVector.size(); j++) {
        Logger::Info(
            "SLIL after ACO Scheduler for dag %s Type %d %s is %d.",
            dataDepGraph_->GetDagID(), j, machMdl_->GetRegTypeName(j).c_str(),
            slilVector[j]);
      }
    }
#endif

    boundStart = Utilities::GetProcessorTime(); //TODO: CHIPPIE: Need this?
    acoScheduleLength_ = acoSched->GetCrntLngth();
    ACOScheduleCost = acoSched->GetCost(); //TODO: CHIPPIE: Compare non-optimal schedules with this.

    if (rgnTimeout == 0) //TODO: CHIPPIE: NOTE: This was a hack to disable B&B before these scheduler enabling flags task.
      isACOOptimal = true;

    //If the Heuristic schedule did not compute the lower bound, need to do it now. //TODO: CHIPPIE: Can it be computed prior to running either the heuristic or ACO scheduler?
    if (false == run_heur_sched)
    {
      //Run initial lower-bound computation.
      if (rgnTimeout == 0) //TODO: CHIPPIE: NOTE: This was a hack to disable B&B before these scheduler enabling flags task.
        costLwrBound_ = CmputCostLwrBound();
      else
        CmputLwrBounds_(false); //TODO: CHIPPIE: I highly suspect that this needs to run before the upper bound & is_optimal checks...YUP. Check line 760 of this file.
      assert(schedLwrBound_ <= initialSched->GetCrntLngth());
    }

    //TODO: CHIPPIE: Add in the upper bound code here.

    InstCount ACOExecCost;
    Config &schedIni = SchedulerOptions::getInstance();
    if (!schedIni.GetBool("USE_ACO", false)) { //TODO: CHIPPIE: What does this flag do? Doesn't seem to actually disable ACO...
      CmputNormCost_(acoSched, CCM_DYNMC, ACOExecCost, true);
    } else {
      CmputNormCost_(acoSched, CCM_STTC, ACOExecCost, false);
    }
    ACOScheduleCost = acoSched->GetCost();
    isACOOptimal = CmputUprBounds_(acoSched, false);
    boundTime = Utilities::GetProcessorTime() - boundStart;
    stats::boundComputationTime.Record(boundTime); //TODO: CHIPPIE: Need this?

    //TODO: CHIPPIE: ACO should not change the upper bound unless it is better (i.e. lower) than the heuristic's.

    if (isACOOptimal)
    {
      cout << "[CHIPPIE: DEBUG] ***** ACO SCHEDULE IS OPTIMAL *****\n"; //TODO: CHIPPIE: REMOVE DEBUGGING STATEMENT.
    }

    //There are 3 possible situations:
    // A) Heuristic was never run. In that case, just use ACO and run with its results, into B&B.
    // B) Heuristic was not optimal, but ACO is. In that case, just use ACO's result for the initial schedule AND the best schedule. And don't run B&B, exit the function (since B&B only runs if the optimal schedule was not found).
    // C) Neither scheduler was optimal. In that case, compare the two schedules and use the one that's better as the input (initialSched) for B&B.

    if (false == run_heur_sched || isACOOptimal || ACOScheduleCost > hurstcCost_) //If the heuristic was not run (and thus no initial schedule was set), or if the heuristic schedule is not optimal but ACO's is, or if neither schedule is optimal but ACO's is better, then set the initial and best schedule to ACO's.
    {
      //TODO: CHIPPIE: Do everything anyway.
      //TODO: CHIPPIE: Determine what needs to be done between both? And determine what needs to be done in the case of heuristic schedule already having run?
      initialSched = acoSched;
      initialScheduleLength = ACOScheduleLength;
      bestSchedLngth_ = initialScheduleLength;
      assert(bestSchedLngth_ >= schedLwrBound_);
      bestSched = bestSched_ = acoSched;

      if (isACOOptimal)
      {
        initialScheduleOptimal = true;
      }
      else
      {
        initialScheduleOptimal = false;
      }

      //TODO: CHIPPIE: Not done with this portion?
      //In the original, the thing that came next was the heuristic lower bound computation. Then the heuristic upper bound computation. Or something liek that.
    }
    else
    {
      //TODO: CHIPPIE: Find a way to do this better.

      //So, presently. To find if a schedule is optimal, that's done while computing the upper bound.
      //Guess what? When the upper bound is calculated, it gets saved.
      //So what happens if the ACO schedule should not be used, and instead the heuristic schedule should be used?
      //Weeeeell...the compute upper bound code (and possibly other fragments, TODO: CHIPPIE: investigate the lower bound code)
      //overwrites whatever the previous stored upper bound is.
      //So if decide to go with the heuristic, then need to recalculate the initial schedule stuff, and the bounds, and TODO: CHIPPIE: determine if there are any other things that must be recalculated before entering B&B.

      //TODO: CHIPPIE: Presently, I'm doing this right before B&B.
    }
    

    //TODO: CHIPPIE: What if ACO is not the best?

    Logger::Info(
        "The ACO schedule is of length %d and spill cost %d. Tot cost = %d",
        acoScheduleLength_, lstSched->GetSpillCost(), bestCost_);

    /*
    //TODO: CHIPPIE: Need to modify this section to not _assign_ it, but to compare with the current best (which could only be the heuristic scheduler...unless that scheduler is disabled) and replace.
    bestSchedLngth_ = acoScheduleLength_;
    assert(bestSchedLngth_ >= schedLwrBound_); //TODO: But should it be an assertion...?
    bestSched = bestSched_ = lstSched; //TODO: CHIPPIE: Don't assign...check if better and replace.
    */

    //TODO: CHIPPIE: There's some other stuff that the old combined heuristic-aco scheduler code has...what of that needs to be copied, and how does it need to be modified?

    //TODO: CHIPPIE: Also, there's a bunch of debug prints and stuff. What do we want done here too?
  } else {
    cout << "TODO: ACO Scheduler is not enabled.\n"; //TODO: CHIPPIE: Remove this when done debugging.
  }

  // Step #4: Find the optimal schedule if the heuristc was not optimal.
  Milliseconds enumStart = Utilities::GetProcessorTime();

#ifdef IS_DEBUG_BOUNDS
  Logger::Info("Sched LB = %d, Sched UB = %d", schedLwrBound_, schedUprBound_);
#endif

  if (run_bb_sched) {
    //Make sure the bounds information are all correct with the chosen initial schedule.
    //A) Upper bound.
    Config &schedIni = SchedulerOptions::getInstance(); //TODO: CHIPPIE: Instead of (potentially) calling this up to like 3 times, make this global to the function, up at the top.
    InstCount ACOExecCost;
    if (!schedIni.GetBool("USE_ACO", false)) { //TODO: CHIPPIE: What does this flag do? Doesn't seem to actually disable ACO...
      CmputNormCost_(initialSched, CCM_DYNMC, ACOExecCost, true);
    } else {
      CmputNormCost_(initialSched, CCM_STTC, ACOExecCost, false);
    }
    CmputUprBounds_(initialSched, false);

    cout << "TODO: BB scheduler is enabled.\n";
    //isLstOptml = false; //TODO: CHIPPIE: Remove this when done debugging. //Yes, this flow works correctly.
    if (false == initialScheduleOptimal) { //TODO: CHIPPIE: Should do a similar check for if ACO is optimal. This should be more generic, like: //(Call it initial schedule (for B&B)) //TODO: Add a isScheduleOptimal flag.
                               //if (isCurrentBestScheduleOptimal == false) instead of explicitly looking at the list schedule.
                               //ALSO: Need to change the first part to something more like:
                               //if ((!run_heur_sched && !run_aco_sched) || ...) //then we have to run the BB algorithm.


                               //TODO: CHIPPIE: ALSO. The run_aco_sched block will need to do the same sort of check...
      cout << "TODO: Running BB scheduler...\n";
      dataDepGraph_->SetHard(true);
      rslt = Optimize_(enumStart, rgnTimeout, lngthTimeout); //TODO: CHIPPIE: This function will use the Branch and Bound algorithm.
      //TODO: CHIPPIE: Also. It currently fails with upper bounds if the heuristic and ACO are disabled...two observations:
      // * there should be some sort of initialization for that probably.
      // * ACO will need to be updated to set the upper bound properly too, since this issue occurs even if ACO is enabled (with the present code)
      Milliseconds enumTime = Utilities::GetProcessorTime() - enumStart;

      if (hurstcTime > 0) {
        enumTime /= hurstcTime;
        stats::enumerationToHeuristicTimeRatio.Record(enumTime);
      }

      if (bestCost_ < hurstcCost_) {
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
      Logger::Info("The list schedule of length %d and cost %d is optimal.",
                  bestSchedLngth_, bestCost_);
    }

    //TODO: CHIPPIE: Should this also be part of the BB_ENABLED flag? Or does it need to always run regardless?
    if (rgnTimeout != 0) {
      bool optimalSchedule = isLstOptml || (rslt == RES_SUCCESS); //TODO: CHIPPIE: Looks like it is, since the last rslt comes from the bb call up a few dozen lines, rslt = Optimize_(enumStart, rgnTimeout, lngthTimeout);
      Logger::Info("Best schedule for DAG %s has cost %d and length %d. The "
                  "schedule is %s",
                  dataDepGraph_->GetDagID(), bestCost_, bestSchedLngth_,
                  optimalSchedule ? "optimal" : "not optimal");
    }
  }

  //TODO: CHIPPIE: Everything hereafter, should it run for _all_ of the schedulers? Regardless of which ones are enabled?
  //I.e. are the following blocks of code BB specific? (Doesn't look it...)

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
    RegAlloc_(bestSched, lstSched);
    //#endif
  }

  enumTime = Utilities::GetProcessorTime() - enumStart;
  stats::enumerationTime.Record(enumTime);

  Milliseconds vrfyStart = Utilities::GetProcessorTime();

  if (vrfySched_) {
    bool isValidSchdul = bestSched->Verify(machMdl_, dataDepGraph_);

    if (isValidSchdul == false) {
      stats::invalidSchedules++;
    }
  }

  vrfyTime = Utilities::GetProcessorTime() - vrfyStart;
  stats::verificationTime.Record(vrfyTime);

  InstCount finalLwrBound = costLwrBound_;
  InstCount finalUprBound = costLwrBound_ + bestCost_;
  if (rslt == RES_SUCCESS)
    finalLwrBound = finalUprBound;

  dataDepGraph_->SetFinalBounds(finalLwrBound, finalUprBound);

  FinishOptml_(); //TODO: CHIPPIE: Everything looks non-BB-specific except this? Maybe?

  //TODO: CHIPPIE: Need to make this an up-to 3-way comparison since ACO has now entered the mix as a separate scheduler.
  bool tookBest = ChkSchedule_(bestSched, lstSched);
  if (tookBest == false) {
    bestCost_ = hurstcCost_;
    bestSchedLngth_ = hurstcSchedLngth_;
  }

  if (run_heur_sched){
    delete lstSchdulr;
    if (bestSched != lstSched)
      delete lstSched;
  }
  if (run_aco_sched) {
    delete acoSchdulr;
    if (bestSched != acoSched) {
      delete acoSched;
    }
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
    bool optimal = isLstOptml || (rslt == RES_SUCCESS); //TODO: CHIPPIE: This also needs to be updated to account for the heuristic enabling/disabled, and the splitoff of ACO from it.
    if ((blocksToKeep == BLOCKS_TO_KEEP::ZERO_COST && bestCost != 0) ||
        (blocksToKeep == BLOCKS_TO_KEEP::OPTIMAL && !optimal) ||
        (blocksToKeep == BLOCKS_TO_KEEP::IMPROVED &&
         !(bestCost < hurstcCost)) ||
        (blocksToKeep == BLOCKS_TO_KEEP::IMPROVED_OR_OPTIMAL &&
         !(optimal || bestCost < hurstcCost))) {
      delete bestSched;
      bestSched = nullptr;
      return rslt;
    }
  }
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
    if (!isLstOptml) {
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

      auto isEnumerated = [&]() { return (!isLstOptml) ? "True" : "False"; }();

      auto isOptimal = [&]() {
        return (isLstOptml || (rslt == RES_SUCCESS)) ? "True" : "False";
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

        if (lstSched == bestSched)
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
#if defined(IS_DEBUG_PRINT_PEAK_FOR_ENUMERATED)//TODO: CHIPPIE: This block will likewise need to be updated...I note that there are some references to isLstOptml, which will need to be updated if the heuristic scheduler is disabled, and also may need to be changed to account for ACO.
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
  rslt = Enumerate_(startTime, rgnTimeout, lngthTimeout); //TODO: CHIPPIE: Actually runs the Branch and Bound algorithm.

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

bool SchedRegion::CmputUprBounds_(InstSchedule *lstSched, bool useFileBounds) {
  if (useFileBounds) {
    hurstcCost_ = dataDepGraph_->GetFileCostUprBound();
    hurstcCost_ -= GetCostLwrBound();
  }

  bestCost_ = hurstcCost_;
  bestSchedLngth_ = hurstcSchedLngth_;

  if (bestCost_ == 0) {
    // If the heuristic schedule is optimal, we are done!
    schedUprBound_ = lstSched->GetCrntLngth();
    return true;
  } else if (isSecondPass) {
    // In the second pass, the upper bound is the length of the min-RP schedule
    // that was found in the first pass with stalls inserted.
    schedUprBound_ = lstSched->GetCrntLngth();
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
