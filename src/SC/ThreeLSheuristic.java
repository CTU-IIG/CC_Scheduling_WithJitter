 /*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package SC;

import ilog.concert.IloException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 *
 * @author annaminaeva
 */
public class ThreeLSheuristic {
    private ProbInstSched probInstSched;
    private ScheduledActs scheduledActs;
    private List<Integer> actsToSchedule;
    private List<Integer> scheduledFromScratch;
    private SubModel subModel;
    
    private int numActivities;

    public ThreeLSheuristic(ProbInstSched problemInstanceScheduling, SubModel subModelRO) throws IloException {
        this.subModel = subModelRO;
        this.probInstSched = problemInstanceScheduling;
        numActivities = problemInstanceScheduling.getNumActs();
        actsToSchedule = new ArrayList<>();
        scheduledFromScratch =  new ArrayList();
        
        if(subModelRO != null){
            if(subModelRO.isScheduledByOpt()){
                subModelRO.end();
            }
        }

        scheduledActs = new ScheduledActs(numActivities,
                problemInstanceScheduling);
    }
    
    private void PrintNonScheduledAndNotPlannedToScheduleActivities(){
        ArrayList<Integer> arraylist=new ArrayList<>();
        arraylist.addAll(scheduledActs.getNumbersOfScheduledActivities()); // add first arraylist
        arraylist.addAll(actsToSchedule); // add Second arraylist

        List<Integer> notPreparedToScheduleActivities = Helpers.DifferenceOfTwoSets(Helpers.CreateArrayWithNaturalNumbers(numActivities), arraylist);
        System.out.println("Not scheduled and Not planned to be scheduled activities are: ");
        for(int j = 0; j < notPreparedToScheduleActivities.size(); j++) {
            System.out.println(notPreparedToScheduleActivities.get(j));
        }
    }
    
    //Attention! it changes numbersOfScheduledActivities in scheduledActivities
    private void CheckResultingScheduleOnDuplicates(){
        Collections.sort(scheduledActs.getNumbersOfScheduledActivities());
        for(int i = 0; i < scheduledActs.getNumbersOfScheduledActivities().size() - 1; i++) {
            if(scheduledActs.getNumbersOfScheduledActivities().get(i) == scheduledActs.getNumbersOfScheduledActivities().get(i+1)){
                System.out.println("\n\n\n\n\n\nProblem in result schedule. Some activity is scheduled twice!\n\n\n\n\n\n\n\n");
                System.exit(0);
            }
        }
    }
    
    private solutionOneAct[] SecondLevelOfScheduling(int numActivityToUnscheduleInStartTimesArray, int numActivityToUnschedule,
            Activity activity) throws IloException{
        scheduledActs.UnscheduleActivity(numActivityToUnscheduleInStartTimesArray);
        solutionOneAct[] problemSolutionForTwoActivities = new solutionOneAct[1];

        subModel = new SubModel(activity, scheduledActs, CC_Scheduling_WithJitter.SOLVE_SUBMODEL_BY_ILP);
        if(subModel.isIsFeasible()){
            subModel.scheduleWithTwoActivities(probInstSched.getActs()[numActivityToUnschedule]);
            problemSolutionForTwoActivities = subModel.solveWithTwoActivities();
        }
        
        return problemSolutionForTwoActivities;
    }
    
    public ScheduledActs Solve() throws IloException{
        solutionOneAct problemSolutionForOneActivity = null;
        boolean someActIsCurUnscheduled = false;
        List<Integer> numRootProblem =  new ArrayList();
        
        SortActivitiesAccordingToThePriorityRule();
        
        int nIter = 0;
        while(scheduledActs.getStartTimes().size() < probInstSched.getNumActs()){   
            nIter++;
            int i = Collections.min(actsToSchedule);
            actsToSchedule.remove(actsToSchedule.indexOf(i));
            Activity activity = probInstSched.getActs()[i];
            
            if(nIter == 6){
                System.out.println("");
            }
            
            //schedule activity by activity 
            subModel = new SubModel(activity, scheduledActs, CC_Scheduling_WithJitter.SOLVE_SUBMODEL_BY_ILP);
            System.out.println(nIter);
            if(subModel.isIsFeasible()){
                problemSolutionForOneActivity = subModel.solve();
            }
            
             // if the solution is found and there is no infeasible variables
            if(problemSolutionForOneActivity != null && subModel.isIsFeasible()){
                //problemSolutionForOneActivity.CheckJitter();
                scheduledActs.AddScheduledActivity(problemSolutionForOneActivity.getStartTimes(), i);
                someActIsCurUnscheduled = false;
                
                //add currently released activity to activity to schedule array
                actsToSchedule = new ArrayList<>();
                addActsToActToScheduleArray();
            }
            else{
                //choose activity to unschedule
                int nActToUnschSTArray = scheduledActs.getScheduledActivityToUnschedule(
                        activity.getMapping(), scheduledFromScratch, activity.getAllPredecessors(), numRootProblem);
                
                if(nActToUnschSTArray == -1){
                    return null;
                }
                
                int nActUnsch = scheduledActs.getNumbersOfScheduledActivities().get(nActToUnschSTArray);
                
                if(numRootProblem.contains(nActUnsch)){
                    //return null;
                    solutionOneAct[] solutionTwoActs = 
                            SecondLevelOfScheduling(nActToUnschSTArray, nActUnsch, activity);
                    
                    if(solutionTwoActs != null && subModel.isIsFeasible()){
                        AssignFoundSolutionTwoActs(nActUnsch, solutionTwoActs, i);
                        //solutionTwoActs[0].CheckJitter();
                        //solutionTwoActs[1].CheckJitter();
                    }
                    else{
                        if(!ThirdLevelScheduling(i, nActUnsch)){
                            return null;
                        }
                    }
                    
                    // add unscheduled activities to the top of the array
                    actsToSchedule = new ArrayList<>();
                    addActsToActToScheduleArray();
                    
                    if(!someActIsCurUnscheduled){
                        if(!numRootProblem.contains(i)){
                            numRootProblem.add(i);
                        }
                    }
                    someActIsCurUnscheduled = false;
                }
                else{
                    scheduledActs.UnscheduleActivity(nActToUnschSTArray);
                    actsToSchedule.add(0,i);
                    if(!someActIsCurUnscheduled){
                        if(!numRootProblem.contains(i)){
                            numRootProblem.add(i);
                        }
                    }
                    someActIsCurUnscheduled = true;
                    System.out.println("Unschedule!");
                }
            }
            
            if(subModel.isScheduledByOpt() && CC_Scheduling_WithJitter.SOLVE_SUBMODEL_BY_ILP){
                subModel.end();
            }
            if(subModel.isScheduledByOpt() && !CC_Scheduling_WithJitter.SOLVE_SUBMODEL_BY_ILP){
                subModel.closeContext();
            }
        }
        
        //CheckResultingScheduleOnDuplicates();
        
        return scheduledActs;
    }
    
    private void SortActivitiesAccordingToThePriorityRule(){
        int[] idInArray = new int[numActivities];
        Arrays.sort(probInstSched.getActs());
        for(int i = 0; i < numActivities; i++) {
            idInArray[probInstSched.getActs()[i].getIdInInputData()] = i;
            probInstSched.getActs()[i].setIdInArray(i);
        }
        
        for(int i = 0; i < numActivities; i++) {
            probInstSched.getActs()[i].changePredecessorsAndSuccessorsAfterSorting(idInArray);
        }
        
        for(int i = 0; i < numActivities; i++) {
            if(probInstSched.getActs()[i].getPreds().isEmpty()){
                actsToSchedule.add(i);
            }
        }
    }

    //This method adds all activities that have their precedence constraints satisfied in scheduledActivities array
    private void addActsToActToScheduleArray(){
        for(int j = 0; j < probInstSched.getNumActs(); j++) {
            if(probInstSched.getActs()[j].ArePredecessorsScheduled(scheduledActs.getNumbersOfScheduledActivities())
            && !scheduledActs.getNumbersOfScheduledActivities().contains(j)){
                actsToSchedule.add(j);
            }
        }
    }
    
    private boolean ThirdLevelScheduling(int numActivityCurScheduled, int numActivityToUnschedule) throws IloException{
        
        // if this pair was already scheduled 'from sratch', heuristic returns fail
        if(scheduledFromScratch.contains(numActivityCurScheduled) && scheduledFromScratch.contains(numActivityToUnschedule)){
            return false;
        }
        
        scheduledActs.UnscheduleAllActivitiesButPreviouslyScheduledAndPreceeding(scheduledFromScratch, 
                probInstSched.getActs()[numActivityToUnschedule], 
                probInstSched.getActs()[numActivityCurScheduled]);
        
        subModel = new SubModel(probInstSched.getActs()[numActivityCurScheduled], 
                scheduledActs, CC_Scheduling_WithJitter.SOLVE_SUBMODEL_BY_ILP);
        subModel.scheduleWithTwoActivities(probInstSched.getActs()[numActivityToUnschedule]);
        
        solutionOneAct[] problemSolutionForTwoActivities = subModel.solveWithTwoActivities();
        //scheduledActivities.PrintTheFinalSchedule(problemInstanceScheduling.getnResources(), problemInstanceScheduling.getHP());
                
        if(problemSolutionForTwoActivities == null){
            return false;
        }
        
        AssignFoundSolutionTwoActs(numActivityToUnschedule,
                problemSolutionForTwoActivities, numActivityCurScheduled);
        
        scheduledFromScratch.add(numActivityCurScheduled);
        scheduledFromScratch.add(numActivityToUnschedule);
        for(int i = 0; i < probInstSched.getActs()[numActivityCurScheduled].getAllPredecessors().size(); i++) {
            scheduledFromScratch.add(probInstSched.getActs()[numActivityCurScheduled].getAllPredecessors().get(i));
        }
        for(int i = 0; i < probInstSched.getActs()[numActivityToUnschedule].getAllPredecessors().size(); i++) {
            scheduledFromScratch.add(probInstSched.getActs()[numActivityToUnschedule].getAllPredecessors().get(i));
        }
        
        return true;
    }
   
    private void AssignFoundSolutionTwoActs(int numActivityToUnschedule, 
            solutionOneAct[] problemSolutionForTwoActivities, int numActivityCurrentlyScheduled) throws IloException{
        
        scheduledActs.AddScheduledActivity(problemSolutionForTwoActivities[0].getStartTimes(), numActivityCurrentlyScheduled);
        scheduledActs.AddScheduledActivity(problemSolutionForTwoActivities[1].getStartTimes(), numActivityToUnschedule);
    }
     
}
