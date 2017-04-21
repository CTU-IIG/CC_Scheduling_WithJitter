/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

package SC;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

/**
 *
 * @author minaeann
 */
public class ScheduledActs {
    private List<Integer> numsSchedActs;
    private List<List<Integer>> startTimes;
    private int nJobsScheduled;
    private int[][] schedule;
    List<List<List<Integer>>> intervalsOfResourceConstraints;
    private ProbInstSched probInst;
    static FileWriter writer;

    public List<List<List<Integer>>> getIntsOfResConstrs() {
        return intervalsOfResourceConstraints;
    }

    public List<Integer> getNumbersOfScheduledActivities() {
        return numsSchedActs;
    }
    
    public int getnJobsScheduled() {
        return nJobsScheduled;
    }
     
    public List<List<Integer>> getStartTimes() {
        return startTimes;
    }

    public ProbInstSched getProbInst() {
        return probInst;
    }
    
    public ScheduledActs(int totalNumOfActivities, ProbInstSched problemInstanceScheduling){
        this.startTimes = new ArrayList<List<Integer>>();
        intervalsOfResourceConstraints =  new ArrayList<List<List<Integer>>>();
        
        for(int k = 0; k < problemInstanceScheduling.getnResources(); k++) {
            intervalsOfResourceConstraints.add(new ArrayList<List<Integer>>());
        }
        
        this.numsSchedActs = new ArrayList();
        this.nJobsScheduled = 0;
        this.probInst =  problemInstanceScheduling;
        schedule = new int[problemInstanceScheduling.getnResources()][problemInstanceScheduling.getHP()];
        Helpers.Initialize2dArrayWithValue(schedule, 0);
    }
    
    private void ConcatenateNewIntervalWithExisting(List<Integer> newInterval, int numOfResource){
        numOfResource = numOfResource - 1;
        int numOfIntervalForTheNew;
        for(numOfIntervalForTheNew = 0; numOfIntervalForTheNew < intervalsOfResourceConstraints.get(numOfResource).size(); numOfIntervalForTheNew++) {
            int a = newInterval.get(0);
            int b = newInterval.get(1);
            int c = intervalsOfResourceConstraints.get(numOfResource).get(numOfIntervalForTheNew).get(0);
            int d = intervalsOfResourceConstraints.get(numOfResource).get(numOfIntervalForTheNew).get(1);
            if(c <= a && d >= a || a <= c && b >= c){
                //the existing interval can be changed since the new one extends the old one
                intervalsOfResourceConstraints.get(numOfResource).get(numOfIntervalForTheNew).set(0, Math.min(a, c));
                intervalsOfResourceConstraints.get(numOfResource).get(numOfIntervalForTheNew).set(1, Math.max(b, d));
                
                //concatenate new interval with the next one if possible
                if(numOfIntervalForTheNew + 1 != intervalsOfResourceConstraints.get(numOfResource).size() &&
                        intervalsOfResourceConstraints.get(numOfResource).get(numOfIntervalForTheNew).get(1) >=
                        intervalsOfResourceConstraints.get(numOfResource).get(numOfIntervalForTheNew + 1).get(0)){
                    intervalsOfResourceConstraints.get(numOfResource).get(numOfIntervalForTheNew).set(1, intervalsOfResourceConstraints.get(numOfResource).get(numOfIntervalForTheNew + 1).get(1));
                    intervalsOfResourceConstraints.get(numOfResource).remove(numOfIntervalForTheNew + 1);
                }
                
                return;
            }
            
            if(c >= b && d >= b){
                //we are already beyond the interval order
                break;
            }
        }
        intervalsOfResourceConstraints.get(numOfResource).add(numOfIntervalForTheNew, newInterval); 
    }
    
    private void AddNewResourceIntervalsWithConcatenation(int[] startTimes, int nSchedAct){
        Activity act = probInst.getActs()[nSchedAct];
        int nJobs = probInst.getHP() / act.getPeriod();
    
        for(int j = 0; j < nJobs; j++) {
            for(int i = 0; i < act.getProcTime(); i++) {
                if(schedule[act.getMapping() - 1][(startTimes[j] + i) % probInst.getHP()] != 0){
                    //collision in the schedule
                    int curValue = schedule[act.getMapping() - 1][(startTimes[j] + i) % probInst.getHP()] - 1;
                    System.out.println("\n Collision in the schedule! Activities " + 
                            nSchedAct + " and " + curValue + " are colliding.\n");
                    System.out.println((startTimes[j] + i) % probInst.getHP());
                    //System.exit(0);
                }
                
                schedule[act.getMapping() - 1][(startTimes[j] + i) % probInst.getHP()] = act.getIdInInputData() + 1;
            }
                    
            List<Integer> newInterval;
            if(startTimes[j] < probInst.getHP() && startTimes[j] + act.getProcTime() > probInst.getHP()){
                newInterval = Arrays.asList(startTimes[j], probInst.getHP());
                ConcatenateNewIntervalWithExisting(newInterval,  act.getMapping());
                
                newInterval = Arrays.asList(0, (startTimes[j] + act.getProcTime()) % probInst.getHP());
                ConcatenateNewIntervalWithExisting(newInterval, act.getMapping());
            }
            else{
                newInterval = Arrays.asList(startTimes[j] % probInst.getHP(), 
                    (startTimes[j] + act.getProcTime()) % probInst.getHP());
                if(startTimes[j] + act.getProcTime() == probInst.getHP()){
                    newInterval.set(1, probInst.getHP());
                }
                
                ConcatenateNewIntervalWithExisting(newInterval, act.getMapping());
            }
        }
    }
    
    public boolean AddScheduledActivity(int[] startTimes_, int noOfScheduledActivity){
        if(probInst.isZJ()){
            int numJobsInSchedule = probInst.getHP() / probInst.getActs()[noOfScheduledActivity].getPeriod();
            int[] newStartTimes = new int[numJobsInSchedule];
            for(int i = 0; i < numJobsInSchedule; i++) {
                newStartTimes[i] = startTimes_[0] + i * probInst.getActs()[noOfScheduledActivity].getPeriod();
            }
            startTimes_ = newStartTimes;
        }
        
        nJobsScheduled += startTimes_.length;
        numsSchedActs.add(noOfScheduledActivity);  
        
        startTimes.add(new ArrayList<Integer>());
        for(int i = 0; i < startTimes_.length; i++){
            startTimes.get(startTimes.size() - 1).add(startTimes_[i]);
        }
        AddNewResourceIntervalsWithConcatenation(startTimes_, noOfScheduledActivity);
        
        return true;
    }

    public void PrintFinalSchedule(int nResources, int HP){
        for(int i = 0; i < nResources; i++) {
            System.out.println("Resource "+ (i + 1) + ":");

            for(int j = 0; j < HP; j++) {
                System.out.format("%5d | ", schedule[i][j]);
            }
            
            System.out.println();
            System.out.println();
        }
    }
    
    public Solution convertToSolution(){
        if(numsSchedActs.size() != probInst.getNumActs()){
            System.out.println("NOT ALL ACTIVITIES ARE SCHEDULED");
            System.exit(1);
        }
        
        int[][] startTimesInt = new int[probInst.getNumActs()][probInst.getMaxNumJobs()];
        for (int i = 0; i < probInst.getNumActs(); i++) {
            for (int j = 0; j < startTimes.get(i).size(); j++) {
                startTimesInt[numsSchedActs.get(i)][j] = startTimes.get(i).get(j);
            }
        }
        
        Solution sol = new Solution(startTimesInt, probInst);
        return sol;
    }
    
    //attention, here you give not an actual number of activity, but the order number of activity in startTimes array
    public List<Integer> UnscheduleActivity(int nUnschedInStartTimesArray){
        //if we unschedule activity that has scheduled successors, we need to unschedule successors as well.
        int actualNumOfActivity = numsSchedActs.get(nUnschedInStartTimesArray);
        List<Integer> ListToUnschedule = new ArrayList<>();
        List<Integer> outputList = new ArrayList<>();
        
        ListToUnschedule.add(nUnschedInStartTimesArray);
        outputList.add(actualNumOfActivity);
        for(int i = 0; i < probInst.getActs()[actualNumOfActivity].getAllSuccessors().size(); i++) {
            int index = numsSchedActs.indexOf(probInst.getActs()[actualNumOfActivity].getAllSuccessors().get(i));
            if(index != -1){
                ListToUnschedule.add(index);
                outputList.add(probInst.getActs()[actualNumOfActivity].getAllSuccessors().get(i));
            }
        }
        
        Collections.sort(ListToUnschedule);
        for(int i = ListToUnschedule.size() - 1; i >= 0; i--) {
            int indexOfActivityToUnschedule = ListToUnschedule.get(i);
            int numOfActivityToUnschedule = numsSchedActs.get(indexOfActivityToUnschedule);
            nJobsScheduled -= (probInst.getHP() / probInst.getActs()[numOfActivityToUnschedule].getPeriod());
            DeleteResourceIntervals(startTimes.get(indexOfActivityToUnschedule), numOfActivityToUnschedule);
 
            startTimes.remove(indexOfActivityToUnschedule);
            numsSchedActs.remove(indexOfActivityToUnschedule);
        }
        
        return outputList;
    }
    
    //output is index in the startTimes array
    public int getScheduledActivityToUnschedule(int usedResource, List<Integer> scheduledFromScratch, 
            List<Integer> allPredecessorsOfCurSchedAct, List<Integer> numRootProblems){
        int output = -1;
        int maxNInstToSched = 0;
        
        if(CC_Scheduling_WithJitter.UNSCHED_RULE == 0){
            for(int i = 0; i < startTimes.size(); i++){
                // First of all, the unscheduled activity must be located on the same resource.
                if(usedResource == probInst.getActs()[numsSchedActs.get(i)].getMapping() &&
                        // Secondly, its promoted jitter requirements cannot be too small (what is to small, by the way?)
                        probInst.getActs()[numsSchedActs.get(i)].getJitter() >= probInst.getMinPeriod() && 
                        // Thirdly, it does not make sense to unschedule predecessor of the currently scheduled activity - 
                        // - actually, sometimes it is necessary to schedule the DAG from scratch
                        !allPredecessorsOfCurSchedAct.contains(numsSchedActs.get(i)) &&
                         // Finally, we try to unschedule the activity with maximum possible moments to schedule
                        maxNInstToSched <= probInst.getActs()[numsSchedActs.get(i)].getSlack()
                        //&& !scheduledFromScratch.contains(numbersOfScheduledActivity.get(i))
                        ){

                    // Unschedule activities with no scheduled successors first
                    boolean hasScheduledSuccessors = false;
                    for(int j = 0; j < numsSchedActs.size(); j++) {
                        if(probInst.getActs()[numsSchedActs.get(i)].getAllSuccessors().contains(numsSchedActs.get(j))){
                            hasScheduledSuccessors = true;
                            break;
                        }
                    }

                    if(hasScheduledSuccessors){
                        continue;
                    }
                    maxNInstToSched = 
                            probInst.getActs()[numsSchedActs.get(i)].getSlack();
                    output = i;
                }
            }

            // first we relax scheduled successors requirements
            int numSucToUnschedule = probInst.getNumActs();
            maxNInstToSched = 0;
            if(output == -1){
                for(int i = 0; i < startTimes.size(); i++){
                    List<Integer> succs = probInst.getActs()[numsSchedActs.get(i)].getAllSuccessors();
                    int numSucToUnscheduleForAct = 0;
                    for(int j = 0; j < succs.size(); j++) {
                        if(numsSchedActs.contains(succs.get(j))){
                            numSucToUnscheduleForAct++;
                        } 
                    }

                    if(usedResource == probInst.getActs()[numsSchedActs.get(i)].getMapping() &&
                            numSucToUnschedule >= numSucToUnscheduleForAct &&
                            !allPredecessorsOfCurSchedAct.contains(numsSchedActs.get(i)) &&
                            probInst.getActs()[numsSchedActs.get(i)].getJitter() >= 3
                            ){

                        for(int j = 0; j < succs.size(); j++) {
                            // if successor of this activity is hard to schedule (in numRootProblems) and already scheduled,
                            // try not to unschedule its predecessors
                            if(numsSchedActs.contains(succs.get(j)) && 
                                    numRootProblems.contains(succs.get(j))){
                                continue;
                            }
                        }

                        numSucToUnschedule = numSucToUnscheduleForAct;
                        output = i;
                   }
               } 
            }

            //second we relax all requirements, but try to choose the activity with the largest jitter requirement 
            int maxJit = 0;
            maxNInstToSched = 0;
            if(output == -1){
               for(int i = 0; i < startTimes.size(); i++){
                    if(usedResource == probInst.getActs()[numsSchedActs.get(i)].getMapping() &&
                            maxJit <= probInst.getActs()[numsSchedActs.get(i)].getJitter() &&
                            !allPredecessorsOfCurSchedAct.contains(numsSchedActs.get(i))
                            ){

                        if(maxJit == probInst.getActs()[numsSchedActs.get(i)].getJitter() &&
                                probInst.getActs()[numsSchedActs.get(i)].getSlack() > 
                                maxNInstToSched){
                            maxNInstToSched = 
                                    probInst.getActs()[numsSchedActs.get(i)].getSlack();
                            maxJit = probInst.getActs()[numsSchedActs.get(i)].getJitter();
                            output = i;
                        }
                   }
               } 
            }
        }
        
        if(CC_Scheduling_WithJitter.UNSCHED_RULE == 1){
            maxNInstToSched = 0;
            for(int i = 0; i < startTimes.size(); i++){
                // First of all, the unscheduled activity must be located on the same resource.
                if(usedResource == probInst.getActs()[numsSchedActs.get(i)].getMapping() &&
                        // We unschedule the activity with maximum slack
                        maxNInstToSched <= probInst.getActs()[numsSchedActs.get(i)].getSlack() &&
                        // Thirdly, it does not make sense to unschedule predecessor of the currently scheduled activity - 
                        // - actually, sometimes it is necessary to schedule the DAG from scratch
                        !allPredecessorsOfCurSchedAct.contains(numsSchedActs.get(i))
                        ){
                    maxNInstToSched = probInst.getActs()[numsSchedActs.get(i)].getSlack();
                    output = i;
                }
            }
        }
        
        return output;
    }
    
    public void UnscheduleAllActivities(){
        nJobsScheduled = 0;
        intervalsOfResourceConstraints =  new ArrayList<List<List<Integer>>>();    
        startTimes.clear();
        numsSchedActs.clear();
        Helpers.Initialize2dArrayWithValue(schedule, 0);
    }
    
    public void UnscheduleAllActivitiesButPreviouslyScheduledAndPreceeding(List<Integer> PreviouslyScheduled, Activity activity1, Activity activity2){
        nJobsScheduled = 0;
        List<List<Integer>> newStartTimes = new ArrayList<List<Integer>>();
        List<Integer> newNumbersOfScheduledActivities = new ArrayList<Integer>();
        intervalsOfResourceConstraints =  new ArrayList<List<List<Integer>>>();
        for(int k = 0; k < probInst.getnResources(); k++) {
            intervalsOfResourceConstraints.add(new ArrayList<List<Integer>>());
        }
        Helpers.Initialize2dArrayWithValue(schedule, 0);
        
        for(int i = 0; i < startTimes.size(); i++) {
            //schedule if it was not previously scheduled from scratch
            if( (PreviouslyScheduled.contains(numsSchedActs.get(i)) && 
                    numsSchedActs.get(i) != activity2.getIdInArray() && 
                    numsSchedActs.get(i) != activity1.getIdInArray() )
                    || activity1.getAllPredecessors().contains(numsSchedActs.get(i))
                    || activity2.getAllPredecessors().contains(numsSchedActs.get(i)))
                    //|| problemInstanceScheduling.getActivities()[numbersOfScheduledActivity.get(i)].getJitter() == 0)
                    {
                newStartTimes.add(startTimes.get(i));
                nJobsScheduled += startTimes.get(i).size();
                newNumbersOfScheduledActivities.add(numsSchedActs.get(i));
                AddNewResourceIntervalsWithConcatenation(Helpers.ArrayListToIntArray(startTimes.get(i)), numsSchedActs.get(i)); 
            }
        }
        numsSchedActs = newNumbersOfScheduledActivities;
        startTimes = newStartTimes;
    }
    
    public void DeleteResourceIntervals(List<Integer> startTimes, int noOfUnScheduledActivity){
        Activity act = probInst.getActs()[noOfUnScheduledActivity];

        int numJobsToUnschedule = act.getHP() / act.getPeriod();
        for(int j = 0; j < numJobsToUnschedule; j++) {
            for(int i = 0; i < act.getProcTime(); i++) {
                schedule[act.getMapping() - 1][(startTimes.get(j) + i) % probInst.getHP()] = 0;
            }
            
            List<Integer> oldInterval;
            if(startTimes.get(j) < probInst.getHP() && startTimes.get(j) + act.getProcTime() > probInst.getHP()){
                oldInterval = Arrays.asList(startTimes.get(j), probInst.getHP());
                ConcatenateNewIntervalWithExisting(oldInterval, act.getMapping());
                
                oldInterval = Arrays.asList(0, (startTimes.get(j) + act.getProcTime()) % probInst.getHP());
                DeleteOldIntervalFromExisting(oldInterval, act.getMapping());
            }
            else{
                oldInterval = Arrays.asList(startTimes.get(j) % probInst.getHP(), 
                    (startTimes.get(j) + act.getProcTime()) % probInst.getHP());
                if(startTimes.get(j) + act.getProcTime() == probInst.getHP()){
                    oldInterval.set(1, probInst.getHP());
                }
                DeleteOldIntervalFromExisting(oldInterval,  act.getMapping());
            }
        }
    }
    
    private void DeleteOldIntervalFromExisting(List<Integer> oldInterval, int numOfResource){
        int numOfInterval;
        numOfResource = numOfResource - 1;
        for(numOfInterval = 0; numOfInterval < intervalsOfResourceConstraints.get(numOfResource).size(); numOfInterval++) {
           int a = oldInterval.get(0);
           int b = oldInterval.get(1);
           int c = intervalsOfResourceConstraints.get(numOfResource).get(numOfInterval).get(0);
           int d = intervalsOfResourceConstraints.get(numOfResource).get(numOfInterval).get(1);
  
           if(c <= a && b <= d){
               if(c == a){
                    intervalsOfResourceConstraints.get(numOfResource).get(numOfInterval).set(0, b);
                    if(intervalsOfResourceConstraints.get(numOfResource).get(numOfInterval).get(0).equals(
                            intervalsOfResourceConstraints.get(numOfResource).get(numOfInterval).get(1))){
                        intervalsOfResourceConstraints.get(numOfResource).remove(numOfInterval);
                    }
                   return;
               }
               
               if(b == d){
                   intervalsOfResourceConstraints.get(numOfResource).get(numOfInterval).set(1, a);
                   if(intervalsOfResourceConstraints.get(numOfResource).get(numOfInterval).get(0).equals(
                           intervalsOfResourceConstraints.get(numOfResource).get(numOfInterval).get(1))){
                       intervalsOfResourceConstraints.get(numOfResource).remove(numOfInterval);
                   }
                   return;
               }
               
               //if the old interval does not lie on the edge of interval [b,c] two new intervals must be created - [c,a] and [b,d]
               intervalsOfResourceConstraints.get(numOfResource).get(numOfInterval).set(1, a);
               intervalsOfResourceConstraints.get(numOfResource).add(numOfInterval + 1, Arrays.asList(b,d));               
               
               return;
           }
        }
    }
    
    public void PrintSchedulesForCANUSE_CASE() throws IOException{
        writer = new FileWriter(Helpers.CANUseCaseFile,true);
        for (int i = 0; i < probInst.getnResources(); i++) {
            writer.write("schedule" + i + " = [");
            for (int j = 0; j < schedule[i].length - 1; j++) {
                writer.write((schedule[i][j]) + ",");
            }
            writer.write(schedule[i][schedule[i].length - 1] + "];\n\n");
        }
        writer.close();
    }
    
}
