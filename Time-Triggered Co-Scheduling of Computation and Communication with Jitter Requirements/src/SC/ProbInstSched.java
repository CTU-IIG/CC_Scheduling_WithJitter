/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package SC;

import static SC.CC_Scheduling_WithJitter.IS_CAN_USE_CASE;
import static SC.CC_Scheduling_WithJitter.writer;
import ilog.concert.IloException;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

/**
 *
 * @author minaeann
 */
public class ProbInstSched {
    private int numActivities;
    private int nResources;
    private int nNetworks;
    private int maxNumJobs;
    private int[] procTimes;
    private int[] periods;
    private int[] assToRes;
    private int[] jitters;
    private List<List<Integer>> precedenceAdjList;
    private List<List<Integer>> followersAdjList;
    private boolean isZJ;
    private boolean isSchedulable = true;
    
    private int numOfPrecedence;
    
    //computed values
    private int HP;
    private int totalNumOfJobs;
    private int numDags;
    private int nActPercent;
    private int minPeriod;
    
    private Activity[] activities;
    private List<DAG> dags;

    public boolean isIsSchedulable() {
        return isSchedulable;
    }
    
    public void CreateFollowersAdjList(){
        followersAdjList = new ArrayList<List<Integer>>();
        for(int i = 0; i < precedenceAdjList.size(); i++){
            followersAdjList.add(new ArrayList<Integer>());
        }
        
        for(int i = 0; i < precedenceAdjList.size(); i++){
            for(int j = 0; j < precedenceAdjList.get(i).size(); j++) {
                followersAdjList.get(precedenceAdjList.get(i).get(j)).add(i);
            }
        }
    }
    
    private void AddTaskToDAG(int numTask, boolean[] includedInDAG, List<Activity> activitysForDAG, List<List<Integer>> precedenceAdjListForDAG,
            List<List<Integer>> followersAdjListForDAG, List<Integer> numberOfTasksInThisDAG){
        includedInDAG[numTask] = true;
        activitysForDAG.add(activities[numTask]);
        precedenceAdjListForDAG.add(new ArrayList<Integer>());
        followersAdjListForDAG.add(new ArrayList<Integer>());
        int numCurrentTaskInDAG = precedenceAdjListForDAG.size() - 1;
        for(int j = 0; j < precedenceAdjList.get(numTask).size(); j++) {
            precedenceAdjListForDAG.get(numCurrentTaskInDAG).add(precedenceAdjList.get(numTask).get(j));
        }
        for(int j = 0; j < followersAdjList.get(numTask).size(); j++) {
            followersAdjListForDAG.get(numCurrentTaskInDAG).add(followersAdjList.get(numTask).get(j));
        }
        numberOfTasksInThisDAG.add(numTask);
    }
    
    private void AddOtherTasksToDAG(boolean[] includedInDAG, List<Activity> activitysForDAG,
            List<List<Integer>> precedenceAdjListForDAG, List<List<Integer>> followersAdjListForDAG,
            List<Integer> numberOfTasksInThisDAG){
        int numCurrentTaskInTaskArray = precedenceAdjListForDAG.size() - 1;
        for(int i = 0; i < precedenceAdjListForDAG.get(numCurrentTaskInTaskArray).size(); i++) {
            int currentPredecessor = precedenceAdjListForDAG.get(numCurrentTaskInTaskArray).get(i);
            if(!numberOfTasksInThisDAG.contains(currentPredecessor)){
                AddTaskToDAG(currentPredecessor, includedInDAG, activitysForDAG, precedenceAdjListForDAG,
                        followersAdjListForDAG, numberOfTasksInThisDAG);
                 AddOtherTasksToDAG(includedInDAG, activitysForDAG, precedenceAdjListForDAG,
                        followersAdjListForDAG, numberOfTasksInThisDAG);
            }
        }
        
        for(int i = 0; i < followersAdjListForDAG.get(numCurrentTaskInTaskArray).size(); i++) {
            int currentFollower = followersAdjListForDAG.get(numCurrentTaskInTaskArray).get(i);
            if(!numberOfTasksInThisDAG.contains(currentFollower)){
                AddTaskToDAG(currentFollower, includedInDAG, activitysForDAG, 
                        precedenceAdjListForDAG, followersAdjListForDAG, numberOfTasksInThisDAG);
                AddOtherTasksToDAG(includedInDAG, activitysForDAG, precedenceAdjListForDAG,
                        followersAdjListForDAG, numberOfTasksInThisDAG);
            }
        }
    }
    
    public void CreateDAGS() throws IloException, IOException{
        boolean[] includedInDAG = new boolean [numActivities];
        dags = new ArrayList<DAG>();
        for(int i = 0; i < numActivities; i++) {
            if(!includedInDAG[i] && (!precedenceAdjList.get(i).isEmpty() || !followersAdjList.isEmpty())){
                //we can create new DAG
                List<Activity> activitysForDAG = new ArrayList<Activity>();
                List<List<Integer>> precedenceAdjListForDAG = new ArrayList<List<Integer>>();
                List<List<Integer>> followersAdjListForDAG = new ArrayList<List<Integer>>();
                List<Integer> numberOfTasksInThisDAG = new ArrayList<Integer>();
                
                //add current activity to the DAG
                AddTaskToDAG(i, includedInDAG, activitysForDAG, precedenceAdjListForDAG, followersAdjListForDAG,
                        numberOfTasksInThisDAG);
                
                AddOtherTasksToDAG(includedInDAG, activitysForDAG, precedenceAdjListForDAG,
                        followersAdjListForDAG, numberOfTasksInThisDAG);
                
                dags.add(new DAG(Helpers.ArrayListToActivityArray(activitysForDAG), precedenceAdjListForDAG, followersAdjListForDAG));
                if(dags.get(dags.size() - 1).IsCyclical()){
                    isSchedulable = false;
                    return;
                }
            }
        }
        numDags = dags.size();
    }
    
    public void CreateActivities(int[] procTimes, int[] periods,
             int[] assToRes, List<List<Integer>> precedenceAdjList, 
             int[] jitters, int solve_with_zero_jitter, double current_utilization) throws IloException, IOException{
        numActivities = precedenceAdjList.size();
        computeHP();
        activities = new Activity[numActivities];
        CreateFollowersAdjList();
        int curNumJobs = 0;
         
        if(!CC_Scheduling_WithJitter.IS_USE_CASE && !CC_Scheduling_WithJitter.IS_CAN_USE_CASE){
            ScaleToRequiredUtilization(current_utilization, false);
        }
        
        double[] utilization = ComputeTotalUtilizationOnEachResource(procTimes, periods);
        
        //check if it is not zero-jitter scheduling
        if(solve_with_zero_jitter == 1){
            isZJ = true;
        }
        
        minPeriod = periods[0];
        for(int i = 0; i < numActivities; i++){
            if(periods[i] < minPeriod){
                minPeriod = periods[i];
            }
            
            int jitter = periods[i] / CC_Scheduling_WithJitter.COEFFICIENT_FOR_JITTER;
            int numJobs = HP / periods[i];
            if(isZJ){
                numJobs = 1;
                jitter = 0;
            }
            
            if(CC_Scheduling_WithJitter.IS_CAN_USE_CASE && i == 74){
                jitter = 0;
            }
            
            activities[i] = new Activity(assToRes[i], procTimes[i], 
                    periods[i], i, i, numJobs, precedenceAdjList.get(i), 
                    followersAdjList.get(i), curNumJobs, HP, jitter);
            curNumJobs += numJobs;
        }
        
        computeTotalAndMaxNumOfJobs();
        CreateDAGS();
        numOfPrecedence = 0;
        for(int i = 0; i < precedenceAdjList.size(); i++) {
            numOfPrecedence += precedenceAdjList.get(i).size();
        }
    }
     
    private void computeHP() {
        long localHP = periods[0];
        for (int i = 1; i < numActivities; i++) {
            if(localHP != periods[i]){
                localHP = localHP * periods[i] / gcd(localHP,periods[i]);
            }
        }
        HP = (int) localHP;
    }
    
    private void computeTotalAndMaxNumOfJobs(){
        totalNumOfJobs = 0;
        maxNumJobs = 0;
        for(int i = 0; i < numActivities; i++){
            if(HP / activities[i].getPeriod() > maxNumJobs){
                maxNumJobs = HP / activities[i].getPeriod();
            }
            totalNumOfJobs += activities[i].getNumJobs();
        }
    }
    
    public static long gcd(double a, int b) {
        return BigInteger.valueOf((int) Math.round(a)).gcd(BigInteger.valueOf(b)).intValue();
    }
    
    public double[] ComputeTotalUtilizationOnEachResource(int[] processingTimes, int[] periods){
	double[] utilization = new double [this.nResources];
    
	for(int i = 0; i < this.nResources; i++){ 
            utilization[i] = 0;
        }
        
        for(int j = 0; j < numActivities; j++) {  
            utilization[assToRes[j] - 1] += 
                    processingTimes[j] * 1.0 / periods[j];
        }
    
	return utilization;
    }
    
    public boolean IsInstanceSchedulable() throws IOException{
        double[] utilization = ComputeTotalUtilizationOnEachResource(procTimes, periods);
        
        if(CC_Scheduling_WithJitter.IS_USE_CASE){
            for(int i = 0; i < nResources; i++){ 
                if(utilization[i] > 1){
                    return false;
                }
                
                if(utilization[i] < Helpers.EPS){
                    nResources--;
                }
            }
        }
        
        for(int i = 0; i < numActivities; i++) {
            if(activities[i].getSlack( )<= 0){
                System.out.println("Some activity cannot be scheduled!");
                writer = new FileWriter(Helpers.outputFile,true);
                writer.write(" Some activity cannot be scheduled!\n");
                writer.close();
                return false;
            }
        }
        
        return true;
    }
    
    public void ScaleToRequiredUtilization(double current_utilization, boolean areActsCreated){
        double[] utilization = ComputeTotalUtilizationOnEachResource(procTimes, periods);
        
        double[] coefficientForScalingECU = new double[utilization.length];
        for (int i = 0; i < utilization.length; i++) {
            coefficientForScalingECU[i] = current_utilization / utilization[i];
        }
        
        for(int i = 0; i < numActivities; i++) {
            if(assToRes[i] <= nResources - nNetworks){
                procTimes[i] *= coefficientForScalingECU[assToRes[i] - 1];
                if(areActsCreated){
                    activities[i].setProcessingTime(procTimes[i]);
                }
            }
            else{
                break;
            }
        }
        
        utilization = ComputeTotalUtilizationOnEachResource(procTimes, periods);
        System.out.println("Utilization on the resources is:");
        for(int i = 0; i < utilization.length; i++) {
            System.out.println(utilization[i]);
        }
        
        /*double coefficientForScalingNetwork = CC_Scheduling_WithJitter.REQUIRED_UTILIZATION_ON_RESOURCES / utilization[nResources - 1];
        for(; i < numActivities; i++) {
            processingTimesOfTasks[i] *= coefficientForScalingNetwork;
        }*/
        for(int j = nResources - nNetworks; j < nResources; j++) {
            double coefficientForScalingNetwork = current_utilization / utilization[j];
            for(int k = 0; k < numActivities; k++) {
                if(assToRes[k] == j + 1){
                    procTimes[k] *= coefficientForScalingNetwork;
                    if(areActsCreated){
                        activities[k].setProcessingTime(procTimes[k]);
                    }
                }
            }
        }
        
        utilization = ComputeTotalUtilizationOnEachResource(procTimes, periods);
        System.out.println("Utilization on the resources is:");
        for(int i = 0; i < utilization.length; i++) {
            System.out.println(utilization[i]);
        }
    }
    
    // Attention! It should be NZJ instance! Also, try problem instance with more cores
    public int makeProblemInstanceToContainApproximatelyNPercZJJobs(int nPercents, 
            List<Integer> prevChosenActs, int nPrevTransf, int nSkipped) throws IOException{   
        nActPercent = 0;
        if(nPercents == 0){
            return 0;
        }
        
        // if all activities should be ZJ, change respectively
        if(nPercents == 100){
            totalNumOfJobs = numActivities;
            isZJ = true;
            for (int i = 0; i < numActivities; i++) {
                activities[i].setJitter(0);
                activities[i].setNumFirstJobForScheduling(i);
                activities[i].setNumJobs(1);
            }
            nActPercent = 100;
            return nActPercent;
        }
        
        int initialNJobsZJ = numActivities;
        int initialNJobsNZJ = totalNumOfJobs - initialNJobsZJ;
        int numRequiredJobsZJ = (int) Math.floor((nSkipped + 1) * 5 * initialNJobsNZJ * 1.0 / 100);
        
        int numNZJTransferredToZJ = 0;
        for(int i = 0; i < numActivities; i++){
            if(activities[i].getPeriod() != HP && !prevChosenActs.contains(i)){
                if(numNZJTransferredToZJ + activities[i].getNumJobs() - 1 <= numRequiredJobsZJ + 1){
                    numNZJTransferredToZJ += activities[i].getNumJobs() - 1;
                    activities[i].setJitter(0);
                    prevChosenActs.add(i);
                }
                
                if(numNZJTransferredToZJ >= numRequiredJobsZJ - 1){
                    nActPercent = nPrevTransf + (int) Math.floor(numNZJTransferredToZJ * 1.0 / initialNJobsNZJ * 100);
                }
            }
        }
        
        return nActPercent;
    }
    
    //ATTENTION! Numbers of activities in dependencies MUST BE in the range from 0 to n (not from 1)
    public ProbInstSched(String fileName, int solve_with_zero_jitter,
            double current_utilization) throws IOException, IloException {
        Scanner in = new Scanner(new File(fileName));
        numActivities = Helpers.ReadIntegerNumber(in);
        nResources = Helpers.ReadIntegerNumber(in);
        nNetworks = Helpers.ReadIntegerNumber(in);
        
        //!there is always one line between two data arrays!
        procTimes = Helpers.ReadIntegerArray(in, numActivities);
        assToRes = Helpers.ReadIntegerArray(in, numActivities);
        periods = Helpers.ReadIntegerArray(in, numActivities);
        precedenceAdjList = Helpers.Read2DIntegerArray(in);
        jitters = Helpers.ReadIntegerArray(in, numActivities);
        
        CreateActivities(procTimes, periods, assToRes, 
                precedenceAdjList, jitters, solve_with_zero_jitter, current_utilization);
    }
    
    public ProbInstSched(){}
    
    public void SetProblemInstanceScheduling(int[] processingTimesOfTasks,int[] periodsOfTasks,int[] activityAssignmentToResources,
            List<List<Integer>> precedenceAdjList, int numResources, int[] jitters, int nNetworks,
            int solve_with_zero_jitter, double current_utilization) throws IOException, IloException {
        numActivities = precedenceAdjList.size();
        nResources = numResources;
        
        //!there is always one line between two data arrays!
        this.procTimes = processingTimesOfTasks;
        this.assToRes = activityAssignmentToResources;
        this.periods = periodsOfTasks;
        this.precedenceAdjList = precedenceAdjList;
        this.jitters = jitters;
        this.nNetworks = nNetworks;
       
        CreateActivities(processingTimesOfTasks, periodsOfTasks, activityAssignmentToResources, precedenceAdjList, jitters, 
                solve_with_zero_jitter, current_utilization);
    }
    
    
    
    
    public int getNumActs() {
        return numActivities;
    }
    
    public Activity[] getActs() {
        return activities;
    }
    
    public int getHP() {
        return HP;
    }
    
    public int getTotalNumOfJobs() {
        return totalNumOfJobs;
    }
    
    public int getNumDags() {
        return numDags;
    }
   
    public int getnResources() {
        return nResources;
    }

    public int getNumOfPrecedence() {
        return numOfPrecedence;
    }

    public boolean isZJ() {
        return isZJ;
    }

    public List<DAG> getDags() {
        return dags;
    }

    public int getMaxNumJobs() {
        return maxNumJobs;
    }

    public int getnActZJPercent() {
        return nActPercent;
    }

    public int getMinPeriod() {
        return minPeriod;
    }

    public void setTotalNumOfJobs(int totalNumOfJobs) {
        this.totalNumOfJobs = totalNumOfJobs;
    }
}
