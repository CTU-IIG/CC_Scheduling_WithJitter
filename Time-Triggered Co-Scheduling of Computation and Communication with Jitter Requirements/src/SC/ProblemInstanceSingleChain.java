package SC;

import java.util.Arrays;


public class ProblemInstanceSingleChain implements Comparable<ProblemInstanceSingleChain>  {
    private int numberOfActivitys;
    private int[] activitysAssignmentToResources;
    private int[] processingTimes;
    private int numOfStartActivityInTheChain;
    private int RequiredPeriod;
    private int RequiredEndToEnd;
    private int RequiredJitter;
    private int IdInInputData;
    private int IdInArray;
    private int numJobsForOneActivity;
    private long HP;
    private int nResources;
    private int numRunnablesInTransaction;

    public int getNumOfStartActivityInTheChain() {
        return numOfStartActivityInTheChain;
    }
    
    public void setParticularAssignment(int assignment, int number){
        activitysAssignmentToResources[number] = assignment;
    }
    
    public void computeNumOfJobs(){
        numJobsForOneActivity = (int) Math.round(this.HP/this.RequiredPeriod);
    }
    
    public int compareTo(ProblemInstanceSingleChain tr) {
        /*if(this.RequiredJitter - tr.RequiredJitter != 0)
            return (this.RequiredJitter - tr.RequiredJitter);
        else{
            return (this.RequiredPeriod - tr.RequiredPeriod);
        }*/
        //return (this.RequiredPeriod - tr.RequiredPeriod)
        if(this.numberOfActivitys == 1 && tr.numberOfActivitys > 1) return 1;
        
        if(tr.numberOfActivitys == 1 && this.numberOfActivitys > 1) return -1;
        
        if(Math.abs(Helpers.SumOverArray(processingTimes) * 1.0 / this.RequiredPeriod - 
                Helpers.SumOverArray(tr.processingTimes) * 1.0 / tr.RequiredPeriod) > Helpers.EPS){
            return Double.compare(Helpers.SumOverArray(tr.processingTimes) * 1.0 / tr.RequiredPeriod,
                Helpers.SumOverArray(this.processingTimes) * 1.0 / this.RequiredPeriod);
        }
        else{
            if(tr.processingTimes[0] != this.processingTimes[0]){
                 return Integer.compare(tr.processingTimes[0], this.processingTimes[0]);
            }
            else{
                return Double.compare(Helpers.SumOverArray(tr.processingTimes) * 1.0 / tr.RequiredPeriod,
                    Helpers.SumOverArray(this.processingTimes) * 1.0 / this.RequiredPeriod);
            }
       }
                
                
    }

    public void setIdInArray(int IdInArray) {
        this.IdInArray = IdInArray;
    }

    public void setIdInInputData(int IdInInputData) {
        this.IdInInputData = IdInInputData;
    }

    public void setActivitysAssignmentToResources(int[] activitysAssignmentToResources) {
        this.activitysAssignmentToResources = activitysAssignmentToResources;
    }

    public void setProcessingTimes(int[] processingTimes) {
        this.processingTimes = processingTimes;
    }
   
    public void setNumberOfActivitiesinChain(int numberOfActivitysinChain) {
        this.numberOfActivitys = numberOfActivitysinChain;
    }

    public void setRequiredPeriod(int RequiredPeriod) {
        this.RequiredPeriod = RequiredPeriod;
    }

    public void setRequiredEndToEnd(int RequiredEndToEnd) {
        this.RequiredEndToEnd = RequiredEndToEnd;
    }

    public void setRequiredJitter(int RequiredJitter) {
        this.RequiredJitter = RequiredJitter;
    }

    public int getNumJobsForOneActivity() {
        return numJobsForOneActivity;
    }
    
    public int getIdInArray() {
        return IdInArray;
    }

    public int[] getProcessingTimes() {
        return processingTimes;
    }
    
    public int getIdInInputData() {
        return IdInInputData;
    }

    public int getNumRunnablesInTransaction() {
        return numRunnablesInTransaction;
    }

    public int getNumberOfActivities() {
        return numberOfActivitys;
    }

    public int[] getActivityAssignmentToResources() {
        return activitysAssignmentToResources;
    }

    public int getRequiredPeriod() {
        return RequiredPeriod;
    }

    public int getRequiredEndToEnd() {
        return RequiredEndToEnd;
    }

    public int getRequiredJitter() {
        return RequiredJitter;
    }

    public int getnResources() {
        return nResources;
    }

    public void AssignFoundMapping(int numberOfActivitysinChain, int[] activityAssignmentToResources, 
            int[] processingTimes, int numOfStartActivityInTheChain, int nResources){
        this.numberOfActivitys = numberOfActivitysinChain;
        this.activitysAssignmentToResources = activityAssignmentToResources;
        this.processingTimes = processingTimes;
        this.numOfStartActivityInTheChain = numOfStartActivityInTheChain;
        this.nResources = nResources;
    }
    
    public ProblemInstanceSingleChain(int numberOfActivitysinChain, int[] activityAssignmentToResources, int RequiredPeriod, int RequiredEndToEnd, int RequiredJitter, int[] processingTimes, int IdInInputData, int numOfStartActivityInTheChain, int nResources) {
        this.numberOfActivitys = numberOfActivitysinChain;
        this.activitysAssignmentToResources = activityAssignmentToResources;
        this.RequiredPeriod = RequiredPeriod;
        this.RequiredEndToEnd = RequiredEndToEnd;
        this.RequiredJitter = RequiredJitter;
        this.processingTimes = processingTimes;
        this.IdInInputData = IdInInputData;
        this.numOfStartActivityInTheChain = numOfStartActivityInTheChain;
        this.nResources = nResources;
        this.HP = HP;
        this.numRunnablesInTransaction = numberOfActivitysinChain - ((int)Math.ceil(numberOfActivitysinChain/2.0) - 1);
        this.computeNumOfJobs();
    }

    public double getHP() {
        return HP;
    }
    
    
}

