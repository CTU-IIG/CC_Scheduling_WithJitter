package SC;

import java.util.ArrayList;
import java.util.List;

/**
 *
 * @author minaeann
 */
public class Activity implements Comparable<Activity>  {
    private int mapping;
    private int processingTimes;
    private int requiredPeriod;
    private int idInInputData;
    private int idInSortedArray;
    private int numJobs;
    private int jitter;
    private int promotedJitter;
    private int criticalLengthBefore;
    private int criticalLengthAfter;
    private int slack;
    private List<Integer> directPredecessors; 
    private List<Integer> allPredecessors; 
    private List<Integer> directSuccessors;
    private List<Integer> allSuccessors; 
    private int numFirstJobForScheduling;
    private int HP;
    
     public List<Integer> getAllPredecessors() {
        return allPredecessors;
    }

    public int getPromotedJitter() {
        return promotedJitter;
    }

    public int getCriticalLengthBefore() {
        return criticalLengthBefore;
    }

    public int getCritLengthAfter() {
        return criticalLengthAfter;
    }

    public int getIdInInputData() {
        return idInInputData;
    }

    public int getIdInArray() {
        return idInSortedArray;
    }

    public int getJitter() {
        return jitter;
    }
    
    public int getNumFirstJоb() {
        return numFirstJobForScheduling;
    }

    public int getNumJobs() {
        return numJobs;
    }

    public int getSlack() {
        return slack;
    }

    public int getMapping() {
        return mapping;
    }

    public int getProcTime() {
        return processingTimes;
    }

    public int getPeriod() {
        return requiredPeriod;
    }

    public List<Integer> getPreds() {
        return directPredecessors;
    }

    public List<Integer> getDirectSuccessors() {
        return directSuccessors;
    }
    
    public List<Integer> getAllSuccessors() {
        return allSuccessors;
    }

    public int getHP() {
        return HP;
    }

    public void setPromotedJitter(int promotedJitter) {
        this.promotedJitter = promotedJitter;
    }

    public void setAllSuccessors(List<Integer> allSuccessors) {
        this.allSuccessors = allSuccessors;
    }


    public void setProcessingTime(int processingTimes) {
        this.processingTimes = processingTimes;
    }
    
    public void setNumFirstJobForScheduling(int numFirstJobForScheduling) {
        this.numFirstJobForScheduling = numFirstJobForScheduling;
    }
    
    public void setCriticalLengthBefore(int criticalLengthBefore) {
        this.criticalLengthBefore = criticalLengthBefore;
    }

    public void setCriticalLengthAfter(int criticalLengthAfter) {
        this.criticalLengthAfter = criticalLengthAfter;
    }

    public void setAllPredecessors(List<Integer> allPredecessors) {
        this.allPredecessors = allPredecessors;
    }
    
    public void setIdInArray(int idInArray) {
        this.idInSortedArray = idInArray;
    }

    public void setJitter(int jitter) {
        this.jitter = jitter;
    }

    public void setNumJobs(int numJobs) {
        this.numJobs = numJobs;
    }

    public void setPeriod(int requiredPeriod) {
        this.requiredPeriod = requiredPeriod;
    }
    
    public Activity(int assignmentToResources, int processingTimes, int requiredPeriod, int idInInputData, 
            int idInArray, int numJobs, List<Integer> directPredecessors, List<Integer> directSuccessors, 
            int numFirstJobForScheduling, int HP, int jitter) {
        this.mapping = assignmentToResources;
        this.processingTimes = processingTimes;
        this.requiredPeriod = requiredPeriod;
        this.idInInputData = idInInputData;
        this.idInSortedArray = idInArray;
        this.numJobs = numJobs;
        this.directPredecessors = directPredecessors;
        this.directSuccessors = directSuccessors;
        this.numFirstJobForScheduling = numFirstJobForScheduling;
        this.HP = HP;
        this.jitter = jitter;
        allPredecessors = new ArrayList<>();
        allSuccessors = new ArrayList<>();
        this.slack = 2 * requiredPeriod;
        this.promotedJitter = jitter;
    }

    public boolean ArePredecessorsScheduled(List<Integer> scheduledActivities){
        boolean[] isPredSched = new boolean [directPredecessors.size()];
        for(int i = 0; i < scheduledActivities.size(); i++) {
            int indexOfDP = directPredecessors.indexOf(scheduledActivities.get(i));
            if(indexOfDP >= 0){
                isPredSched[indexOfDP] = true;
            }
        }
        
        for(int i = 0; i < directPredecessors.size(); i++) {
            if(!isPredSched[i]){
                return false;
            }
        }
        
        return true;
    }
    
    public void computeLengthOfTimeWindowToSchedule(){
        slack = 2 * requiredPeriod - criticalLengthBefore - criticalLengthAfter;
    }

    public void changePredecessorsAndSuccessorsAfterSorting(int[] idInArray){       
        List<Integer> newDirectPredecessors = new ArrayList<Integer>(); 
        for(int j = 0; j < directPredecessors.size(); j++) {
                newDirectPredecessors.add(idInArray[directPredecessors.get(j)]);
        }
        directPredecessors = newDirectPredecessors;
        
        List<Integer> newAllPredecessors = new ArrayList<Integer>(); 
        for(int j = 0; j < allPredecessors.size(); j++) {
            newAllPredecessors.add(idInArray[allPredecessors.get(j)]);
        }
        allPredecessors = newAllPredecessors;
        
        List<Integer> newDirectSuccessors = new ArrayList<Integer>();
        for(int j = 0; j < directSuccessors.size(); j++) {
            newDirectSuccessors.add(idInArray[directSuccessors.get(j)]);
        }
        directSuccessors = newDirectSuccessors;
        
        List<Integer> newAllSuccessors = new ArrayList<Integer>(); 
        for(int j = 0; j < allSuccessors.size(); j++) {
            newAllSuccessors.add(idInArray[allSuccessors.get(j)]);
        }
        allSuccessors = newAllSuccessors;
        
    }

    public int compareTo(Activity activity) {
        int priorityForThisActivity = Math.min(this.promotedJitter, this.slack);
        int priorityForTheOtherActivity = Math.min(activity.promotedJitter, activity.slack);
        
        if(priorityForThisActivity != priorityForTheOtherActivity){
            return Integer.compare(priorityForThisActivity, priorityForTheOtherActivity);
        }
        else{
            if(this.promotedJitter == activity.promotedJitter){
                return Integer.compare(this.slack, activity.slack);
            }
            else{
                return Integer.compare(this.promotedJitter, activity.promotedJitter);
            }
        }
    }
    
}
