/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package SC;

import ilog.concert.IloException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Queue;

/**
 *
 * @author minaeann
 */
public class DAG implements Comparable<DAG>  {
    private int period;
    private List<Integer> numbersOfActivities;
    private Activity[] Activities;
    private List<List<Integer>> precedenceAdjList;
    private List<List<Integer>> allPredecessorsAdjList;
    private List<List<Integer>> allSuccessorsAdjList;
    private List<List<Integer>> followersAdjList;
    private int[] criticalLengthsBefore;
    private int[] criticalLengthsAfter; //contains processing time of the activity itself
    private int[] inheritedJitters;
    private int numActivitiesInDAG;
    private boolean isCyclical;

    public List<List<Integer>> getPrecedenceAdjList() {
        return precedenceAdjList;
    }

    public List<Integer> getNumbersOfActivities() {
        return numbersOfActivities;
    }

    public int getPeriod() {
        return period;
    }

    public int getNumActivitiesInDAG() {
        return numActivitiesInDAG;
    }

    public Activity[] getActivities() {
        return Activities;
    }

    public boolean IsCyclical() {
        return isCyclical;
    }
    
    public DAG(Activity[] activities, List<List<Integer>> precedenceAdjList, List<List<Integer>> followersAdjList) 
            throws IloException, IOException {
        period = activities[0].getPeriod();
        this.Activities = activities;
        numActivitiesInDAG = activities.length;
        this.precedenceAdjList = precedenceAdjList;
        this.followersAdjList = followersAdjList;
        this.numbersOfActivities = new ArrayList<Integer>();
        for(int i = 0; i < numActivitiesInDAG; i++) {
            numbersOfActivities.add(activities[i].getIdInArray());
        } 
        
        ComputeCriticalLengthBeforeAndAfterForEachActivity();
        for(int i = 0; i < numActivitiesInDAG; i++) {
            if(Math.abs(criticalLengthsAfter[i]) > period * 10 || Math.abs(criticalLengthsBefore[i]) > period * 10){
                System.out.println("\n\n\nThere is a cycle!\n\n\n");
                this.isCyclical = true;
            }
        }
        FindAllPredecessorsAndSuccessors();
        ComputeInheritedJitters();
                
        for(int i = 0; i < numActivitiesInDAG; i++) {
            activities[i].setAllPredecessors(allPredecessorsAdjList.get(i));
            activities[i].setAllSuccessors(allSuccessorsAdjList.get(i));
        }
        ImproveHeadsAndTails();
        
        for(int i = 0; i < numActivitiesInDAG; i++) {
            activities[i].setCriticalLengthBefore(criticalLengthsBefore[i]);
            activities[i].setCriticalLengthAfter(criticalLengthsAfter[i]);
            activities[i].setPromotedJitter(inheritedJitters[i]);
            activities[i].computeLengthOfTimeWindowToSchedule();
        }
    }
    
    private void BFS(int numRootNode, boolean isForCriticalLengthBefore){
        List<List<Integer>> adjList;
        int[] criticalLength;
        if(isForCriticalLengthBefore){
            adjList = followersAdjList;
            criticalLength = criticalLengthsBefore;
        }
        else{
            adjList = precedenceAdjList;
            criticalLength = criticalLengthsAfter;
        }
        
        Queue<Integer> Q = new PriorityQueue<>();
        int numNodeToAddCost = numRootNode;
        for(int i = 0; i < adjList.get(numRootNode).size(); i++) {
            int indexOfChildNodeInActivityArray = numbersOfActivities.indexOf(adjList.get(numRootNode).get(i));
            if(!isForCriticalLengthBefore){
                numNodeToAddCost = indexOfChildNodeInActivityArray;
            }
            if(criticalLength[indexOfChildNodeInActivityArray] < criticalLength[numRootNode] + Activities[numNodeToAddCost].getProcTime()){
                criticalLength[indexOfChildNodeInActivityArray] = criticalLength[numRootNode] + Activities[numNodeToAddCost].getProcTime();
                Q.add(adjList.get(numRootNode).get(i));
            }
        }        
        
        while(!Q.isEmpty()){
            int indexOfParentNodeInActivityArray = numbersOfActivities.indexOf(Q.poll());
            numNodeToAddCost = indexOfParentNodeInActivityArray;
            
            for(int i = 0; i < adjList.get(indexOfParentNodeInActivityArray).size(); i++) {
                int indexOfChildNodeInActivityArray = numbersOfActivities.indexOf(adjList.get(indexOfParentNodeInActivityArray).get(i));
                if(!isForCriticalLengthBefore){
                    numNodeToAddCost = indexOfChildNodeInActivityArray;
                }
                
                if(criticalLength[indexOfChildNodeInActivityArray] > 4 * period){
                    System.out.println("Instance is not schedulable - either there is a cycle or precedence relations are too demanding");
                    isCyclical = true;
                    return;
                }
                
                if(criticalLength[indexOfChildNodeInActivityArray] < criticalLength[indexOfParentNodeInActivityArray] + 
                        Activities[numNodeToAddCost].getProcTime()){
                    criticalLength[indexOfChildNodeInActivityArray] = criticalLength[indexOfParentNodeInActivityArray] +
                            Activities[numNodeToAddCost].getProcTime();
                    Q.add(adjList.get(indexOfParentNodeInActivityArray).get(i));
                }
            }
        }
        
        if(isForCriticalLengthBefore){
            criticalLengthsBefore = criticalLength;
        }
        else{
            criticalLengthsAfter = criticalLength;
        }
    }
    
    private void ComputeCriticalLengthBeforeAndAfterForEachActivity(){
        criticalLengthsBefore = new int[numActivitiesInDAG];
        criticalLengthsAfter = new int[numActivitiesInDAG];
        Helpers.InitializeTo(criticalLengthsBefore, 0);
        Helpers.InitializeTo(criticalLengthsAfter, 0);
        
        for(int i = 0; i < numActivitiesInDAG; i++) {
            if(precedenceAdjList.get(i).isEmpty()){
                //It is a root node. Start BFS in this node.
                BFS(i, true);
            }
        }
        
        for(int i = 0; i < numActivitiesInDAG; i++) {
            if(followersAdjList.get(i).isEmpty()){
                //It is a root node. Start BFS in this node.
                criticalLengthsAfter[i] = Activities[i].getProcTime();
                BFS(i, false);
            }
        }
        
    }
    
    private void FindAllPredecessorsAndSuccessors(){
        allPredecessorsAdjList = new ArrayList<List<Integer>>();
        allSuccessorsAdjList = new ArrayList<List<Integer>>();
        for(int i = 0; i < numActivitiesInDAG; i++) {
            allPredecessorsAdjList.add(new ArrayList<Integer>());
            allSuccessorsAdjList.add(new ArrayList<Integer>());
            for(int j = 0; j < precedenceAdjList.get(i).size(); j++) {
                allPredecessorsAdjList.get(i).add(precedenceAdjList.get(i).get(j));
            }
        }
        
        for(int i = 0; i < numActivitiesInDAG; i++) {
            Queue<Integer> Q = new PriorityQueue<>();
            for(int j = 0; j < precedenceAdjList.get(i).size(); j++) {
                Q.add(precedenceAdjList.get(i).get(j));
            }
            
            while(!Q.isEmpty()){
                int numParent = Q.poll();
                for(int j = 0; j < precedenceAdjList.get(numbersOfActivities.indexOf(numParent)).size(); j++) {
                    if(!allPredecessorsAdjList.get(i).contains(precedenceAdjList.get(numbersOfActivities.indexOf(numParent)).get(j))){
                        allPredecessorsAdjList.get(i).add(precedenceAdjList.get(numbersOfActivities.indexOf(numParent)).get(j));
                        Q.add(precedenceAdjList.get(numbersOfActivities.indexOf(numParent)).get(j));
                    }
                }
            }
            
            for(int j = 0; j < allPredecessorsAdjList.get(i).size(); j++) {
                allSuccessorsAdjList.get(numbersOfActivities.indexOf(allPredecessorsAdjList.get(i).get(j))).add(numbersOfActivities.get(i));
            }
        }
    }
    
    private void ImproveHeadsAndTails() throws IloException, IOException{
        // first improve by computing the activities in predecessors (successors) 
        // that are assigned to the same resource
        for(int i = 0; i < numActivitiesInDAG; i++) {
            int sumProcTimesOnTheSameResourceBefore = 0;
            int sumProcTimesOnTheSameResourceAfter = Activities[i].getProcTime();
            for(int j = 0; j < numActivitiesInDAG; j++) {
                if(j!=i && allPredecessorsAdjList.get(i).contains(Activities[j].getIdInInputData()) && 
                        Activities[j].getMapping() == Activities[i].getMapping()){
                    sumProcTimesOnTheSameResourceBefore += Activities[j].getProcTime();
                }
            }
            
            for(int j = 0; j < numActivitiesInDAG; j++) {
                if(j != i && allSuccessorsAdjList.get(i).contains(Activities[j].getIdInInputData()) && 
                        Activities[j].getMapping() == Activities[i].getMapping()){
                    sumProcTimesOnTheSameResourceAfter += Activities[j].getProcTime();
                }
            }
            if(sumProcTimesOnTheSameResourceBefore > criticalLengthsBefore[i]){
                criticalLengthsBefore[i] = sumProcTimesOnTheSameResourceBefore;
            }
            if(sumProcTimesOnTheSameResourceAfter > criticalLengthsAfter[i]){
                criticalLengthsAfter[i] = sumProcTimesOnTheSameResourceAfter;
            }
        }
    }
   
    private void ComputeInheritedJitters(){
        inheritedJitters = new int[numActivitiesInDAG];
        for(int i = 0; i < numActivitiesInDAG; i++) {
            inheritedJitters[i] = Activities[i].getJitter();
            for(int j = 0; j < allSuccessorsAdjList.get(i).size(); j++) {
                if(inheritedJitters[i] > Activities[numbersOfActivities.indexOf(allSuccessorsAdjList.get(i).get(j))].getJitter()){
                    inheritedJitters[i] = Activities[numbersOfActivities.indexOf(allSuccessorsAdjList.get(i).get(j))].getJitter();
                }
            }
        }
    }
    
    public int compareTo(DAG dag) {
        if(this.period - dag.period > Helpers.EPS){
            return Double.compare(this.period, dag.period);
        }
        else{
            return Integer.compare(Helpers.SumOverProcessingTimesInActivitiesArray(dag.Activities), 
                    Helpers.SumOverProcessingTimesInActivitiesArray(this.Activities));
           
       }
                
                
    }
}
