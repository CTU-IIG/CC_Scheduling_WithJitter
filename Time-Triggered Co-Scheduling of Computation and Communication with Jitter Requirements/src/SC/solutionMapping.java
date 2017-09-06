/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

package SC;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class solutionMapping {
    private double[][] mapping;
    private int[] runnablesAssignment;
    private double[] variableIndicatingNotAllocatedECU;
    private double[][] variableIndicatingSeparatenessOfMapping;
    private double communicationUtilization;
    private ProblemInstanceMapping problemInstanceMapping;
    private int numResources;
    private int numRunnables;

    public double[][] getVariableIndicatingSeparatenessOfMapping() {
        return variableIndicatingSeparatenessOfMapping;
    }

    public int[] getRunnablesAssignment() {
        return runnablesAssignment;
    }

    public int getNumResources() {
        return numResources;
    }

    public double getCommunicationUtilization() {
        return communicationUtilization;
    }
    
    private void ConvertMappingToRunnableAssignment(){
        runnablesAssignment = new int[numRunnables];
        for(int i = 0; i < numRunnables; i++) {
            boolean isScheduled = false;
            for(int j = 0; j < numResources; j++) {
                if(mapping[j][i] > Helpers.EPS){
                    //System.out.println(j);
                    runnablesAssignment[i] = j;
                    isScheduled = true;
                    break;
                }
            }
        }
    }
    
    //returns total utilization on the network;
    private double FindMessagesToSchedule(){
        double communicationUtilization = 0;
        int numMessages = 0;
        
        // structure that on ith row and jth column contains the list of labels that are to be sent
        // each label is duplicated by the "0" or -1..-numOrdCriticalMessages value to indicate whether 
        // the message is order critical (not 0) and which message it is exactly
        ArrayList<ArrayList<ArrayList<Integer>>> scheduledMessagesList = new ArrayList<ArrayList<ArrayList<Integer>>>();
        
        for(int i = 0; i < numResources; i++) {
            scheduledMessagesList.add(new ArrayList<ArrayList<Integer>>());
            for(int j = 0; j < numResources; j++) {
                scheduledMessagesList.get(i).add(new ArrayList<Integer>());
            }
        }
        
        // start with order-critical messages
        for(int i = 0; i < problemInstanceMapping.getCommTimeOrderCriticalMessages().length; i++) {
            List currentMessage = problemInstanceMapping.getSenderLabelReceiveOrderCriticalChains().get(i);
            int sendingRunnable = (int) currentMessage.get(0) - 1;
            int receivingRunnable = (int) currentMessage.get(4) - 1;
            int sendingRunnableAssignment = runnablesAssignment[sendingRunnable];
            int receivingRunnableAssignment = runnablesAssignment[receivingRunnable];
            if(sendingRunnableAssignment != receivingRunnableAssignment){
                for(int j = 0; j < 3; j++) {
                    if((int) currentMessage.get(j + 1) > Helpers.EPS){
                        int numCurLabel = (int) currentMessage.get(j + 1);
                        scheduledMessagesList.get(sendingRunnableAssignment).get(receivingRunnableAssignment).add(numCurLabel);
                        if(j == 0){
                            communicationUtilization += problemInstanceMapping.getCommTimeOrderCriticalMessages()[i] * 1.0
                                               / problemInstanceMapping.getPeriodsOfRunnables()[sendingRunnable];
                            numMessages++;
                        }
                    }
                }
            }
        }
        
        int numMessagesFromCurrentRunnable = 0;
        // work with non-order-ctirical messages 
        for(int j = 0; j < problemInstanceMapping.getSenderLabelReceiverNonOrderCriticalChains().size(); j++) {
            List currentMessage = problemInstanceMapping.getSenderLabelReceiverNonOrderCriticalChains().get(j);
            
            // for computing the number of message for this runnable we need to 
            // count from "0" each time when the sending runnable is different
            if(j != 0 && 
                    (int) currentMessage.get(0) != problemInstanceMapping.getSenderLabelReceiverNonOrderCriticalChains().get(j - 1).get(0)){
                numMessagesFromCurrentRunnable = 0;
            }
            
            int sendingRunnableAssignment = runnablesAssignment[(int) currentMessage.get(0) - 1];
            int receivingRunnableAssignment = runnablesAssignment[(int) currentMessage.get(2) - 1];
            if(sendingRunnableAssignment != receivingRunnableAssignment){
                int numCurLabel = (int) currentMessage.get(1);
                if(!scheduledMessagesList.get(sendingRunnableAssignment).get(receivingRunnableAssignment).contains(numCurLabel)){
                    scheduledMessagesList.get(sendingRunnableAssignment).get(receivingRunnableAssignment).add(numCurLabel);
                    communicationUtilization += 
                            problemInstanceMapping.getCommTimeNonOrderCriticalMessages().get((int) currentMessage.get(0) - 1).get(numMessagesFromCurrentRunnable) * 1.0
                                               / problemInstanceMapping.getPeriodsOfRunnables()[(int) currentMessage.get(0) - 1];
                    numMessages++;
                }
            }
            numMessagesFromCurrentRunnable++;
        }

        problemInstanceMapping.setNumOfMessagestoSchedule(numMessages);
        problemInstanceMapping.setScheduledMessagesList(scheduledMessagesList);
        
        return communicationUtilization;
    }
    
    public solutionMapping(double[][] variableIndicatingSeparatenessOfMapping, int numUsedResources, 
            double[][] mapping, double[] variableIndicatingNotAllocatedECU, ProblemInstanceMapping problemInstanceDAG) {
        this.mapping = mapping;
        this.variableIndicatingNotAllocatedECU = variableIndicatingNotAllocatedECU;
        this.problemInstanceMapping = problemInstanceDAG;
        this.numRunnables = mapping[0].length;
        this.numResources = numUsedResources;
        this.variableIndicatingSeparatenessOfMapping = variableIndicatingSeparatenessOfMapping;
        ConvertMappingToRunnableAssignment();
        this.communicationUtilization =  FindMessagesToSchedule();
    }
    
    public void PrintSolution(){
        System.out.println("");
        for(int i = 0; i < numResources; i++) {
            System.out.print("On ECU " + (i+1) + " the following runnables are allocated:\n");
            for(int j = 0; j < numRunnables; j++) {
                if(mapping[i][j] > Helpers.EPS){
                    System.out.print((j+1) + ", ");
                }
            } 
            System.out.println();
        }
        System.out.println();
        System.out.println("The communication utilization is " + this.communicationUtilization);
        
    }
    
    public void OutputResultsIntoFile(String fileName, ProblemInstanceMapping problemInstance) throws FileNotFoundException, UnsupportedEncodingException{
        PrintWriter writer = new PrintWriter(fileName, "UTF-8");
        
        int numActivities = 0;
        for(int i = 0; i < problemInstance.getnTransactionsOrderCritical(); i++) {
            numActivities += problemInstance.ToSingleChain(i).getNumberOfActivities();
        }
        writer.print("NumActivities = " + numActivities + ";\n");
        writer.print("NumTransactions = " + problemInstance.getnTransactionsOrderCritical() + ";\n");
        writer.print("NumResources = " + problemInstance.getnResources() + ";\n");
        
        //numberOfActivitiesInChain
        writer.print("numberOfActivitiesinChain = [");
        for(int i = 0; i < problemInstance.getnTransactionsOrderCritical(); i++) {
            String str;
            if(i < problemInstance.getnTransactionsOrderCritical() - 1){
                str = ", ";
            }
            else{
                str = "]; \n\n";
            }
            writer.print(problemInstance.ToSingleChain(i).getNumberOfActivities()+ str);
        }
        
        
        writer.print("assignmentsOnResources = [");
        for(int i = 0; i < problemInstance.getnTransactionsOrderCritical(); i++) {
            for(int j = 0; j < problemInstance.ToSingleChain(i).getNumberOfActivities(); j++) {
                String str;
                if(i < problemInstance.getnTransactionsOrderCritical() - 1 || j < problemInstance.ToSingleChain(i).getNumberOfActivities() - 1){
                    str = ", ";
                }
                else{
                    str = "]; \n\n";
                }
                writer.print((problemInstance.ToSingleChain(i).getActivityAssignmentToResources()[j] + 1) + str);
            }
        }
        
        writer.print("processingTimes = [");
        for(int i = 0; i < problemInstance.getnTransactionsOrderCritical(); i++) {
            for(int j = 0; j < problemInstance.ToSingleChain(i).getNumberOfActivities(); j++) {
                String str;
                if(i < problemInstance.getnTransactionsOrderCritical() - 1 || j < problemInstance.ToSingleChain(i).getNumberOfActivities() - 1){
                    str = ", ";
                }
                else{
                    str = "]; \n\n";
                }
                writer.print(problemInstance.ToSingleChain(i).getProcessingTimes()[j]+ str);
            }
        }
        
        writer.print("periods = [");
        for(int i = 0; i < problemInstance.getnTransactionsOrderCritical(); i++) {
            String str;
            if(i < problemInstance.getnTransactionsOrderCritical() - 1){
                str = ", ";
            }
            else{
                str = "]; \n\n";
            }
            writer.print(problemInstance.ToSingleChain(i).getRequiredPeriod() + str);
        }
        
        writer.close();
    }
}
