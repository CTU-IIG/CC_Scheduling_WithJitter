package SC;

import static SC.CC_Scheduling_WithJitter.writer;
import ilog.concert.IloException;
import java.util.Scanner;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class ProblemInstanceMapping{
   //mapping related
    private int nCores;
    private int memoryBoundOnECU;
    private double utilizationBound;
    private int numOfMessagestoSchedule;
    
    //for mapping problem
    private ProblemInstanceSingleChain[] problemInstancesSingleChain;
    private int numCommunications;
    private int[] sizeOfRunnables;
    private int[] runnablesInChains;
    private int[] commTimeOrderCriticalMessages;
    private int[] numRunnablesInChains;
    private int[] processingTimesOfRunnables;
    private int[] periodsOfRunnables;
    
    private List<List<Integer>> commTimeNonOrderCriticalMessages;
    private List<List<Integer>> senderLabelReceiveOrderCriticalChains;
    private List<List<Integer>> senderLabelReceiverNonOrderCriticalChains;
    private List<Integer> runnablesNotPartOfCauseEffectChain;
    private List<Integer> senderOfMessage;
    private List<Integer> sizeOfMessage;
    private List<Integer> numOfMessage;
    ArrayList<ArrayList<ArrayList<Integer>>> scheduledMessagesList;
    
    private int nNetworks;
    private int nChains;
    private int numRunnables;
    private solutionMapping solutionMap;
    
    private int[] procTimes;
    private int[] periods;
    private int[] mappings;
    private int[] jitters;
    private List<List<Integer>> precAdjList;
    
    
    //parser of problem instances
    public ProblemInstanceMapping(String fileName, int nCores_) throws IOException {
        Scanner in = new Scanner(new File(fileName));
        nChains = Helpers.ReadIntegerNumber(in);
        nCores = Helpers.ReadIntegerNumber(in);
        nCores = nCores_;
        int totalNumRunnablesInChains = Helpers.ReadIntegerNumber(in);
        memoryBoundOnECU = Helpers.ReadIntegerNumber(in);
        utilizationBound = Helpers.ReadIntegerNumber(in) / 100.0;
        
        //!there is always one line between two data arrays!
        int[] numberOfActivitiesInChain = Helpers.ReadIntegerArray(in, nChains);
        numRunnablesInChains = new int[nChains];
        for(int i = 0; i < nChains; i++) {
            numRunnablesInChains[i] = numberOfActivitiesInChain[i] - ((int)Math.ceil(numberOfActivitiesInChain[i]/2.0) - 1);
        }
        
        runnablesInChains = Helpers.ReadIntegerArray(in, totalNumRunnablesInChains);
        commTimeNonOrderCriticalMessages = Helpers.Read2DIntegerArray(in);
        numRunnables = commTimeNonOrderCriticalMessages.size();
        
        processingTimesOfRunnables = Helpers.ReadIntegerArray(in, numRunnables);
        periodsOfRunnables = Helpers.ReadIntegerArray(in, numRunnables);
        
        if(CC_Scheduling_WithJitter.IS_EXPERIMENT_WITH_DIF_PERIODS){
            for (int i = 0; i < numRunnables; i++) {
                if(CC_Scheduling_WithJitter.is_exp_with_harmonic_periods){
                   if(periodsOfRunnables[i] == 2000){
                       periodsOfRunnables[i] = 5000;
                   }
                }

               if(CC_Scheduling_WithJitter.is_exp_with_monoperiod){
                   periodsOfRunnables[i] = 10000;
                }

                if(CC_Scheduling_WithJitter.is_exp_with_non_harmonic_periods){
                    if(periodsOfRunnables[i] == 1000){
                        periodsOfRunnables[i] = 7000;
                    }
                    if(periodsOfRunnables[i] == 10000){
                        periodsOfRunnables[i] = 12000;
                    }
                }
            }
        }
        
        boolean[] isRunnableAPartOfCauseEffectChain = new boolean [numRunnables];        
        for(int i = 0; i < runnablesInChains.length; i++) {
            isRunnableAPartOfCauseEffectChain[runnablesInChains[i] - 1] = true;
        }
        runnablesNotPartOfCauseEffectChain = new ArrayList<Integer>(); 
        for(int i = 0; i < numRunnables; i++) {
            if(isRunnableAPartOfCauseEffectChain[i] == false){
                runnablesNotPartOfCauseEffectChain.add(i);
            }
        }

        commTimeOrderCriticalMessages = Helpers.ReadIntegerArrayWithoutGivenLegth(in);
        sizeOfRunnables = Helpers.ReadIntegerArray(in,numRunnables);
        senderLabelReceiveOrderCriticalChains = Helpers.Read2DIntegerArray(in);
        senderLabelReceiverNonOrderCriticalChains = Helpers.Read2DIntegerArray(in);
        numCommunications = senderLabelReceiveOrderCriticalChains.size() + senderLabelReceiverNonOrderCriticalChains.size();
        
        jitters = Helpers.ReadIntegerArrayWithoutGivenLegth(in);
        
        // create problem_instances for each chain
        // the scheduling entities are runnables and messages that are part of the chains (nChains)
        // and independent messages and runnables
        problemInstancesSingleChain = new ProblemInstanceSingleChain[nChains +
                senderLabelReceiverNonOrderCriticalChains.size() + runnablesNotPartOfCauseEffectChain.size()];

        int curActivity = 0;
        int curRunnable = 0;
        for(int i = 0; i < nChains; i++){
            int[] processingTimesForChains = new int[numRunnablesInChains[i]];
            for(int j = 0; j <  numRunnablesInChains[i]; j++) {
                processingTimesForChains[j] = processingTimesOfRunnables[runnablesInChains[curRunnable + j] - 1];
            }
            problemInstancesSingleChain[i] = new ProblemInstanceSingleChain(numberOfActivitiesInChain[i], 
                   null, periodsOfRunnables[runnablesInChains[curRunnable] - 1], 0, 0, 
                   processingTimesForChains, i, curActivity, this.nCores, jitters[runnablesInChains[curRunnable] - 1]);

           curActivity += numberOfActivitiesInChain[i];
           curRunnable += this.numRunnablesInChains[i];
        }
    }

    // returns assignment of a given message on network
    // simple first bin strategy, if no network is available returns -1
    private int AssignmentOfCommunicationsOnNetworksForBuses(double[] utilizationOnNetworks, double utilizationOfMessage){
        int assignment = -1;
        for(int i = 0; i < utilizationOnNetworks.length; i++) {
           if(utilizationOnNetworks[i] + utilizationOfMessage <= utilizationBound){
               utilizationOnNetworks[i] += utilizationOfMessage;
               assignment = i;
               break;
           }
        }
        return assignment;
    }
    
    // returns number of the last created activity + 1
    private int AssignFoundMappingForOrderCritical(){
        int curNumRunnable = 0;
        int curNumMessages = 0;
        int currentNumActivities = numRunnables;
        for(int i = 0; i < nChains; i++){
            int numRunnablesInChain = problemInstancesSingleChain[i].getNumRunnablesInTransaction();
            int[] runnablesInThisChain = Helpers.Copy(runnablesInChains, curNumRunnable, curNumRunnable + numRunnablesInChain);
            int[] communicationsInChains = Helpers.Copy(commTimeOrderCriticalMessages, curNumMessages, curNumMessages + numRunnablesInChain - 1);
            for(int j = 0; j < numRunnablesInChain - 1; j++) {
                int runnableSend = runnablesInThisChain[j] - 1;
                int runnableReceive = runnablesInThisChain[j + 1] - 1;
                int curLabel = senderLabelReceiveOrderCriticalChains.get(curNumMessages).get(1);
                int assignmentSource = mappings[runnableSend] - 1;
                int assignmentTarget = mappings[runnableReceive] - 1;
                
                // if this message must be scheduled add it to the activities
                int indexOfLabel = scheduledMessagesList.get(assignmentSource).get(assignmentTarget).indexOf(curLabel);
                if(indexOfLabel != -1){
                    if(!CC_Scheduling_WithJitter.IS_CAN_USE_CASE){
                        mappings[currentNumActivities] = assignmentTarget + solutionMap.getNumResources() + 1;
                    }
                    else{
                        mappings[currentNumActivities] = nCores;
                    }
                    
                    for(int k = 0; k < 3; k++) {
                        int label = senderLabelReceiveOrderCriticalChains.get(curNumMessages).get(k+1);
                        if(label != 0){
                            int curIndexOfLabel = scheduledMessagesList.get(assignmentSource).get(assignmentTarget).indexOf(label);
                            scheduledMessagesList.get(assignmentSource).get(assignmentTarget).remove(curIndexOfLabel);
                        }
                        else{
                            break;
                        }
                    }
                    
                    procTimes[currentNumActivities] = communicationsInChains[j];
                    periods[currentNumActivities] = ToSingleChain(i).getRequiredPeriod();
                    jitters[currentNumActivities] = ToSingleChain(i).getRequiredPeriod();
                    
                    if(CC_Scheduling_WithJitter.IS_CAN_USE_CASE){
                        senderOfMessage.add(assignmentSource);
                        int messageSize = (int) Math.floor(5.0/6.0 * (procTimes[currentNumActivities] - 75) - 44);
                        sizeOfMessage.add(messageSize);
                        numOfMessage.add(currentNumActivities);
                    }
                    
                    //add current message to the precedence adjacency list
                    precAdjList.add(new ArrayList<Integer>());
                    //this message must be added as a predecessor to the next runnable
                    precAdjList.get(runnableReceive).add(currentNumActivities);
                    //moreover, this runnable must be added as a predecessor to the message
                    precAdjList.get(currentNumActivities).add(runnableSend);
                    
                    currentNumActivities++;
                }
                else{
                    if(!precAdjList.get(runnableReceive).contains(runnableSend)){
                        precAdjList.get(runnableReceive).add(runnableSend); 
                    }
                }
                curNumMessages++;
            }
            curNumRunnable += numRunnablesInChain;
        }
        
        return currentNumActivities;
    }
    
    private int AssignFoundMappingNotOrderCritical(int curNActs){  
        int numCurMesOfRunnable = 0;
        for(int i = 0; i < senderLabelReceiverNonOrderCriticalChains.size(); i++) {
            int curLabel = senderLabelReceiverNonOrderCriticalChains.get(i).get(1);
            int runnableSend = senderLabelReceiverNonOrderCriticalChains.get(i).get(0) - 1;
            int runnableReceive = senderLabelReceiverNonOrderCriticalChains.get(i).get(2) - 1;
            int assignmentSource = mappings[runnableSend] - 1;
            int assignmentTarget = mappings[runnableReceive] - 1;
            
            // to compute the indexes for the processing time array, we need 
            // to follow when the sending runnable has change
            if(i != 0 && runnableSend != senderLabelReceiverNonOrderCriticalChains.get(i - 1).get(0) - 1){
                numCurMesOfRunnable = 0;
            }
            
            // if this message must be scheduled add it to the activities
            int indexOfLabel = scheduledMessagesList.get(assignmentSource).get(assignmentTarget).indexOf(curLabel);
            
            //System.out.println(runnableSend + " " + numCurMessageOfThisRunnable);
            
            if(indexOfLabel != -1){
                scheduledMessagesList.get(assignmentSource).get(assignmentTarget).remove(indexOfLabel);
                procTimes[curNActs] = commTimeNonOrderCriticalMessages.get(runnableSend).get(numCurMesOfRunnable);
                periods[curNActs] = periods[runnableSend];
                jitters[curNActs] = periods[runnableSend];
                if(CC_Scheduling_WithJitter.IS_CAN_USE_CASE){
                    senderOfMessage.add(assignmentSource);
                    int messageSize = (int) Math.floor(5.0/6.0 * (procTimes[curNActs] - 75) - 44);
                    sizeOfMessage.add(messageSize);
                    numOfMessage.add(curNActs);
                }
                
                //double messageUtilization = processingTimesOfActivities[currentNumActivities] * 1.0 / periodsOfActivities[currentNumActivities];
                if(!CC_Scheduling_WithJitter.IS_CAN_USE_CASE){
                    mappings[curNActs] = assignmentTarget + solutionMap.getNumResources() + 1;
                }
                else{
                    mappings[curNActs] = nCores;
                }
                
                
                /*activityAssignmentToResources[currentNumActivities] = AssignmentOfCommunicationsOnNetworks(utilizationOnNetworks, messageUtilization);
                if(activityAssignmentToResources[currentNumv] == -1){
                    System.out.println("It's not possible to map messages to the number of networks you provided!");
                    System.exit(0);
                }   
                else{
                    activityAssignmentToResources[currentNumActivities] += problemSolutionForMapping.getNumResources() + 1;
                }*/
                
                //add current message to the precedence adjacency list
                precAdjList.add(new ArrayList<Integer>());
                
                curNActs++;
            }
            numCurMesOfRunnable++;
        }
        return curNActs;
    }
    
    private void PutUseCaseToFile() throws IOException{
        writer = new FileWriter(Helpers.CANUseCaseFile,true);
        writer.write("nCANController = [");
        for (int i = 0; i < senderOfMessage.size() - 1; i++) {
            writer.write((senderOfMessage.get(i) + 1) + ",");
        }
        writer.write((senderOfMessage.get(senderOfMessage.size() - 1) + 1) + "];\n\n");
        
        writer.write("sizeOfMessages = [");
        for (int i = 0; i < sizeOfMessage.size() - 1; i++) {
            writer.write(sizeOfMessage.get(i) + ",");
        }
        writer.write(sizeOfMessage.get(sizeOfMessage.size() - 1) + "];\n\n");
        
        writer.write("numbersOfMessages = [");
        for (int i = 0; i < numOfMessage.size() - 1; i++) {
            writer.write(numOfMessage.get(i) + ",");
        }
        writer.write(numOfMessage.get(numOfMessage.size() - 1) + "];\n\n");
        
        writer.write("mappingOfRunnablesToBoards = [");
        for (int i = 0; i < numRunnables - 1; i++) {
            writer.write((mappings[i]) + ",");
        }
        writer.write((mappings[numRunnables - 1]) + "];\n\n");
        
        writer.close();
    }
    
    public void AssignFoundMapping(solutionMapping solutionMapping_, 
            ProbInstSched probInstSched, int solveZJ, double util) throws IOException, IloException{
        solutionMap = solutionMapping_;
        
        //this.nNetworks = (int) Math.ceil(problemSolutionForMapping.getCommunicationUtilization() * 1.0 / utilizationBound);
        if(CC_Scheduling_WithJitter.IS_CAN_USE_CASE){
            nNetworks = 1;
        }
        else{
            nNetworks = scheduledMessagesList.size();
        }
        
        int nCPUs = solutionMap.getNumResources();
        this.nCores = nCPUs + nNetworks;
        
        double[] utilizationOnNetworks = new double[nNetworks];
        Helpers.InitializeTo(utilizationOnNetworks, 0);
        
        // first fill the runnables part of all the runnable information
        int numActivities = numRunnables + numOfMessagestoSchedule;
        periods = new int [numActivities];
        procTimes = new int [numActivities];
        mappings = new int [numActivities];
        jitters = new int [numActivities];
        
        precAdjList = new ArrayList<>();
        for(int i = 0; i < numRunnables; i++) {
            precAdjList.add(new ArrayList<>());
            periods[i] = periodsOfRunnables[i];
            procTimes[i] = processingTimesOfRunnables[i];
            mappings[i] = solutionMap.getRunnablesAssignment()[i] + 1;
            jitters[i] = periods[i] / CC_Scheduling_WithJitter.COEFFICIENT_FOR_JITTER;
        }
        
        if(CC_Scheduling_WithJitter.IS_CAN_USE_CASE){
            senderOfMessage = new ArrayList<>();
            sizeOfMessage = new ArrayList<>();
            numOfMessage = new ArrayList<>();
        }
        
        int curNumActivities = AssignFoundMappingForOrderCritical();
        AssignFoundMappingNotOrderCritical(curNumActivities);
        
        if(CC_Scheduling_WithJitter.IS_CAN_USE_CASE){
            PutUseCaseToFile();
        }
        probInstSched.SetProblemInstanceScheduling(procTimes, periods, mappings, 
                precAdjList, nCores, jitters, nNetworks, solveZJ, util);
        
    }
 
    
    
    
    public int[] getCommTimeOrderCriticalMessages() {
        return commTimeOrderCriticalMessages;
    }

    public List<List<Integer>> getCommTimeNonOrderCriticalMessages() {
        return commTimeNonOrderCriticalMessages;
    }

    public List<List<Integer>> getSenderLabelReceiveOrderCriticalChains() {
        return senderLabelReceiveOrderCriticalChains;
    }

    public List<List<Integer>> getSenderLabelReceiverNonOrderCriticalChains() {
        return senderLabelReceiverNonOrderCriticalChains;
    }
    
    public int[] getRunnablesInCauseEffectChains() {
        return runnablesInChains;
    }
    
    public ProblemInstanceSingleChain ToSingleChain(int transaction){
        return problemInstancesSingleChain[transaction];
    }

    public int getNumAllCommunications() {
        return numCommunications;
    }
    
    public int getnNetworks() {
        return nNetworks;
    }

    public int[] getPeriodsOfRunnables() {
        return periodsOfRunnables;
    }

    public int[] getProcessingTimesOfRunnables() {
        return processingTimesOfRunnables;
    }

    public int getNumRunnables() {
        return numRunnables;
    }

    public int getnResources() {
        return nCores;
    }

    public int[] getSizeOfRunnables() {
        return sizeOfRunnables;
    }

    public int getMemoryBoundOnECU() {
        return memoryBoundOnECU;
    }

    public double getUtilizationBound() {
        return utilizationBound;
    }
    
    public ProblemInstanceSingleChain[] getProblemInstance() {
        return problemInstancesSingleChain;
    }

    public List<Integer> getRunnablesNotPartOfOrderedChain() {
        return runnablesNotPartOfCauseEffectChain;
    }

    public int getnTransactionsOrderCritical() {
        return nChains;
    }

    public int[] getNumRunnablesInTransactions() {
        return numRunnablesInChains;
    }

    public void setNumOfMessagestoSchedule(int numOfMessagestoSchedule) {
        this.numOfMessagestoSchedule = numOfMessagestoSchedule;
    }

    public void setScheduledMessagesList(ArrayList<ArrayList<ArrayList<Integer>>> scheduledMessagesList) {
        this.scheduledMessagesList = scheduledMessagesList;
    }


}
