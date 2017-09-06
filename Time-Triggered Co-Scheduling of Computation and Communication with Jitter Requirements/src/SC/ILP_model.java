/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package SC;

import ilog.concert.IloException;
import ilog.concert.IloNumVar;
import ilog.concert.IloNumVarType;
import ilog.concert.IloObjective;
import ilog.cplex.IloCplex;

/**
 *
 * @author annaminaeva
 */
public class ILP_model {
    protected IloCplex solverILP;
    protected IloObjective ObjectiveILP;
    protected IloNumVar[] startTimeILP;
    protected int HP;
    protected int nConstr;
    
    protected void addJitterConstraintForAPairOfJobsILP(int numJobEarlier, int numJobLater,
            int noOfTheTaskIn1DarrayEarlierPeriod, int noOfTheTaskIn1DarrayLaterPeriod, Activity act, 
            IloNumVar[] startTime) throws IloException{
        int period = act.getPeriod();
        solverILP.addLe(solverILP.diff(
                        startTime[noOfTheTaskIn1DarrayLaterPeriod],
                        startTime[noOfTheTaskIn1DarrayEarlierPeriod]
                ),
                (numJobLater - numJobEarlier) * period + act.getJitter()
        );
        
        solverILP.addGe(solverILP.diff(
                        startTime[noOfTheTaskIn1DarrayLaterPeriod],
                        startTime[noOfTheTaskIn1DarrayEarlierPeriod]
                ),
                (numJobLater - numJobEarlier) * period - act.getJitter());
        nConstr+=2;
    }
    
    protected void addJitterConstrRelativeFirstAndLastILP(Activity act, int num1InST, int num2InST, 
            IloNumVar[] startTime) throws IloException{
        int period = act.getPeriod();
        solverILP.addLe(solverILP.diff(
                    startTime[num1InST],
                    startTime[num2InST]
                ),
                period - HP + act.getJitter()
        );

        solverILP.addGe(solverILP.diff(
                    startTime[num1InST],
                    startTime[num2InST]
                ),
                period - HP - act.getJitter()
        );
        nConstr+=2;
    }
    
    protected void addJitterConstrForOneActRelativeILP(Activity act, boolean is_for_full,
            IloNumVar[] startTime) throws IloException{
        for(int k = 0; k < act.getNumJobs() - 1; k++) {
            int nTaskVarArrayEarlierPeriod;
            int nTaskVarArrayLaterPeriod;
            if(is_for_full){
                nTaskVarArrayEarlierPeriod = act.getNumFirstJоb() + k;
                nTaskVarArrayLaterPeriod = act.getNumFirstJоb() + k + 1;  
            }
            else{
                nTaskVarArrayEarlierPeriod = k;
                nTaskVarArrayLaterPeriod = k + 1;
            }
            addJitterConstraintForAPairOfJobsILP(k, k + 1, nTaskVarArrayEarlierPeriod, nTaskVarArrayLaterPeriod, act, startTime);
        } 
        
        int num1InST;
        int num2InST;
        if(is_for_full){
            num1InST = act.getNumFirstJоb();
            num2InST = act.getNumFirstJоb() + act.getNumJobs() - 1;  
        }
        else{
            num1InST = 0;
            num2InST = act.getNumJobs() - 1;
        }
        
        addJitterConstrRelativeFirstAndLastILP(act, num1InST, num2InST, startTime);
    }
    
    protected void addJitterConstrForOneActAbsoluteILP(Activity act, boolean is_for_full,
            IloNumVar[] startTime) throws IloException{
        int nJobs = act.getNumJobs();
        for(int k = 0; k < nJobs; k++) {
            for (int j = k + 1; j < nJobs; j++) {
                int nTaskVarArrayEarlierPeriod;
                int nTaskVarArrayLaterPeriod;
                if(is_for_full){
                    nTaskVarArrayEarlierPeriod = act.getNumFirstJоb() + k;
                    nTaskVarArrayLaterPeriod = act.getNumFirstJоb() + j;  
                }
                else{
                    nTaskVarArrayEarlierPeriod = k;
                    nTaskVarArrayLaterPeriod = j;
                }
                addJitterConstraintForAPairOfJobsILP(k, j, nTaskVarArrayEarlierPeriod, nTaskVarArrayLaterPeriod, act, startTime);
            }
        } 
     }
    
    protected void setResConstrNZJPairJobsILP(Activity act1, Activity act2, 
            IloNumVar curSTFirst, IloNumVar curSTSecond, int addedValueToFirst, 
            int bigMCoeff) throws IloException{
        IloNumVar var1 = solverILP.numVar(0, 1, IloNumVarType.Int);
        solverILP.addLe(solverILP.sum(curSTFirst,
                        solverILP.prod(-1.0, curSTSecond),
                        solverILP.prod(-bigMCoeff * HP, var1)
                ),
                -act1.getProcTime() - addedValueToFirst
        );

        solverILP.addLe(solverILP.sum(curSTSecond,
                        solverILP.prod(-1.0, curSTFirst),
                        solverILP.prod(bigMCoeff * HP, var1)
                ),
                -act2.getProcTime() + bigMCoeff * HP + addedValueToFirst
        );
        nConstr+=2;
    }
    
    protected void setResConstrZJPairJobsILP(Activity act1, Activity act2, 
            IloNumVar curSTFirst, IloNumVar curSTSecond, long localHP, 
            int nPeriodFirst, int nPeriodSecond, int addedValueToFirst, 
            int bigMCoeff) throws IloException{
        
        IloNumVar var1 = solverILP.numVar(0, 1, IloNumVarType.Int);
        solverILP.addLe(solverILP.sum(curSTFirst,
                        solverILP.prod(-1.0, curSTSecond),
                        solverILP.prod(-bigMCoeff * localHP, var1)
                ),
                -act1.getProcTime() - nPeriodFirst * act1.getPeriod() 
                        + nPeriodSecond * act2.getPeriod() - addedValueToFirst
        );

        solverILP.addLe(solverILP.sum(curSTSecond,
                        solverILP.prod(-1.0, curSTFirst),
                        solverILP.prod(bigMCoeff * localHP, var1)
                ),
                -act2.getProcTime() + bigMCoeff * localHP + nPeriodFirst * act1.getPeriod() 
                        - nPeriodSecond * act2.getPeriod() + addedValueToFirst
        );
        nConstr+=2;
    }
    
    protected void setResConstrInThe2ndHPILP(Activity act1, Activity act2, IloNumVar[] startTime1,
            IloNumVar[] startTime2, int nFirstJob1, int nFirstJob2, int isZJ) throws IloException{
        int period1 = act1.getPeriod();
        int period2 = act2.getPeriod();
        int nJobs1 = act1.getHP() / period1;
        int nJobs2 = act2.getHP() / period2;
        
        if(act1.getIdInInputData() == act2.getIdInInputData()){
            nJobs1 = 1;
            nJobs2 = 1;
            if(act1.getNumJobs() == 1){
                nJobs1 = 0;
                nJobs2 = 0;
            }
        }
        
        for (int i = 0; i < nJobs1; i++) {
            IloNumVar curSTFirst = startTime1[nFirstJob1 + i * (1 - isZJ)];
            IloNumVar curSTSecond = startTime2[nFirstJob2 + (act2.getNumJobs() - 1) * (1 - isZJ)];
            if(curSTSecond.getUB() + (nJobs2 - 1) * period2 * isZJ - 
                    act2.getHP() + act2.getProcTime() > curSTFirst.getLB() + i * period1 * isZJ){
                if(isZJ == 1){
                    setResConstrZJPairJobsILP(act1, act2, curSTFirst, 
                                curSTSecond, act1.getHP(), i, nJobs2 - 1, 
                                act1.getHP(), 2);
                }
                else{
                    setResConstrNZJPairJobsILP(act1, act2, curSTFirst, curSTSecond, act2.getHP(), 2);
                }
                    
            }
        }

        for (int i = 0; i < nJobs2; i++) {
            IloNumVar curSTFirst = startTime2[nFirstJob2 + i * (1 - isZJ)];
            IloNumVar curSTSecond = startTime1[nFirstJob1 + (act1.getNumJobs() - 1) * (1 - isZJ)];
            if(!(curSTSecond.getUB() + (nJobs1 - 1) * period1 * isZJ - 
                    act1.getHP() + act1.getProcTime() < curSTFirst.getLB() + i * period2 * isZJ)){
                
                if(isZJ == 1){
                    setResConstrZJPairJobsILP(act2, act1, curSTFirst, 
                                    curSTSecond, act1.getHP(), i, nJobs1 - 1, 
                                    act1.getHP(), 2);
                }
                else{
                    setResConstrNZJPairJobsILP(act2, act1, curSTFirst, 
                        curSTSecond, act2.getHP(), 2);
                }
            }
        }
    }
    
    protected void setPrecedenceConstraintsForJobsOfTheActivityILP(Activity act, IloNumVar[] startTime) throws IloException{
        for (int i = 0; i < act.getNumJobs() - 1; i++) {
            solverILP.addGe(solverILP.diff(
                            startTime[i + 1], 
                            startTime[i]
                    ),
                    act.getProcTime()
            );
            nConstr++;
        }
        
        solverILP.addGe(solverILP.diff(
                        startTime[0], 
                        startTime[act.getNumJobs() - 1]
                ),
                act.getProcTime() - act.getHP()
        );
        nConstr++;
    }
    
    public void printNConstr(){
        System.out.println(nConstr);
    }
}
