/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

package SC;

import ilog.concert.IloException;
import ilog.concert.IloNumVar;
import ilog.concert.IloNumVarType;
import ilog.cplex.IloCplex;
import java.io.IOException;

/**
 *
 * @author minaeann
 */
public class FullILP extends ILP_model{
    protected ProbInstSched probInst;
    
    private void PeriodConstraintsSetting() throws IloException{
        for(int i = 0; i < probInst.getNumActs(); i++) {
            int period = probInst.getActs()[i].getPeriod();
            
            for(int k = 0; k < probInst.getActs()[i].getNumJobs(); k++) {
                startTimeILP[probInst.getActs()[i].getNumFirstJоb() + k].setLB(
                        k * period + probInst.getActs()[i].getCriticalLengthBefore());
                
                startTimeILP[probInst.getActs()[i].getNumFirstJоb() + k].setUB(
                        (k + 2) * period - probInst.getActs()[i].getCritLengthAfter());
            }
        }
   }

    private void PrecedenceConstraintsSetting() throws IloException{
        for(int i = 0; i < probInst.getNumActs(); i++) {
            for(int j = 0; j < probInst.getActs()[i].getPreds().size(); j++) {
                int actPrec = probInst.getActs()[i].getPreds().get(j);
                int actFol = i;
                
                for(int k = 0; k < probInst.getActs()[i].getNumJobs(); k++) {
                    int jobPrec = probInst.getActs()[actPrec].getNumFirstJоb() + k;
                    int jobFol = probInst.getActs()[actFol].getNumFirstJоb() + k;
                    solverILP.addGe(
                            solverILP.sum(
                                    startTimeILP[jobFol],
                                    solverILP.prod(-1.0, startTimeILP[jobPrec])
                            ),
                            probInst.getActs()[actPrec].getProcTime()
                    );
               } 
           } 
        }
    }
    
    private void PrecedenceConstraintsForJobsOfOneActivitySettingNZJ() throws IloException{
        for (int i = 0; i < probInst.getNumActs(); i++) {
            Activity act = probInst.getActs()[i];
            IloNumVar[] startTimeCur = new IloNumVar[act.getNumJobs()];
            
            for (int j = act.getNumFirstJоb(); j < act.getNumFirstJоb() + act.getNumJobs(); j++) {
                startTimeCur[j - act.getNumFirstJоb()] = startTimeILP[j];
            }
            setPrecedenceConstraintsForJobsOfTheActivityILP(act, startTimeCur);
        }
        
    }

    protected void ResConstrSetNZJPairOfActivities(Activity act1, Activity act2) throws IloException{
        int jobCounter1stActivity = act1.getNumFirstJоb();
        for(int j = 0; j < HP / act1.getPeriod(); j++) {
            int jobCounter2ndActivity = act2.getNumFirstJоb();
            IloNumVar curSTfromFirst = startTimeILP[jobCounter1stActivity];
            jobCounter1stActivity++;

            int start = 0;
            if(act1.getIdInArray() == act2.getIdInInputData()){
                start = j + 1;
                jobCounter2ndActivity += j + 1;
            }
            
            for(int l = start; l < HP / act2.getPeriod(); l++) {
                IloNumVar curSTfromSecond = startTimeILP[jobCounter2ndActivity];
                jobCounter2ndActivity++;
                if(!(curSTfromFirst.getUB() + act1.getProcTime() < curSTfromSecond.getLB() ||
                    curSTfromSecond.getUB() + act2.getProcTime() < curSTfromFirst.getLB())){
                    
                    setResConstrNZJPairJobsILP(act1, act2, curSTfromFirst, curSTfromSecond, 0, 2);
                }
            }
        } 
        
        int isZJ = 0;
        setResConstrInThe2ndHPILP(act1, act2, startTimeILP, startTimeILP, 
                act1.getNumFirstJоb(), act2.getNumFirstJоb(), isZJ);
    }
    
    private void ResourceConstraintsSettingNZJ() throws IloException{
        for(int h = 0; h < probInst.getNumActs(); h++) {
            for(int p = h; p < probInst.getNumActs(); p++) {
               if(probInst.getActs()[h].getMapping() == 
                       probInst.getActs()[p].getMapping() 
                       //&& !probInst.getActs()[h].getDirectSuccessors().contains(p) 
                       //&& !probInst.getActs()[h].getPreds().contains(p)
                       ){
                   
                    ResConstrSetNZJPairOfActivities(probInst.getActs()[h], probInst.getActs()[p]);
                }
            }
        }
   }

    private void ResourceConstraintsSettingZJ() throws IloException{
        for(int nAct1 = 0; nAct1 < probInst.getNumActs(); nAct1++) {
            Activity act1 = probInst.getActs()[nAct1];
            int period1 = act1.getPeriod();

            for(int nAct2 = nAct1 + 1; nAct2 < probInst.getNumActs(); nAct2++) {
                Activity act2 = probInst.getActs()[nAct2];
                int period2 = act2.getPeriod();
                int localHP = period1 * period2 / (int) ProbInstSched.gcd(period1, period2);

                if(act1.getMapping() == act2.getMapping() 
                        //&& !act1.getAllPredecessors().contains(p) 
                        //&& !act1.getAllSuccessors().contains(p)
                        ){

                    IloNumVar curSTFirst = startTimeILP[nAct1];
                    IloNumVar curSTSecond = startTimeILP[nAct2];

                    for(int nJobs1 = 0; nJobs1 < localHP / period1; nJobs1++) {
                        for(int nJobs2 = 0; nJobs2 < localHP / period2; nJobs2++) {
                            if(!(curSTFirst.getUB() + nJobs1 * period1 + probInst.getActs()[nAct1].getProcTime() 
                                    < curSTSecond.getLB() + nJobs2 * period2 
                                || curSTSecond.getUB() + nJobs2 * period2 + probInst.getActs()[nAct2].getProcTime() 
                                    < curSTFirst.getLB() + nJobs1 * period1 )){
                                int addedValueToFirst = 0;
                                int bigMCoef = 1;
                                setResConstrZJPairJobsILP(act1, act2, curSTFirst, curSTSecond, 
                                        localHP, nJobs1, nJobs2, addedValueToFirst, bigMCoef);
                            }
                        }
                    }
                    
                    int isZJ = 1;
                    setResConstrInThe2ndHPILP(act1, act2, startTimeILP, startTimeILP, nAct1, nAct2, isZJ);
                }
            }
        }
    }
    
    public FullILP(ProbInstSched probInst_) throws IloException{   
        solverILP = new IloCplex();
        probInst = probInst_;
        HP = (int) probInst.getHP();
        
        //encoding from 2D array to 1D array is [i][k] = [i*nJobs + k]
        startTimeILP = solverILP.numVarArray(probInst.getTotalNumOfJobs(),
                0, HP - 1, IloNumVarType.Int);
        //orderVariable = solver.numVarArray(scheduledTransactions.getnJobsScheduled(),
        //       0, 1, IloNumVarType.Bool);
       
        int[] coefficients = new int[probInst.getTotalNumOfJobs()];
        Helpers.InitializeTo(coefficients, 0);
        ObjectiveILP = solverILP.addMinimize(solverILP.scalProd(coefficients, startTimeILP));
                
        // as it is implemented as bound settings, no constraints are created
        PeriodConstraintsSetting();
        
        // Precedence constraints are set without saving them in the program as well. Save time.
        PrecedenceConstraintsSetting();
        
        if(!probInst.isZJ()){
            ResourceConstraintsSettingNZJ();
            PrecedenceConstraintsForJobsOfOneActivitySettingNZJ();
            
            boolean is_for_full = true;
            for(int i = 0; i < probInst.getNumActs(); i++) {
                if(CC_Scheduling_WithJitter.IS_JITTER_RELATIVE){
                    addJitterConstrForOneActRelativeILP(probInst.getActs()[i], is_for_full, startTimeILP);
                }
                else{
                    addJitterConstrForOneActAbsoluteILP(probInst.getActs()[i], is_for_full, startTimeILP);
                }
            }
        }
        else{
            ResourceConstraintsSettingZJ();
        }
        
        //this.ModelToFile(Helpers.outputFileForModels);
    }
    
    public Solution Solve() throws IloException, IOException{
        //this.ModelToFile(Helpers.outputFileForModels);
        solverILP.setParam(IloCplex.IntParam.TimeLimit, CC_Scheduling_WithJitter.TIME_LIMIT);
        if(solverILP.solve()){
            double[][] x = new double[probInst.getNumActs()][probInst.getHP()];
            Helpers.InitializeTo(x, 0);
            double[] startT = solverILP.getValues(startTimeILP);
            
            if(!probInst.isZJ()){
                int curNumJobs = 0;
                for(int i = 0; i < probInst.getNumActs(); i++) {
                    Activity act = probInst.getActs()[i];
                    for(int k = 0; k < act.getNumJobs(); k++) {
                        // check precedence relations
                        for (int j = 0; j < act.getDirectSuccessors().size(); j++) {
                            Activity actSuc = probInst.getActs()[act.getDirectSuccessors().get(j)];
                            if((int) Math.round(solverILP.getValues(startTimeILP)[curNumJobs]) + act.getProcTime()  > 
                                    (int) Math.round(solverILP.getValues(startTimeILP)[actSuc.getNumFirstJоb() + k])){
                                System.out.println("PRECEDENCE CONSTRAINTS ARE NOT SATISFIED");
                                System.exit(0);
                            }
                        }

                        x[i][(int) Math.round(solverILP.getValues(startTimeILP)[curNumJobs]) % HP] = 1.0;
                        curNumJobs++;
                    }
                }
            }
            else{
                for(int i = 0; i < probInst.getNumActs(); i++) {
                    Activity act = probInst.getActs()[i];
                    for(int k = 0; k < probInst.getHP() / act.getPeriod(); k++) {
                        x[i][(int) Math.round((solverILP.getValues(startTimeILP)[i]) + k * act.getPeriod()) % HP] = 1.0;
                    }
                }
            }
            
            Solution problemSolution = new Solution(x, probInst);
            
            return problemSolution;
        }
        else{
            if(solverILP.getStatus() != IloCplex.Status.Infeasible){
                CC_Scheduling_WithJitter.IS_OPTIMAL = false;
            }
            return null;
        }
   }
    
     public void ModelToFile(String outputFile) throws IloException{
            this.solverILP.exportModel(outputFile);
    }
    
     public void end() throws IloException{
       solverILP.end();
   }
}
