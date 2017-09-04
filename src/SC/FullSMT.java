/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package SC;
import com.microsoft.z3.*;
import ilog.concert.IloException;
import ilog.concert.IloNumVar;
import ilog.concert.IloNumVarType;
import java.util.HashMap;
/**
 *
 * @author annaminaeva
 */
public class FullSMT {
    private ProbInstSched probInst;
    private IntExpr[] startTime;
    Context ctx;
    private Solver solver;
    protected int HP;
    
    private void PeriodConstraintsSetting(){
        for(int i = 0; i < probInst.getNumActs(); i++) {
            int period = probInst.getActs()[i].getPeriod();
            
            for(int k = 0; k < probInst.getActs()[i].getNumJobs(); k++) {
                IntExpr LB = ctx.mkInt(k * period + probInst.getActs()[i].getCriticalLengthBefore());
                solver.add(
                        ctx.mkGe(
                                startTime[probInst.getActs()[i].getNumFirstJоb() + k],
                                LB
                        )
                );
                
                IntExpr UB = ctx.mkInt((k + 2) * period - probInst.getActs()[i].getCritLengthAfter());
                solver.add(
                        ctx.mkLe(
                                startTime[probInst.getActs()[i].getNumFirstJоb() + k],
                                UB
                        )
                );
           }
        }
   }
    
    private void PrecedenceConstraintsSetting(){
        for(int i = 0; i < probInst.getNumActs(); i++) {
            for(int j = 0; j < probInst.getActs()[i].getPreds().size(); j++) {
                int actPrec = probInst.getActs()[i].getPreds().get(j);
                int actFol = i;
                
                for(int k = 0; k < probInst.getActs()[i].getNumJobs(); k++) {
                    int jobPrec = probInst.getActs()[actPrec].getNumFirstJоb() + k;
                    int jobFol = probInst.getActs()[actFol].getNumFirstJоb() + k;
                    
                    IntExpr pt = ctx.mkInt(probInst.getActs()[actPrec].getProcTime());
                    solver.add(
                            ctx.mkGe(
                                startTime[jobFol],
                                ctx.mkAdd(startTime[jobPrec], pt)
                            )
                    );
               } 
           } 
        }
    }
    
    private void PrecedenceConstraintsForJobsOfOneActivitySettingNZJ(){
        for (int i = 0; i < probInst.getNumActs(); i++) {
            Activity act = probInst.getActs()[i];
            IntExpr[] startTimeCur = new IntExpr[act.getNumJobs()];
            
            for (int j = act.getNumFirstJоb(); j < act.getNumFirstJоb() + act.getNumJobs(); j++) {
                startTimeCur[j - act.getNumFirstJоb()] = startTime[j];
            }
            
            IntExpr pt = ctx.mkInt(act.getProcTime());
            for (int j = 0; j < act.getNumJobs() - 1; j++) {
                solver.add(
                        ctx.mkGe(
                            startTimeCur[j + 1],
                            ctx.mkAdd(startTimeCur[j], pt)
                        )
                );
            }

            solver.add(
                    ctx.mkGe(
                        startTimeCur[0],
                        ctx.mkAdd(startTimeCur[act.getNumJobs() - 1], ctx.mkInt(act.getProcTime() - act.getHP()))
                    )
            );
        }
    }
    
    protected void setResConstrNZJPairJobs(Activity act1, Activity act2, 
            IntExpr curSTFirst, IntExpr curSTSecond, int addedValueToFirst){
        solver.add(
                ctx.mkOr(
                    ctx.mkLe(
                            ctx.mkAdd(
                                    curSTFirst,
                                    ctx.mkInt(act1.getProcTime() + addedValueToFirst)
                            ),
                            curSTSecond
                    ),
                    ctx.mkLe(
                            ctx.mkAdd(
                                    curSTSecond,
                                    ctx.mkInt(act2.getProcTime() - addedValueToFirst)
                            ),
                            curSTFirst
                    )
                )
        );
    }
    
    protected void ResConstrSetNZJPairOfActivities(Activity act1, Activity act2){
        int period1 = act1.getPeriod();
        int period2 = act2.getPeriod();
        int jobCounter1stActivity = act1.getNumFirstJоb();
        for(int nJob1 = 0; nJob1 < HP / act1.getPeriod(); nJob1++) {
            int jobCounter2ndActivity = act2.getNumFirstJоb();
            IntExpr curSTfromFirst = startTime[jobCounter1stActivity];
            jobCounter1stActivity++;

            int start = 0;
            if(act1.getIdInArray() == act2.getIdInInputData()){
                start = nJob1 + 1;
                jobCounter2ndActivity += nJob1 + 1;
            }
            
            for(int nJob2 = start; nJob2 < HP / act2.getPeriod(); nJob2++) {
                IntExpr curSTfromSecond = startTime[jobCounter2ndActivity];
                jobCounter2ndActivity++;
                int UB1 = (nJob1 + 2) * period1 - act1.getCritLengthAfter();
                int LB1 = nJob1 * period1 + act1.getCriticalLengthBefore();
                int UB2 = (nJob2 + 2) * period2 - act2.getCritLengthAfter();
                int LB2 = nJob2 * period2 + act2.getCriticalLengthBefore();
                if(!(UB1 + act1.getProcTime() < LB2 || UB2 + act2.getProcTime() < LB1)){
                    setResConstrNZJPairJobs(act1, act2, curSTfromFirst, curSTfromSecond, 0);
                }
            }
        } 
        
        int isZJ = 0;
        setResConstrInThe2ndHP(act1, act2, startTime, startTime, 
                act1.getNumFirstJоb(), act2.getNumFirstJоb(), isZJ);
    }
    
    protected void setResConstrZJPairJobs(Activity act1, Activity act2, 
            IntExpr curSTFirst, IntExpr curSTSecond, int nPeriodFirst, 
            int nPeriodSecond, int addedValueToFirst){
        
        solver.add(
                ctx.mkOr(
                    ctx.mkLe(
                            ctx.mkAdd(
                                    curSTFirst,
                                    ctx.mkInt(act1.getProcTime() + addedValueToFirst + nPeriodFirst * act1.getPeriod())
                            ),
                            ctx.mkAdd(
                                    curSTSecond,
                                    ctx.mkInt(nPeriodSecond * act2.getPeriod())
                            )
                                    
                    ),
                    ctx.mkLe(
                            ctx.mkAdd(
                                    curSTSecond,
                                    ctx.mkInt(act2.getProcTime() + nPeriodSecond * act2.getPeriod())
                            ),
                            ctx.mkAdd(
                                    curSTFirst,
                                    ctx.mkInt(addedValueToFirst + nPeriodFirst * act1.getPeriod())
                            )
                    )
                )
        );
    }
    
    
    protected void setResConstrInThe2ndHP(Activity act1, Activity act2, IntExpr[] startTime1,
            IntExpr[] startTime2, int nFirstJob1, int nFirstJob2, int isZJ){
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
            IntExpr curSTFirst = startTime1[nFirstJob1 + i * (1 - isZJ)];
            IntExpr curSTSecond = startTime2[nFirstJob2 + (act2.getNumJobs() - 1) * (1 - isZJ)];
            
            int LB1 = i * period1 + act1.getCriticalLengthBefore();
            int UB2 = (nJobs2 - 1 + 2) * period2 - act2.getCritLengthAfter();
            
            if(UB2 + act2.getProcTime() - act2.getHP() > LB1){
                if(isZJ == 1){
                    setResConstrZJPairJobs(act1, act2, curSTFirst, curSTSecond, i, nJobs2 - 1, 
                                probInst.getHP());
                }
                else{
                    setResConstrNZJPairJobs(act1, act2, curSTFirst, curSTSecond, act2.getHP());
                }  
            }
        }

        for (int i = 0; i < nJobs2; i++) {
            IntExpr curSTFirst = startTime2[nFirstJob2 + i * (1 - isZJ)];
            IntExpr curSTSecond = startTime1[nFirstJob1 + (act1.getNumJobs() - 1) * (1 - isZJ)];
            
            int LB1 = act2.getCriticalLengthBefore() + i * period2;
            int UB2 = (nJobs1 - 1 + 2) * period1 - act1.getCritLengthAfter();
            
            if(!(UB2  - act1.getHP() + act1.getProcTime() < LB1)){
                if(isZJ == 1){
                    setResConstrZJPairJobs(act2, act1, curSTFirst, curSTSecond, i, nJobs1 - 1, 
                                    probInst.getHP());
                }
                else{
                    setResConstrNZJPairJobs(act2, act1, curSTFirst, curSTSecond, probInst.getHP());
                }
            }
        }
    }
    
    private void ResourceConstraintsSettingZJ() {
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

                    IntExpr curSTFirst = startTime[nAct1];
                    IntExpr curSTSecond = startTime[nAct2];

                    for(int nJobs1 = 0; nJobs1 < localHP / period1; nJobs1++) {
                        for(int nJobs2 = 0; nJobs2 < localHP / period2; nJobs2++) {
                            int UB1 = (nJobs1 + 2) * period1 - act1.getCritLengthAfter();
                            int LB1 = nJobs1 * period1 + act1.getCriticalLengthBefore();
                            int UB2 = (nJobs2 + 2) * period2 - act2.getCritLengthAfter();
                            int LB2 = nJobs2 * period2 + act2.getCriticalLengthBefore();
                            if(!(UB1 + probInst.getActs()[nAct1].getProcTime() < LB2 
                                || UB2 + probInst.getActs()[nAct2].getProcTime() < LB1)){
                                int addedValueToFirst = 0;
                                setResConstrZJPairJobs(act1, act2, curSTFirst, curSTSecond, 
                                        nJobs1, nJobs2, addedValueToFirst);
                            }
                        }
                    }
                    
                    int isZJ = 1;
                    setResConstrInThe2ndHP(act1, act2, startTime, startTime, nAct1, nAct2, isZJ);
                }
            }
        }
    }
    
    private void ResourceConstraintsSettingNZJ(){
        for(int h = 0; h < probInst.getNumActs(); h++) {
            for(int p = h; p < probInst.getNumActs(); p++) {
               if(probInst.getActs()[h].getMapping() == 
                       probInst.getActs()[p].getMapping()){
                   
                    ResConstrSetNZJPairOfActivities(probInst.getActs()[h], probInst.getActs()[p]);
                }
            }
        }
   }
    
    protected void addJitterConstraintForAPairOfJobs(int numJobEarlier, int numJobLater,
            int noOfTheTaskIn1DarrayEarlierPeriod, int noOfTheTaskIn1DarrayLaterPeriod, Activity act){
        int period = act.getPeriod();
        solver.add(
                ctx.mkLe(
                        ctx.mkSub(
                                startTime[noOfTheTaskIn1DarrayLaterPeriod],
                                startTime[noOfTheTaskIn1DarrayEarlierPeriod]
                        ),
                        ctx.mkInt((numJobLater - numJobEarlier) * period + act.getJitter())
                )
        );
        
        solver.add(
                ctx.mkGe(
                        ctx.mkSub(
                                startTime[noOfTheTaskIn1DarrayLaterPeriod],
                                startTime[noOfTheTaskIn1DarrayEarlierPeriod]
                        ),
                        ctx.mkInt((numJobLater - numJobEarlier) * period - act.getJitter())
                )
        );
    }
    
    protected void addJitterConstrRelativeFirstAndLast(Activity act, int num1InST, int num2InST){
        int period = act.getPeriod();
        solver.add(
                ctx.mkLe(
                        ctx.mkSub(
                            startTime[num1InST],
                            startTime[num2InST]
                        ),
                        ctx.mkInt(period - HP + act.getJitter())
                )
        );

        solver.add(
                ctx.mkGe(
                    ctx.mkSub(
                        startTime[num1InST],
                        startTime[num2InST]
                    ),
                    ctx.mkInt(period - HP - act.getJitter())
                )
        );
    }
    
    protected void addJitterConstrForOneActRelative(Activity act, boolean is_for_full){
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
            addJitterConstraintForAPairOfJobs(k, k + 1, nTaskVarArrayEarlierPeriod, nTaskVarArrayLaterPeriod, act);
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
        
        addJitterConstrRelativeFirstAndLast(act, num1InST, num2InST);
    }
    
    protected void addJitterConstrForOneActAbsolute(Activity act, boolean is_for_full){
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
                addJitterConstraintForAPairOfJobs(k, j, nTaskVarArrayEarlierPeriod, nTaskVarArrayLaterPeriod, act);
            }
        } 
     }
    
    
    public FullSMT(ProbInstSched probInst_) {
        probInst = probInst_;
        HP = probInst.getHP();
        
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        ctx = new Context(cfg);
        solver = ctx.mkSolver();
        
        //encoding from 2D array to 1D array is [i][k] = [a[i].nStartJob + k]
        startTime = new IntExpr[probInst.getTotalNumOfJobs()];
        for (int i = 0; i < probInst.getTotalNumOfJobs(); i++) {
            startTime[i] = (IntExpr) ctx.mkConst(
                        ctx.mkSymbol("x_" + (i + 1)),
                        ctx.getIntSort());
        }
        
        PeriodConstraintsSetting();
        PrecedenceConstraintsSetting();
        PrecedenceConstraintsForJobsOfOneActivitySettingNZJ();
        
        if(!probInst.isZJ()){
            ResourceConstraintsSettingNZJ();
            PrecedenceConstraintsForJobsOfOneActivitySettingNZJ();
            
            boolean is_for_full = true;
            for(int i = 0; i < probInst.getNumActs(); i++) {
                if(CC_Scheduling_WithJitter.IS_JITTER_RELATIVE){
                    addJitterConstrForOneActRelative(probInst.getActs()[i], is_for_full);
                }
                else{
                    addJitterConstrForOneActAbsolute(probInst.getActs()[i], is_for_full);
                }
            }
        }
        else{
            ResourceConstraintsSettingZJ();
        }
    }
    
    public Solution solve(){
        Params p = ctx.mkParams();
        p.add("timeout", CC_Scheduling_WithJitter.TIME_LIMIT * 1000);
        solver.setParameters(p);
        if(solver.check() == Status.SATISFIABLE){
            Model m = solver.getModel();
            int[] STime = new int[probInst.getTotalNumOfJobs()];
            for (int i = 0; i < probInst.getTotalNumOfJobs(); i++){
                STime[i] = ((IntNum) m.evaluate(startTime[i], false)).getInt() % HP;
                //System.out.println(STime[i]);
            }
            Solution sol = new Solution(STime, probInst, probInst.isZJ());
            
            int curNumJobs = 0;
            for(int i = 0; i < probInst.getNumActs(); i++) {
                Activity act = probInst.getActs()[i];
                for(int k = 0; k < act.getNumJobs(); k++) {
                    // check precedence relations
                    for (int j = 0; j < act.getDirectSuccessors().size(); j++) {
                        Activity actSuc = probInst.getActs()[act.getDirectSuccessors().get(j)];
                        if(((IntNum) m.evaluate(startTime[curNumJobs], false)).getInt() + act.getProcTime()  > 
                                (((IntNum) m.evaluate(startTime[actSuc.getNumFirstJоb() + k], false)).getInt())){
                            System.out.println("PRECEDENCE CONSTRAINTS ARE NOT SATISFIED");
                            System.exit(0);
                        }
                    }
                    
                    curNumJobs++;
                }
            }
            CC_Scheduling_WithJitter.IS_OPTIMAL = true;
            return sol;
        }
        else{
            if(solver.check() == Status.UNKNOWN){
                CC_Scheduling_WithJitter.IS_OPTIMAL = false;
            }
            if(solver.check() == Status.UNSATISFIABLE){
                CC_Scheduling_WithJitter.IS_OPTIMAL = true;
            }
            return null;
        }
    }
    
}
