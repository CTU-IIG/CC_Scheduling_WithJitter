package SC;

import com.microsoft.z3.*;
import ilog.concert.IloException;
import ilog.concert.IloNumVar;
import ilog.concert.IloNumVarType;
import ilog.concert.IloObjective;
import ilog.concert.IloRange;
import ilog.cplex.IloCplex;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;

/**
 *
 * @author minaeann
 */
public class SubModel extends ILP_model{
    //SMT
    private Optimize solverSMT;
    private IntExpr[] startTimeSMT;
    private Context ctx;
    
    //ILP
    private IloNumVar[] startTimeSecondActivity;
    private List<List<List<Integer>>> intsOfResConstrsJobs;
    private int[][] boundsOnJobs;
    private List<List<List<Integer>>> secondIntervalsOfResourceConstraintsForJobs;
    
    private int[][] secondBoundsOnJobs;
    private boolean isFeasible;
    private boolean isScheduledByOpt;
    private List<Integer> nInfeasActs;
    
    private Activity activity;
    private ScheduledActs schedActs;
    private Activity secondActivity;
    private boolean toBeSolvedByILP;

    public boolean isIsFeasible() {
        return isFeasible;
    }

    public boolean isScheduledByOpt() {
        return isScheduledByOpt;
    }

    private void periodConstraintsSetting(Activity activity, int[][] boundsOnJobs) throws IloException{
        int period = activity.getPeriod();
        for(int j = 0; j < activity.getHP() / activity.getPeriod(); j++) {
            boundsOnJobs[j][0] = j * period + activity.getCriticalLengthBefore();
            boundsOnJobs[j][1] = (j + 2) * period - activity.getCritLengthAfter();
        }
    }
    
    private void setPrecedenceConstraints(Activity activity, int[][] boundsOnJobs) throws IloException{
        for(int i = 0; i < activity.getPreds().size(); i++) {
            // if it's the second activity and it is in precedence relations with 
            // the first activity, skip it
            if(secondActivity != null){
                if(secondActivity.getPreds().contains(this.activity.getIdInArray()) || 
                        this.activity.getPreds().contains(secondActivity.getIdInArray())){
                    continue;
                }
            }
            
            for(int j = 0; j < activity.getHP() / activity.getPeriod(); j++) {
                int nPred = activity.getPreds().get(i);
                int indPredInST = schedActs.getNumbersOfScheduledActivities().indexOf(nPred);
                if(indPredInST == -1){
                    System.out.println("Some of the predecessors of currently scheduled activity are not already scheduled");
                }
                
                for(int k = 0; k < activity.getAllSuccessors().size(); k++) {
                   if(Helpers.ArrayListContainsValue(schedActs.getNumbersOfScheduledActivities(), activity.getAllSuccessors().get(k))) {
                       System.out.println("\n\n\n\n\n\n\n\n Problem! One of the successors of the scheduled activity are already scheduled!\n\n\n\n\n\n\n\n");
                   }
                }
                
                int tPredEnds = 
                        schedActs.getStartTimes().get(indPredInST).get(j) +
                        schedActs.getProbInst().getActs()[nPred].getProcTime();
                if(boundsOnJobs[j][0] < tPredEnds){
                    boundsOnJobs[j][0] = tPredEnds;
                }
            }
        }
    }
    
    private void concatenateIntervals(List<List<Integer>> intsOfResConstrs){
        for(int i = 0; i < intsOfResConstrs.size() - 1; i++) {
            if(intsOfResConstrs.get(i).get(0) > intsOfResConstrs.get(i).get(1))
                System.out.println("PROBLEM WITH SORTING WHILE CONCATENATING");
            if(intsOfResConstrs.get(i + 1).get(0) < intsOfResConstrs.get(i).get(1)){
                intsOfResConstrs.get(i).set(1, Math.max(intsOfResConstrs.get(i).get(1), intsOfResConstrs.get(i + 1).get(1)));
                intsOfResConstrs.remove(i + 1);
                i--;
            }
        }
    }
    
    private void obtainResourceIntervalsWithPreemption(int[][] boundsOnJobs, Activity act, List<List<List<Integer>>> intsOfResConstrsJobs){
        int nUsedRes = act.getMapping() - 1;
        int startPrevInt = 0;
        int nJobs = act.getHP() / act.getPeriod();
        for(int j = 0; j < nJobs; j++) {
            //find interval for this job
            int startInterval = startPrevInt;
            boolean isStartIntPrevSet = false;
            
            for(int k = startInterval; k < schedActs.getIntsOfResConstrs().get(nUsedRes).size(); k++) {
                int endCurInt = schedActs.getIntsOfResConstrs().get(nUsedRes).get(k).get(1);
                if(j != nJobs - 1 && endCurInt > boundsOnJobs[j + 1][0] && !isStartIntPrevSet){
                    startPrevInt = k;
                    isStartIntPrevSet = true;
                }
                
                if(boundsOnJobs[j][0] >= schedActs.getIntsOfResConstrs().get(nUsedRes).get(k).get(1)){
                    // due to precedence constraints this interval should not be considered
                    continue;
                }

                if(schedActs.getIntsOfResConstrs().get(nUsedRes).get(k).get(0) < boundsOnJobs[j][1] + act.getProcTime()){
                    intsOfResConstrsJobs.get(j).add(new ArrayList<>());
                    int last = intsOfResConstrsJobs.get(j).size() - 1;
                    intsOfResConstrsJobs.get(j).get(last).add(
                            schedActs.getIntsOfResConstrs().get(nUsedRes).get(k).get(0) - act.getProcTime());
                    intsOfResConstrsJobs.get(j).get(last).add(
                            schedActs.getIntsOfResConstrs().get(nUsedRes).get(k).get(1));
                }

                if(schedActs.getIntsOfResConstrs().get(nUsedRes).get(k).get(1) >= boundsOnJobs[j][1] + act.getProcTime()){
                    /*startPrevInt = k;
                    if(schedActs.getIntsOfResConstrs().get(nUsedRes).get(k).get(1) == boundsOnJobs[j][1] + activity.getProcTime()){
                        startPrevInt = k + 1;
                    }*/
                    break;
                }
                
            }
            
            if(!intsOfResConstrsJobs.get(j).isEmpty()){
                concatenateIntervals(intsOfResConstrsJobs.get(j));
            }
        }
        
        // we need to add intervals of the first period to the last job due to the deadline extention
        int nCurJob = nJobs - 1;
        for (int i = 0; i < schedActs.getIntsOfResConstrs().get(nUsedRes).size(); i++) {
            intsOfResConstrsJobs.get(nCurJob).add(
                    Arrays.asList(
                            schedActs.getIntsOfResConstrs().get(nUsedRes).get(i).get(0) - act.getProcTime() + act.getHP(),
                            schedActs.getIntsOfResConstrs().get(nUsedRes).get(i).get(1) + act.getHP()
                    )
            ); 
        }
        
        if(!intsOfResConstrsJobs.get(nCurJob).isEmpty()){
            // move start interval to the end if the start of first interval is 
            // negative and it's an activity with 1 job
            if(intsOfResConstrsJobs.get(nCurJob).get(0).get(0) < 0 && nJobs == 1){
                intsOfResConstrsJobs.get(nCurJob).add(
                        Arrays.asList(
                                2 * act.getHP() + intsOfResConstrsJobs.get(nCurJob).get(0).get(0),
                                2 * act.getHP()
                        )
                );
            }
            
            concatenateIntervals(intsOfResConstrsJobs.get(nCurJob));
        }
       
    }
    
    private void obtainResourceIntervals(int[][] boundsOnJobs, Activity act, List<List<List<Integer>>> intsOfResConstrsJobs){
        int nUsedRes = act.getMapping() - 1;
        int startPrevInt = 0;
        int nJobs = act.getHP() / act.getPeriod();
        for(int j = 0; j < nJobs; j++) {
            //find interval for this job
            int startInterval = startPrevInt;
            boolean isStartIntPrevSet = false;
            
            for(int k = startInterval; k < schedActs.getIntsOfResConstrs().get(nUsedRes).size(); k++) {
                int endCurInt = schedActs.getIntsOfResConstrs().get(nUsedRes).get(k).get(1);
                if(j != nJobs - 1 
                        && endCurInt > boundsOnJobs[j + 1][0]
                        && !isStartIntPrevSet){
                    startPrevInt = k;
                    isStartIntPrevSet = true;
                }
                
                if(boundsOnJobs[j][0] >= schedActs.getIntsOfResConstrs().get(nUsedRes).get(k).get(1)){
                    // due to precedence constraints this interval should not be considered
                    continue;
                }

                if(schedActs.getIntsOfResConstrs().get(nUsedRes).get(k).get(0) < boundsOnJobs[j][1] + act.getProcTime()){
                    intsOfResConstrsJobs.get(j).add(new ArrayList<>());
                    int last = intsOfResConstrsJobs.get(j).size() - 1;
                    intsOfResConstrsJobs.get(j).get(last).add(
                            schedActs.getIntsOfResConstrs().get(nUsedRes).get(k).get(0) - act.getProcTime());
                    intsOfResConstrsJobs.get(j).get(last).add(
                            schedActs.getIntsOfResConstrs().get(nUsedRes).get(k).get(1));
                }

                if(schedActs.getIntsOfResConstrs().get(nUsedRes).get(k).get(1) >= boundsOnJobs[j][1] + act.getProcTime()){
                    /*startPrevInt = k;
                    if(schedActs.getIntsOfResConstrs().get(nUsedRes).get(k).get(1) == boundsOnJobs[j][1] + activity.getProcTime()){
                        startPrevInt = k + 1;
                    }*/
                    break;
                }
                
            }
            
            if(!intsOfResConstrsJobs.get(j).isEmpty()){
                concatenateIntervals(intsOfResConstrsJobs.get(j));
            }
        }
        
        // we need to add intervals of the first period to the last job due to the deadline extention
        int nCurJob = nJobs - 1;
        for (int i = 0; i < schedActs.getIntsOfResConstrs().get(nUsedRes).size(); i++) {
            //we add them only till the first period
            if(schedActs.getIntsOfResConstrs().get(nUsedRes).get(i).get(0) > boundsOnJobs[nCurJob][1] % act.getPeriod()){
                break;
            }
            
            intsOfResConstrsJobs.get(nCurJob).add(
                    Arrays.asList(
                            schedActs.getIntsOfResConstrs().get(nUsedRes).get(i).get(0) - act.getProcTime() + act.getHP(),
                            schedActs.getIntsOfResConstrs().get(nUsedRes).get(i).get(1) + act.getHP()
                    )
            ); 
        }
        
        if(!intsOfResConstrsJobs.get(nCurJob).isEmpty()){
            // move start interval to the end if the start of first interval is 
            // negative and it's an activity with 1 job
            if(intsOfResConstrsJobs.get(nCurJob).get(0).get(0) < 0 && nJobs == 1){
                intsOfResConstrsJobs.get(nCurJob).add(
                        Arrays.asList(
                                2 * act.getHP() + intsOfResConstrsJobs.get(nCurJob).get(0).get(0),
                                2 * act.getHP()
                        )
                );
            }
            
            concatenateIntervals(intsOfResConstrsJobs.get(nCurJob));
        }
       
    }
    
    private void setConstraintsAndBoundsForScheduledActivities(List<List<Integer>> resIntervals, 
            int numJob, int[][] boundsOnJobs) throws IloException{
        if(resIntervals.get(0).get(0) <= boundsOnJobs[numJob][0]){
            //first interval starts at the beginning of the period
            //set as bound
            boundsOnJobs[numJob][0] = resIntervals.get(0).get(1);
            resIntervals.remove(0);
        }
        
        if(!resIntervals.isEmpty() && 
                resIntervals.get(resIntervals.size() - 1).get(1) >= boundsOnJobs[numJob][1]){
            //first interval starts at the beginning of the period
            //set as bound
            boundsOnJobs[numJob][1] = resIntervals.get(resIntervals.size() - 1).get(0);
            resIntervals.remove(resIntervals.size() - 1);
        }
        
        if(boundsOnJobs[numJob][0] > boundsOnJobs[numJob][1]){
            nInfeasActs.add(numJob);
            isFeasible = false;
        }
    }
    
    private void setSchedActsAndPeriodUsingExistingInts(Activity activity, 
            List<List<List<Integer>>> intsOfResConstrsForJobs, int[][] boundsOnJobs) throws IloException{
        int nUsedResource = activity.getMapping() - 1;
        
        if(!schedActs.getIntsOfResConstrs().get(nUsedResource).isEmpty()){
            for(int j = 0; j < activity.getNumJobs(); j++) {
                if(!intsOfResConstrsForJobs.get(j).isEmpty()){
                    setConstraintsAndBoundsForScheduledActivities(intsOfResConstrsForJobs.get(j), j, boundsOnJobs);
                }
            }
        }
    }
     
    public void setSTBoundsAndIntsForILPNZJ(Activity activity, IloNumVar[] startTime, int[][] boundsOnJobs,
            List<List<List<Integer>>> intsOfResConstrsJobs) throws IloException{
        for(int i = 0; i < activity.getNumJobs(); i++) {
            startTime[i].setLB(boundsOnJobs[i][0]);
            startTime[i].setUB(boundsOnJobs[i][1]);
            
            for(int j = 0; j < intsOfResConstrsJobs.get(i).size(); j++) {
                IloNumVar var1 = solverILP.numVar(0, 1, IloNumVarType.Int);
                solverILP.addGe(
                        solverILP.sum(
                                startTime[i], 
                                solverILP.prod(HP, var1)
                        ), 
                        intsOfResConstrsJobs.get(i).get(j).get(1)
                );
                
                solverILP.addLe(
                        solverILP.sum(
                                startTime[i], 
                                solverILP.prod(HP, var1)
                        ), 
                        intsOfResConstrsJobs.get(i).get(j).get(0) + HP
                );
                nConstr++;
            }
        }
    }
    
    public void setSTBoundsAndIntervalsForILPZJ(Activity activity, IloNumVar[] startTime, int[][] boundsOnJobs,
            List<List<List<Integer>>> resInts) throws IloException{
        startTime[0].setLB(boundsOnJobs[0][0]);
        startTime[0].setUB(boundsOnJobs[0][1]);
        
        int period = activity.getPeriod();
        int nJobs = activity.getHP() / period;
        for(int i = 0; i < nJobs; i++) {
            for(int j = 0; j < resInts.get(i).size(); j++) {
                IloNumVar var1 = solverILP.numVar(0, 1, IloNumVarType.Int);
                solverILP.addGe(
                        solverILP.sum(
                                startTime[0], 
                                solverILP.prod(HP, var1)
                        ), 
                        resInts.get(i).get(j).get(1) - period * i
                );
                solverILP.addLe(
                        solverILP.sum(
                                startTime[0], 
                                solverILP.prod(HP, var1)
                        ), 
                        resInts.get(i).get(j).get(0) + HP - period * i
                );
                nConstr++;
            }
        }
    }
    
    private void setLBAndUB_SMT(IntExpr[] startTime, int index){
        BoolExpr f = ctx.mkGe(
                        startTime[index],
                        ctx.mkInt(boundsOnJobs[index][0])
                );
        solverSMT.Add(f);
       
        f = ctx.mkLe(
                        startTime[index],
                        ctx.mkInt(boundsOnJobs[index][1])
                );
        solverSMT.Add(f);
        
        
        nConstr += 2;
    }
    
    public void setSTBoundsAndIntervalsForSMTZJ(Activity activity, IntExpr[] startTime, int[][] boundsOnJobs,
            List<List<List<Integer>>> resInts){
        setLBAndUB_SMT(startTime, 0);
        
        int period = activity.getPeriod();
        int nJobs = activity.getHP() / period;
        for(int i = 0; i < nJobs; i++) {
            for(int j = 0; j < resInts.get(i).size(); j++) {
                solverSMT.Add(
                    ctx.mkOr(
                        ctx.mkGe(
                                startTime[0],
                                ctx.mkInt(resInts.get(i).get(j).get(1) - period * i)

                        ),
                        ctx.mkLe(
                                startTime[0],
                                ctx.mkInt(resInts.get(i).get(j).get(0) - period * i)
                        )
                    )
                );
                nConstr++;
            }
        }
    }
    
    public void setSTBoundsAndIntsForSATNZJ(Activity activity, IntExpr[] startTime, int[][] boundsOnJobs,
            List<List<List<Integer>>> intsOfResConstrsJobs){
        for(int i = 0; i < activity.getNumJobs(); i++) {
            setLBAndUB_SMT(startTime, i);
            
            for(int j = 0; j < intsOfResConstrsJobs.get(i).size(); j++) {
                BoolExpr f = ctx.mkOr(
                        ctx.mkGe(
                                startTime[i],
                                ctx.mkInt(intsOfResConstrsJobs.get(i).get(j).get(1))
                        ),
                        ctx.mkLe(
                                startTime[i],
                                ctx.mkInt(intsOfResConstrsJobs.get(i).get(j).get(0))
                        )
                    );
                
                solverSMT.Add(f);
                nConstr++;
            }
        }
    }
    
    private void setJitterConstraintsILP(Activity activity, IloNumVar[] startTime) throws IloException{
        if(activity.getJitter() < activity.getSlack()){
            boolean is_for_full = false;
            if(CC_Scheduling_WithJitter.IS_JITTER_RELATIVE){
                addJitterConstrForOneActRelativeILP(activity, is_for_full, startTime);
            }
            else{
                addJitterConstrForOneActAbsoluteILP(activity, is_for_full, startTime);
            }
        }
    }
    
    protected void addJitterConstraintForAPairOfJobsSMT(int numJobEarlier, int numJobLater,
            int noOfTheTaskIn1DarrayEarlierPeriod, int noOfTheTaskIn1DarrayLaterPeriod, 
            Activity act, IntExpr[] startTime){
        int period = act.getPeriod();
        solverSMT.Add(
                ctx.mkLe(
                        ctx.mkSub(
                                startTime[noOfTheTaskIn1DarrayLaterPeriod],
                                startTime[noOfTheTaskIn1DarrayEarlierPeriod]
                        ),
                        ctx.mkInt((numJobLater - numJobEarlier) * period + act.getJitter())
                )
        );
        
        solverSMT.Add(
                ctx.mkGe(
                        ctx.mkSub(
                                startTime[noOfTheTaskIn1DarrayLaterPeriod],
                                startTime[noOfTheTaskIn1DarrayEarlierPeriod]
                        ),
                        ctx.mkInt((numJobLater - numJobEarlier) * period - act.getJitter())
                )
        );
        nConstr += 2;
    }
    
    protected void addJitterConstrRelativeFirstAndLastSMT(Activity act, int num1InST, 
            int num2InST, IntExpr[] startTime){
        int period = act.getPeriod();
        solverSMT.Add(
                ctx.mkLe(
                        ctx.mkSub(
                            startTime[num1InST],
                            startTime[num2InST]
                        ),
                        ctx.mkInt(period - HP + act.getJitter())
                )
        );

        solverSMT.Add(
                ctx.mkGe(
                    ctx.mkSub(
                        startTime[num1InST],
                        startTime[num2InST]
                    ),
                    ctx.mkInt(period - HP - act.getJitter())
                )
        );
        nConstr += 2;
    }
    
    
    protected void addJitterConstrForOneActRelativeSMT(Activity act, IntExpr[] startTime){
        for(int k = 0; k < act.getNumJobs() - 1; k++) {
            int nTaskVarArrayEarlierPeriod = k;
            int nTaskVarArrayLaterPeriod = k + 1;
            addJitterConstraintForAPairOfJobsSMT(k, k + 1, nTaskVarArrayEarlierPeriod, 
                    nTaskVarArrayLaterPeriod, act, startTime);
        } 
        
        int num1InST = 0;
        int num2InST = act.getNumJobs() - 1;
        addJitterConstrRelativeFirstAndLastSMT(act, num1InST, num2InST, startTime);
    }
    
    protected void addJitterConstrForOneActAbsoluteSMT(Activity act, IntExpr[] startTime){
        int nJobs = act.getNumJobs();
        for(int k = 0; k < nJobs; k++) {
            for (int j = k + 1; j < nJobs; j++) {
                int nTaskVarArrayEarlierPeriod = k;
                int nTaskVarArrayLaterPeriod = j;
                addJitterConstraintForAPairOfJobsSMT(k, j, nTaskVarArrayEarlierPeriod, 
                        nTaskVarArrayLaterPeriod, act, startTime);
            }
        } 
     }
    
    private void setJitterConstraintsSMT(Activity activity, IntExpr[] startTime){
        if(activity.getJitter() < activity.getSlack()){
            if(CC_Scheduling_WithJitter.IS_JITTER_RELATIVE){
                addJitterConstrForOneActRelativeSMT(activity, startTime);
            }
            else{
                addJitterConstrForOneActAbsoluteSMT(activity, startTime);
            }
        }
    }
    
    private void scheduleAsILP(Activity activity, IloNumVar[] startTime, int[][] boundsOnJobs, 
            List<List<List<Integer>>> intsOfResConstrsForJobs) throws IloException{
        
        if(schedActs.getProbInst().isZJ()){
            setSTBoundsAndIntervalsForILPZJ(activity, startTime, boundsOnJobs, intsOfResConstrsForJobs);
        }
        else{
            setJitterConstraintsILP(activity, startTime);
            System.out.println(nConstr);
            setSTBoundsAndIntsForILPNZJ(activity, startTime, boundsOnJobs, intsOfResConstrsForJobs);
            System.out.println(nConstr);
            setPrecedenceConstraintsForJobsOfTheActivityILP(activity, startTime);
            System.out.println(nConstr);
            System.out.println("");
        }
    }
    
    private void scheduleAsSMT(Activity activity, IntExpr[] startTime, int[][] boundsOnJobs, 
            List<List<List<Integer>>> intsOfResConstrsForJobs){
        
        
        if(schedActs.getProbInst().isZJ()){
            setSTBoundsAndIntervalsForSMTZJ(activity, startTime, boundsOnJobs, intsOfResConstrsForJobs);
        }
        else{
            setJitterConstraintsSMT(activity, startTime);
            setSTBoundsAndIntsForSATNZJ(activity, startTime, boundsOnJobs, intsOfResConstrsForJobs);
            setPrecedenceConstraintsForJobsOfTheActivitySMT(activity, startTime);
        }
    }
    
    private void setPrecedenceConstraintsForJobsOfTheActivitySMT(Activity act, IntExpr[] startTime){
        IntExpr pt = ctx.mkInt(act.getProcTime());
        for (int j = 0; j < act.getNumJobs() - 1; j++) {
            solverSMT.Add(
                    ctx.mkGe(
                        startTime[j + 1],
                        ctx.mkAdd(startTime[j], pt)
                    )
            );
            nConstr++;
        }

        solverSMT.Add(
                ctx.mkGe(
                    startTime[0],
                    ctx.mkAdd(startTime[act.getNumJobs() - 1], ctx.mkInt(act.getProcTime() - act.getHP()))
                )
        );
        nConstr++;
    }
    
    public SubModel(Activity activity_, ScheduledActs schedActs_, boolean toBeSchedByILP) throws IloException{
        toBeSolvedByILP = toBeSchedByILP;
        isFeasible = true;
        HP = activity_.getHP();
        schedActs = schedActs_;
        activity = activity_;
        nInfeasActs = new ArrayList<>();
        intsOfResConstrsJobs = new ArrayList<>();
        for(int i = 0; i < activity.getHP() / activity.getPeriod(); i++) {
            intsOfResConstrsJobs.add(new ArrayList<>());
        }
        boundsOnJobs = new int[activity.getHP() / activity.getPeriod()][2];
        
        periodConstraintsSetting(activity, boundsOnJobs);
        setPrecedenceConstraints(activity, boundsOnJobs);
 
        // If the activity has relevant jitter requirement, schedule it with ILP model. Otherwise, schedule as soon as possible.
        if(activity.getJitter() < activity.getSlack() - 2){
            int nJobsToSchedule = activity.getNumJobs();
            obtainResourceIntervals(boundsOnJobs, activity, intsOfResConstrsJobs);
            setSchedActsAndPeriodUsingExistingInts(activity,intsOfResConstrsJobs, boundsOnJobs);
            
            if(toBeSchedByILP){
                isScheduledByOpt = true;
                solverILP = new IloCplex();
                
                startTimeILP = solverILP.numVarArray(nJobsToSchedule, 0, activity.getHP() - 1, IloNumVarType.Int);
                scheduleAsILP(activity, startTimeILP, boundsOnJobs, intsOfResConstrsJobs);
                int[] objCoeffs = new int[startTimeILP.length];
                Helpers.InitializeTo(objCoeffs, 1);
                ObjectiveILP = solverILP.addMinimize(solverILP.scalProd(objCoeffs,startTimeILP));
            }
            else{
                HashMap<String, String> cfg = new HashMap<>();
                cfg.put("model", "true");
                //cfg.put("timeout", "1000");
                ctx = new Context(cfg);
                
                solverSMT = ctx.mkOptimize();
                isScheduledByOpt = true;
                startTimeSMT = new IntExpr[nJobsToSchedule];
                for (int i = 0; i < nJobsToSchedule; i++) {
                    startTimeSMT[i] = (IntExpr) ctx.mkConst(
                                ctx.mkSymbol("x_" + (i + 1)),
                                ctx.getIntSort());
                }
                scheduleAsSMT(activity, startTimeSMT, boundsOnJobs, intsOfResConstrsJobs);
                
               
                solverSMT.MkMinimize(ctx.mkAdd(startTimeSMT));
                
                /*BoolExpr assertInt = ctx.mkLe(ctx.mkAdd(startTimeSMT), ctx.mkInt(0));
                System.out.println(ctx.benchmarkToSMTString("lala", "QF_AUFLIRA", "unknown", "", new BoolExpr[0], assertInt));
                System.out.println("");*/
            }
        }
        else{
            if(!CC_Scheduling_WithJitter.IS_PREEMPTION_ALLOWED_IN_HEURISTIC){
                obtainResourceIntervals(boundsOnJobs, activity, intsOfResConstrsJobs);
                setSchedActsAndPeriodUsingExistingInts(activity,intsOfResConstrsJobs, boundsOnJobs);
            }
            else{
                obtainResourceIntervalsWithPreemption(boundsOnJobs, activity, intsOfResConstrsJobs);
            }
        }
        
        //solver.setParam(IloCplex.BooleanParam.PreInd, false);
        //this.ModelToFile(Helpers.outputFileForModels);
    }
    
    /*public void ModelToFile(String outputFile) throws IloException{
            solver.exportModel(outputFile);
    }*/
    
    private int isNumberOutsideIntervals(List<List<Integer>> intsOfResConstrsForJobs, int number){
        for (int i = 0; i < intsOfResConstrsForJobs.size(); i++) {
            if(number > intsOfResConstrsForJobs.get(i).get(0) && number < intsOfResConstrsForJobs.get(i).get(1)){
                return i;
            }
            if(number >= intsOfResConstrsForJobs.get(i).get(1)){
                return -1;
            }
        }
        return -1;
    }
    
    private double setST(int nJob, double endPrevJob){
        double sTime;
        int nInterval = isNumberOutsideIntervals(intsOfResConstrsJobs.get(nJob), (int) endPrevJob);
        if(nInterval == -1){
            sTime = endPrevJob;
        } 
        else{
            sTime =  intsOfResConstrsJobs.get(nJob).get(nInterval).get(1);
        }
        
        return sTime;
    }
    
    private double[] solveNZJ(){
        double[] startTime = new double [activity.getNumJobs()];
        boolean isFirstRound = true;
        for(int j = 0; j < activity.getNumJobs(); j++) {
            if(boundsOnJobs[j][0] > boundsOnJobs[j][1]){
                return null;
            }
            
            if(j > 0){
                int curST = (int) Math.max(boundsOnJobs[j][0], startTime[j - 1]);
                double endPrevJob = startTime[j - 1] + activity.getProcTime();
                if(endPrevJob < curST){
                    startTime[j] = curST;
                }
                else{
                    startTime[j] = setST(j, endPrevJob);
                }
            }
            else{
                startTime[j] = boundsOnJobs[j][0];
            }

            if(j == activity.getNumJobs() - 1){
                if(startTime[j] + activity.getProcTime() - activity.getHP() > startTime[0]){
                    // the last and the first jobs are colliding
                    // move the first job later and check if it's 
                    // not colliding with the second job
                    if(isFirstRound){
                        startTime[0] = setST(j, startTime[j] + activity.getProcTime() - activity.getHP());
                        isFirstRound = false;
                        j = 0;
                    }
                    else{
                        return null;
                    }

                }
            }

            if(startTime[j] > boundsOnJobs[j][1]){
                return null;
            }
        }
        
        return startTime;
    }
    
    private double [] solveNZJWithPreemption(){
        int nStartTimes = 0;
        List<List<Integer>> sTimesArList = new ArrayList<>();
        List<List<Integer>> intsOfActivityResource = schedActs.getIntsOfResConstrs().get(activity.getMapping() - 1);
        int notScheduledProcessingTime = activity.getProcTime();
        for (int i = 0; i < activity.getNumJobs(); i++) {
            sTimesArList.add(new ArrayList<>());
            
        }
        
        double[] sTimes = new double[nStartTimes];
        int curNum = 0;
        for (int i = 0; i < sTimesArList.size(); i++) {
            for (int j = 0; j < sTimesArList.get(i).size(); j++) {
                sTimes[curNum] = sTimesArList.get(i).get(j);
                curNum++;
            }
        }
        return sTimes;
    }
    
    public solutionOneAct solve() throws IloException{
        // this.ModelToFile(Helpers.outputFileForModels);
       
        if(activity.getJitter() < activity.getSlack() - 2){
            if(toBeSolvedByILP){
                if(solverILP.solve()){
                    solutionOneAct problemSolutionForOneActivity = new solutionOneAct(solverILP.getValues(startTimeILP), activity);
                    return problemSolutionForOneActivity;
                }
                else{
                    return null;
                }
            }
            else{
                Params p = ctx.mkParams();
                //p.add("optsmt_engine", "farkas");
                solverSMT.setParameters(p);
                //System.out.println(solverSMT.getStatistics());
                
                if(solverSMT.Check() == Status.SATISFIABLE){
                    Model m = solverSMT.getModel();
                    double[] STime = new double[activity.getNumJobs()];
                    for (int i = 0; i < activity.getNumJobs(); i++){
                        STime[i] = ((IntNum) m.evaluate(startTimeSMT[i], false)).getInt() % HP;
                        System.out.println(STime[i]);
                    }
                    solutionOneAct problemSolutionForOneActivity = new solutionOneAct(STime, activity);
                    return problemSolutionForOneActivity;
                }
                else{
                    return null;
                }
            }
        }
        else{
            double[] sTimes;
            if(CC_Scheduling_WithJitter.IS_PREEMPTION_ALLOWED_IN_HEURISTIC){
                sTimes = solveNZJWithPreemption();
            }
            else{
                sTimes = solveNZJ();
            }
            
            if(sTimes != null){
                return new solutionOneAct(sTimes, activity);
            }
            else{
                return null;
            }
        }
   }
    
    private void setResourceConstraintsForTwoActivitiesNZJILP() throws IloException{
        //set resource constraints 
        for(int j = 0; j < secondActivity.getNumJobs(); j++) {
            IloNumVar startTimeSecond = startTimeSecondActivity[j];
            if(activity.getMapping() == secondActivity.getMapping() 
                    //&& !activity.getAllPredecessors().contains(secondActivity.getIdInArray()) 
                    //   && !activity.getAllSuccessors().contains(secondActivity.getIdInArray())
                    ){
                for(int l = 0; l < activity.getNumJobs(); l++) {
                    IloNumVar startTimeFirst = startTimeILP[l];
                    if(!(startTimeSecond.getUB() + secondActivity.getProcTime() < startTimeFirst.getLB() ||
                            startTimeFirst.getUB() + activity.getProcTime() < startTimeSecond.getLB() )){
                        //The domains of two variables are intersecting, the constraint of exclusivness must be created
                        int addedValueToFirst = 0;
                        int bigMCoeff = 1;
                        setResConstrNZJPairJobsILP(activity, secondActivity, startTimeFirst, 
                                startTimeSecond, addedValueToFirst, bigMCoeff);
                    }
                }
                
                int isZJ = 0;
                setResConstrInThe2ndHPILP(activity, secondActivity, startTimeILP, 
                        startTimeSecondActivity, 0, 0, isZJ);
            }
        }
    }
    
    private void setResourceConstraintsForTwoActivitiesZJILP() throws IloException{
        //set resource constraints 
        int period1 = activity.getPeriod();
        int period2 = secondActivity.getPeriod();
        int numJobs1 = HP / period1;
        int numJobs2 = HP / period2;
        long localHP = period1 * period2 / ProbInstSched.gcd(period1, period2);
        
        if(activity.getMapping() == secondActivity.getMapping()
                //&& !activity.getAllPredecessors().contains(secondActivity.getIdInArray()) 
                       //&& !activity.getAllSuccessors().contains(secondActivity.getIdInArray())
                ){
            for(int j = 0; j < numJobs2; j++) {
                for(int l = 0; l < numJobs1; l++) {
                    int addedValueToFirst = 0;
                    int bigMCoef = 1;
                    if(!(secondBoundsOnJobs[j][1] + secondActivity.getProcTime() < boundsOnJobs[l][0] ||
                            boundsOnJobs[l][1] + activity.getProcTime() < secondBoundsOnJobs[j][0] )){
                        setResConstrZJPairJobsILP(activity, secondActivity, startTimeILP[0], 
                                startTimeSecondActivity[0], localHP, l, j, addedValueToFirst, bigMCoef);
                    }
                }
            }
            
            int isZJ = 1;
            setResConstrInThe2ndHPILP(activity, secondActivity, startTimeILP, 
                    startTimeSecondActivity, 0, 0, isZJ);
        }
    }
    
    public void scheduleWithTwoActivities(Activity secondActivity) throws IloException{
        //schedule first activity as ILP if it was not scheduled as such before
        if(activity.getJitter() >= activity.getSlack() - 2 || !toBeSolvedByILP){
            //if(toBeSolvedByILP){
                isScheduledByOpt = true;
                solverILP = new IloCplex();
                startTimeILP = solverILP.numVarArray(activity.getNumJobs(), 0, activity.getHP() - 1, IloNumVarType.Int);
                scheduleAsILP(activity, startTimeILP, boundsOnJobs, intsOfResConstrsJobs);
            /*}
            else{
                HashMap<String, String> cfg = new HashMap<String, String>();
                cfg.put("model", "true");
                ctx = new Context(cfg);
                solverSMT = ctx.mkSolver();
                
                startTimeSMT = new IntExpr[activity.getNumJobs()];
                for (int i = 0; i < activity.getNumJobs(); i++) {
                    startTimeSMT[i] = (IntExpr) ctx.mkConst(
                                ctx.mkSymbol("x_" + (i + 1)),
                                ctx.getIntSort());
                }
                scheduleAsSMT(activity, startTimeSMT, boundsOnJobs, intsOfResConstrsJobs);
            }*/
        }
        
        this.secondActivity = secondActivity;
        int numJobsToCreateResourceConstraintsFor = secondActivity.getHP() / secondActivity.getPeriod();
        secondIntervalsOfResourceConstraintsForJobs = new ArrayList<>();
        for(int i = 0; i < numJobsToCreateResourceConstraintsFor; i++) {
            secondIntervalsOfResourceConstraintsForJobs.add(new ArrayList<>());
        }
        secondBoundsOnJobs = new int[numJobsToCreateResourceConstraintsFor][2];
        
        periodConstraintsSetting(secondActivity, secondBoundsOnJobs);
        setPrecedenceConstraints(secondActivity, secondBoundsOnJobs);
        obtainResourceIntervals(secondBoundsOnJobs, secondActivity, secondIntervalsOfResourceConstraintsForJobs);
        
        setSchedActsAndPeriodUsingExistingInts(secondActivity, secondIntervalsOfResourceConstraintsForJobs, secondBoundsOnJobs);
        
        startTimeSecondActivity = solverILP.numVarArray(secondActivity.getNumJobs(), 0, secondActivity.getHP() - 1, IloNumVarType.Int);
        scheduleAsILP(secondActivity, startTimeSecondActivity, secondBoundsOnJobs, secondIntervalsOfResourceConstraintsForJobs);
        
        int[] coefficientsForObjectiveFirstStartTimes = new int[startTimeILP.length];
        Helpers.InitializeTo(coefficientsForObjectiveFirstStartTimes, 1);
        int[] coefficientsForObjectiveSecondStartTimes = new int[startTimeSecondActivity.length];
        Helpers.InitializeTo(coefficientsForObjectiveSecondStartTimes, 1);  
        solverILP.remove(ObjectiveILP);
        ObjectiveILP = solverILP.addMinimize(
                solverILP.sum(
                        solverILP.scalProd(
                                coefficientsForObjectiveFirstStartTimes, 
                                startTimeILP
                        ),
                        solverILP.scalProd(
                                coefficientsForObjectiveSecondStartTimes, 
                                startTimeSecondActivity)
                )
        );
        
        if(schedActs.getProbInst().isZJ()){
            setResourceConstraintsForTwoActivitiesZJILP();
        }
        else{
            setResourceConstraintsForTwoActivitiesNZJILP();
        }
       // this.ModelToFile(Helpers.outputFileForModels);
    }
    
    public solutionOneAct[] solveWithTwoActivities() throws IloException{
        //this.ModelToFile(Helpers.outputFileForModels);
        solutionOneAct[] problemSolutionForOneTransaction = new solutionOneAct[2];
        if(CC_Scheduling_WithJitter.IS_VERBOSE){
            System.out.println(activity.getPeriod());
            System.out.println(activity.getProcTime());
            System.out.println(activity.getIdInInputData());
        }
        
        if(solverILP.solve()){
            problemSolutionForOneTransaction[0] = new solutionOneAct(solverILP.getValues(startTimeILP), activity);
            problemSolutionForOneTransaction[1] = new solutionOneAct(solverILP.getValues(startTimeSecondActivity), secondActivity);
            return problemSolutionForOneTransaction;
        }
        else{
            return null;
        }
   }
    
    public void end() throws IloException{
       solverILP.end();
   }
    
    public List<Integer> getNumOfInfeasibleActivities() {
        return nInfeasActs;
    }
    
    public void closeContext(){
        ctx.close();
    }
}
