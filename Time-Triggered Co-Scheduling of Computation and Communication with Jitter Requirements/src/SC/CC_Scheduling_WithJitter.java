/*
	This file is part of the CC_Scheduling_WithJitter program.
	BandP_TDM is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.
	BandP_TDM is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
	GNU General Public License for more details.
	You should have received a copy of the GNU General Public License
	along with BandP_TDM. If not, see <http://www.gnu.org/licenses/>.
 */

package SC;

import ilog.concert.IloException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.List;

/*
    This is the main class of this application, other classes has following objectives:
        1)  Activity.java - Class for one distinct activity.
        2)  DAG.java - Class for a directed acyclic graph (of precedence relations), such o
            perations as finding critical times before/after, finding directed/all predecessors/successors,
            finding if the graph is cyclic (not always) and computing inherited jitter of activities.
        3)  ILP_model.java - Parent class, containing necessary methods for ILP.
        4)  Helpers.java - Class with auxiliary functions and variables, not related directly to any of the 
            existing classes.
        5)  ProblemInstanceMapping.java - Class for problem instance before the mapping is done. 
        6)  ProbInstSched.java - Class for problem instance with mapping. All of the proposed 
            approaches work with instances of this class.
        7)  ProblemInstanceSingleChain.java - Class, necessary to do the mapping, containing distinct cause-effect
            chains.
        8)  Solution.java - Class that contains the scheduling problem solution.
        9)  solutionMapping.java - Class that contains the mapping problem solution.
        10) solutionOneAct.java - Class that contains scheduling problem solution for one activity,
            used by the heuristic.
        11) RunnablesToECUsMapper.java - Class for the ILP model that does mapping of tasks (runnbales) to cores.
        12) ScheduledActs.java - Class that contains already scheduled activities. Used by the 3-LS heuristic.
        13) SubModel.java - Class for the sub-model used in 3-LS heuristic, described in Section 5.2.
        14) ThreeLSheuristic.java - 3-LS heuristic class, described in Section 5.
        15) FullSMT.java - SMT model implementation.
        16) FullILP.java - Class for the ILP model with computation time improvements from Section 4.1 both 
            with zero-jitter (ZJ) and non-zero-jitter (NZJ) requirements.
        17) CC_Scheduling_WithJitter.java - Class containing the main file with the implementation of the solution.
*/

public class CC_Scheduling_WithJitter {
    static final int MIN_NUMB_INSTANCES = 1; //solving starts from problem_instance_{MIN_NUMB_INSTANCES}
    static final int MAX_NUMB_INSTANCES = 100; //solving ends with problem_instance_{MAX_NUMB_INSTANCES}
    static final int N_CORES_MAIN_EXP = 3;
    static final boolean IS_GIVEN_MAPPING = false; //set true if the mapping is apready done in the problem instances
    public static int TIME_LIMIT = 3000; // time limit for the ILP model
    public static boolean IS_OPTIMAL = false; // indicate whether the obtained solution is optimal
    static final boolean IS_JITTER_RELATIVE = true;
    static final int MEMORY_BOUND = 1048576;
    static final int UTILIZATION_BOUND = 100;
    
    // only one of the following parameters can be true
    static final boolean IS_EXPERIMENT_WITH_DIF_PERCENTS_OF_ZJ_ACTS = false;
    static final boolean IS_EXPERIMENT_WITH_DIF_PERIODS = false;
    static final boolean IS_USE_CASE = false; //if it's not use-case, it scales the processing time to the required utilization
    static final boolean IS_CAN_USE_CASE = false;
    
    static final boolean SOLVE_SUBMODEL_BY_ILP = true;
    static final boolean IS_VERBOSE = false;
    static final int COEFFICIENT_FOR_JITTER = 5;
    static final int UNSCHED_RULE = 0;// 0 - described in the article, 1 - solely slack I
    
    static boolean is_exp_with_harmonic_periods;
    static boolean is_exp_with_monoperiod;
    static boolean is_exp_with_non_harmonic_periods;
    static int opt_sol_method;// 0 - ILP, 1 - SMT
    static long startTime; //start time of each run on each instance 
    static int numOcc = 0;
    
    static final String instancePath = "instances/Set 5/problem_instance";
    //static final String instancePath = "/Users/annaminaeva/git/SC_problem_2016/SC problem Java/instances/problem_instance_CAN";
    //static final String instancePath = "/Users/annaminaeva/Dropbox/GeneratedModels/Set 6/problem_instance";
    //static final String instancePath = "/Users/annaminaeva/Dropbox/prace/SC problem related/instances/SET6/problem_instance6_";
    //static final String instancePath = "/Users/annaminaeva/Dropbox/prace/SC problem related/instances/Set 4/problem_instance";
    static final String dat = ".dat";
    static FileWriter writer;
    
    static ProblemInstanceMapping probInstanceMapping;
    static ProbInstSched probInst;
    static SubModel subModelRO;
    
    public static Solution SolveOptimally(double curUtil) throws IloException, IOException{
        IS_OPTIMAL = true; // if solver stops because of time limit w/o optimal solution, it sets IS_OPTIMAL to false
        Solution problemSolution = null;
        startTime = System.currentTimeMillis();
        if(opt_sol_method == 0){
            FullILP fullILPRO1 = new FullILP(probInst);
            problemSolution = fullILPRO1.Solve();
            fullILPRO1.end();
        }
        else{
            FullSMT fullSMT = new FullSMT(probInst);
            problemSolution = fullSMT.solve();
        }
        
        return problemSolution;
    }
    
    public static long[] SolveOptimallyAndPrintTheSolutionToFile(double util_on_res, long currentRunTime, String outputFile) throws IloException, IOException{
        startTime = System.currentTimeMillis();
        Solution solution = SolveOptimally(util_on_res);
        if(IS_VERBOSE && solution != null){
            solution.PrintSolution();
        }

        long[] output = new long[2];
        output[0] = 0;
        if(solution == null){
            output[0] = 1;
            writer = new FileWriter(outputFile,true);
            if(IS_OPTIMAL){
                if(IS_EXPERIMENT_WITH_DIF_PERCENTS_OF_ZJ_ACTS){
                    writer.write(probInst.getnActZJPercent() + " ");
                }
                writer.write((util_on_res - 0.01) + " 1 " + currentRunTime);
            }
            else{
                writer.write(util_on_res + " -1 " + currentRunTime);
            }
            writer.close();
        }
        
        output[1] = System.currentTimeMillis() - startTime;
        return output;
    }
    
    public static solutionMapping DoMapping(int solve_with_ZJ, 
            double utilization_on_resources) throws IloException, IOException{
        RunnablesToECUsMapper runnablesToECUsMapper = new RunnablesToECUsMapper(probInstanceMapping);
        solutionMapping solutionMapping = runnablesToECUsMapper.Solve();
        runnablesToECUsMapper.end();
        if(solutionMapping != null){
            //if the mapping problem was solved and a solution exists
            solutionMapping.PrintSolution();
            probInstanceMapping.AssignFoundMapping(solutionMapping, probInst, 
                    solve_with_ZJ, utilization_on_resources);
            //problemSolutionForMapping.OutputResultsIntoFile(Helpers.outputFileForCplex, problemInstance);
            return solutionMapping;
        }
        else{
            System.out.println("Mapping failed!");
            System.exit(1);
        }
        
        return null;
    }
     
    public static void DoExperimentWithDifferentPercentsOfZJActivities() throws IOException, IloException{
        opt_sol_method = 1;
        //String fileName  = "/Users/annaminaeva/Dropbox/prace/SC problem related/instances/Set 1/problem_instance";
        String fileName  = "/Users/annaminaeva/Dropbox/prace/SC problem related/instances/SET6/problem_instance6_";
        
        for (int nInstance = 1; nInstance < 2; nInstance++) {
            writer = new FileWriter(Helpers.outputFileForZJExperiment,true);
            writer.write(nInstance + "-th instance!\n");
            writer.close();
            for (int nCores = 3; nCores < 8; nCores++) {
                writer = new FileWriter(Helpers.outputFileForZJExperiment,true);
                writer.write(nCores + " cores\n");
                writer.close();
                PrepareProblemInstance(0, 0.3, fileName + String.valueOf(nInstance) + dat, nCores);
                List<Integer> prevChosenActs = new ArrayList<Integer>();
                int nPrevTransf = 0;
                int nContinue = 0;
                for (int percZJ = 0; percZJ <= 10; percZJ += 100) {
                    long currentRunTime = 0;
                    int nPrevTransfBefore = nPrevTransf;
                    nPrevTransf = probInst.makeProblemInstanceToContainApproximatelyNPercZJJobs(percZJ, 
                            prevChosenActs, nPrevTransf, nContinue);
                    if(nPrevTransf == 0 && percZJ != 0){
                        nContinue++;
                        nPrevTransf = nPrevTransfBefore;
                        writer = new FileWriter(Helpers.outputFileForZJExperiment,true);
                        writer.write(percZJ + " 0 0 0\n");
                        writer.close();
                        
                        continue;
                    }
                    else{
                      nContinue = 0;  
                    }
                    
                    System.out.println("");
                    for(double util_on_res = 0.4; util_on_res <= 1.11; util_on_res += 0.01) {
                        probInst.ScaleToRequiredUtilization(util_on_res, true);

                        // Solve optimally if it is the purpose
                        startTime = System.currentTimeMillis();
                        long[] output = SolveOptimallyAndPrintTheSolutionToFile(util_on_res, 
                                currentRunTime, Helpers.outputFileForZJExperiment);
                        //long[] output = SolveHeuristicallyAndPrintTheSolutionToFile(1.0, currentRunTime, Helpers.outputFile);
                    }
                    
                    writer = new FileWriter(Helpers.outputFileForZJExperiment,true);
                    writer.write("\n");
                    writer.close();
                }
                writer = new FileWriter(Helpers.outputFileForZJExperiment,true);
                writer.write("\n\n");
                writer.close();
            }
            
        }
    }
    
    public static void bodyOfExperimentWithDifPeriods(String fileName) throws IOException, IloException {
        long currentRunTime = 0;
        for(int solve_optimally = 0; solve_optimally < 1; solve_optimally++) {
            for(int solve_with_zero_jitter = 0; solve_with_zero_jitter < 2; solve_with_zero_jitter++){
                for(double util_on_res = 0.01; util_on_res <= 1.02; util_on_res += 0.01) {
                    PrepareProblemInstance(solve_with_zero_jitter, util_on_res, fileName, N_CORES_MAIN_EXP);
                    
                    if(solve_optimally == 1){
                        long[] output = SolveOptimallyAndPrintTheSolutionToFile(util_on_res, 
                                currentRunTime, Helpers.outputFileForExperimentWithDifPeriods);
                        currentRunTime = output[1];
                        if(output[0] == 1){
                            util_on_res = 1.5;
                        }
                    }
                    else{
                        long[] output = SolveHeuristicallyAndPrintTheSolutionToFile(util_on_res, currentRunTime, Helpers.outputFileForExperimentWithDifPeriods);
                        currentRunTime = output[1];
                        if(output[0] == 1){
                            util_on_res = 1.5;
                        }
                    }
                }
                writer = new FileWriter(Helpers.outputFileForExperimentWithDifPeriods,true);
                writer.write("\n");
                writer.close();
            } 
        }
    }
    
    public static void DoExperimentWithDifferentPeriods() throws IOException, IloException{
        opt_sol_method = 1;
        String instancePath  = "/Users/annaminaeva/Dropbox/prace/SC problem related/instances/Set 1/problem_instance";
        for (int nInstance = MIN_NUMB_INSTANCES; nInstance < MAX_NUMB_INSTANCES; nInstance++) {
            String fileName = instancePath + String.valueOf(nInstance) + dat;
            //first, solve instance with initial periods
            writer = new FileWriter(Helpers.outputFileForExperimentWithDifPeriods,true);
            writer.write("\n\nInstance with initial periods: \n");
            writer.close();
            bodyOfExperimentWithDifPeriods(fileName);

            //conduct experiment where all periods are harmonic
            writer = new FileWriter(Helpers.outputFileForExperimentWithDifPeriods,true);
            writer.write("\n\nInstance with harmonic periods: \n");
            writer.close();
            is_exp_with_harmonic_periods = true;
            bodyOfExperimentWithDifPeriods(fileName);
            is_exp_with_harmonic_periods = false;

            // conduct experiment where all activities have the same period
            writer = new FileWriter(Helpers.outputFileForExperimentWithDifPeriods,true);
            writer.write("\n\nInstance with mono period: \n");
            writer.close();
            is_exp_with_monoperiod = true;
            bodyOfExperimentWithDifPeriods(fileName);
            is_exp_with_monoperiod = false;

            //conduct experiment where all activities have different periods
            writer = new FileWriter(Helpers.outputFileForExperimentWithDifPeriods,true);
            writer.write("\n\nInstance with different periods: \n");
            writer.close();
            is_exp_with_non_harmonic_periods = true;
            bodyOfExperimentWithDifPeriods(fileName);
            is_exp_with_non_harmonic_periods = false;
        }
    }
    
    public static boolean PrepareProblemInstance(int solve_with_zero_jitter, double util_on_res, String fileName, int nCores) throws IOException, IloException{
        if(!IS_GIVEN_MAPPING){
            probInstanceMapping = new ProblemInstanceMapping(fileName, nCores);
            probInst = new ProbInstSched();
            DoMapping(solve_with_zero_jitter, util_on_res);
        }
        else{
            probInst = new ProbInstSched(fileName, solve_with_zero_jitter, util_on_res);
        }

        if(!probInst.IsInstanceSchedulable() || !probInst.isIsSchedulable()){
            System.out.println("The problem instance 'instance" 
                    + ".dat' is not schedulable - either cyclic or precedence constraints too demanding");
            return false;
        }
        return true;
    }
      
    public static long[] SolveHeuristicallyAndPrintTheSolutionToFile(double util_on_res, long currentRunTime, String outputFile) throws IOException, IloException{
        startTime = System.currentTimeMillis(); 
        ThreeLSheuristic heuristic = new ThreeLSheuristic(probInst, subModelRO);
        ScheduledActs scheduledActs = heuristic.Solve();
        
        if(IS_CAN_USE_CASE){
            scheduledActs.PrintSchedulesForCANUSE_CASE();
        }
        long[] output = new long[2];
        output[0] = 0;
        if(scheduledActs != null){
            Solution sol = scheduledActs.convertToSolution();
        }

        if(IS_VERBOSE && scheduledActs != null){
            scheduledActs.PrintFinalSchedule(probInst.getnResources(), probInst.getHP());
        }

        if(scheduledActs == null){
            writer = new FileWriter(outputFile,true);
            writer.write((util_on_res - 0.01) + " 1 " + currentRunTime);
            writer.close();
            output[0] = 1;
        }
        
        output[1] = System.currentTimeMillis() - startTime;
        if(IS_USE_CASE){
            if(scheduledActs != null){
                writer = new FileWriter(outputFile,true);
                writer.write(" 1 " + (System.currentTimeMillis() - startTime));
                writer.close();
            }
            else{
                writer = new FileWriter(outputFile,true);
                writer.write("not able to solve");
                writer.close();
            }
            
        }
        
        return output;
    }
    
    public static void main(String[] args) throws IloException, UnsupportedEncodingException, IOException { 
        System.out.println("Copyright 2016-2017 Anna Minaeva, Benny Akesson, Zdenek Hanzalek and Dakshina Dasari.");
        System.out.println("The program is distributed under the terms of the GNU General Public License.");
        
        if(IS_EXPERIMENT_WITH_DIF_PERCENTS_OF_ZJ_ACTS){
            DoExperimentWithDifferentPercentsOfZJActivities();
            return;
        }
        
        if(IS_EXPERIMENT_WITH_DIF_PERIODS){
            DoExperimentWithDifferentPeriods();
            return;
        }
        
        for(int t = MIN_NUMB_INSTANCES; t <= MAX_NUMB_INSTANCES; t++){
            if(!IS_CAN_USE_CASE){
                writer = new FileWriter(Helpers.outputFile,true);
                writer.write(t + "-th instance!\n");
                writer.close();
            }
            
            for(int solve_optimally = 0; solve_optimally < 1; solve_optimally++) {
                for(int solve_with_zero_jitter = 0; solve_with_zero_jitter < 2; solve_with_zero_jitter++){
                    int n_opt_solution_methods = 1;
                    if(solve_optimally == 1){
                        n_opt_solution_methods = 2;
                    }
                    for (opt_sol_method = 0; opt_sol_method < n_opt_solution_methods; opt_sol_method++) {
                        long currentRunTime = 0;
                        for(double util_on_res = 0.4; util_on_res <= 1.01; util_on_res += 0.01) {
                            boolean result = PrepareProblemInstance(solve_with_zero_jitter, 
                                    util_on_res, instancePath + String.valueOf(t) + dat, N_CORES_MAIN_EXP);
                            if(!result){
                                util_on_res = 2;
                                solve_with_zero_jitter = 2;
                                solve_optimally = 2;
                                continue;
                            }
                            
                            // Solve optimally if it is the purpose
                            if(solve_optimally == 1){
                                long[] output = SolveOptimallyAndPrintTheSolutionToFile(util_on_res, 
                                        currentRunTime, Helpers.outputFile);
                                currentRunTime = output[1];
                                if(output[0] == 1){
                                    util_on_res = 1.5;
                                }
                            } 
                            else{
                                long[] output = SolveHeuristicallyAndPrintTheSolutionToFile(util_on_res, currentRunTime, Helpers.outputFile);
                                currentRunTime = output[1];
                                if(output[0] == 1){
                                    util_on_res = 1.5;
                                }
                            }  
                        }
                        writer = new FileWriter(Helpers.outputFile,true);
                        writer.write("\n");
                        writer.close();
                    }
                }
                    
            }
            writer = new FileWriter(Helpers.outputFile,true);
            writer.write("\n");
            writer.close();
        }
    }
}

