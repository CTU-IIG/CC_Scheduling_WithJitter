/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

package SC;

import ilog.concert.IloException;
import ilog.concert.IloLinearNumExpr;
import ilog.concert.IloNumVar;
import ilog.concert.IloNumVarType;
import ilog.concert.IloObjective;
import ilog.concert.IloRange;
import ilog.cplex.IloCplex;
import java.util.ArrayList;
import java.util.List;

/**
 *
 * @author minaeann
 */
public class RunnablesToECUsMapper {
    private IloCplex mapSolver;
    private IloObjective Objective;
    private IloNumVar[][] mapping;
    
    private IloNumVar[] utilization;
    private IloNumVar[] RunnablesOnTheSameResourceModuloVariable; // first go non-order-critical messages, then order-critical messages
    private IloNumVar[] numResourcesMinimizationVariable;
    private IloRange[] ChainFeasibilityConstraints;
    private IloRange[] RunnableToOneECUConstraints;
    private IloRange[] MemoryConstraint;
    private IloRange[] UtilizationConstraints;
    private IloRange[] ResourceMinimizationConstraints;
    private IloRange[] ResourceSymmetryBreakingConstraints;
    
    private IloNumVar[] loadBalanceModuloVariable;
    private IloRange[] LoadBalanceConstraints1;
    private IloRange[] LoadBalanceConstraints2;
    
    private IloNumVar[][] moduloVariableForMinimizationNetworkUtilization;
    private IloRange[] ModuloHelpingConstraints1;
    private IloRange[] ModuloHelpingConstraints2;
    private IloRange[] ModuloConstraints1;
    private IloRange[] ModuloConstraints2;
    private double sumOfUtilizationOnNetwork;
    
    private ProblemInstanceMapping problemInstanceMapping;
    
      private void VariablesCreation() throws IloException{
        /* main variables for mapping, mapping_{i,j} is 1 if runnable i is assigned to resource j*/
        mapping = new IloNumVar [problemInstanceMapping.getnResources()][problemInstanceMapping.getNumRunnables()];
        for(int i = 0; i < problemInstanceMapping.getnResources(); i++) {
            mapping[i] = mapSolver.numVarArray(problemInstanceMapping.getNumRunnables(), 0, 1,IloNumVarType.Bool);
        }
        
        /* variable, introduced to allow minimization of used resources */
        numResourcesMinimizationVariable = mapSolver.numVarArray(problemInstanceMapping.getnResources(),
                0, 1, IloNumVarType.Bool);
        
        /* variable for modulo of differences of consecutive mapping_{tr{t,i},j} */
       /* int numCommunications = problemInstanceMapping.getNumAllCommunications();
        int numResources = problemInstanceMapping.getMaxNumResources();
        moduloVariableForMinimizationNetworkUtilization = new IloNumVar[numResources][numCommunications];
        for(int i = 0; i < numResources; i++) {
            moduloVariableForMinimizationNetworkUtilization[i] = mapSolver.numVarArray(numCommunications, 0, 1,IloNumVarType.Bool);
        }
        
        RunnablesOnTheSameResourceModuloVariable = mapSolver.numVarArray(problemInstanceMapping.getNumAllCommunications(),
                0, 1, IloNumVarType.Bool);*/
        
        utilization = mapSolver.numVarArray(problemInstanceMapping.getnResources(),
                0, 1, IloNumVarType.Float);
        loadBalanceModuloVariable = mapSolver.numVarArray(problemInstanceMapping.getnResources() - 1,
                0, 1, IloNumVarType.Float);
    }
    
    /* This criterion aims to optimize load balance on the ECUs/cores */
    private void ObjectiveSettingLoadBalance() throws IloException{
        int maxNumResources = problemInstanceMapping.getnResources();
        LoadBalanceConstraints1 = new IloRange[maxNumResources - 1];
        LoadBalanceConstraints2 = new IloRange[maxNumResources - 1];
        int bigM = 1;
       
        //first create modulo constraints. loadBalanceModuloVariable[i] indicates how much is the difference between
        //i-th and (i+1)-th resource utilization
        for(int i = 0; i < maxNumResources - 1; i++) {
            IloLinearNumExpr expr = mapSolver.linearNumExpr();
            expr.addTerm(1, loadBalanceModuloVariable[i]);
            expr.addTerm(-1, utilization[i]);
            expr.addTerm(1, utilization[i + 1]);
            expr.addTerm(bigM, numResourcesMinimizationVariable[i + 1]);
            LoadBalanceConstraints1[i] = mapSolver.addGe(expr, bigM);
            IloLinearNumExpr expr1 = mapSolver.linearNumExpr();
            expr1.addTerm(1, loadBalanceModuloVariable[i]);
            expr1.addTerm(1, utilization[i]);
            expr1.addTerm(-1, utilization[i + 1]);
            expr1.addTerm(bigM, numResourcesMinimizationVariable[i + 1]);
            LoadBalanceConstraints2[i] = mapSolver.addGe(expr1, bigM);
        }
        
        // assign objective
        IloLinearNumExpr exprObjective = mapSolver.linearNumExpr();
        for(int i = 0; i < maxNumResources - 1; i++) {
            exprObjective.addTerm(1, numResourcesMinimizationVariable[i]);
            exprObjective.addTerm(1, loadBalanceModuloVariable[i]);
        }
        exprObjective.addTerm(1, numResourcesMinimizationVariable[maxNumResources - 1]);
        Objective = mapSolver.addMinimize(exprObjective);
    }
      
    /* Indicate which resource is free:
       sum_{runnables i} mapping[i][r] <= M * minimization_of_num_resources_variable[r] for each r */
    private void SettingResourceMinimizationConstraints() throws IloException{
        ResourceMinimizationConstraints = new IloRange[problemInstanceMapping.getnResources()];
        
        for(int i = 0; i < problemInstanceMapping.getnResources(); i++) {
            IloLinearNumExpr expr = mapSolver.linearNumExpr();
            for(int j = 0; j < problemInstanceMapping.getNumRunnables(); j++) {
                expr.addTerm(1.0, mapping[i][j]);
            }
            int bigM = this.problemInstanceMapping.getNumRunnables();
            expr.addTerm(-1 * bigM, numResourcesMinimizationVariable[i]);
            ResourceMinimizationConstraints[i] = mapSolver.addLe(expr, 0);
        }
    }
    
    /* sum_{runnables} mapping_{i,r} >= sum_{runnables} mapping_{i,r+1} for each resource r */
    private void SettingResourceSymmetryBreakingConstraints() throws IloException{
        ResourceSymmetryBreakingConstraints = new IloRange[problemInstanceMapping.getnResources() - 1];
        for(int i = 0; i < problemInstanceMapping.getnResources() - 1; i++) {
            IloLinearNumExpr expr = mapSolver.linearNumExpr();
            for(int j = 0; j < problemInstanceMapping.getNumRunnables(); j++) {
                expr.addTerm(1.0, mapping[i][j]);
                expr.addTerm(-1.0, mapping[i + 1][j]);
            }
            
            ResourceSymmetryBreakingConstraints[i] = mapSolver.addGe(expr, 0);
        }
    }
    
    /* Each runnable is allocated to one resource, i.e. 
       sum_{resources} mapping[i][r] = 1 for each runnable i */
    private void SettingRunnableToOneECUConstraints() throws IloException{
        RunnableToOneECUConstraints = new IloRange[problemInstanceMapping.getNumRunnables()];
        for(int i = 0; i < problemInstanceMapping.getNumRunnables(); i++) {
            IloLinearNumExpr expr = mapSolver.linearNumExpr();
            for(int j = 0; j < problemInstanceMapping.getnResources(); j++) {
                expr.addTerm(1.0, mapping[j][i]);
            }
            
            RunnableToOneECUConstraints[i] = mapSolver.addEq(expr, 1);
        }
    }
    
    /*
        Each ECU has a limit on operative memory:
        sum_{runnables} mapping[i][r]*size_of_runnable[i] <= limit for each resource r
    */
    private void SettingMemoryConstraints() throws IloException{
        MemoryConstraint = new IloRange[problemInstanceMapping.getnResources()];
        for(int i = 0; i < problemInstanceMapping.getnResources(); i++) {
            IloLinearNumExpr expr = mapSolver.linearNumExpr();
            for(int j = 0; j < problemInstanceMapping.getNumRunnables(); j++) {
                expr.addTerm(problemInstanceMapping.getSizeOfRunnables()[j], mapping[i][j]);
            }
            
            MemoryConstraint[i] = mapSolver.addLe(expr, problemInstanceMapping.getMemoryBoundOnECU());
        }
    }
    
    /*
        Each ECU has a limit on utilization:
        sum_{runnables} mapping[i][r]*utilization[i] <= limit for each resource r
    */
    private void SettingUtilizationConstraints() throws IloException{
        
        UtilizationConstraints = new IloRange[problemInstanceMapping.getnResources()];
        for(int i = 0; i < problemInstanceMapping.getnResources(); i++) {
            IloLinearNumExpr expr = mapSolver.linearNumExpr();
            for(int j = 0; j < problemInstanceMapping.getNumRunnables(); j++) {
                expr.addTerm(problemInstanceMapping.getProcessingTimesOfRunnables()[j] * 1.0 
                        / problemInstanceMapping.getPeriodsOfRunnables()[j], mapping[i][j]);
            }
            
            expr.addTerm(-1, utilization[i]);
            mapSolver.addEq(expr, 0);
            UtilizationConstraints[i] = mapSolver.addLe(mapSolver.prod(utilization[i], 1.0), problemInstanceMapping.getUtilizationBound());
        }
    }
    
    public RunnablesToECUsMapper(ProblemInstanceMapping problemInstanceMapping) throws IloException {
        this.problemInstanceMapping = problemInstanceMapping;
        mapSolver = new IloCplex();
        
        VariablesCreation();
        /*ObjectiveSettingMinimizeNetworkUtilization();
        SettingModuloVariableConstraint();
        SettingChainFeasibilityConstraints();*/
        ObjectiveSettingLoadBalance();
        SettingUtilizationConstraints();
         
        //mapSolver.setParam(IloCplex.IntParam.TimeLimit, CC_Scheduling_WithJitter.TIME_LIMIT);
        SettingResourceMinimizationConstraints();
        SettingResourceSymmetryBreakingConstraints();
        SettingRunnableToOneECUConstraints();
        SettingMemoryConstraints();
       
    }
    
    public void ModelToFile(String outputFile) throws IloException{
            mapSolver.exportModel(outputFile);
    }
    
    public solutionMapping Solve() throws IloException{
        //ModelToFile(Helpers.outputFileForModels);
        if(mapSolver.solve()){
            double[][] x = new double[problemInstanceMapping.getnResources()][problemInstanceMapping.getNumRunnables()];
            for(int i = 0; i < problemInstanceMapping.getnResources(); i++) {
                x[i] = mapSolver.getValues(mapping[i]);
            }
            
            int numUsedResources = mapSolver.getValues(numResourcesMinimizationVariable).length;
            for(int i = 0; i < mapSolver.getValues(numResourcesMinimizationVariable).length; i++) {
                if(mapSolver.getValues(numResourcesMinimizationVariable)[i] < Helpers.EPS){
                    numUsedResources = i;
                    break;
                }
            }
            
            int numMessages = problemInstanceMapping.getNumAllCommunications();
            double[][] moduloVars = new double[problemInstanceMapping.getnResources()][numMessages];
            /*for(int i = 0; i < problemInstanceDAG.getMaxNumResources(); i++) {
                moduloVars[i] = mapSolver.getValues(moduloVariableForMinimizationNetworkUtilization[i]);
            }*/
            
            solutionMapping problemSolutionForMapping = new solutionMapping(moduloVars, numUsedResources,
                    x, mapSolver.getValues(numResourcesMinimizationVariable),problemInstanceMapping);
            
            //System.out.println(mapSolver.getObjValue());
            
            
            return problemSolutionForMapping;
        }
        else{
            return null;
        }
   }
    
    public void end() throws IloException{
       this.mapSolver.end();
   }
}
