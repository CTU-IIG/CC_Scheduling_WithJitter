/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

package SC;

/**
 *
 * @author minaeann
 */
public class Solution {
    double[][] x;
    private ProbInstSched probInst;
    int[] s;
    int[][] startTimesActs;

    private void getSfromX(){
        startTimesActs = new int [probInst.getNumActs()][probInst.getMaxNumJobs()];
        for (int i = 0; i < probInst.getNumActs(); i++) {
            int nJob = 0;
            for (int j = 0; j < probInst.getHP(); j++) {
                if(x[i][j] > Helpers.EPS)  {
                    startTimesActs[i][nJob] = j;
                    nJob++;
                }
            }
        }
    }
    
    public Solution(double[][] x, ProbInstSched problemInstanceScheduling) {
        this.x = x;
        this.probInst = problemInstanceScheduling;
        getSfromX();
        CheckJitter();
    }
    
    public Solution(int[][] startTimesActs_, ProbInstSched problemInstanceScheduling) {
        startTimesActs = startTimesActs_;
        probInst = problemInstanceScheduling;
        CheckJitter();
    }
    
    public Solution(int[] s_, ProbInstSched probInst_, boolean isZJ){
        s = s_;
        probInst = probInst_;
        x = new double[probInst.getNumActs()][probInst.getHP()];
        
        if(!isZJ){
            int curNumJobs = 0;
            for (int i = 0; i < probInst.getNumActs(); i++) {
                Activity act = probInst.getActs()[i];
                for(int k = 0; k < act.getNumJobs(); k++) {
                    x[i][s[curNumJobs]] = 1.0;
                    curNumJobs++;
                }
            }
        }
        else{
            for (int i = 0; i < probInst.getNumActs(); i++) {
                Activity act = probInst.getActs()[i];
                for(int k = 0; k < act.getHP()/act.getPeriod(); k++) {
                    x[i][(s[i] + k * act.getPeriod()) % act.getHP()] = 1.0;
                }
            }
        } 
        getSfromX();
        CheckJitter();
    }
    
    public void PrintSolution(){
        for(int r = 1; r <= probInst.getnResources(); r++){
            int[] schedule = new int[(int) probInst.getHP()];
            Helpers.InitializeTo(schedule, 0);
            
            for(int t = 0; t < probInst.getNumActs(); t++){
                if(probInst.getActs()[t].getMapping() == r){
                    for(int time = 0; time < probInst.getHP(); time++) {
                        if(this.x[t][time] >= Helpers.EPS){
                            for(int i = 0; i < probInst.getActs()[t].getProcTime(); i++){
                                if(Math.round(schedule[(time + i) % probInst.getHP()]) != 0){
                                    int nActInSched = Math.round(schedule[(time + i) % probInst.getHP()]) - 1;
                                    System.out.println("TRAGEDIJAAAAA! Activities "+ t + " and " + nActInSched + " are colliding");
                                    System.exit(1);
                                }

                                schedule[(time + i) % probInst.getHP()] = probInst.getActs()[t].getIdInInputData() + 1;
                            }
                        }

                    }

                }
            }
            
            System.out.println("Resource "+ r + ":");
            //printing
            for(int i = 0; i < probInst.getHP(); i++){
                System.out.format("%2d | ", schedule[i]);
            }
            System.out.println("");
        }
    }
    
    private void CheckJitter(){
        for (int i = 0; i < probInst.getNumActs(); i++) {
            for (int j = 0; j < probInst.getHP() / probInst.getActs()[i].getPeriod() - 1; j++) {
                int period = probInst.getActs()[i].getPeriod();
                int numJobs = probInst.getHP() / period;
                if(CC_Scheduling_WithJitter.IS_JITTER_RELATIVE){
                    numJobs = j + 2; 
                }
                
                for (int k = j + 1; k < numJobs; k++) {
                    if(Math.abs(startTimesActs[i][k] - startTimesActs[i][j]) - (k - j - 1) * period < period - probInst.getActs()[i].getJitter()
                            || (Math.abs(startTimesActs[i][k] - startTimesActs[i][j]) - (k - j - 1) * period > period + probInst.getActs()[i].getJitter())){
                        System.out.println("JITTER IS NOT SATISFIED!!");
                        //System.exit(1);
                    }
                }
                
                int lastJob = probInst.getHP() / period - 1;
                if((startTimesActs[i][0] + probInst.getHP() - startTimesActs[i][lastJob]) > period + probInst.getActs()[i].getJitter()
                            || (startTimesActs[i][0] + probInst.getHP() - startTimesActs[i][lastJob]) <  period - probInst.getActs()[i].getJitter()){
                        System.out.println("JITTER IS NOT SATISFIED!!");
                        //System.exit(1);
                    }
            }
        }
        
    }
}
