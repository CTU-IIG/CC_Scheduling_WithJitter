/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

package SC;

import java.util.List;

public class solutionOneAct {
    int[] startTimes;
    private Activity activity;

    public solutionOneAct(double[] startTimes, Activity activity) {
        this.startTimes = new int[startTimes.length];
        for(int i = 0; i < startTimes.length; i++){
            this.startTimes[i] = (int) Math.round(startTimes[i]);
        }
        this.activity = activity;
    }

    public int[] getStartTimes() {
        return startTimes;
    }

    public Activity getActivity() {
        return activity;
    }
    
    public void PrintSchedule(){
        System.out.println();
        for(int i = 0; i < startTimes.length; i++) {
            System.out.print(startTimes[i] + ", ");
        }
        System.out.println();
        System.out.println();
    }
    
    public void CheckJitter(){
        for (int i = 0; i < startTimes.length - 1; i++) {
            if(Math.abs(startTimes[i + 1] - startTimes[i] - activity.getPeriod()) > activity.getJitter()){
                System.out.println("Jitter requirement is not satisfied");
            }
        }
        if(Math.abs(startTimes[0] + activity.getHP() - startTimes[startTimes.length - 1] - activity.getPeriod()) > activity.getJitter()){
            System.out.println("Jitter requirement is not satisfied");
        }
    }
}
