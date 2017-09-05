The program CC_Scheduling_WithJitter is distributed under the terms of the GNU General Public License.

Authors: Anna Minaeva (minaeann@fel.cvut.cz), Benny Akesson (benny.akesson@gmail.com), Zdenek Hanzalek (hanzalek@fel.cvut.cz) and Dakshina Dasari (Dakshina.Dasari@de.bosch.com)

This is the implementation of the ILP, SMT and 3-LS heuristic approaches on the co-scheduling problem of communication and computation with jitter requirements. 

To run it, IBM ILOG CPLEX Optimization Studio library must be installed and added to the project (“cplex.jar”). Besides, the Z3 theorem prover must be installed and added to the project (“com.microsoft.z3.jar”). Moreover, Project Properties->Run->VM options should contain “-Djava.library.path="/path_to_ibm/IBM/ILOG/CPLEX_Studio126/cplex/bin/x86-64_osx":"path_to_z3/z3/build"” or similar.

“CC_Scheduling_WithJitter.java” contains main function and the implementation of all experimental environment.

—————————————————————————————————————————————————————————————————————

The problem instances are in the folder “instances/”, where there are folders named Set N, N = 1,2,3,4,5 and the folder Case study. They contain instances for Sets 1 to 5 and the case study.

——————————————————————————————————————————————————————————————————————

Remark:

If you find this software useful for your research or you create an algorithm
based on this software, please cite our original paper in your publication list.


Minaeva, A - Akesson, B - Hanzálek, Z. - Dasari, D. : Time-Triggered Co-Scheduling of Computation and Communication with Jitter Requirements.