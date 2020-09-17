Conflict Driven Clause Learning
############################  STEPS TO RUN CDCL SOLVER ################################
Step1 : Open the CDCL.ipynb file in Jupyter Notebook.
Step2 : Specify the test filename and heuristic to be used  in the main function as described below.
	"solver = CDCL("unsat1.cnf","ordered")"
	There are two choices for heuristic : "ordered" and "DLIS"
Step3: Run all the cells present in the notebook.


###########################   Output Format ###############################################
-> In case the answer for problem test file is Unsatisfiable, output is as shown below,
---------------------------- CDCL SOLVER ---------------------------------------- 

Given CNF is  Unsatisfiable 

Time Taken :  0.5480260848999023 s
-------------------------------------------------------------------------------------

-> In case the answer for problem test file is Satisfiable then the satisfying assignment is also printed , output is as shown below.
---------------------------- CDCL SOLVER ---------------------------------------- 

Given CNF is  Satisfiable 

Time Taken :  0.04260087013244629 s
Satisfying assignment:
{1: 1, 2: 0, 3: 0, 4: 1, 5: 0, 6: 1, 7: 0, 8: 0, 9: 0, 10: 1, 11: 0, 12: 0, 13: 1, 14: 1, 15: 1, 16: 0, 17: 1, 18: 0, 19: 0, 20: 1} 
