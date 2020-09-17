#!/usr/bin/env python
# coding: utf-8

# In[1]:


from collections import deque
import operator
import os
class CDCL:
    def __init__(self,filename,heuristic="ordered"):
        self.filename = filename
        self.clauses,self.variables = self.read_file(filename)
        # learned contais a set of new clauses learned during the solution
        self.learned=set()
        #Initially none of the variables are assigned hence value is initialized with -1
        self.assigned=dict.fromkeys(list(self.variables),-1) 
        #self.branch_vars=set()
        self.branch_hist=dict()
        self.propagation_hist=dict()
        # Stores nodes of implication graph formed during BCP
        self.nodes=dict((k,Node(k,-1)) for k in list(self.variables))
        #Stores current level 
        self.level=0
        self.heuristic=heuristic
        
    @staticmethod
    def read_file(self,filename):
        """Function to read clauses and variables from file in DIMACS CNF format"""
        clauses=set()
        variables=set()
        with open(filename) as f:
            lines=[x.strip().split() for x in f.readlines() if(not(x.startswith('c')) and x != '\n')]
        if lines[0][:2] == ['p','cnf']:
            num_of_variables,num_of_clauses = map(int,lines[0][-2:])
        for l in lines[1:]:
            if l[-1] != '0':
                raise FileFormatError('Wrong file format: Number of variables or clauses or both not defined')
            else:
                cl = frozenset(map(int,l[:-1]))
                clauses.add(cl)
                variables.update(map(abs,cl))
        return clauses,variables
    
    def solve(self):
        """Starting point for the solver"""
        while(1):
            con_cl= self.BCP() 
            if con_cl is not None :
                bl,new_clause=self.Analyze_Conflict(con_cl)
                if bl < 0:
                    return "Unsatisfiable"
                self.learned.add(new_clause)
                self.Backtrack(bl)
                self.level = bl
            
            else:
                if not(self.Decide()):
                        break
        return "Satisfiable"

    def compute(self,clause):
        """Function used to determine value of a clause given an assignment"""
        values = list()
        for lit in clause:
            if lit < 0 :
                if self.assigned[abs(lit)] == -1:
                    values.append(-1)
                elif self.assigned[abs(lit)] == 0:
                    values.append(1)
                else:
                    values.append(0)
            else:
                if self.assigned[abs(lit)] == -1:
                    values.append(-1)
                elif self.assigned[abs(lit)] == 0:
                    values.append(0)
                else:
                    values.append(1)
        value = -1 if -1 in values else max(values)
        return value

    def check_for_unit_clause(self,clause):
        """Given a clause check whether it is unit_clause or not
        Return: None if not unit clause else return True and literal because of which it is unit"""
        check=False
        unassigned_lit=None
        values = dict()
        
        if(len(clause) == 1):
            for lit in clause:
                if self.assigned[abs(lit)] == -1 :
                    check = True
                    unassigned_lit = lit
            return check,unassigned_lit

        for lit in clause:
            if lit < 0 :
                if self.assigned[abs(lit)] == -1:
                    values[lit]=-1
                elif self.assigned[abs(lit)] == 0:
                    values[lit]=1
                else:
                    values[lit]=0

            else:
                if self.assigned[abs(lit)] == -1:
                    values[lit]=-1
                elif self.assigned[abs(lit)] == 0:
                    values[lit]=0
                else:
                    values[lit]=1
                    
        unassigned=[]
        for var,val in values.items():
            if val == -1:
                unassigned.append(var)
        
        if len(unassigned) == 1: # If Number of variables which are unassigned is equal to 1
            for var,val in values.items():
                if var != unassigned[0] and val == 0:
                    check = True
                if var != unassigned[0] and val == 1:
                    check = False
                    break
                    
        if check == True:
            unassigned_lit=unassigned[0]
        
        return check,unassigned_lit
                   
            
                
    def update_graph(self, var, clause=None):
        """
            Updates the implication graph 
        """
        node = self.nodes[var]
        node.value = self.assigned[var]
        node.level = self.level
        
        #Updating Parent
        #All the variables except the unit_variable will become parent of the unit_variable 
        if clause:  # clause is None, meaning this is branching, no parents to update
            for v in [abs(lit) for lit in clause if abs(lit) != var]:
                node.parents.append(self.nodes[v])
                self.nodes[v].children.append(node)
            node.clause = clause
        
        
    def BCP(self):
        """ It repeatedly uses Unit Clause Rule until either a conflict is encountered or there are no more implications.
            Returns : conflicting clause if "conflict" is encountered else return None if there are no more implications.
        """
        #For storing propagation information in case when a unit clause is encountered we use a 
        #doubly ended queue it stores the pair (literal,antecedent(literal))
        while True:
            prop_queue=deque()
            
            for clause in [x for x in self.clauses.union(self.learned)]:
                cnf_cl=self.compute(clause)
                if cnf_cl == 1:
                    continue
                #Checking whether we find a conflicting clause at current level. In case we find it we return that clause
                if cnf_cl == 0:  
                    return clause

                else:
                    is_unit,unit_lit= self.check_for_unit_clause(clause) #Checking whether the clause is unit or not
                    if not is_unit:
                        continue
                    pair=(unit_lit,clause)
                    if pair not in prop_queue:
                        prop_queue.append(pair)
                            
            #Checking whether propagation queue is empty or not if empty there is nothing to propagate hence 
            #returning None
            if not prop_queue:      
                return None
            
            #Assigning variables and updating Implication Graph
            for lit,clause in  prop_queue:
                prop_var=abs(lit)
                if lit > 0:
                    self.assigned[prop_var]=1
                else:
                     self.assigned[prop_var]=0
                self.update_graph(prop_var,clause=clause)
                try:
                    self.propagation_hist[self.level].append(lit)
                except KeyError:
                    #print("Key Error")
                    pass  # propagated at level 0
                
    

    def Analyze_Conflict(self,con_cl):
        """
            It is responsible for computing the backtracking level,detecting global unsatisfiability, 
            and adding new constraints on the search in the form of new clauses.
            Returns -1 if conflict is at level 0 else return the backtrack level and learned clause
        """
        def last_assigned_literal(clause):
            """
                Given a clause  seperate its last assigned literal and the remaining literals
            """
            for lit in reversed(assignment_history):
                if lit in clause or -lit in clause:
                    return lit,[l for l in clause if abs(l) != abs(lit)]

        
        #print(self.level)
        if self.level == 0: 
            return -1,None
        
        assignment_history = [self.branch_hist[self.level]]+list(self.propagation_hist[self.level])
        clause = con_cl
        curr_level_lit=set()
        prev_level_lit=set()
        comp_lit=set()# Will stores literals whose corresponding variable is checked for UIP but is not UIP

        
        while True:
            for lit in clause:
                if self.nodes[abs(lit)].level == self.level:
                    curr_level_lit.add(lit)
                else:
                    prev_level_lit.add(lit)
            """
                We keep on searching for the clause until we find a UIP.UIP stands for Unique Implication Point 
                and a unique implication point (UIP) is any node at the current decision level such that any path
                from the decision variable to the conflict node must pass through it.
            """
            if len(curr_level_lit) == 1:     # Stopping criteria indicates we reached a UIP
                break

            last,remaining = last_assigned_literal(curr_level_lit)
            comp_lit.add(abs(last)) 
            curr_level_lit=set(remaining)

            if self.nodes[abs(last)].clause is not None:
                clause = [lit for lit in self.nodes[abs(last)].clause if abs(lit) not in comp_lit]
            else:
                clause=[]

        #Learned clause is the union of current and previous level literals on finding a UIP
        learned_clause = frozenset([l for l in curr_level_lit.union(prev_level_lit)])
        #Backtracking Level is the second highest level of a literal in learned clause if all belong to same level
        #then backtracking level is current-level -1
        if prev_level_lit:
            bl = max([self.nodes[abs(x)].level for x in prev_level_lit])
        else:
            bl = self.level - 1

        return bl, learned_clause



                
            
        
    
    def Backtrack(self,bl):
        """This function backracks to the level specified in the argument by deleting all the nodes with level
        greater than the input level. It also deletes the propagation history and branching history from levels higher
        than the input level."""
        for var,node in self.nodes.items():
            if node.level <= bl:
                node.children[:] = [child for child in node.children if child.level <= bl]
            else:
                node.value=-1
                node.level=-1
                node.parents=[]
                node.children=[]
                node.clause=None
                self.assigned[node.variable]=-1
               
            #Now in a new graph extracting branching variables that are there in previous level
            #self.branch_vars = set([v for v in self.variables if (self.assigned[v] != -1  and len(self.nodes[v].parents)==0)])
                    
            #Deleting propagation and branching history
            all_levels=list(self.propagation_hist.keys())
            for level in all_levels:
                if level <= bl:
                    continue
                del self.propagation_hist[level]
                del self.branch_hist[level]
    
    
    def decide_variable(self,heuristic):
        #If the decision heuristic is oredered we chose the first unassigned variable 
        if heuristic == "ordered":
            ua=[]
            for v in self.variables:
                if self.assigned[v]==-1:
                    ua.append(v)
            #print(ua)
            ua=iter(ua)
            
            #print(next(ua))
            return next(ua),1
        
        if heuristic == "DLIS":
            """
            for a given variable x:
                C(x,p) = # unresolved clauses in which x appears positively
                C(x,n) = # unresolved clauses in which x appears negatively
            find a variable a such that C(a,p) is max, a variable b such that C(b,n) is max
            if C(a,p) > C(b,n), assign a to TRUE, else assign b to FALSE
            """
            
            def all_unresolved_clauses():
                return filter(lambda c: self.compute(c) == -1, self.clauses)

            
            pos = {x: 0 for x in self.variables if self.assigned[x] == -1}
            neg= {x: 0 for x in self.variables if self.assigned[x] == -1}
            for clause in all_unresolved_clauses():
                for v in clause:
                    try:
                        if v > 0:
                            pos[v] += 1
                        else:
                            neg[abs(v)] += 1
                    except KeyError:
                        pass

            pos_count = max(pos.items(), key=operator.itemgetter(1))
            neg_count = max(neg.items(), key=operator.itemgetter(1))
            if pos_count[1] > neg_count[1]:
                return pos_count[0], 1
            else:
                return neg_count[0], 0

    
   
        
    
    def are_all_vars_assigned(self):
        """Returns True if there are no variables to assign otherwise False"""
        p=all(var in self.assigned for var in self.variables) #Check if all varaibles there in assigned_variables list
        q=not any(var for var in self.variables if self.assigned[var] == -1)  # Check if any of the variable is left unassigned denoted by -1
        return p and q

    def Decide(self):
        """
            This function checks whether all variables are assigned or not and if not assigned then chose a heuristic to 
            select a variable for assigning
        """
        if(self.are_all_vars_assigned()):
            return 0
        else:
            # branching
            self.level += 1
            bt_var, bt_val = self.decide_variable(self.heuristic)
            self.assigned[bt_var] = bt_val
            #self.branch_vars.add(bt_var)
            self.branch_hist[self.level] = bt_var
            self.propagation_hist[self.level] = deque()
            self.update_graph(bt_var)
            return 1

    
    



            
        


# In[2]:


#Represent node for Implication Graph
class Node:
    def __init__(self,var,val):
        self.variable=var
        self.value=val
        self.level=-1
        self.parents=[]
        self.children=[]
        self.clause=None


# In[6]:


#Driver Function
import os
import time
if __name__=="__main__":
    solver = CDCL("sat3.cnf","ordered")
    #print(solver.variables)
    start_time = time.time()
    answer=solver.solve()
    total_time=time.time() - start_time
    print("----------------------------","CDCL SOLVER","----------------------------------------",'\n')
    print("Given CNF is ",str(answer),'\n')
    print("Time Taken : ",total_time,"s")
    if answer == "Satisfiable":
        print("Satisfying assignment:")
        print(solver.assigned,'\n')
        #print(solver.learned)
    print("-------------------------------------------------------------------------------------")


# In[ ]:




