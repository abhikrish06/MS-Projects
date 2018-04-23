------------------------------ MODULE syncCon2 ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT N, FAILNUM
ASSUME N <= 5  /\ 0 <= FAILNUM /\ FAILNUM <= 2
Nodes == 1..N

(*
--algorithm syncCon2
{
      variable failNum = FAILNUM, 
              up = [n \in Nodes |-> TRUE],
              pt = [n \in Nodes |-> 0],
              t = [n \in Nodes |-> FALSE],
              d = [n \in Nodes |-> -1],
              mb = [n \in Nodes |-> {}],
              
              
    define {
    SetMin(S) == CHOOSE i \in S: \A j \in S : i <= j
    UpNodes == { n \in Nodes : up[n]=TRUE }  
    }
    
    macro Maybefail( ){
        if( failNum > 0 /\ up[self] )
            { either 
                { up[self] := FALSE; failNum := failNum - 1; } 
              or skip; } ;
        
    }
    
    fair process ( n \in Nodes )
    variable v = 0, prev_value = 0, Q = {}, prev_mb_count=0, ctr=1;             \*"prev_mb_count" keeps the track of the number of nodes that have sent the values to curr node in the previous round
    {                                                                           \* "prev_value" stores the previous minimum value decided by current node
                                                                                \* "ctr" is the round counter needed for the node. the rounds stop when ctr becomes 0
P:  while (up[self] /\ ctr>0) {                                                 \* next round is executed when node is up and ctr is not set to 0                         
        
        if(pt[self]=0) {v:=self;};                                              \* set the v to self for first round else the previous decision
        else {v:=d[self]};
        Q := Nodes;    
                                                                 
PS: while(up[self] /\ Q # {}) {
        with(p \in Q) {
            mb[p]:= mb[p] \union {v};                                           
            Q := Q \{p};              
            Maybefail();              
        };
    };
    
    if(up[self]) pt[self] := pt[self]+1;  

PR: await (up[self] = TRUE /\ (\A k \in UpNodes: pt[self]<=pt[k]));                 
    {   
        prev_value:=d[self];                    
        d[self]:=SetMin(mb[self]);  
        
        \* New rounds are needed if:
        \* CASE 1: decision varies between first and last round
        \* CASE 2: number of messages varies between current and previous round
        if(prev_value # d[self] \/ prev_mb_count # Cardinality(mb[self])) ctr:=1;
        else ctr:=ctr-1;
        
        prev_mb_count:=Cardinality(mb[self]);  
        mb[self]:={};                   
        
        if(ctr=0) t[self]:=TRUE;         
        
    } 
  
    }  \* end_while
    }    \* end_process
}
  
*)
\* BEGIN TRANSLATION
VARIABLES failNum, up, pt, t, d, mb, pc

(* define statement *)
SetMin(S) == CHOOSE i \in S: \A j \in S : i <= j
UpNodes == { n \in Nodes : up[n]=TRUE }

VARIABLES v, prev_value, Q, prev_mb_count, ctr

vars == << failNum, up, pt, t, d, mb, pc, v, prev_value, Q, prev_mb_count, 
           ctr >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ failNum = FAILNUM
        /\ up = [n \in Nodes |-> TRUE]
        /\ pt = [n \in Nodes |-> 0]
        /\ t = [n \in Nodes |-> FALSE]
        /\ d = [n \in Nodes |-> -1]
        /\ mb = [n \in Nodes |-> {}]
        (* Process n *)
        /\ v = [self \in Nodes |-> 0]
        /\ prev_value = [self \in Nodes |-> 0]
        /\ Q = [self \in Nodes |-> {}]
        /\ prev_mb_count = [self \in Nodes |-> 0]
        /\ ctr = [self \in Nodes |-> 1]
        /\ pc = [self \in ProcSet |-> "P"]

P(self) == /\ pc[self] = "P"
           /\ IF up[self] /\ ctr[self]>0
                 THEN /\ IF pt[self]=0
                            THEN /\ v' = [v EXCEPT ![self] = self]
                            ELSE /\ v' = [v EXCEPT ![self] = d[self]]
                      /\ Q' = [Q EXCEPT ![self] = Nodes]
                      /\ pc' = [pc EXCEPT ![self] = "PS"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << v, Q >>
           /\ UNCHANGED << failNum, up, pt, t, d, mb, prev_value, 
                           prev_mb_count, ctr >>

PS(self) == /\ pc[self] = "PS"
            /\ IF up[self] /\ Q[self] # {}
                  THEN /\ \E p \in Q[self]:
                            /\ mb' = [mb EXCEPT ![p] = mb[p] \union {v[self]}]
                            /\ Q' = [Q EXCEPT ![self] = Q[self] \{p}]
                            /\ IF failNum > 0 /\ up[self]
                                  THEN /\ \/ /\ up' = [up EXCEPT ![self] = FALSE]
                                             /\ failNum' = failNum - 1
                                          \/ /\ TRUE
                                             /\ UNCHANGED <<failNum, up>>
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << failNum, up >>
                       /\ pc' = [pc EXCEPT ![self] = "PS"]
                       /\ pt' = pt
                  ELSE /\ IF up[self]
                             THEN /\ pt' = [pt EXCEPT ![self] = pt[self]+1]
                             ELSE /\ TRUE
                                  /\ pt' = pt
                       /\ pc' = [pc EXCEPT ![self] = "PR"]
                       /\ UNCHANGED << failNum, up, mb, Q >>
            /\ UNCHANGED << t, d, v, prev_value, prev_mb_count, ctr >>

PR(self) == /\ pc[self] = "PR"
            /\ (up[self] = TRUE /\ (\A k \in UpNodes: pt[self]<=pt[k]))
            /\ prev_value' = [prev_value EXCEPT ![self] = d[self]]
            /\ d' = [d EXCEPT ![self] = SetMin(mb[self])]
            /\ IF prev_value'[self] # d'[self] \/ prev_mb_count[self] # Cardinality(mb[self])
                  THEN /\ ctr' = [ctr EXCEPT ![self] = 1]
                  ELSE /\ ctr' = [ctr EXCEPT ![self] = ctr[self]-1]
            /\ prev_mb_count' = [prev_mb_count EXCEPT ![self] = Cardinality(mb[self])]
            /\ mb' = [mb EXCEPT ![self] = {}]
            /\ IF ctr'[self]=0
                  THEN /\ t' = [t EXCEPT ![self] = TRUE]
                  ELSE /\ TRUE
                       /\ t' = t
            /\ pc' = [pc EXCEPT ![self] = "P"]
            /\ UNCHANGED << failNum, up, pt, v, Q >>

n(self) == P(self) \/ PS(self) \/ PR(self)

Next == (\E self \in Nodes: n(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(n(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Inv == \A i,j \in Nodes : (t[i]/\t[j]) => (d[i]=d[j])
=====================================
This is submission for following students:

Name: Piyush Saravagi                  Name: Abhishek Krishna
UB Name:  piyushsu                     UB Name:  krishna7
UB ID: 50246596                        UB ID: 50246436
