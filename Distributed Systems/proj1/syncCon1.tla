------------------------------ MODULE syncCon1 ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT N, FAILNUM
ASSUME N <= 5  /\ 0 <= FAILNUM /\ FAILNUM <= 2
Nodes == 1..N
(*
--algorithm syncCon1 
{
      variable FailNum = FAILNUM, 
              up = [n \in Nodes |-> TRUE],
              pt = [n \in Nodes |-> 0],
              t = [n \in Nodes |-> FALSE],
              d = [n \in Nodes |-> -1],
              mb = [n \in Nodes |-> {}];
              
    define {
    SetMin(S) == CHOOSE i \in S: \A j \in S : i <= j
    AllUpNodes == { n \in Nodes : up[n]=TRUE }               \* A set of nodes that have not failed
    }
    
    macro MaybeFail( ){
        if( FailNum > 0 /\ up[self] )
            { either 
                { up[self] := FALSE; FailNum := FailNum - 1; } 
              or skip; } ;
    }
    
    fair process ( n \in Nodes )
    variable v = 0, pv = 0, Q = {};
    {
P:  if ( up[self] ) {
       v:=self;
       Q:= Nodes;
PS: while(up[self] /\ Q # {}) {
        with(p \in Q) {
            mb[p]:= mb[p] \union {v};
            Q := Q \{p};
            MaybeFail();
        };
    }; \* end_while

    if(up[self]) pt[self] := pt[self]+1;

PR: await (up[self] = TRUE /\ \A k \in AllUpNodes: pt[self]=pt[k]); 
        d[self]:=SetMin(mb[self]);
        t[self]:=TRUE;
        
    } \* end_if

    }  \* end_process
    
    }  
}  
*)
\* BEGIN TRANSLATION
VARIABLES FailNum, up, pt, t, d, mb, pc

(* define statement *)
SetMin(S) == CHOOSE i \in S: \A j \in S : i <= j
AllUpNodes == { n \in Nodes : up[n]=TRUE }

VARIABLES v, pv, Q

vars == << FailNum, up, pt, t, d, mb, pc, v, pv, Q >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ FailNum = FAILNUM
        /\ up = [n \in Nodes |-> TRUE]
        /\ pt = [n \in Nodes |-> 0]
        /\ t = [n \in Nodes |-> FALSE]
        /\ d = [n \in Nodes |-> -1]
        /\ mb = [n \in Nodes |-> {}]
        (* Process n *)
        /\ v = [self \in Nodes |-> 0]
        /\ pv = [self \in Nodes |-> 0]
        /\ Q = [self \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> "P"]

P(self) == /\ pc[self] = "P"
           /\ IF up[self]
                 THEN /\ v' = [v EXCEPT ![self] = self]
                      /\ Q' = [Q EXCEPT ![self] = Nodes]
                      /\ pc' = [pc EXCEPT ![self] = "PS"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << v, Q >>
           /\ UNCHANGED << FailNum, up, pt, t, d, mb, pv >>

PS(self) == /\ pc[self] = "PS"
            /\ IF up[self] /\ Q[self] # {}
                  THEN /\ \E p \in Q[self]:
                            /\ mb' = [mb EXCEPT ![p] = mb[p] \union {v[self]}]
                            /\ Q' = [Q EXCEPT ![self] = Q[self] \{p}]
                            /\ IF FailNum > 0 /\ up[self]
                                  THEN /\ \/ /\ up' = [up EXCEPT ![self] = FALSE]
                                             /\ FailNum' = FailNum - 1
                                          \/ /\ TRUE
                                             /\ UNCHANGED <<FailNum, up>>
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << FailNum, up >>
                       /\ pc' = [pc EXCEPT ![self] = "PS"]
                       /\ pt' = pt
                  ELSE /\ IF up[self]
                             THEN /\ pt' = [pt EXCEPT ![self] = pt[self]+1]
                             ELSE /\ TRUE
                                  /\ pt' = pt
                       /\ pc' = [pc EXCEPT ![self] = "PR"]
                       /\ UNCHANGED << FailNum, up, mb, Q >>
            /\ UNCHANGED << t, d, v, pv >>

PR(self) == /\ pc[self] = "PR"
            /\ (up[self] = TRUE /\ \A k \in AllUpNodes: pt[self]=pt[k])
            /\ d' = [d EXCEPT ![self] = SetMin(mb[self])]
            /\ t' = [t EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << FailNum, up, pt, mb, v, pv, Q >>

n(self) == P(self) \/ PS(self) \/ PR(self)

Next == (\E self \in Nodes: n(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(n(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Inv == \A i,j \in Nodes : (t[i]/\t[j]) => (d[i]=d[j])
===============================================================================================
Violation of Agreement property:
The decision value, d[], is set to the minimum of mb[self] value.
Now, when there is no crash node, all nodes send their value to mb[] and minimum is selected.
But, when one or more nodes fail, they are not able to send their value (which could be minimum of all values) to the mailbox of other nodes.
Hence, when the other nodes terminate, they may not able to correctly determine the minimum value.
i.e min(node i) may not be equal to min(node j)

This is submission for following students:

Name: Piyush Saravagi                  Name: Abhishek Krishna
UB Name:  piyushsu                     UB Name:  krishna7
UB ID: 50246596                        UB ID: 50246436
