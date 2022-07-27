--------------------- MODULE Concurrent ----------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

CONSTANTS p1, p2

(* --algorithm Concurrent {
  variables 
    participants = {p1, p2};
    state = [p \in participants |-> "start"];

  \* process (P \in participants)
  \* {
  \*   state[self] := "haha";
  \* };

  \* process (P = "proc")
  \*   variables tmp={}, tmp1={};
  \* {
  \* a:
  \*   tmp := participants;
  \* b:
  \*   while (tmp # {}) {
  \*     with (p \in participants) {
  \*       state[p] := "haha";
  \*       tmp := tmp \ {p};
  \*     }
  \*   }
  \* };

\* does not work
  \* process (P = "proc")
  \*   variables tmp={}, tmp1={}, qs={"q1", "q2", "q3"}, out={};
  \* {
  \*   tmp := participants \union qs;
  \*   while (tmp # {}) {
  \*     while (tmp1 # {}) {
  \*       with (p \in participants) {
  \*         with (q \in qs) {
  \*           \* state[p] := q;
  \*           out := out \union <<p, q>>;
  \*         }
  \*       };
  \*       tmp1 := tmp1 \ {q};
  \*     };
  \*     tmp := tmp \ {p};
  \*   }
  \* };

  process (P = "proc")
    variables tmp={}, tmp1={}, qs={"q1", "q2", "q3"}, out={};
  {
    a:
    tmp1 := {1};
    tmp := participants \X qs;
    b:
    while (tmp # {}) {
      with (pq \in tmp) {
        out := out \union {pq};
        tmp := tmp \ {pq};
      };
    }
  };

}
*)    
\* BEGIN TRANSLATION (chksum(pcal) = "426dea54" /\ chksum(tla) = "64a53852")
VARIABLES participants, state, pc, tmp, tmp1, qs, out

vars == << participants, state, pc, tmp, tmp1, qs, out >>

ProcSet == {"proc"}

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ state = [p \in participants |-> "start"]
        (* Process P *)
        /\ tmp = {}
        /\ tmp1 = {}
        /\ qs = {"q1", "q2", "q3"}
        /\ out = {}
        /\ pc = [self \in ProcSet |-> "a"]

a == /\ pc["proc"] = "a"
     /\ tmp1' = {1}
     /\ tmp' = participants \X qs
     /\ pc' = [pc EXCEPT !["proc"] = "b"]
     /\ UNCHANGED << participants, state, qs, out >>

b == /\ pc["proc"] = "b"
     /\ IF tmp # {}
           THEN /\ \E pq \in tmp:
                     /\ out' = (out \union {pq})
                     /\ tmp' = tmp \ {pq}
                /\ pc' = [pc EXCEPT !["proc"] = "b"]
           ELSE /\ pc' = [pc EXCEPT !["proc"] = "Done"]
                /\ UNCHANGED << tmp, out >>
     /\ UNCHANGED << participants, state, tmp1, qs >>

P == a \/ b

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == P
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* Target == ~ \A p \in participants : state[p] /= "start"

Target == ~ Cardinality(out) = 6

==================================================================
