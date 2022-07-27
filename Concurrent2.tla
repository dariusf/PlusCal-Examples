--------------------- MODULE Concurrent1 ----------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

CONSTANTS p1, p2, q1, q2, q3

(* --algorithm Concurrent {
  variables 
    ps = {p1, p2};
    \* qs = {q1, q2, q3};
    qs = {q1, q2};
    state = [p \in ps |-> "start"];
    out = {};
    \* done1 = FALSE;

\* c.a = 1
\* forall p in P
\* forall c in C
\* p->c: m(p, c); c.a = c.a union {p}

  process (main = "proc")
    \* variables out={};
  {
    \* main1:
    \* out := {1};
    \* await pc["proc1"] = "Done"
    \* main2:
    await \A p \in ps : pc[p] = "Done"
  }

  \* process (Z = "proc1")
  process (p \in ps)
    \* variables out={};
  {
    \* out := {2}
    \* pa:
    await \A q \in qs : pc[q] = "Done"
  }

  process (q \in qs)
    variables auxps = ps;
  {
    \* qb:
    \* with (x \in {1,2}) {
    \*   out := out \union {x};
    \* };
    \* await \A pr \in ps : pc[pr] = "pa";
    \* qa:
    while (auxps /= {}) {
      \* pick some process that is waiting for us to finish.
      \* the others in ps are unconstrained.
      with (pp \in { pr \in ps : pc[pr] = "pa" }) {
        out := out \union {<<pp, self>>};
        auxps := auxps \ {pp};
      }
    }
    \* out :=
      \* LET p = \E IN
      \* out \union {2}
  }

    \* a:
    \* tmp1 := {1};
    \* tmp := participants \X qs;
    \* b:
    \* while (tmp # {}) {
    \*   with (pq \in tmp) {
    \*     out := out \union {pq};
    \*     tmp := tmp \ {pq};
    \*   };
    \* }

}
*)    
\* BEGIN TRANSLATION (chksum(pcal) = "ff6798f1" /\ chksum(tla) = "7cf28813")
VARIABLES ps, qs, state, out, pc, auxps

vars == << ps, qs, state, out, pc, auxps >>

ProcSet == {"proc"} \cup (ps) \cup (qs)

Init == (* Global variables *)
        /\ ps = {p1, p2}
        /\ qs = {q1, q2}
        /\ state = [p \in ps |-> "start"]
        /\ out = {}
        (* Process q *)
        /\ auxps = [self \in qs |-> ps]
        /\ pc = [self \in ProcSet |-> CASE self = "proc" -> "Lbl_1"
                                        [] self \in ps -> "Lbl_2"
                                        [] self \in qs -> "Lbl_3"]

Lbl_1 == /\ pc["proc"] = "Lbl_1"
         /\ \A p \in ps : pc[p] = "Done"
         /\ pc' = [pc EXCEPT !["proc"] = "Done"]
         /\ UNCHANGED << ps, qs, state, out, auxps >>

main == Lbl_1

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ \A q \in qs : pc[q] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << ps, qs, state, out, auxps >>

p(self) == Lbl_2(self)

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ IF auxps[self] /= {}
                     THEN /\ \E pp \in { pr \in ps : pc[pr] = "pa" }:
                               /\ out' = (out \union {<<pp, self>>})
                               /\ auxps' = [auxps EXCEPT ![self] = auxps[self] \ {pp}]
                          /\ pc' = [pc EXCEPT ![self] = "Lbl_3"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED << out, auxps >>
               /\ UNCHANGED << ps, qs, state >>

q(self) == Lbl_3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in ps: p(self))
           \/ (\E self \in qs: q(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* Target == ~ \A p \in participants : state[p] /= "start"

Target == ~
  Cardinality(out) >= 4

\* Target == TRUE

==================================================================
