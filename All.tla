--------------------- MODULE All ----------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

(* --algorithm Concurrent {
  variables 
    ps = {"p1", "p2"};
    qs = {"q1", "q2"};

  \* c.a = 1
  \* forall p in P
  \*   forall c in C
  \*     p->c: m(p, c); c.a = c.a union {p}

  process (main = "main")
  {
    await \A p \in ps : pc[p] = "Done"
  }

  process (p \in ps)
  {
    pa:
    await \A q \in qs : pc[q] = "Done"
  }

  process (q \in qs)
    variables auxps = ps;
    out = {};
  {
    while (auxps /= {}) {
      \* pick some process that is waiting for us to finish.
      \* the others in ps are unconstrained.
      with (pp \in { pr \in ps : pc[pr] = "pa" }) {
        out := out \union {<<pp, self>>};
        auxps := auxps \ {pp};
      }
    }
  }
}
*)    
\* BEGIN TRANSLATION (chksum(pcal) = "6f7cab1" /\ chksum(tla) = "159979a7")
VARIABLES ps, qs, pc, auxps, out

vars == << ps, qs, pc, auxps, out >>

ProcSet == {"main"} \cup (ps) \cup (qs)

Init == (* Global variables *)
        /\ ps = {"p1", "p2"}
        /\ qs = {"q1", "q2"}
        (* Process q *)
        /\ auxps = [self \in qs |-> ps]
        /\ out = [self \in qs |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self = "main" -> "Lbl_1"
                                        [] self \in ps -> "pa"
                                        [] self \in qs -> "Lbl_2"]

Lbl_1 == /\ pc["main"] = "Lbl_1"
         /\ \A p \in ps : pc[p] = "Done"
         /\ pc' = [pc EXCEPT !["main"] = "Done"]
         /\ UNCHANGED << ps, qs, auxps, out >>

main == Lbl_1

pa(self) == /\ pc[self] = "pa"
            /\ \A q \in qs : pc[q] = "Done"
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << ps, qs, auxps, out >>

p(self) == pa(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ IF auxps[self] /= {}
                     THEN /\ \E pp \in { pr \in ps : pc[pr] = "pa" }:
                               /\ out' = [out EXCEPT ![self] = out[self] \union {<<pp, self>>}]
                               /\ auxps' = [auxps EXCEPT ![self] = auxps[self] \ {pp}]
                          /\ pc' = [pc EXCEPT ![self] = "Lbl_2"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED << auxps, out >>
               /\ UNCHANGED << ps, qs >>

q(self) == Lbl_2(self)

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

\* Target == ~
\*   \A px \in {"p1", "p2", "q1", "q2"} : state[px] /= "start"

Target == ~
  /\ TLCGet("level") >= 10

\* Target == ~
\*   \A px \in {"p1", "p2", "q1", "q2"} : state[px] = "Done"

\* Target == ~
\*   Cardinality(out) >= 4

\* Target == TRUE

==================================================================
