--------------------- MODULE Par ----------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

(* --algorithm Par {
  variables 
    x = 0;

  \* x = 1;
  \* x++ || x++

  process (main = "main")
  {
    fork:
    \* join both threads
    await pc["p"] = "Done" /\ pc["q"] = "Done";
    x := x + 2
  }

  process (p \in {"p"})
  {
    pp:
    await pc["main"] = "fork";
    x := x + 1
  }

  process (q \in {"q"})
  {
    qq:
    await pc["main"] = "fork";
    x := x + 1
  }
}
*)    
\* BEGIN TRANSLATION (chksum(pcal) = "dede7f00" /\ chksum(tla) = "7f0575a9")
VARIABLES x, pc

vars == << x, pc >>

ProcSet == {"main"} \cup ({"p"}) \cup ({"q"})

Init == (* Global variables *)
        /\ x = 0
        /\ pc = [self \in ProcSet |-> CASE self = "main" -> "fork"
                                        [] self \in {"p"} -> "pp"
                                        [] self \in {"q"} -> "qq"]

fork == /\ pc["main"] = "fork"
        /\ pc["p"] = "Done" /\ pc["q"] = "Done"
        /\ x' = x + 2
        /\ pc' = [pc EXCEPT !["main"] = "Done"]

main == fork

pp(self) == /\ pc[self] = "pp"
            /\ pc["main"] = "fork"
            /\ x' = x + 1
            /\ pc' = [pc EXCEPT ![self] = "Done"]

p(self) == pp(self)

qq(self) == /\ pc[self] = "qq"
            /\ pc["main"] = "fork"
            /\ x' = x + 1
            /\ pc' = [pc EXCEPT ![self] = "Done"]

q(self) == qq(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in {"p"}: p(self))
           \/ (\E self \in {"q"}: q(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Target == ~
  /\ x = 4

==================================================================
