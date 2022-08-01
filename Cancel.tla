--------------------- MODULE Cancel ----------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

(* --algorithm Concurrent {
  variables 
    ps = {"p1", "p2"};
    ms = {"main1", "main2"};
    a = 0;
    soup = {};
    cancelled = FALSE;
    history = <<>>;
    partner = [main1 |-> "p1", main2 |-> "p2"];

  \* c.a = 0
  \* (forall p in P
  \*   p->c: m; c.a += 1)@l1
  \* ||
  \* c.a = 1 =>* c.cancel l1

  process (main = "main")
  {
    mainwait:
    await a = 1;
    \* cancel l1
    cancelled := TRUE;
    history := Append(history, "cancel");
  }

\* the thread on main that receives from parties
  process (recvp \in ms)
  {
    mainrecv:
    \* try removing this condition
    await ~ cancelled;
    await partner[self] \in soup;
    a := a + 1;
    history := Append(history, "recv");
  }

\* the party threads that send
  process (p \in ps)
  {
    sending:
    soup := soup \union {self};
    history := Append(history, "send");
  }
}
*)    
\* BEGIN TRANSLATION (chksum(pcal) = "27144330" /\ chksum(tla) = "689d42f1")
VARIABLES ps, ms, a, soup, cancelled, history, partner, pc

vars == << ps, ms, a, soup, cancelled, history, partner, pc >>

ProcSet == {"main"} \cup (ms) \cup (ps)

Init == (* Global variables *)
        /\ ps = {"p1", "p2"}
        /\ ms = {"main1", "main2"}
        /\ a = 0
        /\ soup = {}
        /\ cancelled = FALSE
        /\ history = <<>>
        /\ partner = [main1 |-> "p1", main2 |-> "p2"]
        /\ pc = [self \in ProcSet |-> CASE self = "main" -> "mainwait"
                                        [] self \in ms -> "mainrecv"
                                        [] self \in ps -> "sending"]

mainwait == /\ pc["main"] = "mainwait"
            /\ a = 1
            /\ cancelled' = TRUE
            /\ history' = Append(history, "cancel")
            /\ pc' = [pc EXCEPT !["main"] = "Done"]
            /\ UNCHANGED << ps, ms, a, soup, partner >>

main == mainwait

mainrecv(self) == /\ pc[self] = "mainrecv"
                  /\ partner[self] \in soup
                  /\ a' = a + 1
                  /\ history' = Append(history, "recv")
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << ps, ms, soup, cancelled, partner >>

recvp(self) == mainrecv(self)

sending(self) == /\ pc[self] = "sending"
                 /\ soup' = (soup \union {self})
                 /\ history' = Append(history, "send")
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << ps, ms, a, cancelled, partner >>

p(self) == sending(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in ms: recvp(self))
           \/ (\E self \in ps: p(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Target == ~
  \* longest
  \* /\ TLCGet("level") >= 5
  \* no more. look at the complete state graph instead. or write an invariant to check history
  /\ TLCGet("level") >= 6

\* recv cannot occur after cancel
Inv ==
  \A i \in DOMAIN history :
    history[i] = "cancel" =>
      \A j \in 1..Len(history) :
        j > i =>
          history[i] /= "recv"

==================================================================
