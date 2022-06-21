--------------------- MODULE TwoPhaseCommit ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, coord

RECURSIVE FoldLeft(_, _, _)
FoldLeft(Op(_, _), S, value) ==
  IF S = <<>> THEN value
  ELSE LET s == Head(S) IN FoldLeft(Op, Tail(S), Op(s, value)) 

Pick(S) == CHOOSE s \in S : TRUE

RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) ==
  IF S = {} THEN value
  ELSE LET s == Pick(S)
  IN SetReduce(Op, S \ {s}, Op(s, value)) 

Broadcast(state, msg, recipients) ==
    LET op(c, t) == [t EXCEPT ![c] = msg] IN
    SetReduce(op, recipients, state)

(* --algorithm TwoPhaseCommit {
  variables 
    participants = {p1, p2};
    state = [p \in participants |-> "start"];

  process (P \in participants)
  {
    pPh1:
      await state[self] = "propose";
    
      either {
        state[self] := "accept";
      } or {
        state[self] := "refuse";    
      };
    
    pPh2:
      await (state[self] = "commit") \/ (state[self] = "abort");
    
      if (state[self] = "commit") {
        state[self] := "committed";
      } else {
        state[self] := "aborted";          
      };
  };

  process (Coordinator = "c1")
    variables parts = <<>>, aborted = FALSE;    
  {  
    n0:
      parts := participants;

    n1:
      state := Broadcast(state, "propose", parts);

    n3:
      while (parts /= {}) {
        with (r \in parts) {
          await (state[r] = "accept") \/ (state[r] = "refuse");
          if ((state[r] = "refuse")) {
            aborted := TRUE;
          };
          parts := parts \ {r};
        };
      };
        
      parts := participants;
      if (aborted) {
        n4:
          state := Broadcast(state, "abort", parts);
      } else {
        nck:
          assert \A p \in parts : (state[p] = "accept");
        n5:
          state := Broadcast(state, "commit", parts);
      };
  }

}
*)    
\* BEGIN TRANSLATION (chksum(pcal) = "e9d12e6d" /\ chksum(tla) = "4f276897")
VARIABLES participants, state, pc, parts, aborted

vars == << participants, state, pc, parts, aborted >>

ProcSet == (participants) \cup {"c1"}

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ state = [p \in participants |-> "start"]
        (* Process Coordinator *)
        /\ parts = <<>>
        /\ aborted = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in participants -> "pPh1"
                                        [] self = "c1" -> "n0"]

pPh1(self) == /\ pc[self] = "pPh1"
              /\ state[self] = "propose"
              /\ \/ /\ state' = [state EXCEPT ![self] = "accept"]
                 \/ /\ state' = [state EXCEPT ![self] = "refuse"]
              /\ pc' = [pc EXCEPT ![self] = "pPh2"]
              /\ UNCHANGED << participants, parts, aborted >>

pPh2(self) == /\ pc[self] = "pPh2"
              /\ (state[self] = "commit") \/ (state[self] = "abort")
              /\ IF state[self] = "commit"
                    THEN /\ state' = [state EXCEPT ![self] = "committed"]
                    ELSE /\ state' = [state EXCEPT ![self] = "aborted"]
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << participants, parts, aborted >>

P(self) == pPh1(self) \/ pPh2(self)

n0 == /\ pc["c1"] = "n0"
      /\ parts' = participants
      /\ pc' = [pc EXCEPT !["c1"] = "n1"]
      /\ UNCHANGED << participants, state, aborted >>

n1 == /\ pc["c1"] = "n1"
      /\ state' = Broadcast(state, "propose", parts)
      /\ pc' = [pc EXCEPT !["c1"] = "n3"]
      /\ UNCHANGED << participants, parts, aborted >>

n3 == /\ pc["c1"] = "n3"
      /\ IF parts /= {}
            THEN /\ \E r \in parts:
                      /\ (state[r] = "accept") \/ (state[r] = "refuse")
                      /\ IF (state[r] = "refuse")
                            THEN /\ aborted' = TRUE
                            ELSE /\ TRUE
                                 /\ UNCHANGED aborted
                      /\ parts' = parts \ {r}
                 /\ pc' = [pc EXCEPT !["c1"] = "n3"]
            ELSE /\ parts' = participants
                 /\ IF aborted
                       THEN /\ pc' = [pc EXCEPT !["c1"] = "n4"]
                       ELSE /\ pc' = [pc EXCEPT !["c1"] = "nck"]
                 /\ UNCHANGED aborted
      /\ UNCHANGED << participants, state >>

n4 == /\ pc["c1"] = "n4"
      /\ state' = Broadcast(state, "abort", parts)
      /\ pc' = [pc EXCEPT !["c1"] = "Done"]
      /\ UNCHANGED << participants, parts, aborted >>

nck == /\ pc["c1"] = "nck"
       /\ Assert(\A p \in parts : (state[p] = "accept"), 
                 "Failure of assertion at line 75, column 11.")
       /\ pc' = [pc EXCEPT !["c1"] = "n5"]
       /\ UNCHANGED << participants, state, parts, aborted >>

n5 == /\ pc["c1"] = "n5"
      /\ state' = Broadcast(state, "commit", parts)
      /\ pc' = [pc EXCEPT !["c1"] = "Done"]
      /\ UNCHANGED << participants, parts, aborted >>

Coordinator == n0 \/ n1 \/ n3 \/ n4 \/ nck \/ n5

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Coordinator
           \/ (\E self \in participants: P(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

StateOK == /\ (\A p \in participants: state[p] \in {"start", "propose", "accept", "commit", "abort", "committed", "aborted", "refuse"})

\* everyone eventually commits or aborts.
\* this is a temporal property which cannot be checked with stuttering it seems.
Committed == /\ \/ <>(\A p \in participants: state[p] = "committed")
                \/ <>(\A p \in participants: state[p] = "aborted")

Inv ==
  (\A p \in participants: state[p] \in {"committed", "aborted"}) =>
    \/ \A p \in participants: state[p] = "committed"
    \/ \A p \in participants: state[p] = "aborted"

==================================================================
