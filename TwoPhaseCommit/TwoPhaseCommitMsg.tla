--------------------- MODULE TwoPhaseCommitMsg ----------------------
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

SendMessages(messages, msg, recipients) ==
    LET op(c, t) == t \union {[To |-> c, From |-> coord, Type |-> msg]} IN
    SetReduce(op, recipients, messages)

(* --algorithm TwoPhaseCommit {
  variables
    participants = {p1, p2};
    state = [p \in participants |-> "start"];
    messages = {};

  macro Send(from, to, type) {
    messages := messages \union {[To |-> to, From |-> from, Type |-> type]};
  }

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  process (P \in participants)
  {
    pPh1:
      await state[self] = "propose";
      Receive(coord, self, "prepare");

      either {
        state[self] := "accept";
        Send(self, coord, "prepared");
      } or {
        state[self] := "refuse";
        Send(self, coord, "aborted");
      };

    pPh2:
      await (state[self] = "commit") \/ (state[self] = "abort");
      either {
        Receive(coord, self, "commit");
      } or {
        Receive(coord, self, "abort");
      };

      if (state[self] = "commit") {
        state[self] := "committed";
        Send(self, coord, "committed");
      } else {
        state[self] := "aborted";
        Send(self, coord, "aborted");
      };
  };

  process (Coordinator = "c1")
    variables parts = <<>>, aborted = FALSE;
  {
    n0:
      parts := participants;

    n1:
      state := Broadcast(state, "propose", parts);
      messages := SendMessages(messages, "prepare", parts);

    n3:
      while (parts /= {}) {
        with (r \in parts) {
          either {
            Receive(coord, r, "prepared");
          } or {
            Receive(coord, r, "abort");
          };
          await (state[r] = "accept") \/ (state[r] = "refuse");
          if ((state[r] = "refuse") /\ [From |-> r, To |-> coord, Type |-> "abort"] \in messages) {
            aborted := TRUE;
          };
          parts := parts \ {r};
        };
      };

      parts := participants;
      if (aborted) {
        n4:
          state := Broadcast(state, "abort", parts);
          messages := SendMessages(messages, "abort", parts);
      } else {
        nck:
          assert \A p \in parts : (state[p] = "accept");
        n5:
          state := Broadcast(state, "commit", parts);
          messages := SendMessages(messages, "commit", parts);
      };
  }

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "660f34c9" /\ chksum(tla) = "73cfb4a7")
VARIABLES participants, state, messages, pc, parts, aborted

vars == << participants, state, messages, pc, parts, aborted >>

ProcSet == (participants) \cup {"c1"}

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ state = [p \in participants |-> "start"]
        /\ messages = {}
        (* Process Coordinator *)
        /\ parts = <<>>
        /\ aborted = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in participants -> "pPh1"
                                        [] self = "c1" -> "n0"]

pPh1(self) == /\ pc[self] = "pPh1"
              /\ state[self] = "propose"
              /\ [To |-> self, From |-> coord, Type |-> "prepare"] \in messages
              /\ \/ /\ state' = [state EXCEPT ![self] = "accept"]
                    /\ messages' = (messages \union {[To |-> coord, From |-> self, Type |-> "prepared"]})
                 \/ /\ state' = [state EXCEPT ![self] = "refuse"]
                    /\ messages' = (messages \union {[To |-> coord, From |-> self, Type |-> "aborted"]})
              /\ pc' = [pc EXCEPT ![self] = "pPh2"]
              /\ UNCHANGED << participants, parts, aborted >>

pPh2(self) == /\ pc[self] = "pPh2"
              /\ (state[self] = "commit") \/ (state[self] = "abort")
              /\ \/ /\ [To |-> self, From |-> coord, Type |-> "commit"] \in messages
                 \/ /\ [To |-> self, From |-> coord, Type |-> "abort"] \in messages
              /\ IF state[self] = "commit"
                    THEN /\ state' = [state EXCEPT ![self] = "committed"]
                         /\ messages' = (messages \union {[To |-> coord, From |-> self, Type |-> "committed"]})
                    ELSE /\ state' = [state EXCEPT ![self] = "aborted"]
                         /\ messages' = (messages \union {[To |-> coord, From |-> self, Type |-> "aborted"]})
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << participants, parts, aborted >>

P(self) == pPh1(self) \/ pPh2(self)

n0 == /\ pc["c1"] = "n0"
      /\ parts' = participants
      /\ pc' = [pc EXCEPT !["c1"] = "n1"]
      /\ UNCHANGED << participants, state, messages, aborted >>

n1 == /\ pc["c1"] = "n1"
      /\ state' = Broadcast(state, "propose", parts)
      /\ messages' = SendMessages(messages, "prepare", parts)
      /\ pc' = [pc EXCEPT !["c1"] = "n3"]
      /\ UNCHANGED << participants, parts, aborted >>

n3 == /\ pc["c1"] = "n3"
      /\ IF parts /= {}
            THEN /\ \E r \in parts:
                      /\ \/ /\ [To |-> r, From |-> coord, Type |-> "prepared"] \in messages
                         \/ /\ [To |-> r, From |-> coord, Type |-> "abort"] \in messages
                      /\ (state[r] = "accept") \/ (state[r] = "refuse")
                      /\ IF (state[r] = "refuse") /\ [From |-> r, To |-> coord, Type |-> "abort"] \in messages
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
      /\ UNCHANGED << participants, state, messages >>

n4 == /\ pc["c1"] = "n4"
      /\ state' = Broadcast(state, "abort", parts)
      /\ messages' = SendMessages(messages, "abort", parts)
      /\ pc' = [pc EXCEPT !["c1"] = "Done"]
      /\ UNCHANGED << participants, parts, aborted >>

nck == /\ pc["c1"] = "nck"
       /\ Assert(\A p \in parts : (state[p] = "accept"), 
                 "Failure of assertion at line 105, column 11.")
       /\ pc' = [pc EXCEPT !["c1"] = "n5"]
       /\ UNCHANGED << participants, state, messages, parts, aborted >>

n5 == /\ pc["c1"] = "n5"
      /\ state' = Broadcast(state, "commit", parts)
      /\ messages' = SendMessages(messages, "commit", parts)
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

StateOK ==
  /\ (\A p \in participants: state[p] \in {"start", "propose", "accept", "commit", "abort", "committed", "aborted", "refuse"})

\* everyone eventually commits or aborts.
\* this is a temporal property which cannot be checked with stuttering it seems.
Committed == /\ \/ <>(\A p \in participants: state[p] = "committed")
                \/ <>(\A p \in participants: state[p] = "aborted")

Inv ==
  (\A p \in participants: state[p] \in {"committed", "aborted"}) =>
    \/ \A p \in participants:
      \* /\ state[p] = "committed"
      /\ [From |-> p, To |-> coord, Type |-> "committed"] \in messages
    \/ \A p \in participants:
      \* /\ state[p] = "aborted"
      /\ [From |-> p, To |-> coord, Type |-> "aborted"] \in messages

Mapping == INSTANCE TwoPhaseCommit
Refinement == Mapping!Spec

==================================================================
