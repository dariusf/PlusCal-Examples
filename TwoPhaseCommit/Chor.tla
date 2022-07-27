--------------------- MODULE Chor ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, coord

(* --algorithm Chor {
  variables
    participants = {p1, p2};
    out = {};
    messages = {};

  macro Send(from, to, type) {
    messages := messages \union {[To |-> to, From |-> from, Type |-> type]};
  }

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  choreography
    (P \in participants),
    (C = coord)
      variables
        aborted = {},
        committed = {},
        has_aborted = FALSE;
  {
    all (p \in participants) {
      Send(coord, p, "prepare");
      out := out \union {<<p, coord>>};
    }
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "7abe3a2c" /\ chksum(tla) = "937bbcdf")
VARIABLES participants, out, messages, pc, ps_1, ps_6, aborted, committed, 
          has_aborted

vars == << participants, out, messages, pc, ps_1, ps_6, aborted, committed, 
           has_aborted >>

ProcSet == (participants) \cup (participants) \cup (participants) \cup {coord}

Init == (* Global variables *)
        /\ participants = {p1, p2}
        /\ out = {}
        /\ messages = {}
        (* Process proc_0 *)
        /\ ps_1 = [self \in participants |-> participants]
        (* Process proc_5 *)
        /\ ps_6 = [self \in participants |-> participants]
        (* Process C *)
        /\ aborted = {}
        /\ committed = {}
        /\ has_aborted = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in participants -> "Lbl_1"
                                        [] self \in participants -> "Lbl_2"
                                        [] self \in participants -> "Lbl_3"
                                        [] self = coord -> "Lbl_4"]

Lbl_1(self) == /\ pc[self] = "Lbl_1"
               /\ IF ps_1[self] # {}
                     THEN /\ LET  == pp_2 \in { pr_3 \in << "participants" >> : pc[pr_3] = "pa_4"} IN
                               ps_1' = [ps_1 EXCEPT ![self] = ps_1[self] \ {{pp_2}}]
                          /\ pc' = [pc EXCEPT ![self] = "Lbl_1"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ ps_1' = ps_1
               /\ UNCHANGED << participants, out, messages, ps_6, aborted, 
                               committed, has_aborted >>

proc_0(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self] = "Lbl_2"
               /\ \A p \in << "participants" >> : pc[p] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << participants, out, messages, ps_1, ps_6, 
                               aborted, committed, has_aborted >>

P(self) == Lbl_2(self)

Lbl_3(self) == /\ pc[self] = "Lbl_3"
               /\ IF ps_6[self] # {}
                     THEN /\ LET  == pp_7 \in { pr_8 \in << "participants" >> : pc[pr_8] = "pa_9"} IN
                               ps_6' = [ps_6 EXCEPT ![self] = ps_6[self] \ {{pp_7}}]
                          /\ pc' = [pc EXCEPT ![self] = "Lbl_3"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ ps_6' = ps_6
               /\ UNCHANGED << participants, out, messages, ps_1, aborted, 
                               committed, has_aborted >>

proc_5(self) == Lbl_3(self)

Lbl_4 == /\ pc[coord] = "Lbl_4"
         /\ \A p \in << "participants" >> : pc[p] = "Done"
         /\ pc' = [pc EXCEPT ![coord] = "Done"]
         /\ UNCHANGED << participants, out, messages, ps_1, ps_6, aborted, 
                         committed, has_aborted >>

C == Lbl_4

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == C
           \/ (\E self \in participants: proc_0(self))
           \/ (\E self \in participants: P(self))
           \/ (\E self \in participants: proc_5(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==================================================================
