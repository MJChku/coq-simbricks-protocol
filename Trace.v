From Coq Require Import Lists.List Arith.PeanoNat Lia Program.Wf.
Import ListNotations.
Open Scope nat_scope.

Require Import STR.EventDSL.

Import DSL Events.

(* A trace is bounded if successive timestamps differ ≤ k *)
Definition gap_ok (k : nat) (t1 t2 : TimedEvent) : Prop :=
  let '(_, ts1) := t1 in
  let '(_, ts2) := t2 in
  ts2 - ts1 <= k.

Definition gap_exact (k : nat) (t1 t2 : TimedEvent) : Prop :=
  let '(_, ts1) := t1 in
  let '(_, ts2) := t2 in
  ts2 - ts1 = k.

Fixpoint bounded_trace         
         (tr : list TimedEvent)
         (link_delay  : nat) : Prop :=
  match tr with
  | [] | [_] => True
  | t1 :: ((t2 :: rest) as tail) =>  
        gap_ok link_delay t1 t2
      /\ bounded_trace tail link_delay
  end.

Fixpoint live_trace
          (tr : list TimedEvent)
          (link_delay  : nat) : Prop :=
    match tr with
    | [] | [_] => True
    | t1 :: ((t2 :: rest) as tail) =>  
          gap_exact link_delay t1 t2
        /\ live_trace tail link_delay
    end.
  
(* Example events *)
Definition sample_events : list TimedEvent :=
  [ mkEvent 0 SYNC 1;
    mkEvent 1 MMIO_READ_REQ 1;
    mkEvent 2 MMIO_READ_REQ 1;
    mkEvent 3 MMIO_READ_REQ 1;
    mkEvent 4 MMIO_READ_REQ 1;
    mkEvent 5 SYNC 3;
    mkEvent 6 DMA_READ_REQ 3;
    mkEvent 7 SYNC 5;
    mkEvent 8 SYNC 7;
    mkEvent 9 MMIO_READ_REQ 7
  ]. 
