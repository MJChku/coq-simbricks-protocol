
From Coq Require Import Lists.List Arith.PeanoNat Lia Program.Wf.
Import ListNotations.
Open Scope nat_scope.

Require Import STR.EventDSL STR.Trace.

Import DSL Events.
(* --------------------------------------------------- *)
(** 6. A looping program that consumes an external list and logs it *)
Fixpoint consume (ts : list TimedEvent) : State unit :=
  match ts with
  | [] => ret tt
  | t :: ts' =>
      enq_log t ;;            (* record t in our trace B *)
      consume ts'
  end.

(** 6. Trace-length property *)
Lemma consume_extends_trace :
  forall ts cfg res cfg',
    consume ts cfg = (res, cfg') ->
    length (get_trace cfg') = length (get_trace cfg) + length ts.
Proof.
induction ts as [|t ts IH]; intros [h [tr q]] res [h' [tr' q']] Hrun.
  - (* ts = [] *) simpl in Hrun. inversion Hrun. firstorder.
  - (* ts = t :: ts *)
    simpl in Hrun. unfold enq_log in Hrun. unfold bind in Hrun.
    remember (consume ts (h, (tr ++ [t], q))) as R eqn:E.
    destruct R as [res2 [h2 [tr2 q2]]]. inversion Hrun; subst; clear Hrun.
    symmetry in E. 
    assert( (res2 , (h2, (tr2, q2))) = (res, (h', (tr', q')))).
    {
      replace (res, (h', (tr', q'))) with (consume ts (mkConfig h (tr ++ [t]) q)).
      symmetry in E. apply E.
    }
    inversion H.
    specialize (IH (h, (tr ++ [t], q)) res2 (h2, (tr2, q2)) E). simpl in IH.
    subst.
    unfold get_trace in *. simpl in *.
    rewrite length_app in IH. simpl in IH. simpl in *. rewrite IH. rewrite <- Nat.add_assoc. reflexivity.
Qed.

Definition process_event (t : TimedEvent) (my_ts delay : nat) : State unit :=
  let id  := get_id  t in
  let ev  := get_evt  t in
  match ev with
  | MMIO_READ_REQ  => enq_event_ord ((id, MMIO_READ_RESP), my_ts + delay)
  | DMA_READ_REQ   => enq_event_ord ((id, DMA_READ_RESP),  my_ts + delay)
  | SYNC           => enq_event_ord ((id, SYNC),           my_ts)
  | _              => ret tt
  end.


Definition start_cfg : Config := mkConfig heap_empty [] [].

Definition test_event_queue : State unit :=
  enq_event_ord (mkEvent 0 MMIO_READ_RESP 10) ;;
  enq_event_ord (mkEvent 1 MMIO_READ_RESP 1) ;;
  enq_event_ord (mkEvent 2 MMIO_READ_RESP 200) ;;
  enq_event_ord (mkEvent 3 MMIO_READ_RESP 30) ;;
  ret tt.

Compute let '(_, cfg') := test_event_queue start_cfg in
         (get_heap cfg', get_eq cfg', get_trace cfg').

Fixpoint commit_q (q : EQ) (my_ts : nat) (tr : Trace) : Trace*EQ :=
  match q with
  | [] => (tr, [])
  | (ev, ts) :: qs =>
    if Nat.leb ts my_ts then
      let tr' := tr ++ [(ev, ts)] in
      commit_q qs my_ts tr'
    else
      (tr, (ev, ts) :: qs)
  end.

Fixpoint committed_to_time (q : list TimedEvent) (ts : nat) : Prop :=
  match q with
  | [] => True
  | ((_, _), t) :: q' => t > ts /\ committed_to_time q' ts
  end.

Lemma committed_check_first :
  forall n ev ts' q ts,
    sorted_ts ((n, ev, ts') :: q) ->
    ts' > ts ->
    committed_to_time q ts.
Proof.
  intros.
  induction q.
  - firstorder.
  - simpl. destruct a as [ [ n' ev' ] ts'' ]. split.
    + destruct H. eapply Nat.lt_le_trans.
      apply H0. apply H.
    + apply IHq.
      simpl. simpl in H.
      destruct q.
      * firstorder.
      * destruct p as [ [ n'' ev'' ] ts''' ]. split.
        eapply Nat.le_trans; apply H.
        apply H.
Qed.            
                           
Lemma commit_q_committed :
  forall q ts tr tr' q',
    commit_q q ts tr = (tr', q') ->
    sorted_ts q ->
    committed_to_time q' ts.
Proof.
  intros. generalize dependent tr.
  induction q; intros.
  - simpl in H. inversion H. firstorder.
  - simpl in H. destruct a as [ev ts'].
    remember (ts' <=? ts) as eq. destruct eq.
    + apply IHq in H.
      assumption.
      {
        simpl in H0. destruct q.
        - firstorder.
        - destruct t. destruct H0. assumption. 
      }
    + inversion H. simpl.
      apply eq_sym in Heqeq.
      rewrite Compare_dec.leb_iff_conv in Heqeq.
      destruct ev. split.
      * apply Heqeq.
      * eapply committed_check_first.
        apply H0.
        apply Heqeq.
Qed.

Definition commit_events (my_ts : nat) : State unit :=
  fun '(h,(tr,q)) =>
    (tt, (h, commit_q q my_ts tr)).

Fixpoint commit_all_q (q : EQ) (tr : Trace) :  Trace*EQ :=
  match q with
  | [] => (tr, [])
  | (ev, ts) :: qs =>
      let tr' := tr ++ [(ev, ts)] in
      commit_all_q qs tr'
  end.

Definition commit_all_events : State unit :=
  fun '(h, (tr,q)) =>
    (tt, (h, commit_all_q q tr)).

(** Recursive consumer *)
Fixpoint consume_loop
        (ts   : list TimedEvent)
        (ptr  : nat)               (* pointer where we keep current time *)
        (ptr_last_sync  : nat)               (* pointer where we keep last synced time *)
        (dly  : nat)
        (link_delay : nat)
        : State unit :=
  match ts with
  | []        => ret tt
  | (ev, ts_now) :: ts'  =>
          cur_opt <- read ptr ;;
          let cur_ts := option_default 0 cur_opt in 
          (* match cur_opt with Some n => n | None => 0 end in *)

          (* let cur_ts := if Nat.ltb cur_ts ts_now then ts_now else cur_ts in *)
          let cur_ts := ts_now in
          write ptr cur_ts ;;

          (* process one incoming event*)
          process_event (ev, ts_now) cur_ts dly ;;

           (* commit all events *)
          commit_events cur_ts ;;

          consume_loop ts' ptr ptr_last_sync dly link_delay
  end.

Definition consume_events
        (ts       : list TimedEvent)
        (start_ts : nat)
        (delay    : nat)
        (link_delay    : nat)
        : State unit :=
  p <- new 0 ;;
  p2 <- new 0;;
  write p start_ts ;;
  write p2 start_ts ;;
  consume_loop ts p p2 delay link_delay;;
  commit_all_events.

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

(* Run consume_events with start_ts = 0, delay = 1, link_delay = 2 *)
Compute (let '(_, cfg') := consume_events sample_events 0 1 2 start_cfg in
         (get_heap cfg', get_eq cfg', get_trace cfg')).


(* Check boundedness with maximum gap k = 2 *)
Compute (let '(_, cfg') := consume_events sample_events 0 1 2 start_cfg in
         bounded_trace (get_trace cfg') 2).

(* Check liveness with exact gap k = 2 *)
Compute let sync_trace:= filter (fun x => let evnt := get_evt x in match evnt with SYNC => true | _ => false end) sample_events in
        let '(_, cfg') := consume_events sync_trace 0 1 2 start_cfg in
        live_trace (get_trace cfg') 2.

(* Check that the trace is not live *)
Lemma consume_loop_bounded :
  forall ts ptr ptr_last_sync delay link_delay h tr p res h' tr' p',
    consume_loop ts ptr ptr_last_sync delay link_delay (h, (tr, p)) 
    = (res, (h', (tr', p'))) ->
    bounded_trace tr link_delay ->
    bounded_trace tr' link_delay.
Proof.
Admitted.

Lemma consume_events_bounded_trace :
  forall ts start_ts delay link_delay cfg res cfg',
    consume_events ts start_ts delay link_delay cfg = (res, cfg') ->
    bounded_trace (get_trace cfg) link_delay ->
    bounded_trace (get_trace cfg') link_delay.
Proof.
Admitted.
    
