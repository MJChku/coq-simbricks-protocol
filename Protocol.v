
From Coq Require Import Lists.List Arith.PeanoNat Lia Program.Wf.
Import ListNotations.
Open Scope nat_scope.

Require Import STR.EventDSL STR.Trace.

Import DSL Events.

(* A simple looping program that consumes an external list and logs it *)
Fixpoint consume (ts : list TimedEvent) : State unit :=
  match ts with
  | [] => ret tt
  | t :: ts' =>
      enq_log t ;; (* record t in our trace *)
      consume ts'
  end.


(* Simple length property *)
Lemma consume_extends_trace :
  forall ts cfg res cfg',
    consume ts cfg = (res, cfg') ->
    length (get_trace cfg') = length (get_trace cfg) + length ts.
Proof.
induction ts as [|t ts IH]; intros [h [tr q]] res [h' [tr' q']] Hrun.
  - simpl in Hrun. inversion Hrun. firstorder.
  - simpl in Hrun. unfold enq_log in Hrun. unfold bind in Hrun.
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

(* what event to generate for each type of event? req corresponds to resp *)
Definition process_event (t : TimedEvent) (my_ts delay : nat) : State unit :=
  let id  := get_id  t in
  let ev  := get_evt  t in
  match ev with
  | MMIO_READ_REQ  => enq_event_ord ((id, MMIO_READ_RESP), my_ts + delay)
  | DMA_READ_REQ   => enq_event_ord ((id, DMA_READ_RESP),  my_ts + delay)
  | SYNC           => enq_event_ord ((id, SYNC),           my_ts)
  | _              => ret tt
  end.

(* process_event does not change trace *)
Lemma process_event_unchanged_trace :
  forall t my_ts delay h tr q res h' tr' q',
    process_event t my_ts delay (h, (tr, q)) = (res, (h', (tr', q'))) ->
    tr = tr'.
Proof.
  intros.
  unfold process_event in H.
  unfold enq_event_ord in H.
  destruct (get_evt t); inversion H; subst; reflexivity.
Qed.

(* process_event preserves sorted property of EventQueue *)
Lemma process_event_queue_remains_sorted :
  forall t my_ts delay h tr q res h' tr' q',
    process_event t my_ts delay (h, (tr, q)) = (res, (h', (tr', q'))) ->
    sorted_ts q ->
    sorted_ts q'.
Proof.
  intros.
  unfold process_event in H.
  unfold enq_event_ord in H.
  destruct (get_evt t); inversion H; subst.
  all: try apply insert_ts_sorted_list; assumption.
Qed.  
  
Definition start_cfg : Config := mkConfig heap_empty [] [].

Definition test_event_queue : State unit :=
  enq_event_ord (mkEvent 0 MMIO_READ_RESP 10) ;;
  enq_event_ord (mkEvent 1 MMIO_READ_RESP 1) ;;
  enq_event_ord (mkEvent 2 MMIO_READ_RESP 200) ;;
  enq_event_ord (mkEvent 3 MMIO_READ_RESP 30) ;;
  ret tt.

Compute let '(_, cfg') := test_event_queue start_cfg in
         (get_heap cfg', get_eq cfg', get_trace cfg').


(* commit events in the event queue upto the my_ts timestamp *)
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


(* no events befind ts in the event queue *)
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

(* commit_q guarantees there is nothing left in the EventQueue to commit to the timestamp *)
Lemma commit_q_no_more_to_commit :
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

(* Events in the trace remain there after commit_q *)
Lemma commit_q_trace_remains :
  forall q ts tr tr' q' x,
    commit_q q ts tr = (tr', q') ->
    In x tr -> In x tr'.
Proof.
  intros.
  generalize dependent tr.
  induction q; intros.
  - inversion H. subst. assumption.
  - simpl in H.
    destruct a as [ ev ts_ev ].
    destruct (ts_ev <=? ts).
    + eapply IHq.
      * apply H.
      * eapply incl_appl in H0.
        apply H0.
        apply incl_refl.
    + inversion H. subst. assumption.
Qed.

(* commit_q guarantees that every event to be committed appears in the trace *)
Lemma commit_q_committed :
  forall q ts tr tr' q' ev ts_ev,
    commit_q q ts tr = (tr', q') ->
    In (ev, ts_ev) q ->
    sorted_ts q ->
    ts_ev <= ts ->
    In (ev, ts_ev) tr'.
Proof.
  intros. generalize dependent tr.
  induction q; intros.
  - inversion H0.
  - destruct a as [ ev' ts_ev' ].
    apply in_inv in H0. destruct H0.
    + simpl in H. inversion H0. subst.
      rewrite <- Nat.leb_le in H2.
      rewrite H2 in H.
      eapply commit_q_trace_remains.
      * apply H.
      * apply in_or_app. right. simpl. left. reflexivity.
    + eapply IHq.
      * assumption.
      * simpl in H1.
        destruct q.
        -- firstorder.
        -- destruct t. apply H1.
      * eapply sorted_ts_in_order in H1.
        2: {
          simpl.
          right.
          apply H0.
        }
        simpl in H.
        eapply Nat.le_trans with (p := ts) in H1.
        2: apply H2.
        rewrite <- Nat.leb_le in H1.
        rewrite H1 in H.
        apply H.
Qed.

(* commit_q preserves sorted property of the EventQueue *)
Lemma commit_q_sorted :
  forall q ts tr tr' q',
    commit_q q ts tr = (tr', q') ->
    sorted_ts q ->
    sorted_ts q'.
Proof.
  intros. generalize dependent tr.
  induction q; intros.
  - inversion H. firstorder.
  - destruct a as [ ev ts_ev ].
    simpl in H.
    destruct (ts_ev <=? ts).
    + eapply IHq.
      destruct q.
      * firstorder.
      * simpl in H0. simpl.
        destruct t as [ ev' ts_ev' ].
        apply H0.
      * apply H.
    + inversion H.
      apply H0.
Qed.        

(* commit events to log upto a my_ts timestamp *)
Definition commit_events (my_ts : nat) : State unit :=
  fun '(h,(tr,q)) =>
    (tt, (h, commit_q q my_ts tr)).

(* commit all events to log regardless of the timestamp*)
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
  | (ev, ts_ev) :: ts'  =>
          write ptr ts_ev ;;

          (* process one incoming event*)
          process_event (ev, ts_ev) ts_ev dly ;;

           (* commit all events *)
          commit_events ts_ev ;;

          consume_loop ts' ptr ptr_last_sync dly link_delay
  end.

(* real protocol code *)
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

Fixpoint all_sync (tr : list TimedEvent) : Prop :=
  match tr with
  | [] => True
  | ((id, ev), ts) :: tr' => ev = SYNC /\ all_sync tr'
  end.

(* all_sync means any event inside is a SYNC *)
Lemma in_all_sync :
  forall tr x,
    all_sync tr -> In x tr -> get_evt x = SYNC.
Proof.
  intros.
  induction tr.
  - firstorder.
  - destruct a as [ [ i ev ] ts ].
    apply in_inv in H0.
    destruct H0.
    + rewrite <- H0.
      simpl.
      apply H.
    + apply IHtr.
      apply H.
      apply H0.
Qed.

(* A tactic to find which heaps and queues are equal after running certain commands *)
Ltac find_equivalences :=
  repeat match goal with
    | [ H: (let (_, cfg) := write ?ptr ?ts_ev (?h, (?tr, ?p)) in _) = _ |- _ ] =>
        remember (write ptr ts_ev (h, (tr, p))) as retw eqn: Heqretw;
        destruct retw as [ resw [ hw [ trw pw ] ] ];
        apply eq_sym in Heqretw;
        pose proof Heqretw as Heqretw';
        apply write_unchanged_queue in Heqretw';
        destruct Heqretw'; subst
    | [ H: (let (_, cfg) := process_event (?id, ?type, ?ts_ev) ?ts_ev ?delay (?h, (?tr, ?p)) in _ ) = _ |- _ ] =>
        remember (process_event (id, type, ts_ev) ts_ev delay (h, (tr, p))) as retpe eqn: Heqretpe;
        destruct retpe as [ respe [ hpe [ trpe ppe ] ] ];
        apply eq_sym in Heqretpe;
        pose proof Heqretpe as Heqretpe';
        apply process_event_unchanged_trace in Heqretpe'; subst
    | [ H: (let (_, cfg) := commit_events ?ts_ev (?h, (?tr, ?p)) in _) = _ |- _ ] =>
        remember (commit_events ts_ev (h, (tr, p))) as retce eqn: Heqretce;
        destruct retce as [ resce [ hce [ trce pce ] ] ];
        unfold commit_events in Heqretce;
        inversion Heqretce; subst
    end.

(* If an event was in the original trace, it will remain in the final trace *)
Lemma consume_loop_trace_remains :
  forall ts ptr ptr_last_sync delay link_delay h tr p res h' tr' p' x,
    consume_loop ts ptr ptr_last_sync delay link_delay (h, (tr, p))
    = (res, (h', (tr', p'))) -> In x tr -> In x tr'.
Proof.
  intros.
  generalize dependent p'. generalize dependent tr'. generalize dependent h'.
  generalize dependent p. generalize dependent tr. generalize dependent h.
  induction ts; intros.
  - simpl in H.
    inversion H. subst.
    assumption.
  - destruct a as [ [ id type ] ts_ev ].
    simpl in H.
    unfold bind in H.

    find_equivalences.

    apply eq_sym in H4.
    eapply commit_q_trace_remains in H4.
    2: apply H0.
    eapply IHts.
    + apply H4.
    + apply H.
Qed.

(* If a SYNC event was in either traces, it will appear in the final trace *)
Lemma consume_loop_sync_in_trace :
  forall ts ptr ptr_last_sync delay link_delay h tr p res h' tr' p' x,
    consume_loop ts ptr ptr_last_sync delay link_delay (h, (tr, p))
    = (res, (h', (tr', p'))) ->
    sorted_ts p ->
    get_evt x = SYNC ->
    In x tr \/ In x ts -> In x tr'.
Proof.
  intros.
  generalize dependent p'. generalize dependent tr'. generalize dependent h'.
  generalize dependent p. generalize dependent tr. generalize dependent h.
  induction ts; intros.
  - simpl in H.
    inversion H. subst.
    destruct H2.
    + assumption.
    + firstorder.
  - destruct a as [ [ id type ] ts_ev ].
    simpl in H.
    unfold bind in H.

    find_equivalences.

    destruct H2.
    (* If in original trace, we can use lemma above to show it appears in the final trace *)
    + eapply consume_loop_trace_remains.
      * apply H.
      * eapply commit_q_trace_remains.
        -- apply eq_sym. apply H6.
        -- apply H2.
    (* If in other trace, we show that it appears in the final trace *)
    + eapply IHts.
      * destruct H2.
        (* Event is the first one in the other trace *)
        -- left.
           rewrite <- e in H1. simpl in H1. subst.
           unfold process_event in Heqretpe.
           simpl in Heqretpe.
           inversion Heqretpe.
           specialize insert_ts_in with (id, SYNC, ts_ev) pw; intros.
           rewrite H4 in H1.
           apply eq_sym in H6.
           eapply commit_q_committed in H6.
           ++ apply H6.
           ++ apply H1.
           ++ rewrite <- H4.
              apply insert_ts_sorted_list.
              assumption.
           ++ apply Nat.le_refl.
        (* Event is in the rest of the other trace *)
        -- right. apply i.
      * apply process_event_queue_remains_sorted in Heqretpe.
        2: assumption.
        eapply commit_q_sorted in Heqretpe.
        2: apply eq_sym in H6; apply H6.
        apply Heqretpe.
      * apply H.
Qed.

Lemma consume_loop_all_sync_in_trace :
  forall ts ptr ptr_last_sync delay link_delay h tr p res h' tr' p' x,
    consume_loop ts ptr ptr_last_sync delay link_delay (h, (tr, p))
    = (res, (h', (tr', p'))) ->
    sorted_ts p ->
    all_sync ts ->
    In x tr \/ In x ts -> In x tr'.
Proof.
  intros.
  destruct H2.
  - eapply consume_loop_trace_remains.
    + apply H.
    + apply H2.
  - eapply in_all_sync in H1.
    2: apply H2.
    eapply consume_loop_sync_in_trace in H.
    + apply H.
    + apply H0.
    + apply H1.
    + right. apply H2.
Qed.

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
    
