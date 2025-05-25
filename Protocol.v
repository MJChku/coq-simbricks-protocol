
From Coq Require Import Lists.List Arith.PeanoNat Lia Program.Wf.
Import ListNotations.
Open Scope nat_scope.

Require Import STR.EventDSL STR.Trace STR.SuperTrace STR.SuperTraceMerge.

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

(* Merge into super trace, drops sync messages *)
Compute let '(_, cfg') := consume_events sample_events 0 19 2 start_cfg in
        let super_trace :=  (merge_traces sample_events (get_trace cfg')) in 
        strace_end_ts super_trace.

Definition sync_filter (tr : list TimedEvent) : list TimedEvent :=
  filter (fun x =>
            let evnt := get_evt x in
            match evnt with
            | SYNC => true
            | _ => false end) tr.

(* all_sync means all events in the trace are SYNC *)
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

(* all_sync distributes across concatenation *)
Lemma all_sync_dist :
  forall tr tr',
    all_sync (tr ++ tr') -> all_sync tr /\ all_sync tr'.
Proof.
  intros.
  induction tr.
  - split.
    + firstorder.
    + apply H.
  - destruct a as [ [ id type ] ts ].
    simpl in H.
    split.
    + simpl.
      split.
      * apply H.
      * apply IHtr. apply H.
    + apply IHtr. apply H.
Qed.

(* sync_filter returns an all_sync list *)
Lemma sync_filter_all_sync :
  forall tr,
    all_sync (sync_filter tr).
Proof.
  intros.
  induction tr.
  - firstorder.
  - destruct a as [ [ id type ] ts ].
    destruct type.
    5: { simpl. split. reflexivity. assumption. }
    all: simpl; assumption.
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

(* Running consume loop means that all SYNC in either trace appears in the final trace *)
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

(* A lemma to prove boundedness by ensuring each element is either the biggest or there is another element that is not too much higher than it *)
Lemma bounded_trace_in_sorted :
  forall tr link_delay,
    sorted_ts tr ->
    (
      forall x, In x tr ->
                (forall y, In y tr -> get_ts x >= get_ts y) \/
                (exists y, get_ts y > get_ts x /\ In y tr /\ gap_ok link_delay x y)) ->
    bounded_trace tr link_delay.
Proof.
  intros.
  induction tr.
  - firstorder.
  - destruct tr.
    + firstorder.
    + destruct a as [ eva tsa ]. destruct t as [ evt tst ].
      simpl.
      split.
      * specialize H0 with (eva, tsa).
        specialize in_eq with (a := (eva, tsa))(l := (evt, tst) :: tr). intros.
        apply H0 in H1.
        destruct H1.
        -- specialize H1 with (evt, tst).
           specialize in_eq with (a := (evt, tst))(l := tr). intros.
           eapply in_cons in H2.
           apply H1 in H2.
           simpl in H2.
           lia.
        -- destruct H1.
           destruct x as [ ev ts ].
           simpl in H1.
           destruct H1 as ( Hts & Hin & Hgap ).
           destruct Hin.
           ++ inversion H1. lia.
           ++ destruct H.
              eapply sorted_ts_in_order in H2.
              2: apply H1.
              lia.
      * apply IHtr.
        -- apply H.
        -- intros.
           pose proof H1.
           eapply incl_tl in H1.
           2: apply incl_refl.
           apply H0 in H1.
           destruct H1.
           ++ left.
              intros.
              apply H1.
              eapply incl_tl.
              2: apply H3.
              apply incl_refl.
           ++ right.
              destruct H1.
              exists x0.
              split; [ | split ].
              ** apply H1.
              ** destruct H1 as ( Htscmp & Hin & Hgap ).                 
                 destruct Hin.
                 {
                   destruct x as [ ev' ts' ].
                   eapply sorted_ts_in_order in H.
                   2: {
                     simpl.
                     right.
                     apply H2.
                   }
                   rewrite <- H1 in Htscmp.
                   simpl in Htscmp.
                   apply Arith_base.le_not_gt_stt in H.
                   contradiction.
                 }
                 apply H1.
              ** apply H1.
Qed.

Fixpoint first_sync (tr : list TimedEvent) : option nat :=
  match tr with
  | [] => None
  | ((id, ev), ts) :: tr' =>
      match ev with
      | SYNC => Some ts
      | _ => first_sync tr'
      end
  end.

Fixpoint last_sync (tr : list TimedEvent) : option nat :=
  match tr with
  | [] => None
  | ((id, ev), ts) :: tr' =>
      match ev with
      | SYNC =>
          match (last_sync tr') with
          | None => Some ts
          | Some v => Some v
          end
      | _ => last_sync tr'
      end
  end.

Definition first_event (tr : list TimedEvent) : option TimedEvent :=
  match tr with
  | [] => None
  | x :: tr' => Some x
  end.

Definition first_event_ts (tr : list TimedEvent) : option nat :=
  match first_event tr with
  | None => None
  | Some (ev, ts) => Some ts
  end.

Fixpoint last_event (tr : list TimedEvent) : option TimedEvent :=
  match tr with
  | [] => None
  | [x] => Some x
  | x :: tr' => last_event tr'
  end.

Definition last_event_ts (tr : list TimedEvent) : option nat :=
  match last_event tr with
  | None => None
  | Some (ev, ts) => Some ts
  end.

Lemma last_event_ts_some :
  forall ts tr,
    last_event_ts tr = Some ts -> exists ev, last_event tr = Some (ev, ts).
Proof.
  intros.
  unfold last_event_ts in H.
  remember (last_event tr) as le.
  destruct le.
  - destruct t as [ evt tst ].
    exists evt.
    inversion H.
    reflexivity.
  - inversion H.
Qed.    

(* Adding an element to the front does not change last event *)
Lemma last_event_append_front :
  forall x tr,
    tr <> [] -> last_event tr = last_event (x :: tr).
Proof.
  intros.
  destruct tr.
  - firstorder.
  - reflexivity.
Qed.

(* Extending the list in front does not change last event *)
Lemma last_event_extend_front :
  forall l tr,
    tr <> [] -> last_event tr = last_event (l ++ tr).
Proof.
  intros.
  induction l.
  - firstorder.
  - destruct tr.
    + firstorder.
    + specialize app_cons_not_nil with TimedEvent l tr t. intros.
      apply not_eq_sym in H0.
      eapply last_event_append_front in H0.
      rewrite <- app_comm_cons.
      rewrite IHl.
      apply H0.
Qed.

(* The last event of the list is in the list *)
Lemma last_event_in :
  forall x tr,
    last_event tr = Some x -> In x tr.
Proof.
  intros.
  induction tr.
  - inversion H.
  - destruct tr.
    + inversion H. firstorder.
    + erewrite <- last_event_append_front in H.
      2: apply not_eq_sym; apply nil_cons.
      apply IHtr in H.
      right. apply H.
Qed.

(* Every element in a sorted list has timestamp no higher than the last element *)
Lemma sorted_ts_cmp_last :
  forall x y tr,
    sorted_ts tr ->
    last_event tr = Some y ->
    In x tr ->
    get_ts x <= get_ts y.
Proof.
  intros.
  induction tr.
  - inversion H0.
  - destruct a as [ eva tsa ]. destruct tr.
    + inversion H0.
      inversion H1.
      * subst. firstorder.
      * inversion H2.
    + destruct H1.
      * apply last_event_in in H0.
        subst.
        destruct y as [ evy tsy ].
        eapply sorted_ts_in_order; unfold get_ts in *.
        2: apply H0.
        apply H.
      * eapply IHtr.
        -- destruct t as [ evt tst ]. apply H.
        -- erewrite last_event_append_front.
           2: apply not_eq_sym; apply nil_cons.
           apply H0.
        -- apply H1.
Qed.      

(* If the first and last event of a list is close enough, the entire list is bounded *)
Lemma bounded_events_in_btw :
  forall x y tr link_delay,
    first_event tr = Some x ->
    last_event tr = Some y ->
    sorted_ts tr ->
    gap_ok link_delay x y ->
    bounded_trace tr link_delay.
Proof.
  intros. generalize dependent x.
  induction tr; intros.
  - firstorder.
  - destruct tr.
    + firstorder.
    + destruct x as [ evx tsx ].
      destruct t as [ evt tst ].
      destruct y as [ evy tsy ].
      split.
      * inversion H. subst.
        eapply sorted_ts_cmp_last in H1.
        2: apply H0.
        2: eapply in_cons; apply in_eq.
        unfold gap_ok in *.
        simpl in H1.
        lia.
      * eapply IHtr.
        -- erewrite last_event_append_front.
           2: apply not_eq_sym; apply nil_cons.
           apply H0.
        -- destruct a. apply H1.
        -- reflexivity.
        -- inversion H. subst.
           unfold gap_ok in *.
           destruct H1.
           lia.
Qed.

(* Prove boundedness from subcomponents *)
Lemma bounded_trace_from_split :
  forall l1 x l2 link_delay,
    bounded_trace (l1 ++ [x]) link_delay ->
    bounded_trace (x :: l2) link_delay ->
    bounded_trace (l1 ++ x :: l2) link_delay.
Proof.
  intros.
  induction l1.
  - apply H0.
  - remember (l1 ++ x :: l2) as l. destruct l.
    + apply app_cons_not_nil in Heql.
      contradiction.
    + simpl. rewrite <- Heql.
      remember (l1 ++ [x]) as l'. destruct l'.
      * apply eq_sym in Heql'.
        apply app_eq_nil in Heql'.
        destruct Heql'.
        inversion H2.
      * simpl in H.
        rewrite <- Heql' in H.
        rewrite <- app_nil_l with (l := l2) in Heql.
        rewrite app_comm_cons in Heql.
        rewrite app_assoc in Heql.
        rewrite <- Heql' in Heql.
        inversion Heql. subst.
        split.
        -- apply H.
        -- apply IHl1. apply H.
Qed.

(* Sorted property distributes over ++ *)
Lemma sorted_ts_dist :
  forall l1 l2,
    sorted_ts (l1 ++ l2) -> sorted_ts l1 /\ sorted_ts l2.
Proof.
  intros.
  induction l1.
  - split.
    + firstorder.
    + apply H.
  - destruct a as [ eva tsa ].
    destruct l2.
    + split.
      * rewrite app_nil_r in H. apply H.
      * firstorder.
    + remember (l1 ++ t :: l2) as l. destruct l.
      * apply app_cons_not_nil in Heql.
        contradiction.
      * simpl in H. rewrite <- Heql in H.
        destruct t0 as [ evt0 tst0 ].
        split.
        -- destruct l1.
           ++ firstorder.
           ++ inversion Heql. subst.
              split.
              ** apply H.
              ** apply IHl1. apply H.
        -- apply IHl1. apply H.
Qed.

Fixpoint ts_list (tr : list TimedEvent) : list nat :=
  match tr with
  | [] => []
  | (ev, ts) :: tr' => ts :: (ts_list tr')
  end.

(* A sorted list can be split such that we get a list with all elements smaller than a timestamp, the smallest element with the timestamp, and the rest of the list *)
Lemma in_split_first_ts :
  forall x l,
    sorted_ts l ->
    In x l ->
    exists l1 l2 y,
      get_ts x = get_ts y
      /\ l = l1 ++ y :: l2
      /\ (forall z, In z l1 -> get_ts z < get_ts y).
Proof.
  intros.
  induction l.
  - inversion H0.
  - destruct l.
    + inversion H0.
      * subst. exists [], [], x.
        split; [ | split ].
        -- reflexivity.
        -- reflexivity.
        -- intros. inversion H1.
      * inversion H1.
    + destruct a as [ eva tsa ].
      destruct t as [ evt tst ].
      destruct x as [ evx tsx ].
      case_eq (tsa ?= tsx); intros Heq.
      * apply Nat.compare_eq in Heq.
        exists [], ((evt, tst) :: l), (eva, tsa).
        split; [ | split ].
        -- simpl.
           subst.
           reflexivity.
        -- reflexivity.
        -- intros. inversion H1.
      * rewrite Nat.compare_lt_iff in Heq.
        destruct H.
        apply IHl in H1.
        2: {
          apply in_inv in H0.
          destruct H0.
          - inversion H0.
            lia.
          - apply H0.
        }          
        destruct H1 as ( l1 & l2 & y & Hts & Hl & Hgt ).
        exists ((eva, tsa) :: l1), l2, y.
        split; [ | split ].
        -- apply Hts.
        -- rewrite Hl. reflexivity.
        -- intros.
           destruct y as [ evy tsy ].
           destruct z as [ evz tsz ].
           apply in_inv in H1.
           destruct H1.
           ++ unfold get_ts in *. inversion H1. lia.
           ++ apply Hgt. apply H1.
      * rewrite Nat.compare_gt_iff in Heq.
        apply sorted_ts_in_order in H0.
        2: apply H.
        lia.
Qed.         

(* If a trace is bounded, adding more events between the timestamps will not make it unbounded *)
Lemma bounded_trace_more_events:
  forall tr tr' link_delay,
    incl tr tr' ->
    sorted_ts tr ->
    sorted_ts tr' ->
    first_event_ts tr = first_event_ts tr' ->
    last_event_ts tr = last_event_ts tr' ->
    bounded_trace tr link_delay ->
    bounded_trace tr' link_delay.
Proof.
  intros. generalize dependent tr'.
  induction tr; intros.
  - destruct tr'.
    + firstorder.
    + destruct t. inversion H2.
  - destruct tr.
    + destruct a as [ eva tsa ].
      apply bounded_trace_in_sorted.
      * apply H1.
      * intros.
        left.
        intros.
        pose proof H1.
        destruct tr'.
        -- apply incl_l_nil in H. inversion H.
        -- destruct t as [ evt tst ].
           destruct x as [ evx tsx ].
           destruct y as [ evy tsy ].
           simpl in H2. inversion H2. subst.
           eapply sorted_ts_in_order in H1.
           2: { apply H5. }
           unfold last_event_ts in H3 at 1. simpl in H3.
           apply eq_sym in H3.
           apply last_event_ts_some in H3.
           destruct H3.
           eapply sorted_ts_cmp_last in H7.
           2: { apply H3. }
           2: apply H6.
           unfold get_ts in *.
           lia.
    + destruct a as [ eva tsa ].
      destruct t as [ evt tst ].
      apply incl_cons_inv in H.
      destruct H.
      apply incl_cons_inv in H5.
      destruct H5.
      pose proof H5.
      apply in_split_first_ts in H5.
      2: apply H1.
      destruct H5 as ( l1 & l2 & [ evy tsy ] & Hts & Hl & Hgt ).
      simpl in Hts. subst.
      apply bounded_trace_from_split.
      * destruct l1.
        -- firstorder.
        -- destruct t as [ evt' tst' ].
           unfold first_event_ts in H2. inversion H2. subst.
           eapply bounded_events_in_btw.
           ++ reflexivity.
           ++ erewrite <- last_event_extend_front.
              2: { unfold "<>"; intros. inversion H5. }
              reflexivity.
           ++ rewrite <- app_nil_l with (l := l2) in H1.
              rewrite app_comm_cons in H1.
              rewrite app_assoc in H1.
              apply sorted_ts_dist in H1.
              apply H1.
           ++ simpl. apply H4.
      * eapply IHtr.
        -- apply H0.
        -- apply H4.
        -- apply incl_cons.
           ++ rewrite in_app_iff in H7.
              destruct H7.
              ** apply Hgt in H5.
                 simpl in H5.
                 lia.
              ** apply H5.
           ++ unfold incl.
              intros.
              unfold incl in H6.
              specialize H6 with a.
              destruct a as [ eva' tsa' ].
              pose proof H5.
              apply H6 in H5.
              rewrite in_app_iff in H5.
              destruct H5.
              ** apply Hgt in H5.
                 simpl in H5.
                 destruct H0.
                 eapply sorted_ts_in_order in H9.
                 2: apply in_cons; apply H8.
                 lia.
              ** apply H5.
        -- apply sorted_ts_dist in H1.
           apply H1.
        -- reflexivity.
        -- unfold last_event_ts in H3.
           rewrite <- last_event_append_front in H3.
           2: { apply not_eq_sym. apply nil_cons. }
           rewrite <- last_event_extend_front in H3.
           2: { apply not_eq_sym. apply nil_cons. }
           apply H3.
Qed.

Lemma not_nil_last_event :
  forall tr,
    tr <> [] -> last_event tr <> None.
Proof.
  intros.
  induction tr.
  - contradiction.
  - destruct tr.
    + simpl. unfold "<>". intros. inversion H0.
    + rewrite <- last_event_append_front.
      2: apply not_eq_sym; apply nil_cons.
      apply IHtr.
      apply not_eq_sym; apply nil_cons.
Qed.

Lemma last_event_nil :
  forall tr,
    last_event tr = None -> tr = [].
Proof.
  intros.
  induction tr.
  - reflexivity.
  - destruct tr.
    + inversion H.
    + inversion H.
      apply IHtr in H1.
      inversion H1.
Qed.

Lemma consume_loop_last_event_bound :
  forall ts ptr ptr_last_sync delay link_delay h tr p res h' tr' p',
    consume_loop ts ptr ptr_last_sync delay link_delay (h, (tr, p)) = (res, (h', (tr', p'))) ->
    sorted_ts (tr ++ ts) ->
    (tr ++ ts = [] /\ tr' = []) \/
      (exists x y, last_event (tr ++ ts) = Some x /\
                     last_event tr' = Some y /\
                     get_ts x >= get_ts y).
Proof.
  intros.
  generalize dependent p'. generalize dependent tr'. generalize dependent h'.
  generalize dependent p. generalize dependent tr. generalize dependent h.
  induction ts; intros.
  - inversion H. subst. destruct tr'.
    + left. split; reflexivity.
    + right. remember (last_event (t :: tr')) as e. destruct e.
      * exists t0, t0. split; [ | split ].
        -- rewrite app_nil_r. apply eq_sym. apply Heqe.
        -- reflexivity.
        -- lia.
      * apply eq_sym in Heqe.
        apply last_event_nil in Heqe.
        inversion Heqe.
  - right.
    
    destruct a as [ [ id type ] ts_ev ].
    simpl in H.
    unfold bind in H.

    find_equivalences.

    apply IHts in H.
    + destruct H.
      * destruct H.
        apply app_eq_nil in H.
        destruct H.
        subst.

    
    

(* What property do we need between the last events and first events? *)
Lemma consume_loop_all_sync_bounded :
  forall ts ptr ptr_last_sync delay link_delay h tr p res h' tr' p' x y,
    consume_loop ts ptr ptr_last_sync delay link_delay (h, (tr, p)) = (res, (h', (tr', p'))) ->
    all_sync ts ->
    bounded_trace tr link_delay ->
    bounded_trace ts link_delay ->
    last_event tr = Some x ->
    first_event ts = Some y ->
    gap_ok link_delay x y ->
    bounded_trace tr' link_delay.
Proof.
  intros.
  

Lemma consume_loop_bounded :
  forall ts ptr ptr_last_sync delay link_delay h tr p res h' tr' p',
    consume_loop ts ptr ptr_last_sync delay link_delay (h, (tr, p)) = (res, (h', (tr', p'))) ->
    bounded_trace tr link_delay ->
    bounded_trace (sync_filter ts) link_delay ->
    bounded_trace tr' link_delay.
Proof.
  intros.
  

(* Not true due to delay *)
Lemma consume_loop_bounded_from_sync :
  forall ts ptr ptr_last_sync delay link_delay h tr p res h' tr' p' ts0 tr0 p0 res0 h0' tr0' p0',
    consume_loop ts ptr ptr_last_sync delay link_delay (h, (tr, p)) = (res, (h', (tr', p'))) ->
    consume_loop ts0 ptr ptr_last_sync delay link_delay (h, (tr0, p0)) = (res0, (h0', (tr0', p0'))) ->
    (forall x, In x tr -> In x tr0) ->
    (forall y, In y p -> In y p0) ->
    (forall z, In z ts -> In z ts0) ->
    bounded_trace tr' link_delay ->
    bounded_trace tr0' link_delay.
Proof. Admitted.      

Lemma consume_loop_all_sync_same :
  forall ts ptr ptr_last_sync delay link_delay h tr res h' tr',
    consume_loop ts ptr ptr_last_sync delay link_delay (h, (tr, [])) = (res, (h', (tr', []))) ->
    all_sync tr ->
    all_sync ts ->
    tr ++ ts = tr'.
Proof. Admitted.
  
                  

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
    
