(* EventDSL : instantiate CoreDSL with TimedEvent *)

From Coq Require Import Lists.List Arith.PeanoNat Lia Program.Wf.
Import ListNotations.
From ExtLib.Structures Require Import Monads.
Export MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.

Require Import STR.CoreDSL STR.Events.

Module EInst <: DSL_SIG.
  Definition V  := nat.
  Definition TE := TimedEvent.
End EInst.

Module DSL := MakeDSL(EInst).           (* generic ops *)
Import DSL Events.

(* ordered insertion *)
Fixpoint insert_ts (e:TimedEvent) (q:list TimedEvent) : list TimedEvent :=
  match q with
  | [] => [e]
  | x :: xs =>
      if Nat.leb (get_ts e) (get_ts x)
      then e :: q
      else x :: insert_ts e xs
  end.

Definition enq_event_ord (e: TimedEvent) : State unit :=
  fun '(h,(tr,q)) => (tt, mkConfig h tr (insert_ts e q)).

(* simple property: list stays sorted *)
Fixpoint sorted_ts (q: list TimedEvent) : Prop :=
  match q with
  | [] | [_] => True
  | (_,t1) :: ((_,t2) :: tl) as tail => t1 <= t2 /\ sorted_ts tail
  end.

(* anything in a sorted list has an equal or higher timestamp of the first element *)
Lemma sorted_ts_in_order :
  forall q ev ts ev' ts',
    sorted_ts ((ev, ts) :: q) ->
    In (ev', ts') ((ev, ts) :: q) ->
    ts <= ts'.
Proof.
  intros.
  induction q.
  - destruct H0.
    + inversion H0. subst.
      apply Nat.le_refl.
    + inversion H0.
  - destruct a as [ ev'' ts'' ].
    destruct H0; [ | destruct H0 ].
    + inversion H0. subst. apply Nat.le_refl.
    + inversion H0. subst. apply H.
    + apply IHq. destruct q.
      * firstorder.
      * destruct p as [ evp tsp ].
        split.
        -- eapply Nat.le_trans; apply H.
        -- apply H.
      * simpl. right. assumption.
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

Lemma insert_ts_length :
  forall e q, length (insert_ts e q) = S (length q).
Proof.
  intros [ev' ts'] q; induction q as [|[ev ts] q IH]; simpl; auto.
  destruct (Nat.leb ts' ts); simpl; lia.
Qed.

Lemma enq_event_ord_length :
  forall cfg e,
    length (get_eq (snd (enq_event_ord e cfg))) =
    S (length (get_eq cfg)).
Proof.
  intros. 
  destruct cfg as [h [tr q]].
  unfold enq_event_ord. 
  unfold get_eq.
  simpl. 
  apply insert_ts_length.
Qed.

Lemma insert_ts_in :
  forall e q, In e (insert_ts e q).
Proof.
  intros e q; induction q as [|x q IH]; simpl in *.
  - destruct e as [ev ts]. 
    simpl. firstorder.
  - unfold get_ts. destruct e as [ev ts']; destruct x as [ev' ts].
    destruct (ts' <=? ts) eqn:Hle; simpl.
    firstorder.
    firstorder.
Qed.

Lemma insert_ts_sorted_list :
  forall e q,
    sorted_ts q ->
    sorted_ts (insert_ts e q).
Proof.
  intros [ev' ts'] q Hs.
  induction q; simpl in *.
  - trivial.
  - unfold get_ts. destruct a as [ev ts].
    destruct (Nat.leb ts' ts) eqn:Hcmp.
    + apply Nat.leb_le in Hcmp. firstorder.
    + apply Nat.leb_gt in Hcmp. firstorder.
      destruct q as [| (ev2,t2) q'] eqn:Eq; simpl in *.
      lia. subst.
      destruct ( ts' <=? t2) eqn: Hcmp2.
      apply Nat.leb_le in Hcmp2. firstorder. lia.
      firstorder.
Qed.


Lemma insert_ts_sorted :
  forall cfg e,
    sorted_ts (get_eq cfg) ->
    sorted_ts (insert_ts e (get_eq cfg)).
Proof.
  unfold get_eq in *.
  intros.
  destruct cfg as [h [tr q]] eqn:Hcfg.
  simpl in *.
  apply insert_ts_sorted_list.
  apply H.
Qed.

Lemma insert_ts_elements :
  forall e q q',
    insert_ts e q = q' -> (forall x, In x q' -> x = e \/ In x q).
Proof.
  intros. generalize dependent q'.
  induction q; intros.
  - left.
    simpl in H.
    subst.
    simpl in H0.
    destruct H0.
    + rewrite H.
      reflexivity.
    + contradiction.
  - simpl in H.
    remember (get_ts e <=? get_ts a) as cmp.
    destruct cmp.
    + subst.
      apply in_inv in H0.
      destruct H0.
      * left.
        rewrite H.
        reflexivity.
      * right.
        apply H.
    + subst.
      apply in_inv in H0.
      destruct H0.
      * right.
        subst.
        apply in_eq.
      * apply IHq in H.
        2: reflexivity.
        destruct H.
        -- left.
           apply H.
        -- right.
           apply in_cons.
           apply H.
Qed.
           
Lemma enq_event_ord_sorted :
  forall cfg e,
    sorted_ts (get_eq cfg) ->
    sorted_ts (get_eq (snd (enq_event_ord e cfg))).
Proof.
  intros.
  unfold get_eq in *.
  unfold enq_event_ord.
  destruct cfg as [h [tr q]] eqn:Hcfg.
  simpl in *.
  apply insert_ts_sorted_list.
  apply H.
Qed.

(* demo program: record four events then commit them *)
Definition demo : State unit :=
  enq_event_ord ((1, SYNC),    1) ;;
  enq_event_ord ((2, MMIO_READ_REQ), 10) ;;
  enq_event_ord ((3, MMIO_READ_RESP),20) ;;
  enq_event_ord ((4, SYNC),    3) ;;
  ret tt.

Definition empty_cfg : Config := mkConfig heap_empty [] [].

Compute (let '(_, cfg') := demo empty_cfg in (get_heap cfg', get_eq cfg')).

(* enqueue keeps queue sorted *)
Lemma demo_sorted :
  let '(_, cfg') := demo empty_cfg in
  sorted_ts (get_eq cfg').
Proof.
  unfold demo, empty_cfg; simpl.
  repeat (rewrite <- insert_ts); repeat constructor; lia.
Qed.
