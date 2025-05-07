(*** SuperTrace : unordered events with (id, deps, duration) ***************)
From Coq Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.

Require Import CoreDSL Events.
Open Scope nat_scope.
Open Scope monad_scope.

(*------------------------------------------------------------------*)
(** 1 .  Event payload ************************************************)

Record SuperEvent := {
  se_id   : nat;          (* unique identifier                  *)
  se_kind : Event;        (* we still keep the semantic tag     *)
  se_deps : list nat;     (* ids that must be done before start *)
  se_dur  : nat           (* time once deps are satisfied       *)
}.

(*------------------------------------------------------------------*)
(** 2 .  Instantiate the generic DSL ********************************)

Module SuperInst <: DSL_SIG.
  Definition V  := nat.
  Definition TE := SuperEvent.
End SuperInst.

Module SDsl := MakeDSL(SuperInst).
Import SDsl.

(* Throughout this file  Trace = list SuperEvent (from MakeDSL). *)

(* projections *)
Definition sp_id  (e:SuperEvent) := se_id  e.
Definition sp_evt (e:SuperEvent) := se_kind e.
Definition sp_dur (e:SuperEvent) := se_dur  e.

(*------------------------------------------------------------------*)
(** 3 .  Merging two traces (unordered) *****************************)

(* If an id appears in both, keep the left copy. *)
Fixpoint find_se (id:nat)(tr:Trace) : bool :=
  match tr with
  | [] => false
  | e::tl => if Nat.eqb id (se_id e) then true else find_se id tl
  end.

Fixpoint merge_trace (t1 t2:Trace) : Trace :=
  match t1 with
  | [] => t2
  | e::tl =>
      if find_se (se_id e) t2
      then merge_trace tl t2
      else e :: merge_trace tl t2
  end.

Lemma merge_preserves_left :
  forall t1 t2 e, In e t1 -> In e (merge_trace t1 t2).
Proof.
  induction t1 as [|x tl IH]; intros t2 e Hin; simpl in *; auto.
  destruct Hin as [Heq|Hin]; subst.
  - destruct (find_se (se_id x) t2); simpl; auto.
  - destruct (find_se (se_id x) t2); simpl; auto.
Qed.

(*------------------------------------------------------------------*)
(** 4 .  Dependency-resolution predicate ****************************)

Definition deps_resolved (tr:Trace) : Prop :=
  forall e d, In e tr -> In d (se_deps e) ->
              exists f, In f tr /\ se_id f = d.

Lemma merge_no_dangling :
  forall t1 t2,
    deps_resolved t1 -> deps_resolved t2 ->
    deps_resolved (merge_trace t1 t2).
Proof.
  unfold deps_resolved.
  intros t1 t2 H1 H2 e d Hin Hdep.
  induction t1 as [|x tl IH]; simpl in Hin.
  - (* came from right trace *)
    apply H2 with (e:=e); auto.
  - destruct (find_se (se_id x) t2) eqn:Hex.
    + (* x hidden by right trace *)
      apply IH; auto; destruct Hin; subst; auto.
    + (* x kept *)
      destruct Hin as [Heq|Hin]; subst.
      * apply H1 with (e:=x); auto; left; reflexivity.
      * apply IH; auto.
Qed.

(*------------------------------------------------------------------*)
(** 5 .  Example ****************************************************)

Definition s1 : SuperEvent := {| se_id:=1; se_kind:=SYNC; se_deps:=[];     se_dur:=1|}.
Definition s2 : SuperEvent := {| se_id:=2; se_kind:=MMIO_READ_REQ; se_deps:=[1]; se_dur:=2|}.
Definition s3 : SuperEvent := {| se_id:=3; se_kind:=DMA_READ_REQ;  se_deps:=[1;2]; se_dur:=3|}.

Definition trace_A : Trace := [s1;s2].
Definition trace_B : Trace := [s3].

Compute merge_trace trace_A trace_B.

Example merge_ok :
  deps_resolved trace_A ->
  deps_resolved trace_B ->
  deps_resolved (merge_trace trace_A trace_B).
Proof. intros; eapply merge_no_dangling; eauto. Qed.
