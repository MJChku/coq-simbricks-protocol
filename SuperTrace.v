(* SuperTrace : unordered events with (id, deps, duration) *)
From Coq Require Import Lists.List Arith.PeanoNat Lia.
From Coq Require Import Wellfounded Relation_Definitions Relation_Operators.
Import ListNotations.
Open Scope nat_scope.
Require Import STR.Events STR.EventDSL. 


Record SuperEvent := {          
  se_id   : nat;
  se_deps : list nat;
  se_dur  : nat }.

Definition mkSuperEvent sid deps dur : SuperEvent :=
  {| se_id := sid; se_deps := deps; se_dur := dur |}.

Definition STrace := list SuperEvent.

Definition get_se_id   := se_id.
Definition get_se_deps := se_deps.
Definition get_se_dur  := se_dur.

Fixpoint find_se (sid:nat)(tr:STrace) : option SuperEvent :=
  match tr with
  | []       => None
  | e :: tl  => if Nat.eqb sid (se_id e) then Some e else find_se sid tl
  end.

Example example_strace : STrace :=
  [ mkSuperEvent 0 []       10
  ; mkSuperEvent 1 [0]      1
  ; mkSuperEvent 2 [0]      200
  ; mkSuperEvent 3 [1;2]    5
  ; mkSuperEvent 4 [3]      100
  ; mkSuperEvent 5 [4]      50
  ; mkSuperEvent 6 [5]      20
  ; mkSuperEvent 7 [6]      10 ].

Compute find_se 3 example_strace.  

Set Implicit Arguments.

Definition list_max (l : list nat) : nat :=
  fold_left Nat.max l 0.

Fixpoint finish_time_fuel
         (fuel : nat)
         (e    : SuperEvent)
         (tr   : STrace) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      match se_deps e with
      | [] => se_dur e  (* no dependencies, just return duration *)
      | deps  =>
        let dep_finish :=
          map (fun d =>
                match find_se d tr with
                | Some de => finish_time_fuel fuel' de tr
                | None => 0  (* impossible *)
                end)
              deps in
        let max_dep := list_max dep_finish in
        max_dep + se_dur e
      end
  end.

Definition finish_time (e : SuperEvent) (tr : STrace) : nat :=
  finish_time_fuel (length tr) e tr.

Definition strace_end_ts (tr : STrace) : nat :=
  list_max (map (fun e => finish_time e tr) tr).

Compute strace_end_ts example_strace.


Definition simple_strace (str : STrace) : Prop :=
  forall ev,
  In ev str ->
  get_se_dur ev = 1.


Lemma find_se_in :
  forall sid tr ev,
    find_se sid tr = Some ev ->
    In ev tr.
Proof.
  induction tr as [|h t IH]; simpl; intros ev Hfind.
  - discriminate.
  - destruct (Nat.eqb sid (se_id h)) eqn:Heq.
    + inversion Hfind; subst; auto.
    + right; apply IH; exact Hfind.
Qed.


Lemma find_se_some_id sid tr ev :
  find_se sid tr = Some ev -> se_id ev = sid.
Proof.
  intros.
  induction tr.
  - discriminate.
  - simpl in H. 
    destruct (Nat.eqb sid (se_id a)) eqn:Heq.
    apply Nat.eqb_eq in Heq.
    inversion H. rewrite Heq. 
    rewrite H1. reflexivity.      
    apply IHtr in H. auto. 
Qed.

Lemma in_length_strace :
  forall e (tr: list SuperEvent ),
    In e tr ->
    length tr > 0.
Proof.
  intros e tr Hin.
  induction tr as [|h t IH].
  - inversion Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst. simpl. lia.
    + apply IH in Hin'. simpl. lia.
Qed. 


Lemma fold_left_max_le :
  forall l acc n,
    acc <= n ->
    (forall x, In x l -> x <= n) ->
    fold_left Nat.max l acc <= n.
Proof.
  induction l as [|x xs IH]; intros acc n Hacc Hall.
  - exact Hacc.
  - simpl.
    assert (Hx : x <= n) by (apply Hall; left; reflexivity).
    assert (Hmx : Nat.max acc x <= n)
      by (apply Nat.max_case_strong; lia).
    apply IH; try assumption.
    intros y Hy; apply Hall; right; exact Hy.
Qed.


Lemma list_max_le :
  forall l n,
    (forall x, In x l -> x <= n) ->
    list_max l <= n.
Proof.
  intros l n H.
  unfold list_max.
  apply fold_left_max_le; auto; lia.
Qed.


Lemma finish_time_fuel_le :
  forall fuel tr e,
    fuel <= length tr ->
    In e tr ->
    simple_strace tr -> 
    finish_time_fuel fuel e tr <= fuel.
Proof.
  induction fuel as [|fuel IH]; intros tr e Hfuel Hin Hsimp.
  - simpl. lia.
  - simpl.
    destruct (se_deps e) as [|d deps] eqn:Hdeps.
    + unfold simple_strace in Hsimp.
      specialize (Hsimp _ Hin).  
      unfold get_se_dur in Hsimp.
      rewrite Hsimp. lia.
    + set (dep_finish :=
             map (fun d0 =>
                    match find_se d0 tr with
                    | Some de => finish_time_fuel fuel de tr
                    | None    => 0
                    end)
                 (d :: deps)).
      assert (Hbound :
                forall x, In x dep_finish -> x <= fuel).
      { unfold dep_finish.
        intros x Hinx.
        apply in_map_iff in Hinx.
        destruct Hinx as [x0 [Hx Hd0in]]. subst x.
        destruct (find_se x0 tr) eqn:Hfind.
        - apply find_se_in in Hfind.
          apply IH; try assumption; lia.
        - lia.
      }

      unfold simple_strace in Hsimp.
      specialize (Hsimp _ Hin).
      unfold get_se_dur in Hsimp.
      rewrite Hsimp.
      replace (S fuel) with (fuel + 1) by lia.
      apply Nat.add_le_mono_r.
      apply list_max_le with (n := fuel). 
      exact Hbound.
Qed.


Lemma strace_ts_is_bounded :
  forall str,
    simple_strace str -> 
    strace_end_ts str <= length str.
Proof.
  intros str Hsimp. 
  unfold strace_end_ts.
  apply list_max_le with (n := length str).
  intros ts Hin_map.
  apply in_map_iff in Hin_map.
  destruct Hin_map as [ev [Heq Hin_str]].
  subst ts.
  apply finish_time_fuel_le
        with (fuel := length str)
             (tr   := str)
             (e    := ev); auto; lia.
Qed.


Definition dep_edge (tr : STrace) (x y : SuperEvent) : Prop :=
  In x tr /\ In y tr /\ In (se_id y) (se_deps x).

(* note SuperEventOrder is not transitive *)
Inductive SuperEventOrder (tr : STrace)
        : SuperEvent -> SuperEvent -> Prop :=
| SStep  : forall x y,
    dep_edge tr x y ->
    SuperEventOrder tr x y
| STrans : forall x y z,
    SuperEventOrder tr x y ->
    dep_edge tr y z ->
    SuperEventOrder tr x z.

Definition old_acyclic_strace (tr:STrace) : Prop :=
  forall e1 e2,
    SuperEventOrder tr e1 e2 ->
    ~ (SuperEventOrder tr e2 e1).
Compute old_acyclic_strace example_strace. 

Lemma SStep_dep :
  forall tr x y,
    SuperEventOrder tr x y ->
    exists z, dep_edge tr z y.
Proof.
  intros tr x y Hxy.
  induction Hxy.
  - eauto.
  - eauto.
Qed.


Fixpoint rank_fixpoint
         (fuel : nat)
         (e    : SuperEvent)
         (tr   : STrace) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      match se_deps e with
      | [] => 1
      | deps  =>
        let dep_finish :=
          map (fun d =>
                match find_se d tr with
                | Some de => rank_fixpoint fuel' de tr
                | None => 0  (* impossible *)
                end)
              deps in
        let max_dep := list_max dep_finish in
        S max_dep
      end
  end.

(* acyclic using wellfound *)
(* confirm wellfound doesn't allow reflexivity *)
Lemma wf_irreflexive :
  forall {A} (R : A -> A -> Prop),
    well_founded R ->
    forall x, not (R x x).
Proof.
  intros A R WF x Rx.
  pose proof (WF x) as Accx.
  induction Accx as [x Hpred IH].
  specialize (Hpred x Rx). 
  specialize IH with x.
  auto.
Qed.


Lemma wf_asymmetry :
  forall {A} (R : A -> A -> Prop),
    well_founded R ->
    forall x y, 
    R x y -> 
    ~ (R y x).
Proof.
  intros A R WF.
  apply (well_founded_ind WF
            (fun x => forall y, R x y -> ~ R y x)).
  intros x IH y Rxy Ryx.
  firstorder.
Qed.

(* 
https://rocq-prover.org/doc/v8.9/stdlib/Coq.Relations.Relation_Operators.html
Inductive clos_trans (x: A) : A -> Prop :=
    | t_step (y:A) : R x y -> clos_trans x y
    | t_trans (y z:A) : clos_trans x y -> clos_trans y z -> clos_trans x z.
*)

Lemma wf_no_positive_cycle
      {A} (R : A -> A -> Prop) :
  well_founded R ->
  forall x, ~ (clos_trans A R x x).
Proof.
   intros WF.
   apply wf_irreflexive.
   apply wf_clos_trans.
   apply WF.
Qed.


Definition dep_rel (tr : STrace) : relation SuperEvent :=
  fun x y => In x tr /\ In y tr /\ In (se_id x) (se_deps y).

Definition acyclic_strace (tr : STrace) : Prop :=
  well_founded (dep_rel tr).

Section Chain.

Variable tr : STrace.
Hypothesis Hwf : acyclic_strace tr.

Inductive chain_n : nat -> SuperEvent -> Prop :=
| chain0 : forall e,
    In e tr ->
    chain_n 0 e
| chainS : forall k x y,
    chain_n k x ->
    dep_rel tr x y ->
    chain_n (S k) y.

Lemma chain_n_inv :
    forall k e,
      chain_n (S k) e ->
      exists x, chain_n k x /\ dep_rel tr x e.
Proof.
  intros k e H.
  inversion H. subst.
  exists x. auto.  
Qed.

Lemma chain_n_exists_trivial:
  forall e,
    In e tr ->
    exists k, chain_n k e.
Proof.
  intros e Hin.
  exists 0. apply chain0. exact Hin.
Qed.


Lemma chain_n_exists:
  forall e e',
    dep_rel tr e e' -> 
    exists k, k > 0 /\ chain_n k e'.
Proof.
  intros e e' Hdep.
  remember Hdep as Hdep_original.
  clear HeqHdep_original.
  destruct Hdep as [Hin_e Hin_e' Hin_dep].
  apply chain_n_exists_trivial in Hin_e.
  destruct Hin_e as [k Hchain].
  exists (S k).
  split.
  - lia.
  - apply chainS with e; auto.  
Qed.


Lemma chain_n_bound :
  forall x k, 
  chain_n k x -> k < length tr.
Proof.
  intros x k.
  apply (well_founded_induction
           (A := SuperEvent)
           (R := dep_rel tr)
           Hwf
           (fun x =>
              chain_n k x -> k < length tr)).
  intros.
  induction H0.
  - apply in_length_strace in H0.
    lia.
  - specialize (H x0).
    apply H in H1. apply H1.
Admitted.

End Chain.
