(*** SuperTrace : unordered events with (id, deps, duration) ***************)
From Coq Require Import Lists.List Arith.PeanoNat Lia.
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

Definition dep_edge (tr : STrace) (x y : SuperEvent) : Prop :=
  In x tr /\ In y tr /\ In (se_id y) (se_deps x).

Inductive SuperEventOrder (tr : STrace)
        : SuperEvent -> SuperEvent -> Prop :=
| SStep  : forall x y,
    dep_edge tr x y ->
    SuperEventOrder tr x y
| STrans : forall x y z,
    SuperEventOrder tr x y ->
    dep_edge tr y z ->
    SuperEventOrder tr x z.

Definition acyclic_strace (tr:STrace) : Prop :=
  forall e1 e2,
    SuperEventOrder tr e1 e2 ->
    ~ (SuperEventOrder tr e2 e1).
Compute acyclic_strace example_strace. 

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
