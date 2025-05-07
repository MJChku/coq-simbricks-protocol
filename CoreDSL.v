(*** CoreDSL : a parametric heap/trace/event-queue DSL *********************)
From Coq Require Import Init.Nat Lists.List Arith.PeanoNat.
From ExtLib.Structures Require Import Monads.
Export MonadNotation.
Open Scope monad_scope.
Import ListNotations.

Module Type DSL_SIG.
  Parameter V  : Type.      (* heap payloads                  *)
  Parameter TE : Type.      (* trace / event-queue entry      *)
End DSL_SIG.

Module MakeDSL (M : DSL_SIG).
  Import M.

  (*------------------------------------------------------------------*)
  (** 1. Data *********************************************************)
  Definition Heap   := list (nat * V).
  Definition Trace  := list TE.
  Definition EQ     := list TE.               (* event queue            *)
  Definition Config := (Heap * (Trace * EQ))%type.

  Definition get_heap  (c:Config) : Heap := fst c.
  Definition get_trace (c:Config) : Trace := fst (snd c).
  Definition get_eq    (c:Config) : EQ :=   snd (snd c).
  Definition mkConfig h tr q : Config := (h,(tr,q)).

  Definition State (A : Type) : Type := Config -> (A * Config).

  Definition ret {A} (a : A) : State A := fun cfg => (a, cfg).

  Definition bind {A B} (m : State A) (k : A -> State B) : State B :=
    fun cfg => let (a, cfg') := m cfg in k a cfg'.

  #[global] Instance Monad_State : Monad State := {
    ret  := @ret;
    bind := @bind
  }.

  (* --- 2.3  Heap operations ------------------------ *)
  Definition heap_empty : Heap := [].

  Definition removeb (p : nat) (h : Heap) : Heap :=
    filter (fun pq => negb (Nat.eqb p (fst pq))) h.

  Fixpoint heap_lookup (p : nat) (h : Heap) : option V :=
    match h with
    | [] => None
    | (q,v) :: t => if Nat.eqb p q then Some v else heap_lookup p t
    end.

  Definition heap_update (h : Heap) (p : nat) (ov : option V) : Heap :=
    let h' := removeb p h in
    match ov with
    | None   => h'
    | Some v => (p,v) :: h'
    end.

  Definition max_ptr (h : Heap) : nat :=
    fold_left (fun m '(p,_) => Nat.max m p) h 0.

  (* --- 2.4  Primitive actions ---------------------- *)
  Definition new (init : V) : State nat :=
    fun '(h,(tr,q)) =>
      let p := S (max_ptr h) in
      let h' := heap_update h p (Some init) in
      (p, mkConfig h' tr q).

  Definition read (p : nat) : State (option V) :=
    fun '(h,(tr,q)) =>
      (heap_lookup p h, mkConfig h tr q).

  Definition write (p : nat) (v : V) : State unit :=
    fun '(h,(tr,q)) =>
      let h' := heap_update h p (Some v) in
      (tt, mkConfig h' tr q).

  Definition delete (p : nat) : State unit :=
    fun '(h,(tr,q)) =>
      let h' := heap_update h p None in
      (tt, mkConfig h' tr q).

  Definition enq_log (e : TE) : State unit :=
    fun '(h,(tr,q)) =>
      (tt, mkConfig h (tr ++ [e]) q).

  Definition enq_event (e : TE) : State unit :=
    fun '(h,(tr,q)) =>
      (tt, mkConfig h tr (q ++ [e])).

  Definition pass : State unit := fun cfg => (tt, cfg).

  Definition option_default {A} (d : A) (o : option A) : A :=
  match o with
  | Some x => x
  | None  => d
  end.

End MakeDSL.
