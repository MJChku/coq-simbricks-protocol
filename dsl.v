From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.
From Coq Require Import Arith.PeanoNat.
Require Import Arith.
From ExtLib.Structures Require Import Monads.
Export MonadNotation.
Open Scope monad_scope.
Import ListNotations.

(* --------------------------------------------------- *)
(** 1. Signature specifying the two type parameters *)
Module Type DSL_SIG.
  Parameter V  : Type.
  Parameter TE : Type.
End DSL_SIG.

(** 2. Functor that builds the DSL for any [V] and [TE] *)
Module MakeDSL (M : DSL_SIG).
  Import M.

  (* --- 2.1  Heap, Trace, Config -------------------- *)
  Definition Heap   : Type := list (nat * V).
  Definition Trace  : Type := list TE.
  Definition Config : Type := (Heap * Trace)%type.

  (* --- 2.2  State monad ---------------------------- *)
  Definition State (A : Type) : Type := Config -> (A * Config).

  Definition ret {A} (a : A) : State A := fun cfg => (a, cfg).
  Definition bind {A B} (m : State A) (k : A -> State B) : State B :=
    fun cfg => let (a, cfg') := m cfg in k a cfg'.

  (* Register State as an instance of the ext-lib Monad typeclass *)
  #[global] Instance Monad_State : Monad State :=
  { ret  := @ret
  ; bind := @bind }.

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
  Definition new : State nat :=
    fun '(h, tr) =>
      let p := S (max_ptr h) in
      (p, (h, tr)).

  Definition read (p : nat) : State (option V) :=
    fun '(h, tr) => (heap_lookup p h, (h, tr)).

  Definition write (p : nat) (v : V) : State unit :=
    fun '(h, tr) => (tt, (heap_update h p (Some v), tr)).

  Definition delete (p : nat) : State unit :=
    fun '(h, tr) => (tt, (heap_update h p None, tr)).

  Definition loge (e : TE) : State unit :=
    fun '(h, tr) => (tt, (h, tr ++ [e]) ).

  Definition pass : State unit :=
    fun '(h, tr) => (tt, (h, tr)).

End MakeDSL.

(* --------------------------------------------------- *)
(** 3. Provide a concrete module that satisfies [DSL_SIG] *)
Module NatInst <: DSL_SIG.
  Definition V  := nat.
  Definition TE := nat.
End NatInst.

(* 4. Instantiate the functor with this module *)
(* Module NatDSL := MakeDSL(NatInst). *)
(* Import NatDSL. *)


Inductive Event : Type :=
| MMIO_READ_REQ
| MMIO_READ_RESP
| DMA_READ_REQ
| DMA_READ_RESP
| SYNC.

Definition TimedEvent : Type := (Event * nat).


(* Provide an instance of the DSL that records these events *)
(* Provide an instance of the DSL that records **event × timestamp** pairs *)
Module EventInst <: DSL_SIG.
  Definition V  := nat.
  Definition TE := TimedEvent.   (* an event tagged with a timestamp *)
End EventInst.

Module EventDSL := MakeDSL(EventInst).
Import EventDSL.

Fixpoint insert_ts (e : TimedEvent) (tr : Trace) : Trace :=
  let '(_, ts') := e in
  match tr with
  | [] => [e]
  | (ev, ts) :: tr' as full =>
      if Nat.leb ts' ts
      then e :: full               (* place before first >= timestamp *)
      else (ev, ts) :: insert_ts e tr'
  end.

(* Override the plain [loge] with an ordered version *)
Definition loge_ord (e : TimedEvent) : State unit :=
  fun '(h, tr) => (tt, (h, insert_ts e tr)).

Definition demo : State unit :=
  ret tt.

Definition init_cfg : Config := (heap_empty, []). 

Compute demo init_cfg.

(* --------------------------------------------------- *)
(** 6. A looping program that consumes an external list and logs it *)
Fixpoint consume (ts : list TimedEvent) : State unit :=
  match ts with
  | [] => ret tt
  | t :: ts' =>
      loge t ;;            (* record t in our trace B *)
      consume ts'
  end.

(** 6. Trace-length property *)
Lemma consume_extends_trace :
  forall ts cfg res cfg',
    consume ts cfg = (res, cfg') ->
    length (snd cfg') = length (snd cfg) + length ts.
Proof.
Admitted.
  (* induction ts as [|t ts IH]; intros [h tr] res [h' tr'] Hrun.
  - (* ts = [] *) simpl in Hrun. inversion Hrun. firstorder.
  - (* ts = t :: ts *)
    simpl in Hrun. unfold loge in Hrun. unfold bind in Hrun.
    remember (consume ts (h, tr ++ [t])) as R eqn:E.
    destruct R as [res2 [h2 tr2]]. inversion Hrun; subst; clear Hrun.
    symmetry in E. 
    assert( (res2 , (h2 , tr2)) = (res, (h', tr'))).
    {
      replace (res, (h', tr')) with (consume ts (h, tr ++ [t])).
      symmetry in E. apply E.
    }
    inversion H.
    specialize (IH (h, tr ++ [t]) res2 (h2, tr2) E). simpl in IH.
    subst.
    rewrite app_length in IH. simpl in IH. simpl in *. rewrite IH. rewrite <- Nat.add_assoc. reflexivity.
Qed. *)

(** Process a single timed event ********************************************)
Definition process_event (t : TimedEvent) (my_ts delay : nat) : State unit :=
  match t with
  | (MMIO_READ_REQ , _) => loge_ord (MMIO_READ_RESP , my_ts + delay)
  | (DMA_READ_REQ , _)  => loge_ord (DMA_READ_RESP , my_ts + delay)
  | _                   => ret tt                        (* responses → no log *)
  end.

Require Import Program.Wf.
Require Import Lia.

Program Fixpoint send_sync_event
        (last_ts gap link_delay : nat)
        (should_loge : bool)
        { measure (gap) } : State nat :=
  match link_delay with
  | 0 => ret last_ts
  | _ =>
    match gap, should_loge with 
    | 0, false => ret (last_ts - link_delay)
    | 0, true => loge_ord (SYNC, last_ts) ;; ret last_ts
    | _, true => loge_ord (SYNC, last_ts) ;;
              send_sync_event (last_ts + link_delay) (gap-link_delay) link_delay (Nat.leb link_delay gap)
    | _, false => send_sync_event (last_ts + link_delay) (gap-link_delay) link_delay (Nat.leb link_delay gap) 
    end
  end.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed. 

(** Recursive consumer ******************************************************)
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
          cur_last_sync_opt <- read ptr_last_sync ;;
          let cur_last_sync := match cur_last_sync_opt with Some n => n | None => 0 end in
          let cur := match cur_opt with Some n => n | None => 0 end in
          let cur' := if Nat.ltb cur ts_now then ts_now else cur in
          write ptr cur' ;;
          loged_ts <- send_sync_event cur_last_sync (cur' - cur_last_sync) link_delay false ;;
          let next_sync_ts := if Nat.leb loged_ts cur_last_sync then cur_last_sync else loged_ts in 
          write ptr_last_sync next_sync_ts ;; 
          process_event (ev, ts_now) cur dly ;;
          consume_loop ts' ptr ptr_last_sync dly link_delay
  end.

Definition consume_events
        (ts       : list TimedEvent)
        (start_ts : nat)
        (delay    : nat)
        (link_delay    : nat)
        : State unit :=
  p <- new ;;
  p2 <- new ;;
  _ <- write p start_ts ;;
  _ <- write p2 start_ts ;;
  consume_loop ts p p2 delay link_delay.

Open Scope nat_scope.

(*--------------------------------------------------------------------*)
(** A trace is “link-bounded” if successive timestamps differ ≤ k ****)
Definition gap_ok (k : nat) (t1 t2 : TimedEvent) : Prop :=
  let '(_, ts1) := t1 in
  let '(_, ts2) := t2 in
  ts2 - ts1 <= k.

Fixpoint bounded_trace         
         (tr : list TimedEvent)
         (k  : nat) : Prop :=
  match tr with
  | [] | [_] => True
  | t1 :: (t2 :: rest as tail) =>  
        gap_ok k t1 t2
      /\ bounded_trace tail k  
  end.
