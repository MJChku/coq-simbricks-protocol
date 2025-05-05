From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.
From Coq Require Import Arith.PeanoNat.
Require Import Arith.
From ExtLib.Structures Require Import Monads.
Export MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.
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

  (* --- 2.1  Heap, Trace, EventQueue, Config -------- *)
  Definition Heap       : Type := list (nat * V).
  Definition Trace      : Type := list TE.
  Definition EventQueue : Type := list TE.

  Definition Config : Type := Heap * (Trace * EventQueue)%type.

  Definition get_heap (c : Config) : Heap := fst c.
  Definition get_trace (c : Config) : Trace := fst (snd c).
  Definition get_queue (c : Config) : EventQueue := snd (snd c).

  Definition mkConfig (h : Heap) (tr : Trace) (q : EventQueue) : Config :=
    (h, (tr, q)).

  (* --- 2.2  State monad ---------------------------- *)
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


Fixpoint insert_ts (e : TimedEvent) (q : EventQueue) : EventQueue :=
  let '(_, ts') := e in
  match q with
  | [] => [e]
  | ((ev, ts) :: q') as full =>
      if Nat.leb ts' ts
      then e :: full               (* place before first >= timestamp *)
      else (ev, ts) :: insert_ts e q'
  end.

(* Override the plain [loge] with an ordered version *)
Definition enq_event_ord (e : TimedEvent) : State unit :=
  fun '(h, (tr, q)) => (tt, (h, (tr, insert_ts e q))).


Definition demo : State unit :=
  ret tt.

Definition init_cfg : Config := mkConfig heap_empty [] []. 

Compute demo init_cfg.

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
    rewrite app_length in IH. simpl in IH. simpl in *. rewrite IH. rewrite <- Nat.add_assoc. reflexivity.
Qed.

(** Process a single timed event ********************************************)
Definition process_event (t : TimedEvent) (my_ts delay : nat) : State unit :=
  match t with
  | (MMIO_READ_REQ , _) => enq_event_ord (MMIO_READ_RESP, my_ts + delay)
  | (DMA_READ_REQ , _)  => enq_event_ord (DMA_READ_RESP, my_ts + delay)
  | _                   => ret tt                  
  end.


Definition start_cfg : Config := mkConfig heap_empty [] [].

Definition test_event_queue : State unit :=
  enq_event_ord (MMIO_READ_RESP, 1) ;;
  enq_event_ord (MMIO_READ_RESP, 1) ;;
  enq_event_ord (MMIO_READ_RESP, 1) ;;
  enq_event_ord (MMIO_READ_RESP, 1) ;;
  ret tt.

Compute (let '(_, cfg') := test_event_queue start_cfg in
         (get_heap cfg', get_queue cfg', get_trace cfg')).

Require Import Program.Wf.
Require Import Lia.

Program Fixpoint send_sync_event
        (last_ts gap link_delay : nat)
        (should_enq_log : bool)
        { measure (gap) } : State nat :=
  match link_delay with
  | 0 => ret last_ts
  | _ =>
    match gap, should_enq_log with 
    | 0, false => ret (last_ts - link_delay)
    | 0, true => enq_event_ord (SYNC, last_ts) ;; ret last_ts
    | _, true => enq_event_ord (SYNC, last_ts) ;;
              send_sync_event (last_ts + link_delay) (gap-link_delay) link_delay (Nat.leb link_delay gap)
    | _, false => send_sync_event (last_ts + link_delay) (gap-link_delay) link_delay (Nat.leb link_delay gap) 
    end
  end.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed. 

Definition send_out_sync (ptr_last_sync my_ts link_delay : nat) : State unit :=
  cur_last_sync_opt <- read ptr_last_sync ;;
  let cur_last_sync := match cur_last_sync_opt with Some n => n | None => 0 end in
  loged_ts <- send_sync_event cur_last_sync (my_ts - cur_last_sync) link_delay false ;;
  let next_sync_ts := if Nat.leb loged_ts cur_last_sync then cur_last_sync else loged_ts in 
  write ptr_last_sync next_sync_ts ;; 
  ret tt.

Fixpoint commit_q (q : EventQueue) (my_ts : nat) (h : Heap) (tr : Trace) : (unit * Config) :=
  match q with
  | [] => (tt, (h, (tr, [])))
  | (ev, ts) :: qs =>
    if Nat.leb ts my_ts then
      let tr' := tr ++ [(ev, ts)] in
      commit_q qs my_ts h tr'
    else
      (tt, (h, (tr, (ev, ts) :: qs)))
  end.

Definition commit_events (my_ts : nat) : State unit :=
  fun '(h,(tr,q)) =>
    commit_q q my_ts h tr.

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
          let cur_ts := match cur_opt with Some n => n | None => 0 end in

          (* let cur_ts := if Nat.ltb cur_ts ts_now then ts_now else cur_ts in *)
          let cur_ts := ts_now in
          write ptr cur_ts ;;
          
          (* send periodic sync message*)
          send_out_sync ptr_last_sync cur_ts link_delay ;;

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
  consume_loop ts p p2 delay link_delay.

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
  | t1 :: ((t2 :: rest) as tail) =>  
        gap_ok k t1 t2
      /\ bounded_trace tail k  
  end.


Definition sample_events : list TimedEvent :=
  [ (MMIO_READ_REQ, 1);
    (MMIO_READ_REQ, 1);
    (MMIO_READ_REQ, 1);
    (MMIO_READ_REQ, 1);
    (DMA_READ_REQ , 3);
    (MMIO_READ_REQ, 7) 
    ].


(* Run consume_events with start_ts = 0, delay = 1, link_delay = 2 *)
Compute (let '(_, cfg') := consume_events sample_events 0 1 2 start_cfg in
         (get_heap cfg', get_queue cfg', get_trace cfg')).

(* Check boundedness with maximum gap k = 2 *)
Compute (let '(_, cfg') := consume_events sample_events 0 1 2 start_cfg in
         bounded_trace (get_trace cfg') 2).

Lemma consume_loop_bounded :
  forall ts ptr ptr_last_sync delay link_delay h tr p res h' tr' p',
    consume_loop ts ptr ptr_last_sync delay link_delay (h, (tr, p)) 
      = (res, (h', (tr', p'))) ->
    bounded_trace tr' link_delay.
Proof.
  intros.
Admitted.

Lemma consume_events_bounded_trace :
  forall ts start_ts delay link_delay cfg res cfg',
    consume_events ts start_ts delay link_delay cfg = (res, cfg') ->
    bounded_trace (snd cfg') link_delay.
Proof.
Admitted.
