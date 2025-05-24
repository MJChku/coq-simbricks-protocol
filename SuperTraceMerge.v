From Coq Require Import Lists.List Arith.PeanoNat Lia Program.Wf.
Import ListNotations.
Open Scope nat_scope.

Require Import STR.Trace STR.SuperTrace.

Import Events Trace.

Definition is_req (e : Event) : bool :=
  match e with
  | MMIO_READ_REQ | DMA_READ_REQ => true
  | _                            => false
  end.

Definition is_resp (e : Event) : bool :=
  match e with
  | MMIO_READ_RESP | DMA_READ_RESP => true
  | _                              => false
  end.

 (* for id lookup *)
Fixpoint in_nat (n : nat) (l : list nat) : bool :=
  match l with
  | []      => false
  | x :: xs => if Nat.eqb n x then true else in_nat n xs
  end.

Fixpoint lookup_nat (k : nat) (m : list (nat * nat)) : option nat :=
  match m with
  | []            => None
  | (k',v) :: tl  => if Nat.eqb k k' then Some v else lookup_nat k tl
  end.

Fixpoint collect_req_ts (tes : list TimedEvent) : list (nat * nat) :=
  match tes with
  | [] => []
  | ((id, ev), ts) :: tl =>
      let tail := collect_req_ts tl in
      if is_req ev then (id, ts) :: tail else tail
  end.

Fixpoint gather_req_ids (tes : list TimedEvent) : list nat :=
  match tes with
  | [] => []
  | ((id, ev), _) :: tl =>
      let tail := gather_req_ids tl in
      if is_req ev
      then 
        if in_nat id tail then tail else id :: tail
      else tail
  end.

Record ProtoEvent := {
  proto_old_id : nat;      (* old id in the TimedEvent *)
  proto_is_req : bool;     (* true for request and false for response        *)
  proto_dur    : nat       (* ts_req for req;  ts_resp -ts_req for resp              *)
}.

Fixpoint collect_proto (req_ts : list (nat * nat))
                       (tes    : list TimedEvent)
                       : list ProtoEvent :=
  match tes with
  | [] => []
  | ((id,ev),ts) :: tl =>
      let tail := collect_proto req_ts tl in
      if is_req ev then
        {| proto_old_id := id ; proto_is_req := true ;  proto_dur := ts |} :: tail
      else if is_resp ev then
        match lookup_nat id req_ts with
        | Some ts0 =>
            {| proto_old_id := id ; proto_is_req := false ;
               proto_dur := ts - ts0 |} :: tail
        | None => tail               (* unmatched response is dropped *)
        end
      else tail                     (* SYNC or anything else ignored *)
  end.

(* Allocate fresh se_id values for request only  *)
Fixpoint build_req_map (ids : list nat) (next : nat)
                       : list (nat * nat) :=
  match ids with
  | []       => []
  | id :: tl => (id,next) :: build_req_map tl (S next)
  end.


(* Allocate fresh se_id values for response only, request reuse id from reqmap *)
Fixpoint build_super_trace (ps     : list ProtoEvent)
                     (reqmap : list (nat * nat))
                     (state  : nat * STrace)   (* (next_id for response, acc) *)
                     : nat * STrace :=
  match ps with
  | [] => state
  | pe :: tl =>
      let '(next_id, acc) := state in
      let state' :=
        if proto_is_req pe then
          (* a request: id is already in reqmap *)
          match lookup_nat (proto_old_id pe) reqmap with
          | Some sid => (next_id,
                         (* empty dependencies, maybe also create dependencies for request? *)
                         (mkSuperEvent sid [] (proto_dur pe)) :: acc)
          | None => (next_id, acc)      (* impossible *)
          end
        else
          (* a response: depends on its request’s new id *)
          match lookup_nat (proto_old_id pe) reqmap with
          | Some req_sid =>
              let se := mkSuperEvent next_id [req_sid] (proto_dur pe) in
              (S next_id, se :: acc)
          | None => (next_id, acc)          (* drop *)
          end in
      build_super_trace tl reqmap state'
  end.

Definition merge_many_traces_into_strace (traces : list (list TimedEvent)) : STrace :=
  let all_te    := concat traces in
  let req_ids   := gather_req_ids all_te in
  let req_map   := build_req_map req_ids 0 in
  let req_ts    := collect_req_ts all_te in
  let protos    := collect_proto req_ts all_te in
  let '(_, strace) := build_super_trace protos req_map (length req_ids, []) in
  rev strace. (* build super trace reversed the list, but don't matter *)

Definition merge_traces (t1 t2 : list TimedEvent) : STrace :=
  merge_many_traces_into_strace [t1 ; t2].


Definition tA : list TimedEvent :=
  [ ((1 , MMIO_READ_REQ ), 10)
  ; ((1 , MMIO_READ_RESP), 27)  
  ].

Definition tB : list TimedEvent :=
  [ ((0 , DMA_READ_REQ ), 20)
  ; ((0 , DMA_READ_RESP), 47) 
  ].

Compute merge_traces tA tB.