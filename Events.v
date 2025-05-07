From Coq Require Import Init.Nat.

Inductive Event :=
| MMIO_READ_REQ 
| MMIO_READ_RESP
| DMA_READ_REQ  
| DMA_READ_RESP
| SYNC.

Scheme Equality for Event.
Definition eqb_event := Event_beq.

(* -------- triple: (unique-id, event, timestamp) ------------------------- *)
Definition TimedEvent : Type := ((nat * Event) * nat)%type.

(* projections *)
Definition get_id  (te : TimedEvent) : nat :=
  let '((i, _), _) := te in i.

Definition get_evt (te : TimedEvent) : Event :=
  let '((_, e), _) := te in e.

Definition get_ts  (te : TimedEvent) : nat :=
  let '(_, t) := te in t.

Definition mkEvent (i : nat) (e : Event) (t : nat) : TimedEvent :=
  ((i, e), t).


