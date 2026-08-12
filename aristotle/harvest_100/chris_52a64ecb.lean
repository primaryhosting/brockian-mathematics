/-!
# Bail On Unrecognized Is Sound
Category: Proof-Carrying Apps
Target: PCA.Coverage.bail_on_unrecognized_is_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The model

An *isolation engine* processes a stream of events.  Each event is either
*recognized* (it lies inside the engine's verified coverage fragment) or not.
Recognized events are handled by the engine's `step` function; unrecognized
events cause the engine to *bail* into a designated safe fallback (`bail`).

The soundness statement we prove is the central design justification for this
architecture: to know that a safety invariant `Inv` holds along **every**
execution, it suffices to verify `step` on the **recognized** fragment only,
together with the (single, event-independent) fact that bailing is safe.

The development is self-contained: it needs nothing beyond Lean 4 core, so the
file has no imports.  (Mathlib's `List.foldl` API — e.g. `List.foldl_cons` —
would let one phrase `PCA.Coverage.Engine.run` as a `List.foldl`; the induction
below is the same one that `List.foldl` recursion performs, so no external
lemma is required.)
-/

namespace PCA
namespace Coverage

universe u v

/-- An isolation engine over a state space `S` and an event alphabet `E`.

* `recognized e` says that event `e` is inside the engine's verified
  coverage fragment;
* `step s e` is the handler used on recognized events;
* `bail s` is the safe fallback taken on unrecognized events. -/
structure Engine (S : Type u) (E : Type v) where
  /-- Coverage test: is this event inside the verified fragment? -/
  recognized : E → Bool
  /-- Handler for recognized events. -/
  step : S → E → S
  /-- Fallback taken on an unrecognized event. -/
  bail : S → S

variable {S : Type u} {E : Type v}

/-- One step of the engine: dispatch on recognition, bailing when the event is
outside the verified coverage fragment. -/
def Engine.handle (M : Engine S E) (s : S) (e : E) : S :=
  if M.recognized e then M.step s e else M.bail s

/-- Run the engine on a whole trace of events. -/
def Engine.run (M : Engine S E) (s : S) : List E → S
  | [] => s
  | e :: tr => M.run (M.handle s e) tr

@[simp] theorem Engine.run_nil (M : Engine S E) (s : S) : M.run s [] = s := rfl

@[simp] theorem Engine.run_cons (M : Engine S E) (s : S) (e : E) (tr : List E) :
    M.run s (e :: tr) = M.run (M.handle s e) tr := rfl

/-- On a recognized event the engine behaves exactly like its handler. -/
@[simp] theorem Engine.handle_of_recognized (M : Engine S E) (s : S) {e : E}
    (he : M.recognized e = true) : M.handle s e = M.step s e := by
  simp [Engine.handle, he]

/-- On an unrecognized event the engine bails, *ignoring the event entirely*:
no unverified data can influence the resulting state. -/
@[simp] theorem Engine.handle_of_unrecognized (M : Engine S E) (s : S) {e : E}
    (he : M.recognized e = false) : M.handle s e = M.bail s := by
  simp [Engine.handle, he]

/-- Single-step soundness: if the invariant is preserved by `step` on the
recognized fragment and by `bail`, then it is preserved by `handle` on *all*
events. -/
theorem handle_preserves_inv (M : Engine S E) (Inv : S → Prop)
    (hstep : ∀ s e, Inv s → M.recognized e = true → Inv (M.step s e))
    (hbail : ∀ s, Inv s → Inv (M.bail s))
    (s : S) (e : E) (hs : Inv s) : Inv (M.handle s e) := by
  unfold Engine.handle
  cases he : M.recognized e with
  | false => simpa using hbail s hs
  | true => simpa using hstep s e hs he

/-- **Bailing on unrecognized input is sound.**

If a safety invariant `Inv` is preserved by the engine's handler on every
*recognized* event, and is preserved by the bail action, then `Inv` holds after
running the engine on an **arbitrary** trace — including traces containing
events the engine was never verified against.

Thus verification effort may be confined to the recognized coverage fragment:
everything outside it is discharged once and for all by the bail action. -/
theorem bail_on_unrecognized_is_sound (M : Engine S E) (Inv : S → Prop)
    (hstep : ∀ s e, Inv s → M.recognized e = true → Inv (M.step s e))
    (hbail : ∀ s, Inv s → Inv (M.bail s))
    (s : S) (hs : Inv s) (tr : List E) : Inv (M.run s tr) := by
  induction tr generalizing s with
  | nil => simpa using hs
  | cons e tr ih =>
      exact ih _ (handle_preserves_inv M Inv hstep hbail s e hs)

/-! ## Complements: the bail policy is not vacuous

Two sanity checks showing the theorem above is not obtained by crippling the
engine: on a fully recognized trace the engine is exactly the unguarded
handler, and any bail is provoked by a genuinely unrecognized event. -/

/-- Unguarded execution: always apply `step`, never bail. -/
def Engine.runRaw (M : Engine S E) (s : S) : List E → S
  | [] => s
  | e :: tr => M.runRaw (M.step s e) tr

/-- **Completeness on the covered fragment.**  If every event of the trace is
recognized, the guarded engine agrees with the unguarded handler: guarding
costs nothing inside the coverage fragment. -/
theorem run_eq_runRaw_of_all_recognized (M : Engine S E) (s : S) :
    ∀ (tr : List E), (∀ e ∈ tr, M.recognized e = true) → M.run s tr = M.runRaw s tr
  | [], _ => rfl
  | e :: tr, h => by
      have he : M.recognized e = true := h e (List.mem_cons_self ..)
      simp only [Engine.run_cons, M.handle_of_recognized s he]
      exact run_eq_runRaw_of_all_recognized M _ tr
        (fun a ha => h a (List.mem_cons_of_mem _ ha))

/-- If the engine's behaviour on a trace differs from the unguarded one, the
trace must contain an unrecognized event: the engine never bails spuriously. -/
theorem exists_unrecognized_of_run_ne (M : Engine S E) (s : S) (tr : List E)
    (h : M.run s tr ≠ M.runRaw s tr) : ∃ e ∈ tr, M.recognized e = false := by
  refine Classical.byContradiction (fun hc => h ?_)
  refine run_eq_runRaw_of_all_recognized M s tr (fun e he => ?_)
  cases hr : M.recognized e with
  | true => rfl
  | false => exact absurd ⟨e, he, hr⟩ hc

end Coverage
end PCA

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

