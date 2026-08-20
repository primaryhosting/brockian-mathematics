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

