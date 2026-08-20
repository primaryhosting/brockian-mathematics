/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.WriteIntegrity

/-- A write request submitted to the isolation engine: a claimed author, a
payload, and an integrity token that is supposed to certify the pair. -/
structure Write where
  author : Nat
  payload : Nat
  token : Nat
  deriving DecidableEq

/-- The integrity token that a genuine author would attach to a write. -/

theorem sound_iff_no_forge (check : Write → Bool) :
    Sound check ↔ ¬ ∃ w, Forges check w := by
  constructor
  · rintro hs ⟨w, hacc, hna⟩
    exact hna (hs w hacc)
  · intro h w hacc
    exact Classical.byContradiction fun hna => h ⟨w, hacc, hna⟩

end PCA.WriteIntegrity

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

