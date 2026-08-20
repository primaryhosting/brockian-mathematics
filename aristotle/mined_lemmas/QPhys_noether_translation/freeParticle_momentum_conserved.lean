/-
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- If a Lagrangian `L q v` is invariant under translations `q ↦ q + s` of the position
variable, then its partial derivative with respect to position vanishes. -/

theorem freeParticle_momentum_conserved (m q₀ u : ℝ) :
    ∀ t₁ t₂ : ℝ,
      (fun _ w : ℝ => m * w) (q₀ + u * t₁) ((fun _ : ℝ => u) t₁) =
        (fun _ w : ℝ => m * w) (q₀ + u * t₂) ((fun _ : ℝ => u) t₂) := by
  obtain ⟨h1, -, h3, -, h5⟩ := freeParticle_satisfies_noether_hypotheses m q₀ u
  exact noether_translation_momentum (fun _ y => m * y ^ 2 / 2) (fun _ _ => 0)
    (fun _ w => m * w) h1 h3 (fun t => q₀ + u * t) (fun _ => u) h5

end QPhys

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

