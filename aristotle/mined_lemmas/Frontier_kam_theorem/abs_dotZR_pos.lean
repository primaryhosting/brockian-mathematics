import Mathlib
/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

variable {n : ℕ}

/-- The Euclidean pairing `⟨c, x⟩ = ∑ⱼ cⱼ xⱼ` on `Fin n → ℝ`. -/

lemma abs_dotZR_pos {ω : Fin n → ℝ} {γ τ : ℝ} (hγ : 0 < γ) (hω : Diophantine ω γ τ)
    {k : Fin n → ℤ} (hk : k ≠ 0) : 0 < |dotZR k ω| := by
  have hp : (0 : ℝ) < (l1Norm k) ^ τ := Real.rpow_pos_of_pos (l1Norm_pos hk) τ
  exact lt_of_lt_of_le (div_pos hγ hp) (hω k hk)

