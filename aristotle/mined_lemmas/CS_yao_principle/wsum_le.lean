import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
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

namespace CS

open Set

variable {A I : Type*} [Fintype A] [Fintype I]

/-- The expected cost of the randomized algorithm given by the distribution `p` over the
deterministic algorithms `A`, run on the input `i`. -/

lemma wsum_le (hw : w ∈ stdSimplex ℝ X) {M : ℝ} (hM : ∀ x, f x ≤ M) :
    ∑ x, w x * f x ≤ M := by
  have h1 : ∑ x, w x * f x ≤ ∑ x, w x * M :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hM x) (hw.1 x)
  have h2 : ∑ x, w x * M = M := by rw [← Finset.sum_mul, hw.2, one_mul]
  linarith

end Weighted

section Basic

variable {c : A → I → ℝ}

omit [Fintype I] in
