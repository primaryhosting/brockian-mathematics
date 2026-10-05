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

set_option grind.warning false

namespace CS

section Yao

variable {A I : Type*} [Fintype A] [Fintype I]

/-- The expected cost of the randomized algorithm given by the distribution `p` over
deterministic algorithms, run on the input `i`. -/

lemma inf'_le_weighted [Nonempty A] {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A) (g : A → ℝ) :
    Finset.univ.inf' Finset.univ_nonempty g ≤ ∑ a, p a * g a := by
  obtain ⟨hp0, hp1⟩ := hp
  calc Finset.univ.inf' Finset.univ_nonempty g
      = ∑ a, p a * Finset.univ.inf' Finset.univ_nonempty g := by
        rw [← Finset.sum_mul, hp1, one_mul]
    _ ≤ ∑ a, p a * g a :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (Finset.inf'_le g (Finset.mem_univ a)) (hp0 a)

/-- A convex combination is at most the maximum. -/
