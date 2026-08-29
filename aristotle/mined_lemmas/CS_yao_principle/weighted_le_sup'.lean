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

lemma weighted_le_sup' [Nonempty A] {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A) (g : A → ℝ) :
    ∑ a, p a * g a ≤ Finset.univ.sup' Finset.univ_nonempty g := by
  obtain ⟨hp0, hp1⟩ := hp
  calc ∑ a, p a * g a
      ≤ ∑ a, p a * Finset.univ.sup' Finset.univ_nonempty g :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (Finset.le_sup' g (Finset.mem_univ a)) (hp0 a)
    _ = Finset.univ.sup' Finset.univ_nonempty g := by rw [← Finset.sum_mul, hp1, one_mul]

/-- **Weak duality** (the easy half of Yao's principle): the distributional cost of any input
distribution is a lower bound for the randomized cost of any randomized algorithm. -/
