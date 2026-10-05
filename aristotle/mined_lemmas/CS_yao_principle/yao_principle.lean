/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to come before any module docstring, so the required header appears
-- at the top of the file as a plain comment and again here as the module docstring.)

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

variable {A I : Type*} [Fintype A] [Fintype I] [Nonempty A] [Nonempty I]

/-- The worst-case expected cost of the randomized algorithm given by the distribution `p`
over deterministic algorithms:  `max over inputs i of  E_{a ~ p} [c a i]`. -/

theorem yao_principle (c : A → I → ℝ) :
    sInf (randCost c '' stdSimplex ℝ A) = sSup (distCost c '' stdSimplex ℝ I) := by
  classical
  obtain ⟨m, M, hmM⟩ := exists_bounds c
  have hAne : (stdSimplex ℝ A).Nonempty := stdSimplex_nonempty
  have hIne : (stdSimplex ℝ I).Nonempty := stdSimplex_nonempty
  have hRne : (randCost c '' stdSimplex ℝ A).Nonempty := hAne.image _
  have hDne : (distCost c '' stdSimplex ℝ I).Nonempty := hIne.image _
  -- bounds
  have hRbdd : BddBelow (randCost c '' stdSimplex ℝ A) := by
    refine ⟨m, ?_⟩
    rintro x ⟨p, hp, rfl⟩
    obtain ⟨i₀⟩ := ‹Nonempty I›
    have h1 : ∑ a, p a * m ≤ ∑ a, p a * c a i₀ :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hmM a i₀).1 (hp.1 a)
    have h2 : ∑ a, p a * m = m := by rw [← Finset.sum_mul, hp.2, one_mul]
    calc m = ∑ a, p a * m := h2.symm
      _ ≤ ∑ a, p a * c a i₀ := h1
      _ ≤ randCost c p := le_randCost c p i₀
  have hDbdd : BddAbove (distCost c '' stdSimplex ℝ I) := by
    refine ⟨M, ?_⟩
    rintro x ⟨q, hq, rfl⟩
    obtain ⟨a₀⟩ := ‹Nonempty A›
    have h1 : ∑ i, q i * c a₀ i ≤ ∑ i, q i * M :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hmM a₀ i).2 (hq.1 i)
    have h2 : ∑ i, q i * M = M := by rw [← Finset.sum_mul, hq.2, one_mul]
    calc distCost c q ≤ ∑ i, q i * c a₀ i := distCost_le c q a₀
      _ ≤ ∑ i, q i * M := h1
      _ = M := h2
  refine le_antisymm ?_ ?_
  · -- hard direction: `sInf ≤ sSup`
    set V : ℝ := sSup (distCost c '' stdSimplex ℝ I) with hV
    have hv : ∀ q ∈ stdSimplex ℝ I, ∃ a, ∑ i, q i * c a i ≤ V := by
      intro q hq
      obtain ⟨a, ha⟩ := exists_distCost_eq c q
      refine ⟨a, ?_⟩
      rw [ha]
      exact le_csSup hDbdd ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hple⟩ := exists_randomized_of_forall_dist c V hv
    calc sInf (randCost c '' stdSimplex ℝ A) ≤ randCost c p := csInf_le hRbdd ⟨p, hp, rfl⟩
      _ ≤ V := randCost_le hple
  · -- easy direction: `sSup ≤ sInf`
    refine csSup_le hDne ?_
    rintro x ⟨q, hq, rfl⟩
    refine le_csInf hRne ?_
    rintro y ⟨p, hp, rfl⟩
    exact distCost_le_randCost hp hq

end CS

