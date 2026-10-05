/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₈`, indexed by `ZMod 8`
(vertex `i` is adjacent to `i + 1` and `i - 1`), with complex entries. -/

theorem huckel_C8 (μ : ℂ) :
    (∃ v : ZMod 8 → ℂ, v ≠ 0 ∧ C8adj.mulVec v = μ • v) ↔
      ∃ k : ℕ, k < 8 ∧ μ = ((2 * Real.cos (2 * Real.pi * (k : ℝ) / 8) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    have hroot := huckel_C8_root μ v hv0 hv
    have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      norm_cast
      exact Real.sq_sqrt (by norm_num)
    rcases mul_eq_zero.mp hroot with h | h4
    · rcases mul_eq_zero.mp h with h0 | h2
      · -- μ = 0, k = 2
        refine ⟨2, by norm_num, ?_⟩
        rw [h0]
        have : (2 * Real.pi * ((2 : ℕ) : ℝ) / 8 : ℝ) = Real.pi / 2 := by push_cast; ring
        rw [this, Real.cos_pi_div_two]
        norm_num
      · -- μ² = 2
        have : (μ - ((Real.sqrt 2 : ℝ) : ℂ)) * (μ + ((Real.sqrt 2 : ℝ) : ℂ)) = 0 := by
          linear_combination h2 - hs2
        rcases mul_eq_zero.mp this with hp | hm
        · refine ⟨1, by norm_num, ?_⟩
          have hμ : μ = ((Real.sqrt 2 : ℝ) : ℂ) := by linear_combination hp
          rw [hμ]
          norm_cast
          have hpi : (2 * Real.pi * 1 / 8 : ℝ) = Real.pi / 4 := by ring
          rw [hpi, Real.cos_pi_div_four]
          ring
        · refine ⟨3, by norm_num, ?_⟩
          have hμ : μ = -((Real.sqrt 2 : ℝ) : ℂ) := by linear_combination hm
          rw [hμ]
          norm_cast
          have hpi : (2 * Real.pi * 3 / 8 : ℝ) = Real.pi - Real.pi / 4 := by ring
          rw [hpi, Real.cos_pi_sub, Real.cos_pi_div_four]
          ring
    · -- μ² = 4
      have : (μ - 2) * (μ + 2) = 0 := by linear_combination h4
      rcases mul_eq_zero.mp this with hp | hm
      · refine ⟨0, by norm_num, ?_⟩
        have hμ : μ = 2 := by linear_combination hp
        rw [hμ]
        norm_num
      · refine ⟨4, by norm_num, ?_⟩
        have hμ : μ = -2 := by linear_combination hm
        rw [hμ]
        have : (2 * Real.pi * ((4 : ℕ) : ℝ) / 8 : ℝ) = Real.pi := by push_cast; ring
        rw [this, Real.cos_pi]
        norm_num
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun j => om ((k : ZMod 8) * j), ?_, huckel_C8_eigenvector k hk⟩
    intro h
    have h0 := congrFun h 0
    simp [om_zero] at h0

end Chem

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

