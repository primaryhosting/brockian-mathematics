/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Real Matrix SimpleGraph

namespace Chem

/-- The Hückel level of the `k`-th molecular orbital of the cyclic `C₃` system,
in units of the resonance integral `β` (relative to `α`): `2 cos (2πk/3)`. -/
noncomputable def huckelLevelC3 (k : ℕ) : ℝ := 2 * Real.cos (2 * Real.pi * k / 3)

lemma huckelLevelC3_zero : huckelLevelC3 0 = 2 := by
  simp [huckelLevelC3]

lemma huckelLevelC3_one : huckelLevelC3 1 = -1 := by
  have h : (2 : ℝ) * Real.pi * (1 : ℕ) / 3 = Real.pi - Real.pi / 3 := by
    push_cast; ring
  rw [huckelLevelC3, h, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

lemma huckelLevelC3_two : huckelLevelC3 2 = -1 := by
  have h : (2 : ℝ) * Real.pi * (2 : ℕ) / 3 = 2 * Real.pi - (Real.pi - Real.pi / 3) := by
    push_cast; ring
  rw [huckelLevelC3, h, Real.cos_two_pi_sub, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

/-- The adjacency matrix of the cycle graph `C₃` is the all-ones matrix minus the identity. -/
lemma adjMatrix_cycleGraph_three (i j : Fin 3) :
    (SimpleGraph.cycleGraph 3).adjMatrix ℝ i j = if i = j then 0 else 1 := by
  rw [SimpleGraph.adjMatrix_apply]
  rcases eq_or_ne i j with h | h
  · simp [h]
  · have : (SimpleGraph.cycleGraph 3).Adj i j := by
      rw [SimpleGraph.cycleGraph_three_eq_top]
      exact h
    simp [this, h]

/-- The characteristic polynomial of the adjacency matrix of `C₃` is `X³ - 3X - 2`. -/
lemma charpoly_adjMatrix_cycleGraph_three :
    ((SimpleGraph.cycleGraph 3).adjMatrix ℝ).charpoly = X ^ 3 - 3 * X - 2 := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp only [charmatrix_apply, Matrix.diagonal_apply, adjMatrix_cycleGraph_three]
  norm_num [Fin.ext_iff]
  ring

lemma prod_huckelLevelC3 :
    ∏ k ∈ Finset.range 3, (X - C (huckelLevelC3 k)) = (X ^ 3 - 3 * X - 2 : ℝ[X]) := by
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero, huckelLevelC3_zero, huckelLevelC3_one, huckelLevelC3_two]
  simp only [map_neg, map_one, map_ofNat]
  ring

/-- The three Hückel levels of `C₃`, in raw form. -/
lemma two_cos_zero : 2 * Real.cos (2 * Real.pi * ((0 : ℕ) : ℝ) / 3) = 2 := huckelLevelC3_zero

lemma two_cos_one : 2 * Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) / 3) = -1 := huckelLevelC3_one

lemma two_cos_two : 2 * Real.cos (2 * Real.pi * ((2 : ℕ) : ℝ) / 3) = -1 := huckelLevelC3_two

/-- **Hückel theory for the cyclopropenyl system (C₃).**
The characteristic polynomial of the adjacency matrix of the cycle graph `C₃` factors as
`∏_{k=0}^{2} (X - 2 cos (2πk/3))`; consequently the spectrum (set of eigenvalues) of the
adjacency matrix is exactly the set of Hückel levels `2 cos (2πk/3)` for `k = 0, 1, 2`
(namely `2, -1, -1`). -/
theorem huckel_C3 :
    ((SimpleGraph.cycleGraph 3).adjMatrix ℝ).charpoly =
      ∏ k ∈ Finset.range 3, (X - C (2 * Real.cos (2 * Real.pi * (k : ℝ) / 3))) ∧
    spectrum ℝ ((SimpleGraph.cycleGraph 3).adjMatrix ℝ) =
      {x : ℝ | ∃ k : ℕ, k < 3 ∧ x = 2 * Real.cos (2 * Real.pi * (k : ℝ) / 3)} := by
  constructor
  · rw [charpoly_adjMatrix_cycleGraph_three, ← prod_huckelLevelC3]
    rfl
  · ext x
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_adjMatrix_cycleGraph_three]
    simp only [Set.mem_setOf_eq, IsRoot.def, eval_sub, eval_pow, eval_X, eval_mul, eval_ofNat]
    constructor
    · intro h
      have hfac : (x - 2) * (x + 1) ^ 2 = 0 := by nlinarith [h]
      rcases mul_eq_zero.1 hfac with h' | h'
      · refine ⟨0, by norm_num, ?_⟩
        rw [two_cos_zero]
        linarith
      · refine ⟨1, by norm_num, ?_⟩
        rw [two_cos_one]
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h'
        linarith
    · rintro ⟨k, hk, rfl⟩
      interval_cases k
      · rw [two_cos_zero]; norm_num
      · rw [two_cos_one]; norm_num
      · rw [two_cos_two]; norm_num

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

