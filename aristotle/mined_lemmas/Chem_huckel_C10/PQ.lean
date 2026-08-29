/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency eigenvalues of the cycle graph `C₁₀` are `2 cos (2πk/10)`, `k = 0, …, 9`:
the characteristic polynomial of the adjacency matrix of `SimpleGraph.cycleGraph 10`
factors as `∏ k, (X - 2 cos (2πk/10))`.
-/

namespace Chem

open Polynomial Matrix

/-! ### Arithmetic in `Fin 10`

`Fin 10` carries the modular addition and multiplication of `ZMod 10`, but Mathlib does not
register a `CommRing` instance on it, so `ring` is unavailable; the few needed ring identities
are checked by `decide`. -/

set_option maxRecDepth 10000 in

lemma PQ : PMat * QMat = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 10, PMat i k * QMat k j = (10 : ℂ)⁻¹ * ee (k * (i - j)) := by
    intro k
    simp only [PMat, QMat, fin_ten_mul_sub i j k, ee_add]
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum, sum_ee]
  by_cases h : i = j
  · subst h; norm_num
  · have : i - j ≠ 0 := sub_ne_zero.mpr h
    simp [h, this]

