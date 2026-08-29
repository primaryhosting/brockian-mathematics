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

lemma lam_eq (k : Fin 10) : ((lam k : ℝ) : ℂ) = ee k + ee (-k) := by
  have h := Complex.two_cos ((2 * Real.pi * (k : ℝ) / 10 : ℝ) : ℂ)
  rw [ee_neg, ee_eq_exp, lam]
  push_cast [Complex.ofReal_cos]
  rw [← Complex.exp_neg]
  push_cast at h
  simp only [neg_mul] at h
  linear_combination h

/-- The (discrete-Fourier) eigenvector matrix. -/
