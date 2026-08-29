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

lemma ee_eq_exp (k : Fin 10) :
    ee k = Complex.exp (((2 * Real.pi * (k : ℝ) / 10 : ℝ) : ℂ) * Complex.I) := by
  have : ((2 * Real.pi * (k : ℝ) / 10 : ℝ) : ℂ) * Complex.I
      = ((k : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 10) := by push_cast; ring
  rw [this, Complex.exp_nat_mul]
  rfl

