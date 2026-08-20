/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Complex

/-! ### A primitive 17-th root of unity and the associated additive character -/

/-- A primitive 17-th root of unity. -/

lemma ee_add_ee_neg (k : ZMod 17) : ee k + ee (-k) = lam k := by
  rw [ee_neg, ee_eq_exp, exp_add_inv, lam, Complex.ofReal_cos]

/-- The Fourier vector `j ↦ exp (2πi k j / 17)` is an eigenvector of the adjacency matrix
of `C₁₇` with eigenvalue `2 cos (2πk/17)`. -/
