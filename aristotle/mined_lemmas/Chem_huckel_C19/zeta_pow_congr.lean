/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex SimpleGraph Finset

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

lemma zeta_pow_congr {m n : ℕ} (h : m % 19 = n % 19) : zeta ^ m = zeta ^ n := by
  rw [← zeta_pow_mod m, ← zeta_pow_mod n, h]

/-- Orthogonality of the discrete Fourier characters: `∑ⱼ ζ^(aj) ζ^(-jb) = 19·[a = b]`. -/
