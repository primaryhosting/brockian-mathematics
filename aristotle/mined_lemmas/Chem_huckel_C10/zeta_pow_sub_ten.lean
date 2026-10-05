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
-/

namespace Chem

open Matrix SimpleGraph Polynomial

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₀`.  This is the Hückel matrix of
cyclodecapentaene in units where the Coulomb integral `α` is `0` and the resonance integral
`β` is `1`. -/

lemma zeta_pow_sub_ten {n : ℕ} (hn : 10 ≤ n) : zeta ^ n = zeta ^ (n - 10) := by
  conv_lhs => rw [show n = (n - 10) + 10 by omega]
  rw [pow_add, zeta_pow_ten, mul_one]

