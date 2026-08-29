/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Complex

namespace Chem

/-- A primitive 18-th root of unity. -/

theorem ch_add_ch_neg (k : Fin 18) : ch k + ch (-k) = mu k := by
  rw [ch_neg, ch_eq_exp, mu, ← Complex.exp_neg, ← neg_mul, ← Complex.two_cos]
  push_cast [Complex.ofReal_cos]
  ring

