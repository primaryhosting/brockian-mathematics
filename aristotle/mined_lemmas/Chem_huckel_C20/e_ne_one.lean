/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring `/-! ... -/` before the `import`
line, so the required header appears here as an ordinary block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-! ### The primitive 20-th root of unity and the associated character -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

lemma e_ne_one {a : ZMod 20} (ha : a ≠ 0) : e a ≠ 1 := by
  intro h
  have hdvd : (20 : ℕ) ∣ a.val := om_prim.dvd_of_pow_eq_one a.val h
  have h1 : a.val < 20 := ZMod.val_lt a
  have h2 : a.val ≠ 0 := fun hh => ha ((ZMod.val_eq_zero a).mp hh)
  omega

/-- Orthogonality of characters on `ZMod 20`. -/
