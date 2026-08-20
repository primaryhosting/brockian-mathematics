import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean 4 requires `import` commands to occur at the very beginning of a file,
before any module docstring, hence the header comment above appears just after the import.
-/

open Complex Polynomial Matrix

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma pow_mod_eighteen (x : ℂ) (hx : x ^ 18 = 1) (a : ℕ) : x ^ (a % 18) = x ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 18]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

/-- The eigenvalue attached to index `k`: `2 cos (2πk/18)`. -/
