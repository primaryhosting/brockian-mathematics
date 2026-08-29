import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
(The `import Mathlib` line must precede the module docstring: Lean 4 requires all
`import` commands to appear at the very beginning of a file.)
-/

namespace Chem

open Matrix SimpleGraph Finset

/-- A primitive 13-th root of unity. -/

lemma zt_pow_mod (m : ℕ) : zt ^ (m % 13) = zt ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 13]
  rw [pow_add, pow_mul, zt_pow_thirteen, one_pow, one_mul]

/-- The character `k ↦ ζ^k` of `Fin 13` (viewed as `ℤ/13ℤ`). -/
