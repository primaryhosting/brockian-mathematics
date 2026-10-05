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

lemma F_apply (i k : Fin 13) : F i k = ev (i * k) := by
  simp [F, Matrix.vandermonde_apply, ev, Fin.val_mul, zt_pow_mod, pow_mul]

