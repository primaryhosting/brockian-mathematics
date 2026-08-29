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

lemma zt_pow_thirteen : zt ^ 13 = 1 := zt_isPrimitiveRoot.pow_eq_one

