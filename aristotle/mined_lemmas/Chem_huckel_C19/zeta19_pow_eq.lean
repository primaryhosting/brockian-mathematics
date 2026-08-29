import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to precede any module documentation, so the requested
header comment appears immediately after the single `import Mathlib` line.)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₉`, i.e. the Hückel matrix of the
carbon skeleton of a 19-membered annulene (with `α = 0`, `β = 1`). -/

lemma zeta19_pow_eq (k : ℕ) : zeta19 ^ k = Complex.exp (((2 * Real.pi * k / 19 : ℝ) : ℂ) * I) := by
  rw [zeta19, ← Complex.exp_nsmul]
  congr 1
  push_cast
  ring

