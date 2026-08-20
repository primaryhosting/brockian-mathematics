import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped Real

namespace Chem

/-! ### A primitive 13-th root of unity -/

/-- A primitive 13-th root of unity. -/

noncomputable def D13 : Matrix (Fin 13) (Fin 13) ℂ :=
  Matrix.diagonal fun k : Fin 13 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 13) : ℝ) : ℂ)

/-- The `(j, k)` entry of `P13` is the `j`-th power of the `k`-th root of unity. -/
