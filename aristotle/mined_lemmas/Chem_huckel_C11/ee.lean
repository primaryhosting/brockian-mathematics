import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial Finset

namespace Chem

/-- A primitive 11th root of unity. -/

noncomputable def ee (m : Fin 11) : ℂ := zeta ^ m.val

/-- The Hückel eigenvalues of the cycle `C₁₁` (in units of `β`, with `α = 0`). -/
