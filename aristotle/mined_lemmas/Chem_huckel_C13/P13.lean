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

noncomputable def P13 : Matrix (Fin 13) (Fin 13) ℂ := Matrix.vandermonde fun j => qc j

/-- The diagonal matrix of Hückel eigenvalues. -/
