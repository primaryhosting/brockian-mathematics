import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Polynomial

namespace Chem

/-- A primitive 9th root of unity. -/

noncomputable def Wm : Matrix (Fin 9) (Fin 9) ℂ :=
  fun k l => (9 : ℂ)⁻¹ * om ^ ((k : ℕ) * (9 - (l : ℕ)))

