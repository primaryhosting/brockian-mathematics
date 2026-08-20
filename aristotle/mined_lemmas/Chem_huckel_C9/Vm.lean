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

noncomputable def Vm : Matrix (Fin 9) (Fin 9) ℂ := fun j k => om ^ ((j : ℕ) * (k : ℕ))

/-- The (scaled) inverse DFT matrix. -/
