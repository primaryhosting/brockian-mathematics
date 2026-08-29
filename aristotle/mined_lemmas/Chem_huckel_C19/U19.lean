import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Matrix

namespace Chem

/-- A primitive 19-th root of unity. -/

noncomputable def U19 : (Matrix (Fin 19) (Fin 19) ℂ)ˣ := ⟨F19, G19, F_mul_G, G_mul_F⟩

