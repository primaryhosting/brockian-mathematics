/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Complex

namespace Chem

/-- A primitive 18-th root of unity. -/

noncomputable def W : Matrix (Fin 18) (Fin 18) ℂ := fun k l => (18 : ℂ)⁻¹ * ch (-(k * l))

/-- The Hückel eigenvalues of `C₁₈`. -/
