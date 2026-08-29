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

noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 18)

/-- The additive character `x ↦ ω ^ x` on `Fin 18`. -/
