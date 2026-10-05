/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Finset Matrix

/-- Complexified Minkowski space: four complex coordinates. -/
abbrev CMinkowski : Type := Fin 4 → ℂ

/-- The Minkowski metric signature `(+,-,-,-)`. -/

def ConnectedToIdentity (L : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∃ p : ℝ → Matrix (Fin 4) (Fin 4) ℂ,
    Continuous p ∧ p 0 = 1 ∧ p 1 = L ∧ ∀ t, IsComplexLorentz (p t)

/-- The total spacetime inversion `x ↦ -x`, i.e. the (P·T) part of the CPT operation on
spacetime arguments. -/
