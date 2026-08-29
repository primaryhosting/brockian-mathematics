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

def cptInversion : Matrix (Fin 4) (Fin 4) ℂ := -1

/-- A one-parameter family of complex Lorentz transformations: a complex boost with
imaginary rapidity in the `(0,1)`-plane combined with a rotation in the `(2,3)`-plane.
At `t = π` it equals total spacetime inversion `-1`. -/
