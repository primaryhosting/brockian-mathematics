/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Matrix

namespace Phys

/-! ## Complexified Minkowski space and the complex Lorentz group -/

/-- Real Minkowski space `ℝ^{1,3}`. -/
abbrev Spacetime := Fin 4 → ℝ

/-- Complexified Minkowski space `ℂ^4`, the domain of the analytically continued
Wightman functions. -/
abbrev CSpace := Fin 4 → ℂ

/-- The Minkowski bilinear form on real Minkowski space (signature `+ - - -`). -/

noncomputable def inversionPath (t : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![ (Real.cos (π * t) : ℂ), Complex.I * (Real.sin (π * t) : ℂ), 0, 0;
      Complex.I * (Real.sin (π * t) : ℂ), (Real.cos (π * t) : ℂ), 0, 0;
      0, 0, (Real.cos (π * t) : ℂ), -(Real.sin (π * t) : ℂ);
      0, 0, (Real.sin (π * t) : ℂ), (Real.cos (π * t) : ℂ) ]

