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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

/-! ## Complexified Minkowski space and the complex Lorentz group -/

/-- Complexified Minkowski space `ℂ⁴`. -/
abbrev CVec : Type := Fin 4 → ℂ

/-- The (bilinear, not sesquilinear) Minkowski form of signature `(+,-,-,-)` on complexified
Minkowski space. -/

noncomputable def ptPath (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![Complex.cos θ, Complex.I * Complex.sin θ, 0, 0;
     Complex.I * Complex.sin θ, Complex.cos θ, 0, 0;
     0, 0, Complex.cos θ, -Complex.sin θ;
     0, 0, Complex.sin θ, Complex.cos θ]

/-- Every member of the path `ptPath` preserves the complex Minkowski form. -/
