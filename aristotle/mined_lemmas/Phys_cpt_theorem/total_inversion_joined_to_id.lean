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

theorem total_inversion_joined_to_id :
    ∃ L : ℝ → Matrix (Fin 4) (Fin 4) ℂ,
      Continuous L ∧ L 0 = 1 ∧ L 1 = -1 ∧ ∀ t, IsComplexLorentz (L t) :=
  ⟨inversionPath, inversionPath_continuous, inversionPath_zero, inversionPath_one,
    inversionPath_lorentz⟩

/-! ## Jost points -/

/-- `x` is a *Jost point*: every nontrivial nonnegative combination of the consecutive
difference vectors `x k - x (k+1)` is spacelike.  At such configurations locality of the
field implies weak local commutativity. -/
