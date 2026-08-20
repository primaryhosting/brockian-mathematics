/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header above is a
-- plain comment and is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Set Topology
open scoped ComplexInnerProductSpace

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section Aux


def HasGenerator (U : ℝ → (H ≃ₗᵢ[ℂ] H)) (x y : H) : Prop :=
  Tendsto (fun t : ℝ => t⁻¹ • (U t x - x)) (𝓝[≠] (0 : ℝ)) (𝓝 (Complex.I • y))

section Basic

variable {U : ℝ → (H ≃ₗᵢ[ℂ] H)}

/-- Unitarity: the adjoint of `U t` is `U (-t)`. -/
