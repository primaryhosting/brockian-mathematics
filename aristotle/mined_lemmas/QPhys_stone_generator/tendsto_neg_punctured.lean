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


theorem tendsto_neg_punctured : Tendsto (fun t : ℝ => -t) (𝓝[≠] (0:ℝ)) (𝓝[≠] (0:ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0:ℝ))
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht

end Aux

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space `H`:
a family `U t` of unitaries (surjective linear isometries) with `U 0 = 1`,
`U (s + t) = U s ∘ U t`, and `t ↦ U t x` continuous for every `x`. -/
structure IsUnitaryGroup (U : ℝ → (H ≃ₗᵢ[ℂ] H)) : Prop where
  zero : ∀ x, U 0 x = x
  add : ∀ s t x, U (s + t) x = U s (U t x)
  cont : ∀ x, Continuous fun t => U t x

/-- `HasGenerator U x y` says that `x` lies in the domain of the (Stone) generator `A` of the
one-parameter group `U` and that `A x = y`; i.e. `t ↦ U t x` is differentiable at `t = 0` with
derivative `i • y`, the normalization corresponding to `U t = exp (i t A)`. -/
