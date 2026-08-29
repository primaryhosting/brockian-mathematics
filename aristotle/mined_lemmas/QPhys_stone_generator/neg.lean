import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set Filter Topology Complex
open scoped LinearPMap

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space `H`:
a family `U : ℝ → (H →L[ℂ] H)` with `U 0 = 1`, `U (s + t) = U s ∘ U t`, each `U t` norm
preserving (hence unitary, since the group law provides the inverse `U (-t)`), and such that
`t ↦ U t x` is continuous for every `x` (strong continuity). -/
structure IsUnitaryGroup (U : ℝ → H →L[ℂ] H) : Prop where
  map_zero : U 0 = 1
  map_add : ∀ s t, U (s + t) = (U s).comp (U t)
  norm_map : ∀ t x, ‖U t x‖ = ‖x‖
  continuous_apply : ∀ x, Continuous fun t => U t x

omit [CompleteSpace H] in
/-- Sanity check that the hypotheses are satisfiable: the constant family `U t = 1` is a
strongly continuous one-parameter unitary group. -/

theorem neg (hU : IsUnitaryGroup U) : IsUnitaryGroup (fun t => U (-t)) where
  map_zero := by simpa using hU.map_zero
  map_add := by
    intro s t
    have : -(s + t) = (-s) + (-t) := by ring
    rw [this, hU.map_add]
  norm_map := fun t x => hU.norm_map (-t) x
  continuous_apply := fun x => (hU.continuous_apply x).comp continuous_neg

end IsUnitaryGroup

/-- The domain of the generator: those `x` for which `t ↦ U t x` is differentiable at `0`. -/
