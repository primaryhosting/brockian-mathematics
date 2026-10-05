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

theorem mem_unitary (hU : IsUnitaryGroup U) (t : ℝ) : U t ∈ unitary (H →L[ℂ] H) := by
  constructor
  · show star (U t) * U t = 1
    have : star (U t) = U (-t) := hU.adjoint_eq t
    rw [this]
    show (U (-t)).comp (U t) = 1
    rw [← hU.map_add]
    simpa using hU.map_zero
  · show U t * star (U t) = 1
    have : star (U t) = U (-t) := hU.adjoint_eq t
    rw [this]
    show (U t).comp (U (-t)) = 1
    rw [← hU.map_add]
    simpa using hU.map_zero

omit [CompleteSpace H] in
/-- The time-reversed group `t ↦ U (-t)` is again a strongly continuous unitary group. -/
