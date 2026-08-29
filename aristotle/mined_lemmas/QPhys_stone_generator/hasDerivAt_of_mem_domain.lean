import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Stone's theorem: the infinitesimal generator of a strongly continuous one-parameter
unitary group on a complex Hilbert space is (essentially) the self-adjoint operator
`A` with `U t = exp (t * I * A)`; here we prove that the generator, defined as an
unbounded operator (a `LinearPMap`) on its natural domain, is self-adjoint.
-/

namespace QPhys

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space. -/
structure IsUnitaryGroup (U : ℝ → (H →L[ℂ] H)) : Prop where
  /-- `U 0` is the identity. -/
  map_zero : U 0 = 1
  /-- The group law. -/
  map_add : ∀ s t, U (s + t) = U s * U t
  /-- Each `U t` is unitary. -/
  unitary : ∀ t, U t ∈ unitary (H →L[ℂ] H)
  /-- Strong continuity. -/
  strongly_continuous : ∀ x, Continuous fun t => U t x

/-- The natural domain of the infinitesimal generator of `U`: the vectors `x` for which
`t ↦ U t x` is differentiable at `0`. -/

lemma hasDerivAt_of_mem_domain (x : (generator U).domain) :
    HasDerivAt (fun t : ℝ => U t (x : H)) (Complex.I • generator U x) 0 := by
  have hx : DifferentiableAt ℝ (fun t : ℝ => U t (x : H)) 0 := x.2
  have : Complex.I • generator U x = deriv (fun t : ℝ => U t (x : H)) 0 := by
    rw [generator_apply, smul_smul]
    simp
  rw [this]
  exact hx.hasDerivAt

/-- The generator is a symmetric operator. -/
