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

lemma hasDerivAt_resolventVec (hU : IsUnitaryGroup U) (z : H) :
    HasDerivAt (fun t : ℝ => U t (resolventVec U z)) (resolventVec U z - z) 0 := by
  have hcont : Continuous (fun s : ℝ => Real.exp (-s) • U s z) := continuous_integrand hU z
  have hF : HasDerivAt (fun t : ℝ => ∫ s in (0 : ℝ)..t, Real.exp (-s) • U s z)
      (Real.exp (-(0 : ℝ)) • U 0 z) 0 := (hcont.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hd := (Real.hasDerivAt_exp 0).smul
    ((hasDerivAt_const (0 : ℝ) (resolventVec U z)).sub hF)
  have hfun : (fun t : ℝ => U t (resolventVec U z))
      = fun t : ℝ => Real.exp t • (resolventVec U z - ∫ s in (0 : ℝ)..t, Real.exp (-s) • U s z) :=
    funext (apply_resolventVec hU z)
  rw [hfun]
  have hd' : HasDerivAt
      (fun t : ℝ => Real.exp t • (resolventVec U z - ∫ s in (0 : ℝ)..t, Real.exp (-s) • U s z))
      (Real.exp 0 • (0 - Real.exp (-(0 : ℝ)) • U 0 z)
        + Real.exp 0 • (resolventVec U z - ∫ s in (0 : ℝ)..(0 : ℝ), Real.exp (-s) • U s z)) 0 := hd
  convert hd' using 1
  rw [hU.map_zero]
  simp
  abel

