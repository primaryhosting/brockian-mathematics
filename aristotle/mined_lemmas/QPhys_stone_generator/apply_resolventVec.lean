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

lemma apply_resolventVec (hU : IsUnitaryGroup U) (z : H) (t : ℝ) :
    U t (resolventVec U z)
      = Real.exp t • (resolventVec U z - ∫ s in (0 : ℝ)..t, Real.exp (-s) • U s z) := by
  have hcont : Continuous (fun s : ℝ => Real.exp (-s) • U s z) := continuous_integrand hU z
  have hint : IntegrableOn (fun s : ℝ => Real.exp (-s) • U s z) (Ioi (0 : ℝ)) :=
    integrableOn_integrand hU z
  have step2 : ∀ s : ℝ, U t (Real.exp (-s) • U s z)
      = Real.exp t • (Real.exp (-(s + t)) • U (s + t) z) := by
    intro s
    have hUts : U t (U s z) = U (s + t) z := by
      rw [show s + t = t + s by ring, hU.map_add]
      rfl
    rw [ContinuousLinearMap.map_smul_of_tower, hUts, smul_smul, ← Real.exp_add]
    congr 1
    ring_nf
  calc U t (resolventVec U z)
      = ∫ s in Ioi (0 : ℝ), U t (Real.exp (-s) • U s z) := by
        rw [resolventVec, ContinuousLinearMap.integral_comp_comm _ hint]
    _ = ∫ s in Ioi (0 : ℝ), Real.exp t • (Real.exp (-(s + t)) • U (s + t) z) := by
        simp only [step2]
    _ = Real.exp t • ∫ s in Ioi (0 : ℝ), Real.exp (-(s + t)) • U (s + t) z :=
        integral_smul _ _
    _ = Real.exp t • ∫ s in Ioi (0 + t), Real.exp (-s) • U s z := by
        rw [show (∫ s in Ioi (0 : ℝ), Real.exp (-(s + t)) • U (s + t) z)
            = ∫ s in Ioi (0 + t), Real.exp (-s) • U s z from
          setIntegral_Ioi_shift (fun u : ℝ => Real.exp (-u) • U u z) 0 t]
    _ = Real.exp t • (resolventVec U z - ∫ s in (0 : ℝ)..t, Real.exp (-s) • U s z) := by
        rw [zero_add, setIntegral_Ioi_eq_sub _ hcont hint t]
        rfl

