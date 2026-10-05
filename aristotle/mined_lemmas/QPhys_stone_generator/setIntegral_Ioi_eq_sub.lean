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

lemma setIntegral_Ioi_eq_sub (g : ℝ → H) (hc : Continuous g)
    (hi : IntegrableOn g (Ioi (0 : ℝ))) (t : ℝ) :
    (∫ s in Ioi t, g s) = (∫ s in Ioi (0 : ℝ), g s) - ∫ s in (0 : ℝ)..t, g s := by
  rcases le_total 0 t with h | h
  · have hsplit : (∫ s in Ioi (0 : ℝ), g s) = (∫ s in Ioc (0 : ℝ) t, g s) + ∫ s in Ioi t, g s := by
      rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        hc.integrableOn_Ioc (hi.mono_set (Ioi_subset_Ioi h)), Set.Ioc_union_Ioi_eq_Ioi h]
    rw [intervalIntegral.integral_of_le h, hsplit]
    abel
  · have hsplit : (∫ s in Ioi t, g s) = (∫ s in Ioc t (0 : ℝ), g s) + ∫ s in Ioi (0 : ℝ), g s := by
      rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        hc.integrableOn_Ioc hi, Set.Ioc_union_Ioi_eq_Ioi h]
    rw [intervalIntegral.integral_of_ge h, hsplit]
    abel

/-- The fundamental identity `U t (R z) = e^t (R z - ∫_0^t e^{-s} U s z ds)`. -/
