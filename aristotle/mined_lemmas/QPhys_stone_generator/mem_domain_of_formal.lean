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

lemma mem_domain_of_formal (hU : IsUnitaryGroup U) (y w : H)
    (hy : ∀ v : (generator U).domain, (inner ℂ w (v : H) : ℂ) = inner ℂ y ((generator U) v)) :
    ∃ hmem : y ∈ (generator U).domain, generator U ⟨y, hmem⟩ = w := by
  obtain ⟨x, hx⟩ := surjective_sub_I hU (w - Complex.I • y)
  have hw : w = (generator U) x - Complex.I • (x : H) + Complex.I • y := by
    rw [hx]; abel
  have hwAx : w - (generator U) x = Complex.I • (y - (x : H)) := by
    rw [hw, smul_sub]; abel
  have horth : ∀ p : H, (inner ℂ (y - (x : H)) p : ℂ) = 0 := by
    intro p
    obtain ⟨v, hv⟩ := surjective_add_I hU p
    have h1 : (inner ℂ y ((generator U) v) : ℂ) = inner ℂ w (v : H) := (hy v).symm
    have h2 : (inner ℂ (x : H) ((generator U) v) : ℂ) = inner ℂ ((generator U) x) (v : H) :=
      (generator_isFormalAdjoint hU x v).symm
    have h3 : (inner ℂ w (v : H) : ℂ) - inner ℂ ((generator U) x) (v : H)
        = -Complex.I * ((inner ℂ y (v : H) : ℂ) - inner ℂ (x : H) (v : H)) := by
      rw [← inner_sub_left, hwAx, inner_smul_left, inner_sub_left]
      simp
    rw [← hv, inner_sub_left, inner_add_right, inner_add_right, inner_smul_right,
      inner_smul_right, h1, h2]
    linear_combination h3
  have hu : y - (x : H) = 0 := inner_self_eq_zero.mp (horth _)
  have hyx : y = (x : H) := by rwa [sub_eq_zero] at hu
  have hmem : y ∈ (generator U).domain := hyx ▸ x.2
  refine ⟨hmem, ?_⟩
  have hsub : (⟨y, hmem⟩ : (generator U).domain) = x := Subtype.ext hyx
  rw [hsub, hw, hyx]
  abel

/-- **Stone's theorem**: the infinitesimal generator of a strongly continuous
one-parameter unitary group on a complex Hilbert space is self-adjoint. -/
