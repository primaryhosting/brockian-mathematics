/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Stone's theorem: the generator of a strongly continuous one-parameter unitary group

Let `H` be a complex Hilbert space and let `U : ℝ → H →L[ℂ] H` be a strongly continuous
one-parameter unitary group, i.e. `U 0 = 1`, `U (s + t) = U s * U t`, every `U t` is unitary,
and `t ↦ U t x` is continuous for every `x`.

The *generator* of `U` is the (in general unbounded) operator `A` whose domain consists of the
vectors `x` for which `t ↦ U t x` is differentiable at `0`, and which is given there by
`A x = -I • (d/dt)|_{t = 0} (U t x)`, so that formally `U t = exp (I * t * A)`.

The main result, `QPhys.stone_generator`, is that `A` is self-adjoint as a partially defined
operator (`LinearPMap`).

The proof follows the classical argument:

* `A` is symmetric, by differentiating `t ↦ ⟪U t x, U t y⟫`;
* `A ± I` are surjective, using the resolvent `x ↦ ∫ t in Ioi 0, exp (-t) • U t x`;
* consequently the domain of `A` is dense, and every symmetric operator with `A ± I` surjective
  is self-adjoint.
-/

open MeasureTheory Set

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The domain of the (infinitesimal) generator of a one-parameter family `U : ℝ → H →L[ℂ] H`:
the set of vectors `x` for which `t ↦ U t x` is differentiable at `0`. -/

theorem adjoint_le_gen (hU : IsUnitaryGroup U) : (gen U).adjoint ≤ gen U := by
  have hdense : Dense ((gen U).domain : Set H) := dense_genDomain hU
  have hfa := LinearPMap.adjoint_isFormalAdjoint (T := gen U) hdense
  have main : ∀ y : (gen U).adjoint.domain, ∃ w : genDomain U,
      (w : H) = (y : H) ∧ genLinear U w = (gen U).adjoint y := by
    intro y
    obtain ⟨w, hw⟩ := exists_gen_sub_I hU ((gen U).adjoint y - Complex.I • (y : H))
    have hAv : ∀ v : genDomain U,
        inner ℂ (genLinear U v) ((y : H)) = inner ℂ (v : H) ((gen U).adjoint y) := by
      intro v
      rw [← inner_conj_symm (v : H) ((gen U).adjoint y), hfa y v, inner_conj_symm]
      rfl
    have hperp : ∀ v : genDomain U,
        inner ℂ (genLinear U v + Complex.I • (v : H)) ((y : H) - (w : H)) = (0 : ℂ) := by
      intro v
      have e1 : inner ℂ (genLinear U v + Complex.I • (v : H)) ((y : H))
          = inner ℂ (v : H) ((gen U).adjoint y - Complex.I • (y : H)) := by
        rw [inner_add_left, inner_smul_left, hAv v, inner_sub_right, inner_smul_right]
        simp [Complex.conj_I]
        ring
      have hsym : inner ℂ (genLinear U v) (w : H) = inner ℂ (v : H) (genLinear U w) :=
        gen_isFormalAdjoint hU v w
      have e2 : inner ℂ (genLinear U v + Complex.I • (v : H)) ((w : H))
          = inner ℂ (v : H) (genLinear U w - Complex.I • (w : H)) := by
        rw [inner_add_left, inner_smul_left, hsym, inner_sub_right, inner_smul_right]
        simp [Complex.conj_I]
        ring
      rw [inner_sub_right, e1, e2, hw, sub_self]
    have hzero : (y : H) - (w : H) = 0 := by
      obtain ⟨u, hu⟩ := exists_gen_add_I hU ((y : H) - (w : H))
      have h := hperp u
      rw [hu] at h
      exact inner_self_eq_zero.mp h
    have hyw : (w : H) = (y : H) := (sub_eq_zero.mp hzero).symm
    refine ⟨w, hyw, ?_⟩
    have hrw : genLinear U w
        = ((gen U).adjoint y - Complex.I • (y : H)) + Complex.I • (w : H) := by
      rw [← hw]; abel
    rw [hrw, hyw]
    abel
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨w, h1, _⟩ := main ⟨v, hv⟩
    have h2 := w.2
    rw [h1] at h2
    exact h2
  · intro a b hab
    obtain ⟨w, h1, h2⟩ := main a
    have hb : b = (⟨(w : H), w.2⟩ : genDomain U) := by
      apply Subtype.ext
      rw [← hab, ← h1]
    show (gen U).adjoint a = gen U b
    rw [hb, ← h2]
    rfl

/-- Stone's theorem: the generator of a strongly continuous one-parameter unitary group
is self-adjoint. -/
