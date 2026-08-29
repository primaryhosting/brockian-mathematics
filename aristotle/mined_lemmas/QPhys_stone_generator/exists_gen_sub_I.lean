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

theorem exists_gen_sub_I (hU : IsUnitaryGroup U) (y : H) :
    ∃ w : genDomain U, genLinear U w - Complex.I • (w : H) = y := by
  set x : H := Complex.I • y with hx
  set V : ℝ → H →L[ℂ] H := fun t => U (-t) with hV
  have hd : HasDerivAt (fun s : ℝ => U (-s) (resolvent V x)) (resolvent V x - x) 0 :=
    hasDerivAt_resolvent hU.neg x
  -- reverse time
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) 0 := (hasDerivAt_id 0).neg
  have hd2 : HasDerivAt (fun s : ℝ => U s (resolvent V x)) (x - resolvent V x) 0 := by
    have hd' : HasDerivAt (fun s : ℝ => U (-s) (resolvent V x)) (resolvent V x - x) (-(0 : ℝ)) := by
      rwa [neg_zero]
    have := HasDerivAt.scomp (0 : ℝ) hd' hneg
    simp only [Function.comp_def, neg_neg] at this
    have heq : (-1 : ℝ) • (resolvent V x - x) = x - resolvent V x := by module
    rwa [heq] at this
  have hmem : resolvent V x ∈ genDomain U := ⟨_, hd2⟩
  refine ⟨⟨resolvent V x, hmem⟩, ?_⟩
  rw [genLinear_of_hasDerivAt hmem hd2]
  have h1 : -Complex.I • (x - resolvent V x) - Complex.I • resolvent V x = -Complex.I • x := by
    module
  rw [h1, hx, smul_smul]
  simp

end Resolvent

section Main

variable {U : ℝ → H →L[ℂ] H}

/-- The domain of the generator is dense. -/
