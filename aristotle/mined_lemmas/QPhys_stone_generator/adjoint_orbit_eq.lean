/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean does not allow a module docstring before the `import` line, so the header above is a
plain block comment; the same header is repeated as a module docstring below.)
-/
import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Stone's theorem: the infinitesimal generator of a strongly continuous one-parameter
unitary group on a complex Hilbert space is self-adjoint (as an unbounded, i.e. partially
defined, operator).
-/

namespace QPhys

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The domain of the infinitesimal generator of a one-parameter group `U`:
the set of vectors `x` for which the orbit map `t ↦ U t x` is differentiable at `0`. -/

lemma adjoint_orbit_eq {y : H} (hy : y ∈ (generator U).adjoint.domain) (tau : ℝ) :
    U (-tau) y - y
      = ∫ s in (0:ℝ)..tau, Complex.I • U (-s) ((generator U).adjoint ⟨y, hy⟩) := by
  set z : H := (generator U).adjoint ⟨y, hy⟩ with hzdef
  have hdense := dense_generatorDomain U hU0 hUadd hUcont
  refine Dense.eq_of_inner_right (K := (generator U).domain) hdense ?_
  rintro ⟨x, hx⟩
  have hx' : x ∈ generatorDomain U := hx
  have hcont : Continuous fun s : ℝ => Complex.I * inner ℂ (U s x) z :=
    continuous_const.mul ((hUcont x).inner continuous_const)
  have hint : (∫ s in (0:ℝ)..tau, Complex.I * inner ℂ (U s x) z)
      = inner ℂ (U tau x) y - inner ℂ (U 0 x) y :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_inner_orbit U hU0 hUadd hUcont hy hx' s)
      (hcont.intervalIntegrable _ _)
  have hcontz : Continuous fun s : ℝ => Complex.I • U (-s) z :=
    (((hUcont z).comp continuous_neg)).const_smul Complex.I
  have hswap : inner ℂ x (∫ s in (0:ℝ)..tau, Complex.I • U (-s) z)
      = ∫ s in (0:ℝ)..tau, inner ℂ x (Complex.I • U (-s) z) := by
    have := (ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℂ x)
      (a := (0:ℝ)) (b := tau) (μ := MeasureTheory.volume)
      (hcontz.intervalIntegrable 0 tau)).symm
    simpa using this
  have hpt : ∀ s : ℝ, inner ℂ x (Complex.I • U (-s) z) = Complex.I * inner ℂ (U s x) z := by
    intro s
    rw [inner_smul_right, inner_U_left U hU0 hUadd hUnorm s x z]
  rw [hswap]
  simp only [hpt]
  rw [hint, inner_sub_right, inner_U_left U hU0 hUadd hUnorm tau x y, hU0 x]

include hU0 hUadd hUnorm hUcont in
/-- Every vector in the domain of the adjoint is in the domain of the generator, with the
expected derivative. -/
