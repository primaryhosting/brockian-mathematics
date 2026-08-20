import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Essential self-adjointness of the free Laplacian

This file proves that the free Laplacian `-Δ`, defined on the Schwartz space
`𝓢(ℝ^d, ℂ)` inside `L²(ℝ^d, ℂ)`, is essentially self-adjoint.

## Formalisation of essential self-adjointness

An unbounded operator is modelled here by a pair of linear maps `ι, A : D →ₗ[ℂ] H`
out of an abstract "domain" module `D`: `ι` is the (dense-range) inclusion of the
operator domain into the Hilbert space `H`, and `A` is the operator itself.

* `Brockian.Weyl.FreeLaplacian2.IsAdjointPair ι A u v` says that `(u, v)` belongs to the graph
  of the adjoint operator `A*`, i.e. `⟪v, ι f⟫ = ⟪u, A f⟫` for all `f` in the domain.
* `Brockian.Weyl.FreeLaplacian2.IsEssentiallySelfAdjoint ι A` says that the domain is dense,
  that `A` is symmetric, and that the adjoint `A*` is symmetric.  For a densely defined
  symmetric operator, symmetry of `A*` is the standard characterisation of essential
  self-adjointness (it is equivalent to `A* = A** = closure of A` being self-adjoint).

The abstract criterion `isEssentiallySelfAdjoint_of_dense_ranges` is von Neumann's basic
criterion: a densely defined symmetric operator with `Ran(A + i)` and `Ran(A - i)` dense is
essentially self-adjoint.

## Main results

* `Brockian.Weyl.FreeLaplacian2.fourier_freeLaplacian`: the Fourier transform conjugates the free
  Laplacian into multiplication by the symbol `4 π² ‖ξ‖²`.
* `Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier`: the free
  Laplacian on `𝓢(ℝ^d, ℂ) ⊆ L²(ℝ^d, ℂ)` is essentially self-adjoint.  The statement is
  unconditional: the Fourier-side input is supplied by `fourier_freeLaplacian`.
-/

namespace Brockian.Weyl.FreeLaplacian2

open MeasureTheory SchwartzMap Real Filter Topology
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap ContDiff

noncomputable section

/-! ## An abstract criterion for essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {D : Type*} [AddCommGroup D] [Module ℂ D]

/-- `IsAdjointPair ι A u v` states that the pair `(u, v)` belongs to the graph of the adjoint
of the operator `A` with domain `ι`, that is, `⟪v, ι f⟫ = ⟪u, A f⟫` for every `f` in the
domain. -/

theorem dense_range_freeLaplacianL2_add_smul (d : ℕ) (c : ℂ) (hc : c.im ≠ 0) :
    Dense (Set.range (freeLaplacianL2 d + c • schwartzToL2 d)) := by
  have hden : ∀ x : EuclSpace d, ((freeSymbol d x : ℝ) : ℂ) + c ≠ 0 := fun x h =>
    hc (by simpa using congrArg Complex.im h)
  have htoLp_add : ∀ a b : 𝓢(EuclSpace d, ℂ),
      (a + b).toLp 2 (volume : Measure (EuclSpace d))
        = a.toLp 2 (volume : Measure (EuclSpace d))
          + b.toLp 2 (volume : Measure (EuclSpace d)) :=
    fun a b => map_add (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclSpace d))) a b
  have htoLp_smul : ∀ (z : ℂ) (a : 𝓢(EuclSpace d, ℂ)),
      (z • a).toLp 2 (volume : Measure (EuclSpace d))
        = z • a.toLp 2 (volume : Measure (EuclSpace d)) :=
    fun z a => map_smul (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclSpace d))) z a
  have hbot : (LinearMap.range (freeLaplacianL2 d + c • schwartzToL2 d))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hint : ∀ f : 𝓢(EuclSpace d, ℂ),
        ∫ x, (starRingEnd ℂ) ((((freeSymbol d x : ℝ) : ℂ) + c) * 𝓕 f x)
          * (𝓕 v : Lp ℂ 2 (volume : Measure (EuclSpace d))) x = 0 := by
      intro f
      have hmem : (freeLaplacian d f + c • f).toLp 2 (volume : Measure (EuclSpace d))
          ∈ LinearMap.range (freeLaplacianL2 d + c • schwartzToL2 d) := by
        refine ⟨f, ?_⟩
        simp only [LinearMap.add_apply, LinearMap.smul_apply, freeLaplacianL2_apply,
          schwartzToL2_apply]
        rw [htoLp_add, htoLp_smul]
      have h1 : ⟪(freeLaplacian d f + c • f).toLp 2 (volume : Measure (EuclSpace d)), v⟫
          = (0 : ℂ) := hv _ hmem
      rw [← MeasureTheory.Lp.inner_fourier_eq, SchwartzMap.toLp_fourier_eq,
        inner_toLp_left] at h1
      refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)) h1
      have hval : 𝓕 (freeLaplacian d f + c • f) x = 𝓕 (freeLaplacian d f) x + c * 𝓕 f x := by
        change (fourierTransformCLM ℂ) (freeLaplacian d f + c • f) x = _
        rw [map_add, map_smul]
        simp
      have heq : (((freeSymbol d x : ℝ) : ℂ) + c) * 𝓕 f x
          = 𝓕 (freeLaplacian d f + c • f) x := by
        rw [hval, fourier_freeLaplacian]
        ring
      simp only [heq]
    have hV : (𝓕 v : Lp ℂ 2 (volume : Measure (EuclSpace d))) = 0 := by
      rw [Lp.eq_zero_iff_ae_eq_zero]
      apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
        ((Lp.memLp (𝓕 v : Lp ℂ 2 (volume : Measure (EuclSpace d)))).locallyIntegrable
          (by norm_num))
      intro χ hχ hχc
      obtain ⟨Φ, hΦ⟩ := exists_schwartz_div d c hc hχ hχc
      have hf := hint (𝓕⁻ Φ)
      rw [show 𝓕 (𝓕⁻ Φ) = Φ from FourierTransform.fourier_fourierInv_eq Φ] at hf
      refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)) hf
      rw [hΦ x, mul_div_cancel₀ _ (hden x)]
      simp [Complex.real_smul]
    calc v = 𝓕⁻ (𝓕 v : Lp ℂ 2 (volume : Measure (EuclSpace d))) :=
          (FourierTransform.fourierInv_fourier_eq v).symm
      _ = 0 := by rw [hV, FourierTransform.fourierInv_zero]
  have hclosure := (Submodule.topologicalClosure_eq_top_iff
    (K := LinearMap.range (freeLaplacianL2 d + c • schwartzToL2 d))).mpr hbot
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.mpr hclosure
  simpa [LinearMap.coe_range] using hd

/-- **The free Laplacian is essentially self-adjoint.**

`-Δ`, defined on the Schwartz space `𝓢(ℝ^d, ℂ)` viewed inside `L²(ℝ^d, ℂ)`, is essentially
self-adjoint: its domain is dense, it is symmetric, and its adjoint is symmetric.

The proof is via the Fourier transform (see `fourier_freeLaplacian`), which conjugates `-Δ`
into multiplication by the real symbol `4 π² ‖ξ‖²`; the statement is unconditional. -/
