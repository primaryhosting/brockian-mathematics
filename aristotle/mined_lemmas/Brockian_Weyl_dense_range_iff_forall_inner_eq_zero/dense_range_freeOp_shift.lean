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
# Symmetric operators, deficiency spaces and the basic criterion of essential self-adjointness

This file develops the small amount of unbounded-operator theory that is needed to state and
prove that a Schrödinger operator is essentially self-adjoint.

An *operator with domain `D`* on a complex Hilbert space `H` is encoded here as a pair of
linear maps `ι T : D →ₗ[ℂ] H`, where `ι` describes how the (abstract) domain `D` sits inside
`H` and `T` is the action of the operator.  (Taking `D` to be a submodule of `H` and `ι` its
inclusion recovers the usual picture; the extra generality is convenient because the natural
domain of a Schrödinger operator is a space of Schwartz functions.)

The main definition is `Brockian.Weyl.IsEssentiallySelfAdjoint`, which is the classical *basic
criterion* of von Neumann (see e.g. Reed–Simon, *Methods of Modern Mathematical Physics I*,
Theorem VIII.3): a densely defined symmetric operator is essentially self-adjoint if and only
if the ranges of `T + i` and `T - i` are dense.  The theorem
`Brockian.Weyl.dense_range_smul_sub_iff_deficiency` records the equivalent formulation in terms
of the *deficiency spaces*: no nonzero `v ∈ H` solves the weak (adjoint) equation `T* v = ∓ i v`.

The remaining results are the analytic tools used later:

* `Brockian.Weyl.norm_add_I_smul_lower_bound`: the basic lower bound `‖T x + i b ι x‖ ≥ |b| ‖ι x‖`
  for a symmetric operator;
* `Brockian.Weyl.dense_range_add_of_relatively_bounded`: a small perturbation lemma, which is the
  engine both of the Kato–Rellich argument and of the transfer of density in the spectral
  parameter;
* `Brockian.Weyl.dense_range_shift_of_dense_range_shift`: density of the range of `T + i b'`
  follows from density of the range of `T + i b` whenever `|b' - b| < b`.
-/

noncomputable section

open scoped ComplexInnerProductSpace

namespace Brockian.Weyl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {D : Type*} [AddCommGroup D] [Module ℂ D]

/-- An operator `T` with domain described by `ι` is *symmetric* if `⟪T x, ι y⟫ = ⟪ι x, T y⟫`. -/

theorem dense_range_freeOp_shift {b : ℝ} (hb : b ≠ 0) :
    Dense (Set.range fun φ : 𝓢(ℝ, ℂ) => freeOp φ + ((b : ℂ) * I) • iotaS φ) := by
  set e : L2R ≃ₗᵢ[ℂ] L2R := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ with he
  have hcoe : ∀ f : L2R, e f = 𝓕 f := fun _ => rfl
  have key : ∀ φ : 𝓢(ℝ, ℂ), e (freeOp φ + ((b : ℂ) * I) • iotaS φ)
      = iotaS ((𝓕 (negD2 φ) : 𝓢(ℝ, ℂ)) + ((b : ℂ) * I) • (𝓕 φ : 𝓢(ℝ, ℂ))) := by
    intro φ
    rw [map_add, map_smul, hcoe, hcoe, freeOp_apply, fourier_iotaS, fourier_iotaS,
      map_add, map_smul]
  suffices hd : Dense (Set.range fun φ : 𝓢(ℝ, ℂ) =>
      e (freeOp φ + ((b : ℂ) * I) • iotaS φ)) by
    have h1 : DenseRange (⇑e.symm) := e.symm.surjective.denseRange
    have h2 := h1.comp hd e.symm.continuous
    simpa [Function.comp_def] using h2
  simp only [key]
  intro v
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := MeasureTheory.MemLp.exist_eLpNorm_sub_le (p := 2)
    (by simp) (by norm_num) (MeasureTheory.Lp.memLp v) hε
  set gS : 𝓢(ℝ, ℂ) := hg₁.toSchwartzMap hg₂ with hgS
  have hgScs : HasCompactSupport (⇑gS) := hg₁
  obtain ⟨φ, hφ⟩ := exists_schwartz_solution hb gS hgScs
  refine ⟨iotaS gS, ⟨φ, congrArg iotaS hφ⟩, ?_⟩
  have hae : (v : ℝ → ℂ) - ((iotaS gS : L2R) : ℝ → ℂ) =ᵐ[volume] (v : ℝ → ℂ) - g := by
    filter_upwards [gS.coeFn_toLp 2 volume] with x hx
    have hgx : ((gS.toLp 2 volume : L2R) : ℝ → ℂ) x = g x := hx
    simp [hgx]
  simp only [Metric.mem_closedBall', MeasureTheory.Lp.dist_def,
    MeasureTheory.eLpNorm_congr_ae hae]
  grw [hg₃, ENNReal.toReal_ofReal hε.le]
  exact ENNReal.ofReal_ne_top

/-- **The free Schrödinger operator `-d²/dx²` with domain `𝓢(ℝ, ℂ)` is essentially
self-adjoint in `L²(ℝ)`.** -/
