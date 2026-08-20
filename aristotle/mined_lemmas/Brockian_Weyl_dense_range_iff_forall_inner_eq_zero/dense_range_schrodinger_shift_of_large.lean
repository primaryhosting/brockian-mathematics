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

theorem dense_range_schrodinger_shift_of_large {V : ℝ → ℝ} (hV : MemLp (cx V) ⊤ volume)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ x, ‖(V x : ℂ)‖ ≤ M) {b : ℝ} (hb : M < |b|) :
    Dense (Set.range fun φ : 𝓢(ℝ, ℂ) => schrodingerOp V hV φ + ((b : ℂ) * I) • iotaS φ) := by
  have hbne : b ≠ 0 := by
    intro h
    rw [h] at hb
    simp at hb
    linarith
  set A : 𝓢(ℝ, ℂ) →ₗ[ℂ] L2R := shift iotaS freeOp b with hA
  set B : 𝓢(ℝ, ℂ) →ₗ[ℂ] L2R := (mulPotential V hV) ∘ₗ iotaS with hB
  have hAdense : Dense (Set.range A) := dense_range_freeOp_shift hbne
  have habs : 0 < |b| := lt_of_le_of_lt hM0 hb
  have hbound : ∀ φ, ‖B φ‖ ≤ (M / |b|) * ‖A φ‖ := by
    intro φ
    have h1 : ‖B φ‖ ≤ M * ‖iotaS φ‖ := norm_mulPotential_le hV hM (iotaS φ)
    have h2 : |b| * ‖iotaS φ‖ ≤ ‖A φ‖ := norm_add_I_smul_lower_bound freeOp_symmetric b φ
    rw [div_mul_eq_mul_div, le_div_iff₀ habs]
    calc ‖B φ‖ * |b| ≤ (M * ‖iotaS φ‖) * |b| := by
          exact mul_le_mul_of_nonneg_right h1 (le_of_lt habs)
      _ = M * (|b| * ‖iotaS φ‖) := by ring
      _ ≤ M * ‖A φ‖ := mul_le_mul_of_nonneg_left h2 hM0
  have hc : M / |b| < 1 := (div_lt_one habs).2 hb
  have hdense := dense_range_add_of_relatively_bounded A B hc hbound hAdense
  have hEq : (fun φ => A φ + B φ)
      = fun φ : 𝓢(ℝ, ℂ) => schrodingerOp V hV φ + ((b : ℂ) * I) • iotaS φ := by
    funext φ
    simp only [hA, hB, shift_apply, LinearMap.coe_comp, Function.comp_apply,
      schrodingerOp_apply]
    abel
  rwa [hEq] at hdense

/-- **Essential self-adjointness of the Schrödinger operator `-d²/dx² + V` under weak
regularity of the potential.**

If the real potential `V` is measurable and essentially bounded (`MemLp (fun x ↦ (V x : ℂ)) ⊤`,
which is exactly the *weak regularity* assumption: no smoothness whatsoever is required), then
the operator `u ↦ -u'' + V u`, with domain the Schwartz space `𝓢(ℝ, ℂ)` inside `L²(ℝ)`, is
essentially self-adjoint. -/
