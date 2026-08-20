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

theorem dense_range_add_of_relatively_bounded (A B : D →ₗ[ℂ] H) {c : ℝ} (hc : c < 1)
    (hB : ∀ x, ‖B x‖ ≤ c * ‖A x‖) (hA : Dense (Set.range A)) :
    Dense (Set.range fun x => A x + B x) := by
  -- we may assume `0 ≤ c`
  set c' : ℝ := max c 0 with hc'
  have hc'1 : c' < 1 := max_lt hc one_pos
  have hc'0 : 0 ≤ c' := le_max_right _ _
  have hB' : ∀ x, ‖B x‖ ≤ c' * ‖A x‖ := fun x =>
    (hB x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have key := dense_range_iff_forall_inner_eq_zero (A + B)
  simp only [LinearMap.add_apply] at key
  rw [show (fun x => A x + B x) = ⇑(A + B) from rfl, key]
  intro v hv
  by_contra hv0
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have main : ∀ ε > (0 : ℝ), (1 - c') * ‖v‖ ≤ ε * (1 + c') := by
    intro ε hε
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 (hA.closure_eq ▸ Set.mem_univ v) ε hε
    have hdist : ‖A x - v‖ < ε := by
      rw [← dist_eq_norm]; simpa [dist_comm] using hx
    have hAx : ‖A x‖ ≤ ‖v‖ + ε := by
      have := norm_sub_norm_le (A x) v
      linarith
    have h0 : ⟪A x, v⟫ + ⟪B x, v⟫ = 0 := by
      have := hv x
      rwa [inner_add_left] at this
    have e1 : ⟪A x, v⟫ = ⟪A x - v, v⟫ + ⟪v, v⟫ := by
      rw [inner_sub_left]; ring
    have hb1 : ‖⟪A x - v, v⟫‖ ≤ ε * ‖v‖ := by
      refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
      exact mul_le_mul_of_nonneg_right hdist.le (norm_nonneg _)
    have hb2 : ‖⟪B x, v⟫‖ ≤ c' * (‖v‖ + ε) * ‖v‖ := by
      refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
      have hbx : ‖B x‖ ≤ c' * (‖v‖ + ε) :=
        (hB' x).trans (mul_le_mul_of_nonneg_left hAx hc'0)
      exact mul_le_mul_of_nonneg_right hbx (norm_nonneg _)
    have hvv : ⟪v, v⟫ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_num
    have : ‖v‖ ^ 2 ≤ ε * ‖v‖ + c' * (‖v‖ + ε) * ‖v‖ := by
      have hsum : ((‖v‖ ^ 2 : ℝ) : ℂ) = -⟪A x - v, v⟫ - ⟪B x, v⟫ := by
        rw [← hvv]
        have := h0
        rw [e1] at this
        linear_combination this
      have hnorm : (‖v‖ ^ 2 : ℝ) = ‖((‖v‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖v‖ ^ 2 = ‖((‖v‖ ^ 2 : ℝ) : ℂ)‖ := hnorm
        _ = ‖-⟪A x - v, v⟫ - ⟪B x, v⟫‖ := by rw [hsum]
        _ ≤ ‖(-⟪A x - v, v⟫ : ℂ)‖ + ‖(⟪B x, v⟫ : ℂ)‖ := norm_sub_le _ _
        _ ≤ ε * ‖v‖ + c' * (‖v‖ + ε) * ‖v‖ := by
            rw [norm_neg]; exact add_le_add hb1 hb2
    nlinarith
  have : (1 - c') * ‖v‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h2 : 0 < ε / (1 + c') := by positivity
    have := main (ε / (1 + c')) h2
    have hpos : (0 : ℝ) < 1 + c' := by linarith
    calc (1 - c') * ‖v‖ ≤ ε / (1 + c') * (1 + c') := this
      _ = ε := by field_simp
      _ = 0 + ε := by ring
  nlinarith

/-- If the range of `T + i b` is dense and `|b' - b| < |b|`, then the range of `T + i b'` is
dense as well. -/
