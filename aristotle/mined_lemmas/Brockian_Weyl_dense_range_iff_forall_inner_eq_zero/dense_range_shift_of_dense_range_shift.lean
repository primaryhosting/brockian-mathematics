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

theorem dense_range_shift_of_dense_range_shift {ι T : D →ₗ[ℂ] H} (hsym : IsSymmetricOn ι T)
    {b b' : ℝ} (hb : 0 < |b|) (hbb : |b' - b| < |b|)
    (h : Dense (Set.range fun x => T x + ((b : ℂ) * Complex.I) • ι x)) :
    Dense (Set.range fun x => T x + ((b' : ℂ) * Complex.I) • ι x) := by
  set A : D →ₗ[ℂ] H := shift ι T b with hA
  set B : D →ₗ[ℂ] H := (((b' - b : ℝ) : ℂ) * Complex.I) • ι with hBdef
  have hAdense : Dense (Set.range A) := h
  have hbound : ∀ x, ‖B x‖ ≤ (|b' - b| / |b|) * ‖A x‖ := by
    intro x
    have h1 : ‖B x‖ = |b' - b| * ‖ι x‖ := by
      simp only [hBdef, LinearMap.smul_apply, norm_smul, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
    have h2 : |b| * ‖ι x‖ ≤ ‖A x‖ := norm_add_I_smul_lower_bound hsym b x
    rw [h1]
    rw [div_mul_eq_mul_div, le_div_iff₀ hb]
    have h3 : |b| * ‖ι x‖ ≤ ‖A x‖ := h2
    calc |b' - b| * ‖ι x‖ * |b| = |b' - b| * (|b| * ‖ι x‖) := by ring
      _ ≤ |b' - b| * ‖A x‖ := by
          exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  have hc : |b' - b| / |b| < 1 := by
    rw [div_lt_one hb]; exact hbb
  have hdense := dense_range_add_of_relatively_bounded A B hc hbound hAdense
  have hEq : (fun x => A x + B x) = fun x => T x + ((b' : ℂ) * Complex.I) • ι x := by
    funext x
    simp only [hA, hBdef, shift_apply, LinearMap.smul_apply, add_assoc, ← add_smul]
    congr 2
    push_cast
    ring
  rwa [hEq] at hdense

end Perturbation

/-!
### The closure of an essentially self-adjoint operator is self-adjoint

This section justifies the name `IsEssentiallySelfAdjoint`: if the criterion holds, then the
closure of the graph of `T` coincides with the graph of its adjoint, i.e. the closure of `T` is
a self-adjoint operator.
-/

section GraphClosure

/-- The graph of the operator `(ι, T)`, as a submodule of `H × H`. -/
