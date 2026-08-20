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

lemma norm_le_norm_sub_I_smul_of_mem_closure (hsym : IsSymmetricOn ι T) {p : H × H}
    (hp : p ∈ closure (opGraph ι T : Set (H × H))) : ‖p‖ ≤ ‖p.2 - Complex.I • p.1‖ := by
  have hclosed : IsClosed {p : H × H | ‖p‖ ≤ ‖p.2 - Complex.I • p.1‖} := by
    refine isClosed_le continuous_norm ?_
    exact (continuous_snd.sub (continuous_const.smul continuous_fst)).norm
  refine hclosed.closure_subset_iff.2 ?_ hp
  rintro _ ⟨x, rfl⟩
  show ‖((ι x, T x) : H × H)‖ ≤ ‖T x - Complex.I • ι x‖
  have hpyth : ‖T x + (((-1 : ℝ) : ℂ) * Complex.I) • ι x‖ ^ 2 = ‖T x‖ ^ 2 + ‖ι x‖ ^ 2 := by
    rw [norm_add_I_smul_sq hsym (-1) x]; ring
  have hrw : T x + (((-1 : ℝ) : ℂ) * Complex.I) • ι x = T x - Complex.I • ι x := by
    push_cast
    rw [neg_one_mul, neg_smul]
    abel
  rw [hrw] at hpyth
  have hmax : ‖((ι x, T x) : H × H)‖ = max ‖ι x‖ ‖T x‖ := rfl
  have h1 : ‖((ι x, T x) : H × H)‖ ^ 2 ≤ ‖T x - Complex.I • ι x‖ ^ 2 := by
    rw [hpyth, hmax]
    rcases max_cases ‖ι x‖ ‖T x‖ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      nlinarith [norm_nonneg (ι x), norm_nonneg (T x)]
  have h2 : (0 : ℝ) ≤ ‖T x - Complex.I • ι x‖ := norm_nonneg _
  nlinarith [norm_nonneg ((ι x, T x) : H × H)]

variable [CompleteSpace H]

/-- Every `h : H` is of the form `w - i v` with `(v, w)` in the closure of the graph.  This is
the key surjectivity statement behind von Neumann's criterion. -/
