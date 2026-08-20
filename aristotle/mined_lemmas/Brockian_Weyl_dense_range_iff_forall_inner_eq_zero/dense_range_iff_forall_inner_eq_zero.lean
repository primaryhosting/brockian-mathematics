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

theorem dense_range_iff_forall_inner_eq_zero (f : D →ₗ[ℂ] H) :
    Dense (Set.range f) ↔ ∀ v : H, (∀ x, ⟪f x, v⟫ = 0) → v = 0 := by
  have hset : ((LinearMap.range f : Submodule ℂ H) : Set H) = Set.range f := by
    ext v; simp [LinearMap.mem_range]
  constructor
  · intro hdense v hv
    have h0 : ⟪v, v⟫ = (0 : ℂ) := by
      have hc : Continuous fun w : H => ⟪w, v⟫ :=
        continuous_inner.comp (Continuous.prodMk continuous_id continuous_const)
      have : ∀ w ∈ closure (Set.range f), ⟪w, v⟫ = (0 : ℂ) := by
        intro w hw
        refine (isClosed_eq hc continuous_const).closure_subset_iff.2 ?_ hw
        rintro _ ⟨x, rfl⟩; exact hv x
      exact this v (by rw [hdense.closure_eq]; trivial)
    simpa using inner_self_eq_zero.1 h0
  · intro h
    have hbot : (LinearMap.range f : Submodule ℂ H)ᗮ = ⊥ := by
      refine Submodule.eq_bot_iff _ |>.2 fun v hv => ?_
      exact h v fun x => hv (f x) ⟨x, rfl⟩
    have := (Submodule.topologicalClosure_eq_top_iff (K := (LinearMap.range f : Submodule ℂ H))).2
      hbot
    have hcl : closure (Set.range f) = Set.univ := by
      have : ((LinearMap.range f : Submodule ℂ H).topologicalClosure : Set H) = Set.univ := by
        rw [this]; rfl
      rwa [Submodule.topologicalClosure_coe, hset] at this
    exact dense_iff_closure_eq.2 hcl

/-- The deficiency-space formulation of density of the range of `T - z`: the range of `T - z`
is dense if and only if the *deficiency equation* `T* v = conj z • v`, read weakly, has no
nonzero solution. -/
