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

theorem exists_mem_closure_opGraph (h : IsEssentiallySelfAdjoint ι T) (y : H) :
    ∃ p ∈ closure (opGraph ι T : Set (H × H)), p.2 - Complex.I • p.1 = y := by
  set C : Submodule ℂ (H × H) := (opGraph ι T).topologicalClosure with hC
  have hCset : (C : Set (H × H)) = closure (opGraph ι T : Set (H × H)) := rfl
  have hCclosed : IsClosed (C : Set (H × H)) := (opGraph ι T).isClosed_topologicalClosure
  haveI : CompleteSpace C := hCclosed.completeSpace_coe
  set fmap : (H × H) →L[ℂ] H :=
    (ContinuousLinearMap.snd ℂ H H) - Complex.I • (ContinuousLinearMap.fst ℂ H H) with hfmap
  set f : C →L[ℂ] H := fmap.comp C.subtypeL with hf
  have hbound : ∀ p : C, ‖(p : H × H)‖ ≤ ‖f p‖ := by
    intro p
    have := norm_le_norm_sub_I_smul_of_mem_closure h.symmetric (p := (p : H × H)) p.2
    simpa [hf, hfmap] using this
  have hanti : AntilipschitzWith 1 f := by
    refine AntilipschitzWith.of_le_mul_dist fun p q => ?_
    have hpq : ‖(p : H × H) - (q : H × H)‖ ≤ ‖f (p - q)‖ := hbound (p - q)
    simpa [dist_eq_norm, map_sub] using hpq
  have hclosedRange : IsClosed (Set.range f) := hanti.isClosed_range f.uniformContinuous
  have hdenseRange : Dense (Set.range f) := by
    refine Dense.mono ?_ h.dense_range_sub_I
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨(ι x, T x), ?_⟩, ?_⟩
    · exact subset_closure ⟨x, rfl⟩
    · simp [hf, hfmap]
  have hall : Set.range f = Set.univ := hclosedRange.closure_eq ▸ hdenseRange.closure_eq
  obtain ⟨p, hp⟩ : ∃ p : C, f p = y := by
    have : y ∈ Set.range f := by rw [hall]; trivial
    exact this
  exact ⟨(p : H × H), p.2, by simpa [hf, hfmap] using hp⟩

/-- **The closure of an essentially self-adjoint operator is self-adjoint.**  If `(ι, T)`
satisfies von Neumann's criterion, the closure of its graph is equal to its own adjoint. -/
