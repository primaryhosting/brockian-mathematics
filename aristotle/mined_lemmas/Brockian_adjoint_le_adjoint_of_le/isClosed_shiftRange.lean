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
# A basic criterion for essential self-adjointness

This file develops, from scratch, the classical criterion of von Neumann:

If `A` is a densely defined symmetric operator on a complex Hilbert space `H` such that the
ranges of `A + i` and `A - i` are dense — stated here in the equivalent form that a vector
orthogonal to such a range vanishes — then the adjoint `A†` is self-adjoint.  This is exactly
the statement that `A` is *essentially self-adjoint*: the closure of `A` (which is `A††`) is
self-adjoint, equivalently `A` has a unique self-adjoint extension, namely `A†`.

## Main results

* `Brockian.isSelfAdjoint_adjoint_of_denseRange`: the criterion.
* `Brockian.eq_adjoint_of_isSelfAdjoint_of_le`: uniqueness of the self-adjoint extension.
-/

open scoped ComplexInnerProductSpace
open LinearPMap

noncomputable section

namespace Brockian

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Antitonicity of the adjoint: an extension has a smaller adjoint. -/

theorem isClosed_shiftRange {B : H →ₗ.[ℂ] H} (hcl : B.IsClosed) {z : ℂ}
    (hns : ∀ x : B.domain, ‖B x + z • (x : H)‖ ^ 2 = ‖B x‖ ^ 2 + ‖(x : H)‖ ^ 2) :
    IsClosed (shiftRange B z : Set H) := by
  classical
  set G := B.graph
  haveI : CompleteSpace G := hcl.completeSpace_coe
  set L : (H × H) →L[ℂ] H :=
    (ContinuousLinearMap.snd ℂ H H) + z • (ContinuousLinearMap.fst ℂ H H) with hL
  set Ψ : G → H := fun v => L (v : H × H) with hΨ
  have hrange : (shiftRange B z : Set H) = Set.range Ψ := by
    ext y
    simp only [SetLike.mem_coe, mem_shiftRange_iff, Set.mem_range, hΨ, hL]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨((x : H), B x), by rw [LinearPMap.mem_graph_iff]; exact ⟨x, rfl, rfl⟩⟩, by simp⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff B).mp v.2
      exact ⟨x, by simp [hx1, hx2]⟩
  rw [hrange]
  have hanti : AntilipschitzWith 1 Ψ := by
    refine AntilipschitzWith.of_le_mul_dist ?_
    intro v w
    have hvw : (v : H × H) - (w : H × H) ∈ B.graph := Submodule.sub_mem _ v.2 w.2
    obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff B).mp hvw
    have hxe : ((v : H × H) - w) = ((x : H), B x) := Prod.ext hx1.symm hx2.symm
    have key := hns x
    have h1 : Ψ v - Ψ w = B x + z • (x : H) := by
      simp only [hΨ, hL, ← _root_.map_sub]
      rw [hxe]
      simp [add_comm]
    have hd : dist (Ψ v) (Ψ w) = ‖B x + z • (x : H)‖ := by rw [dist_eq_norm, h1]
    have hd2 : dist v w = ‖((x : H), B x)‖ := by
      rw [Subtype.dist_eq, dist_eq_norm, hxe]
    rw [hd, hd2, NNReal.coe_one, one_mul, Prod.norm_def]
    refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (norm_nonneg _) ?_
    rw [key]
    rcases max_cases ‖(x : H)‖ ‖B x‖ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      nlinarith [sq_nonneg ‖B x‖, sq_nonneg ‖(x : H)‖]
  exact hanti.isClosed_range (L.uniformContinuous.comp uniformContinuous_subtype_val)

/-- **von Neumann's criterion.** A densely defined symmetric operator `A` such that the ranges
of `A + i` and of `A - i` have trivial orthogonal complement is essentially self-adjoint:
its adjoint is self-adjoint. -/
