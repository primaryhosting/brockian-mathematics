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

theorem isSelfAdjoint_adjoint_of_denseRange {A : H →ₗ.[ℂ] H} (hdense : Dense (A.domain : Set H))
    (hsym : ∀ x y : A.domain, ⟪A x, (y : H)⟫ = ⟪(x : H), A y⟫)
    (hplus : ∀ u : H, (∀ x : A.domain, ⟪u, A x + Complex.I • (x : H)⟫ = 0) → u = 0)
    (hminus : ∀ u : H, (∀ x : A.domain, ⟪u, A x - Complex.I • (x : H)⟫ = 0) → u = 0) :
    IsSelfAdjoint A.adjoint := by
  set S := A.adjoint with hS
  have hAS : A ≤ S := symmetric_le_adjoint hdense hsym
  have hSdense : Dense (S.domain : Set H) := hdense.mono (by exact_mod_cast hAS.1)
  have hSS : S.adjoint ≤ S := adjoint_le_adjoint_of_le hdense hAS
  have hASS : A ≤ S.adjoint := le_adjoint_adjoint hdense hSdense
  have hS'sym : ∀ x y : S.adjoint.domain, ⟪S.adjoint x, (y : H)⟫ = ⟪(x : H), S.adjoint y⟫ := by
    intro x y
    rw [(LinearPMap.adjoint_isFormalAdjoint hSdense) x ⟨(y : H), hSS.1 y.2⟩]
    congr 1
    exact (hSS.2 (x := y) (y := ⟨(y : H), hSS.1 y.2⟩) rfl).symm
  have hS'closed : S.adjoint.IsClosed := LinearPMap.adjoint_isClosed hSdense
  have hns := norm_shift_sq hS'sym (z := Complex.I) (by simp) (by simp)
  have hKclosed : IsClosed (shiftRange S.adjoint Complex.I : Set H) :=
    isClosed_shiftRange hS'closed hns
  haveI : CompleteSpace (shiftRange S.adjoint Complex.I) := hKclosed.completeSpace_coe
  have hKtop : shiftRange S.adjoint Complex.I = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro u hu
    refine hplus u fun x => ?_
    have hx : (x : H) ∈ S.adjoint.domain := hASS.1 x.2
    have hval : S.adjoint ⟨(x : H), hx⟩ = A x := (hASS.2 (x := x) (y := ⟨(x : H), hx⟩) rfl).symm
    have hmem : A x + Complex.I • (x : H) ∈ shiftRange S.adjoint Complex.I := by
      rw [mem_shiftRange_iff]
      exact ⟨⟨(x : H), hx⟩, by rw [hval]⟩
    rw [← inner_eq_zero_symm]
    exact (Submodule.mem_orthogonal _ u).mp hu _ hmem
  have hker : ∀ w : S.domain, S w + Complex.I • (w : H) = 0 → (w : H) = 0 := by
    intro w hw
    refine hminus (w : H) fun x => ?_
    have h1 := (LinearPMap.adjoint_isFormalAdjoint hdense) w x
    have h2 : S w = -(Complex.I • (w : H)) := by linear_combination (norm := module) hw
    rw [inner_sub_right, ← h1, h2, inner_neg_left, inner_smul_left, inner_smul_right]
    simp [Complex.conj_I]
  have hSS' : S ≤ S.adjoint := by
    have hmain : ∀ (u : H) (hu : u ∈ S.domain), ∃ (h : u ∈ S.adjoint.domain),
        S.adjoint ⟨u, h⟩ = S ⟨u, hu⟩ := by
      intro u hu
      have hmem : S ⟨u, hu⟩ + Complex.I • u ∈ shiftRange S.adjoint Complex.I := by
        rw [hKtop]; trivial
      rw [mem_shiftRange_iff] at hmem
      obtain ⟨x, hx⟩ := hmem
      have hxS : (x : H) ∈ S.domain := hSS.1 x.2
      have hxval : S ⟨(x : H), hxS⟩ = S.adjoint x :=
        (hSS.2 (x := x) (y := ⟨(x : H), hxS⟩) rfl).symm
      have hw0 : S (⟨u, hu⟩ - ⟨(x : H), hxS⟩)
          + Complex.I • ((⟨u, hu⟩ - ⟨(x : H), hxS⟩ : S.domain) : H) = 0 := by
        rw [LinearPMap.map_sub]
        have hc : ((⟨u, hu⟩ - ⟨(x : H), hxS⟩ : S.domain) : H) = u - (x : H) := rfl
        rw [hc, hxval, smul_sub]
        linear_combination (norm := module) -hx
      have hzero := hker _ hw0
      have huv : u = (x : H) := by
        have hc : ((⟨u, hu⟩ - ⟨(x : H), hxS⟩ : S.domain) : H) = u - (x : H) := rfl
        rw [hc] at hzero
        exact sub_eq_zero.mp hzero
      subst huv
      exact ⟨x.2, by rw [← hxval]⟩
    refine ⟨fun u hu => (hmain u hu).1, ?_⟩
    rintro ⟨u, hu⟩ ⟨u', hu'⟩ h
    simp only at h
    subst h
    exact ((hmain u hu).2).symm
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm hSS hSS'

/-- If `A` is essentially self-adjoint, then `A.adjoint` is its unique self-adjoint
extension. -/
