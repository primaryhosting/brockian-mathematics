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

/-
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Redux.LinAlg

open Matrix Finset Module

variable {d : ℕ}

/-- The quadratic form `x ↦ Re ⟪x, M x⟫` associated with a matrix `M`, on `EuclideanSpace ℂ (Fin d)`.
-/

theorem weyl_posIndexAbove {d : ℕ} {A E : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hE : E.IsHermitian) (θ : ℝ)
    (hEθ : ∀ i, |hE.eigenvalues i| ≤ θ) :
    posIndexAbove (hA.add hE) θ ≤ posIndex hA := by
  classical
  set hAE : (A + E).IsHermitian := hA.add hE
  set s : Finset (Fin d) := Finset.univ.filter (fun i => θ < hAE.eigenvalues i) with hs
  set t : Finset (Fin d) := Finset.univ.filter (fun i => ¬ (0 < hA.eigenvalues i)) with ht
  set V := eigSpan hAE s with hV
  set W := eigSpan hA t with hW
  -- the two eigenspaces meet trivially
  have hdisj : V ⊓ W = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    obtain ⟨hxV, hxW⟩ := Submodule.mem_inf.mp hx
    have h1 : θ * ‖x‖ ^ 2 < qf (A + E) x :=
      qf_gt_of_mem_eigSpan hAE (fun j hj => (Finset.mem_filter.mp hj).2) hxV hx0
    have h2 : qf A x ≤ 0 * ‖x‖ ^ 2 :=
      qf_le_of_mem_eigSpan hA (fun j hj => not_lt.mp (Finset.mem_filter.mp hj).2) hxW
    have h3 : qf E x ≤ θ * ‖x‖ ^ 2 :=
      qf_le_of_eigenvalues_le hE (fun j => (abs_le.mp (hEθ j)).2) x
    rw [qf_add] at h1
    nlinarith [h1, h2, h3]
  -- hence the dimensions add up to at most `d`
  have hsum : finrank ℂ V + finrank ℂ W ≤ d := by
    have hkey := Submodule.finrank_sup_add_finrank_inf_eq V W
    have hle : finrank ℂ (V ⊔ W : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
        ≤ finrank ℂ (EuclideanSpace ℂ (Fin d)) := Submodule.finrank_le _
    rw [hdisj, finrank_bot, add_zero] at hkey
    rw [finrank_euclideanSpace_fin] at hle
    omega
  rw [hV, hW, finrank_eigSpan, finrank_eigSpan] at hsum
  have hcompl : (Finset.univ.filter (fun i => 0 < hA.eigenvalues i)).card + t.card
      = d := by
    rw [ht, Finset.card_filter_add_card_filter_not]
    simp
  have hposIndex : posIndex hA = (Finset.univ.filter (fun i => 0 < hA.eigenvalues i)).card := by
    rw [posIndex, posIndexAbove, Set.toFinset_setOf]
  have hposAbove : posIndexAbove hAE θ = s.card := by
    rw [posIndexAbove, hs, Set.toFinset_setOf]
  rw [hposAbove, hposIndex]
  omega

end Zeta23Redux.LinAlg

