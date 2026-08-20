import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The real quadratic form `x ↦ re ⟪x, M x⟫` associated to a matrix `M`. -/

theorem weyl_posIndexAbove {A E : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hE : E.IsHermitian) (theta : ℝ)
    (hbound : ∀ i, |hE.eigenvalues i| ≤ theta) :
    posIndexAbove (hA.add hE) theta ≤ posIndex hA := by
  classical
  set hAE : (A + E).IsHermitian := hA.add hE with hAEdef
  set S₁ : Finset (Fin d) := Finset.univ.filter fun i => theta < hAE.eigenvalues i with hS1
  set P₁ : Finset (Fin d) := Finset.univ.filter fun i => 0 < hA.eigenvalues i with hP1
  set T₁ : Finset (Fin d) := Finset.univ.filter fun i => ¬ (0 < hA.eigenvalues i) with hT1
  set S : Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
    Submodule.span ℂ (hAE.eigenvectorBasis '' (S₁ : Set (Fin d))) with hSdef
  set T : Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
    Submodule.span ℂ (hA.eigenvectorBasis '' (T₁ : Set (Fin d))) with hTdef
  have hdisj : S ⊓ T = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hxm
    by_contra hx0
    obtain ⟨hxS, hxT⟩ := Submodule.mem_inf.1 hxm
    have h1 : theta * ‖x‖ ^ 2 < qform (A + E) x :=
      qform_gt_of_inner_eq_zero hAE S₁
        (fun i hi => by simpa [hS1] using hi)
        (fun i hi => inner_eq_zero_of_mem_span _ _ hxS hi) hx0
    have h2 : qform E x ≤ theta * ‖x‖ ^ 2 :=
      qform_le hE (fun i => (abs_le.1 (hbound i)).2) x
    have h3 : qform A x ≤ 0 :=
      qform_nonpos_of_inner_eq_zero hA T₁
        (fun i hi => by
          have := (Finset.mem_filter.1 (hT1 ▸ hi)).2
          linarith [not_lt.1 this])
        (fun i hi => inner_eq_zero_of_mem_span _ _ hxT hi)
    rw [qform_add] at h1
    linarith
  have hfr := Submodule.finrank_sup_add_finrank_inf_eq S T
  rw [hdisj] at hfr
  have hle : Module.finrank ℂ (S ⊔ T : Submodule ℂ (EuclideanSpace ℂ (Fin d))) ≤ d := by
    have h := Submodule.finrank_le (S ⊔ T)
    rwa [finrank_euclideanSpace_fin] at h
  have hSc : Module.finrank ℂ S = S₁.card := finrank_span_image _ _
  have hTc : Module.finrank ℂ T = T₁.card := finrank_span_image _ _
  have hcard : P₁.card + T₁.card = d := by
    rw [hP1, hT1, Finset.card_filter_add_card_filter_not]
    simp
  have hbot : Module.finrank ℂ (⊥ : Submodule ℂ (EuclideanSpace ℂ (Fin d))) = 0 := by simp
  rw [hbot, hSc, hTc] at hfr
  show S₁.card ≤ P₁.card
  omega

end Zeta23Redux.LinAlg

