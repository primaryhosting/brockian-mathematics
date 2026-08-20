import RequestProject.Degree

open Finset

namespace Frontier

/-! # Huang's sensitivity theorem: `s(f) ≥ √(deg f)`

Using the full-degree case `Frontier.huang_sensitivity` together with a restriction argument
to a subcube, we obtain the general statement: the sensitivity of a Boolean function is at
least the square root of its degree.
-/

section Coeff

variable {n : ℕ}

/-- Uniqueness of the multilinear representation. -/

lemma finrank_suppSub (S : Finset (Q n)) :
    Module.finrank ℝ (suppSub S) = S.card := by
  have hcard : Module.finrank ℝ (Q n → ℝ) = 2 ^ n := by
    simp [Module.finrank_fintype_fun_eq_card]
  set f : (Q n → ℝ) →ₗ[ℝ] ({x : Q n // x ∉ S} → ℝ) :=
    LinearMap.funLeft ℝ ℝ (Subtype.val : {x : Q n // x ∉ S} → Q n) with hf
  have hsurj : Function.Surjective f :=
    LinearMap.funLeft_surjective_of_injective ℝ ℝ _ Subtype.val_injective
  have h1 : Module.finrank ℝ (LinearMap.range f) + Module.finrank ℝ (LinearMap.ker f)
      = Module.finrank ℝ (Q n → ℝ) := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, hcard] at h1
  have h2 : Module.finrank ℝ ({x : Q n // x ∉ S} → ℝ) = 2 ^ n - S.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl]
    simp [Fintype.card_coe]
  have h3 : S.card ≤ 2 ^ n := by
    have := Finset.card_le_univ S
    simpa using this
  rw [h2, hf] at h1
  unfold suppSub
  generalize (2 : ℕ) ^ n = M at h1 h3
  omega

/-- The existence of an eigenvector of the signed adjacency operator supported in `S`. -/
