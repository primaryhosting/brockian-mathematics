import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma card_filter_val_lt (p r : ℕ) (hr : r ≤ p) :
    (Finset.filter (fun i : Fin p => (i : ℕ) < r) Finset.univ).card = r := by
  classical
  have h : (Finset.filter (fun i : Fin p => (i : ℕ) < r) Finset.univ).image (Fin.val)
      = Finset.range r := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro ha; exact ⟨⟨a, lt_of_lt_of_le ha hr⟩, ha, rfl⟩
  have h2 : (Finset.filter (fun i : Fin p => (i : ℕ) < r) Finset.univ).card
      = ((Finset.filter (fun i : Fin p => (i : ℕ) < r) Finset.univ).image (Fin.val)).card :=
    (Finset.card_image_of_injective _ Fin.val_injective).symm
  rw [h2, h, Finset.card_range]

