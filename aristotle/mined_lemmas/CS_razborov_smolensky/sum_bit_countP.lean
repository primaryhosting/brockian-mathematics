import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma sum_bit_countP {α : Type*} (w : α → Bool) (L : List α) :
    (L.map (fun j => bit q (w j))).sum = ((L.countP w : ℕ) : ZMod q) := by
  induction L with
  | nil => simp [bit]
  | cons a L ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
      cases w a <;> simp [bit]
      ring

