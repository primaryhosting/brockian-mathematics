import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem exists_buildList_singleton (w : α → ℝ) (ts : List (HTree α)) (hne : ts ≠ []) :
    ∃ t : HTree α, buildList w ts = [t] := by
  have h := buildList_length_eq_one w ts.length ts rfl hne
  match hbl : buildList w ts, h with
  | [t], _ => exact ⟨t, rfl⟩

variable (α) in
/-- The initial list of one-leaf trees, one for each symbol. -/
