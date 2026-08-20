import Mathlib
import RequestProject.ArrowImpossibility

/-!
# Arrow impossibility, phrased with `Fintype`

`RequestProject.ArrowImpossibility` is deliberately self-contained (it uses no imports at
all), so it expresses finiteness of the voter set by `Frontier.FinitelyMany`.  This file
records the same statement with Mathlib's `Fintype` hypothesis.
-/

namespace Frontier

universe v


theorem exists_pivot {V : Type v} (T : List V → Prop)
    (hinv : ∀ u w : List V, (∀ x, x ∈ u ↔ x ∈ w) → (T u ↔ T w)) (h0 : ¬ T []) :
    ∀ s : List V, T s → ∃ (S : List V) (i : V), i ∉ S ∧ ¬ T S ∧ T (i :: S) := by
  intro s
  induction s with
  | nil => intro h; exact absurd h h0
  | cons a t ih =>
      intro h
      by_cases ht : T t
      · exact ih ht
      · by_cases ha : a ∈ t
        · refine absurd ((hinv (a :: t) t ?_).mp h) ht
          intro x
          rw [List.mem_cons]
          constructor
          · rintro (rfl | hx)
            · exact ha
            · exact hx
          · exact Or.inr
        · exact ⟨t, a, ha, ht, h⟩

/-! ## Profiles used in the proof -/

section Profiles

variable {V : Type v}

open Classical in
/-- The profile in which the voters of `S` rank `b` first (then `a`, then `c`) and all
other voters rank `b` last (after `a`, then `c`). -/
