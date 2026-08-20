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

set_option grind.warning false

namespace CS

variable {α : Type*} [LinearOrder α]

/-- Merge two lists, assumed sorted, into one list. -/

theorem sorted_merge : ∀ l₁ l₂ : List α, l₁.Pairwise (· ≤ ·) → l₂.Pairwise (· ≤ ·) →
    (merge l₁ l₂).Pairwise (· ≤ ·)
  | [], l, _, h => by simpa using h
  | a :: as, [], h, _ => by simpa using h
  | a :: as, b :: bs, h₁, h₂ => by
      rw [List.pairwise_cons] at h₁ h₂
      rw [merge_cons_cons]
      split
      · rename_i hab
        rw [List.pairwise_cons]
        refine ⟨?_, sorted_merge as (b :: bs) h₁.2 (List.pairwise_cons.2 h₂)⟩
        intro x hx
        rcases mem_merge.1 hx with hx | hx
        · exact h₁.1 x hx
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hab
          · exact le_trans hab (h₂.1 x hx)
      · rename_i hab
        have hba : b ≤ a := le_of_not_ge hab
        rw [List.pairwise_cons]
        refine ⟨?_, sorted_merge (a :: as) bs (List.pairwise_cons.2 h₁) h₂.2⟩
        intro x hx
        rcases mem_merge.1 hx with hx | hx
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hba
          · exact le_trans hba (h₁.1 x hx)
        · exact h₂.1 x hx
  termination_by l₁ l₂ => l₁.length + l₂.length

