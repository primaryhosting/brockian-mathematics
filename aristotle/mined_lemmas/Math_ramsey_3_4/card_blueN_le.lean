import Mathlib
/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
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

namespace Math

/-- `MonoClique c b T` says that all pairs of distinct vertices of `T` get colour `b`
under the (edge-)colouring `c`. -/

lemma card_blueN_le (hsymm : ∀ x y, c x y = c y x)
    (hR : ∀ T : Finset (Fin 9), T.card = 3 → ¬ MonoClique c true T)
    (hB : ∀ T : Finset (Fin 9), T.card = 4 → ¬ MonoClique c false T) (v : Fin 9) :
    (blueN c v).card ≤ 5 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨B, hBsub, hB6⟩ :=
    Finset.exists_subset_card_eq (s := blueN c v) (n := 6) (by omega)
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
  have hB'card : (B.erase w).card = 5 := by rw [Finset.card_erase_of_mem hw, hB6]
  have hsum : ((B.erase w).filter (fun u => c w u = true)).card
      + ((B.erase w).filter (fun u => c w u = false)).card = 5 := by
    have h := Finset.card_filter_add_card_filter_not (s := B.erase w)
      (p := fun u => c w u = true)
    have h2 : (B.erase w).filter (fun u => ¬ (c w u = true))
        = (B.erase w).filter (fun u => c w u = false) := by
      simp [Bool.not_eq_true]
    rw [h2] at h
    omega
  by_cases h3 : 3 ≤ ((B.erase w).filter (fun u => c w u = true)).card
  · obtain ⟨T, hTsub, hT3⟩ := Finset.exists_subset_card_eq h3
    refine blueN_no_false_triangle hsymm hB v T ?_ hT3 ?_
    · intro x hx
      exact hBsub (Finset.mem_of_mem_erase (Finset.mem_filter.mp (hTsub hx)).1)
    · refine (redN_mono_false hsymm hR w).subset ?_
      intro x hx
      have hx' := Finset.mem_filter.mp (hTsub hx)
      rw [mem_redN]
      exact ⟨Finset.ne_of_mem_erase hx'.1, hx'.2⟩
  · have h3b : 3 ≤ ((B.erase w).filter (fun u => c w u = false)).card := by omega
    obtain ⟨T, hTsub, hT3⟩ := Finset.exists_subset_card_eq h3b
    by_cases hred : MonoClique c true T
    · exact hR T hT3 hred
    · obtain ⟨x, hx, y, hy, hxy, hne⟩ : ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ c x y = false := by
        unfold MonoClique at hred
        push_neg at hred
        obtain ⟨x, hx, y, hy, hxy, h⟩ := hred
        exact ⟨x, hx, y, hy, hxy, by simpa using h⟩
      have hxm := Finset.mem_filter.mp (hTsub hx)
      have hym := Finset.mem_filter.mp (hTsub hy)
      refine blueN_no_false_triangle hsymm hB v {w, x, y} ?_ ?_ ?_
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hBsub hw
        · exact hBsub (Finset.mem_of_mem_erase hxm.1)
        · exact hBsub (Finset.mem_of_mem_erase hym.1)
      · rw [Finset.card_eq_three]
        exact ⟨w, x, y, (Finset.ne_of_mem_erase hxm.1).symm,
          (Finset.ne_of_mem_erase hym.1).symm, hxy, rfl⟩
      · have hT2 : MonoClique c false {x, y} := by
          intro a ha b hb hab
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact absurd rfl hab
          · exact hne
          · rw [hsymm]; exact hne
          · exact absurd rfl hab
        refine MonoClique.insert_vertex hsymm hT2 ?_
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact hxm.2
        · exact hym.2

