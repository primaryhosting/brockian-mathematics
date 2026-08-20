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

lemma sgnp_flip_of_mem (p : Fin n → Prop) [DecidablePred p] (x : Q n) {j : Fin n}
    (hj : p j) : sgnp p (flipAt x j) = - sgnp p x := by
  by_cases hx : x j = true
  · have hmem : j ∈ univ.filter (fun k => p k ∧ x k = true) := by simp [hj, hx]
    have hset : univ.filter (fun k => p k ∧ (flipAt x j) k = true)
        = (univ.filter (fun k => p k ∧ x k = true)).erase j := by
      ext k
      by_cases hk : k = j
      · subst hk; simp [hx]
      · simp [flipAt_apply_of_ne _ hk, hk]
    have hcard : cnt p (flipAt x j) + 1 = cnt p x := by
      unfold cnt
      rw [hset, Finset.card_erase_of_mem hmem]
      exact Nat.succ_pred_eq_of_pos (Finset.card_pos.2 ⟨j, hmem⟩)
    unfold sgnp
    rw [← hcard]
    ring
  · have hx' : x j = false := by simpa using hx
    have hnot : j ∉ univ.filter (fun k => p k ∧ x k = true) := by simp [hx']
    have hset : univ.filter (fun k => p k ∧ (flipAt x j) k = true)
        = insert j (univ.filter (fun k => p k ∧ x k = true)) := by
      ext k
      by_cases hk : k = j
      · subst hk; simp [hx', hj]
      · simp [flipAt_apply_of_ne _ hk, hk]
    have hcard : cnt p (flipAt x j) = cnt p x + 1 := by
      unfold cnt; rw [hset, Finset.card_insert_of_notMem hnot]
    unfold sgnp
    rw [hcard]
    ring

end Sign

section Matrix

variable {n : ℕ}

/-- The Huang sign of the edge `{x, flipAt x i}`. -/
