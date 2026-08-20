import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

variable {V : Type*} [DecidableEq V]

/-- The neighbours of `v` inside the vertex set `s`. -/

theorem fiveColorable_of_fourDegenerate :
    ∀ (n : ℕ) (s : Finset V) (G : SimpleGraph V), s.card ≤ n → FourDegenerate s G →
      FiveColorable s G := by
  intro n
  induction n with
  | zero =>
      intro s G hs _
      have : s = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hs)
      subst this
      exact ⟨fun _ => 0, by simp [IsProperColoring]⟩
  | succ n ih =>
      intro s G hs hdeg
      rcases Finset.eq_empty_or_nonempty s with rfl | hne
      · exact ⟨fun _ => 0, by simp [IsProperColoring]⟩
      obtain ⟨v, hv, hd⟩ := hdeg s (Finset.Subset.refl s) hne
      have hcard : (s.erase v).card ≤ n := by
        have := Finset.card_erase_of_mem hv
        omega
      have hdeg' : FourDegenerate (s.erase v) G := fun t ht =>
        hdeg t (ht.trans (Finset.erase_subset _ _))
      obtain ⟨c', hc'⟩ := ih (s.erase v) G hcard hdeg'
      obtain ⟨f, hf⟩ := exists_free_color (nbrs s G v) c' hd
      refine ⟨Function.update c' v f, ?_⟩
      intro x hx y hy hadj
      by_cases hxv : x = v
      · subst hxv
        have hyx : y ≠ x := (hadj.ne).symm
        have hy' : y ∈ nbrs s G x := mem_nbrs.2 ⟨hy, hyx, hadj⟩
        simp only [Function.update_apply, if_neg hyx]
        exact fun h => hf y hy' h.symm
      · by_cases hyv : y = v
        · subst hyv
          have hxy : x ≠ y := hadj.ne
          have hx' : x ∈ nbrs s G y := mem_nbrs.2 ⟨hx, hxy, hadj.symm⟩
          simp only [Function.update_apply, if_neg hxy]
          exact fun h => hf x hx' h
        · simp only [Function.update_apply, if_neg hxv, if_neg hyv]
          exact hc' x (Finset.mem_erase.2 ⟨hxv, hx⟩) y (Finset.mem_erase.2 ⟨hyv, hy⟩) hadj

/-- Every `4`-degenerate finite graph is `5`-colourable. -/
