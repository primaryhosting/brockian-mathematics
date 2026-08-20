/-
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace GaleStewart

universe u

variable {X : Type u}

/-- The list of the first `n` moves of the play `a`. -/

theorem winT_strategy {W : Set (List X)} :
    ∀ {p : List X}, WinT W p → ∃ σ : List X → X,
      ∀ a : ℕ → X, hist a p.length = p →
        (∀ n, p.length ≤ n → Even n → a n = σ (hist a n)) → ∃ m, hist a m ∈ W := by
  classical
  intro p t
  induction t with
  | @base p hp =>
      refine ⟨fun _ => Classical.arbitrary X, fun a ha _ => ⟨p.length, ?_⟩⟩
      rw [ha]; exact hp
  | @moveI p x hev t ih =>
      obtain ⟨σ', hσ'⟩ := ih
      refine ⟨fun q => if q.length = p.length then x else σ' q, fun a ha hfollow => ?_⟩
      have hx : a p.length = x := by
        have := hfollow p.length le_rfl hev
        rw [this, ha]
        simp
      have hnext : hist a (p ++ [x]).length = p ++ [x] := by
        have : (p ++ [x]).length = p.length + 1 := by simp
        rw [this, hist_succ, ha, hx]
      refine hσ' a hnext ?_
      intro n hn hne
      have hlen : (p ++ [x]).length = p.length + 1 := by simp
      rw [hlen] at hn
      have h1 : a n = (fun q => if q.length = p.length then x else σ' q) (hist a n) :=
        hfollow n (by omega) hne
      rw [h1]
      have hne2 : (hist a n).length ≠ p.length := by simp; omega
      simp only [hne2, if_false]
  | @moveII p hodd f ih =>
      choose g hg using ih
      refine ⟨fun q => g (q.getD p.length (Classical.arbitrary X)) q, fun a ha hfollow => ?_⟩
      set x := a p.length
      have hnext : hist a (p ++ [x]).length = p ++ [x] := by
        have : (p ++ [x]).length = p.length + 1 := by simp
        rw [this, hist_succ, ha]
      refine hg x a hnext ?_
      intro n hn hne
      have hlen : (p ++ [x]).length = p.length + 1 := by simp
      rw [hlen] at hn
      have h1 : a n = g ((hist a n).getD p.length (Classical.arbitrary X)) (hist a n) :=
        hfollow n (by omega) hne
      rw [h1, hist_getD a _ (show p.length < n by omega)]

/-- If player I has no derivation from the empty position, then player II has a strategy
keeping the play out of `W` forever. -/
