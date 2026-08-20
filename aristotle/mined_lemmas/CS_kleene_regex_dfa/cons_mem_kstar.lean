import Mathlib

/-!
# Antimirov partial derivatives and finiteness of left quotients

This file develops Antimirov's partial derivatives of a regular expression, and uses them to
show that a language described by a regular expression has only finitely many left quotients.
Combined with the Myhill–Nerode theorem this gives the "regular expression → DFA" direction of
Kleene's theorem.
-/

namespace CS

open RegularExpression

variable {α : Type*}

/-- The language of a set of regular expressions: the union of the languages they describe. -/

theorem cons_mem_kstar {L : Language α} {x y : List α} (hx : x ∈ L) (hy : y ∈ L∗) :
    x ++ y ∈ L∗ := by
  rw [Language.mem_kstar] at hy ⊢
  obtain ⟨ls, rfl, hls⟩ := hy
  refine ⟨x :: ls, by simp, ?_⟩
  intro z hz
  rcases List.mem_cons.1 hz with rfl | hz
  · exact hx
  · exact hls z hz

/-- Kleene's recursion: adding a new allowed intermediate state `k`. -/
