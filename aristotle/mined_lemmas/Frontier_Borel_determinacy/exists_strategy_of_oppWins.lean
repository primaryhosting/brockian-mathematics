import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

variable {A : Type u}

/-! ## The game framework

We consider infinite two–player games on a set `A` of moves.  A *play* is a sequence
`x : ℕ → A`; player `0` chooses the moves `x n` with `n` even, player `1` chooses the moves
`x n` with `n` odd.  A *strategy* is a function `List A → A` assigning a move to every finite
position (the player only consults it at their own turns). -/

/-- The length-`n` initial segment of a play. -/

lemma exists_strategy_of_oppWins (i : ℕ) (T : List A → Prop) :
    ∀ {p : List A}, OppWins i T p →
      ∃ s : List A → A, ∀ x : ℕ → A, pre x p.length = p →
        (∀ n, p.length ≤ n → n % 2 ≠ i % 2 → x n = s (pre x n)) → ∃ n, ¬ T (pre x n) := by
  classical
  haveI : Inhabited A := Classical.inhabited_of_nonempty inferInstance
  intro p hp
  induction hp with
  | @out p hT =>
      refine ⟨fun _ => default, fun x hx _ => ⟨p.length, ?_⟩⟩
      rw [hx]; exact hT
  | @move p a hturn _ ih =>
      obtain ⟨s', hs'⟩ := ih
      refine ⟨fun q => if q = p then a else s' q, ?_⟩
      intro x hx hcons
      have h0 : x p.length = a := by
        have h1 := hcons p.length le_rfl hturn
        rw [hx] at h1
        simpa using h1
      have hlen : (p ++ [a]).length = p.length + 1 := by simp
      have hx1 : pre x (p ++ [a]).length = p ++ [a] := by
        rw [hlen, pre_succ, hx, h0]
      refine hs' x hx1 (fun n hn hpar => ?_)
      rw [hlen] at hn
      have hne : pre x n ≠ p := by
        intro hq
        have := congrArg List.length hq
        simp at this
        omega
      have h2 := hcons n (by omega) hpar
      simpa [hne] using h2
  | @all p hturn _ ih =>
      choose s' hs' using ih
      refine ⟨fun q => if p.length < q.length then s' (q.getD p.length default) q else default, ?_⟩
      intro x hx hcons
      have hlen : (p ++ [x p.length]).length = p.length + 1 := by simp
      have hx1 : pre x (p ++ [x p.length]).length = p ++ [x p.length] := by
        rw [hlen, pre_succ, hx]
      refine hs' (x p.length) x hx1 (fun n hn hpar => ?_)
      rw [hlen] at hn
      have hlt : p.length < n := by omega
      have h2 := hcons n (le_of_lt hlt) hpar
      rw [h2]
      have h3 : (pre x n).getD p.length default = x p.length := pre_getD x hlt default
      simp only [pre_length]
      rw [if_pos hlt, h3]

variable [TopologicalSpace A] [DiscreteTopology A]

omit [Nonempty A] in
/-- A closed set is determined by finite initial segments: a play outside a closed set has a
finite initial segment witnessing this. -/
