import Mathlib
/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

/-!
## Infinite two-player games of perfect information

We work with the Gale–Stewart game on a nonempty type `A`:  players I and II alternately
choose elements of `A`, player I moving first, producing an infinite play `x : ℕ → A`.
Player I wins the play iff `x ∈ W`.
-/

namespace Frontier

variable {A : Type*}

/-- The list of the first `n` moves of the play `x`. -/

theorem force_strategy {T S : List A → Prop} {p : List A} (h : Force T S p) :
    ∃ s : List A → A, ∀ x : ℕ → A, takePrefix x p.length = p →
      Consistent T s x p.length → ∃ n, S (takePrefix x n) := by
  classical
  induction h with
  | @here p hS =>
      exact ⟨fun _ => Classical.arbitrary A, fun x hx _ => ⟨p.length, by rw [hx]; exact hS⟩⟩
  | @reach p hp a _ IH =>
      obtain ⟨s', hs'⟩ := IH
      refine ⟨fun q => if q = p then a else s' q, fun x hx H => ?_⟩
      have h1 : x p.length = a := by
        have := H p.length le_rfl (by rw [hx]; exact hp)
        rw [hx] at this; simpa using this
      have h2 : takePrefix x (p.length + 1) = p ++ [a] := by
        rw [takePrefix_succ, hx, h1]
      have hlen : (p ++ [a]).length = p.length + 1 := by simp
      refine hs' x (by rw [hlen]; exact h2) ?_
      intro n hn hT
      rw [hlen] at hn
      have hval := H n (Nat.le_of_succ_le hn) hT
      have hne : takePrefix x n ≠ p := by
        intro hEq
        have := congrArg List.length hEq
        rw [length_takePrefix] at this
        omega
      simpa [hne] using hval
  | @opp p _ _ IH =>
      choose s' hs' using IH
      refine ⟨fun q => s' (q.getD p.length (Classical.arbitrary A)) q, fun x hx H => ?_⟩
      have h2 : takePrefix x (p.length + 1) = p ++ [x p.length] := by
        rw [takePrefix_succ, hx]
      have hlen : (p ++ [x p.length]).length = p.length + 1 := by simp
      refine hs' (x p.length) x (by rw [hlen]; exact h2) ?_
      intro n hn hT
      rw [hlen] at hn
      have hval := H n (Nat.le_of_succ_le hn) hT
      have hbeta : x n = s' ((takePrefix x n).getD p.length (Classical.arbitrary A))
          (takePrefix x n) := hval
      rwa [getD_takePrefix (show p.length < n by omega)] at hbeta

/-- If the `T`-player cannot force reaching `S` from `p`, then the opponent has a strategy
which avoids `S` forever. -/
