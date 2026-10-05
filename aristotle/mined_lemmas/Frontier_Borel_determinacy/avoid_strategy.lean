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

theorem avoid_strategy {T S : List A → Prop} {p : List A} (h : ¬ Force T S p) :
    ∃ s : List A → A, ∀ x : ℕ → A, takePrefix x p.length = p →
      Consistent (fun q => ¬ T q) s x p.length → ∀ n, p.length ≤ n → ¬ S (takePrefix x n) := by
  classical
  have key : ∀ q : List A, ∃ a : A, ¬ Force T S q → ¬ T q → ¬ Force T S (q ++ [a]) := by
    intro q
    by_cases hq : ¬ Force T S q ∧ ¬ T q
    · have : ∃ a : A, ¬ Force T S (q ++ [a]) := by
        by_contra hcon
        push_neg at hcon
        exact hq.1 (Force.opp hq.2 (fun a => hcon a))
      obtain ⟨a, ha⟩ := this
      exact ⟨a, fun _ _ => ha⟩
    · exact ⟨Classical.arbitrary A, fun h1 h2 => absurd ⟨h1, h2⟩ hq⟩
  choose f hf using key
  refine ⟨f, ?_⟩
  intro x hx H
  have main : ∀ n, p.length ≤ n → ¬ Force T S (takePrefix x n) := by
    intro n
    induction n with
    | zero =>
        intro hn
        have hp0 : p.length = 0 := Nat.le_zero.mp hn
        rw [← hp0, hx]
        exact h
    | succ n IH =>
        intro hn
        rcases Nat.lt_or_ge n p.length with hlt | hge
        · have : p.length = n + 1 := by omega
          rw [← this, hx]
          exact h
        · have hIH := IH hge
          rw [takePrefix_succ]
          by_cases hT : T (takePrefix x n)
          · intro hF
            exact hIH (Force.reach hT (x n) hF)
          · have hval : x n = f (takePrefix x n) := H n hge hT
            rw [hval]
            exact hf _ hIH hT
  intro n hn hS
  exact main n hn (Force.here hS)

/-!
### Gale–Stewart: open and closed games are determined
-/

/-- Combinatorial closedness: membership in `W` is determined by all finite prefixes. -/
