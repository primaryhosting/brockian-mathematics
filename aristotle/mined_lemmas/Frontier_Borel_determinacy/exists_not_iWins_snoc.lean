/-
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above repeats verbatim as a module docstring below; Lean 4 does not allow a
-- module docstring to precede the `import` commands.)

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

/-! ## Infinite two-player games on sequences -/

/-- A strategy is a map from the finite history of moves played so far to the next move. -/

lemma exists_not_iWins_snoc {S : Set (ℕ → A)} {p : List A}
    (h : ¬ IWins S p) : ∃ b : A, ¬ IWins S (p ++ [b]) := by
  by_contra hcon
  push_neg at hcon
  choose f hf using fun b => (hcon b)
  refine h ⟨fun l => f (l.getD p.length default) l, fun x hx => ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  set b := x p.length with hb
  refine hf b x ⟨?_, fun n hn hno => ?_⟩
  · have hlen : (p ++ [b]).length = p.length + 1 := by simp
    rw [hlen, hist_succ, hx1]
  · have hn' : p.length < n := by simpa using hn
    have hxn := hx2 n (le_of_lt hn') hno
    simp only [hist_getD x hn'] at hxn
    exact hxn

/-- **Gale–Stewart theorem** (base case of Borel determinacy): a game whose payoff set is open
is determined. -/
