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

lemma not_iWins_snoc_of_even {S : Set (ℕ → A)} {p : List A} (hp : Even p.length)
    (h : ¬ IWins S p) (a : A) : ¬ IWins S (p ++ [a]) := by
  classical
  rintro ⟨σ, hσ⟩
  refine h ⟨fun l => if l = p then a else σ l, fun x hx => ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  have hfirst : x p.length = a := by
    have := hx2 p.length le_rfl hp
    simpa [hx1] using this
  have hext : hist x (p ++ [a]).length = p ++ [a] := by
    have : (p ++ [a]).length = p.length + 1 := by simp
    rw [this, hist_succ, hx1, hfirst]
  refine hσ x ⟨hext, fun n hn hne => ?_⟩
  have hn' : p.length < n := by simpa using hn
  have hne' : hist x n ≠ p := by
    intro hcon
    have := congrArg List.length hcon
    simp at this
    omega
  have := hx2 n (le_of_lt hn') hne
  simpa [hne'] using this

