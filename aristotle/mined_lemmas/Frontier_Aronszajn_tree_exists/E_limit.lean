/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Ordinal Set Cardinal
open scoped Classical

namespace Frontier

/-- The first uncountable ordinal `ω₁`. -/

theorem E_limit {a : Ordinal} (h0 : a ≠ 0) (hs : ¬ ∃ b, a = b + 1) (x : Ordinal) :
    E a x = if hx : ∃ n, x < cseq a n then Eaux a (Nat.find hx) x else 0 := by
  have key : ∀ (n : ℕ) (y : Ordinal),
      (Nat.rec (motive := fun _ => Ordinal → ℕ) (fun _ => 0)
        (fun m fm z => if z < cseq a m then fm z
          else max (E (cseq a (m + 1)) z) m) n : Ordinal → ℕ) y = Eaux a n y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih => intro y; rw [Eaux_succ]; simp only []; split <;> simp [ih]
  rw [E_eq]; unfold Estep
  rw [dif_neg h0, dif_neg hs]
  split
  · exact key _ _
  · rfl

/-! ### The two invariants -/

/-- `f` is finite-to-one below `a`. -/
