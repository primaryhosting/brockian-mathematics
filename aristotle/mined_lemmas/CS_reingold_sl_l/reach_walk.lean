/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (it uses only the Lean 4 core library), so that the
required header comment above can literally be the first thing in the file.
-/

namespace CS

/-! ## Counting -/

/-- `HasCard α N` says that the type `α` embeds into `Fin N`; i.e. `α` has at most `N`
elements, so an element of `α` can be stored in `⌈log₂ N⌉` bits. -/

theorem reach_walk {n d : Nat} (G : RotGraph n d) (s : Fin n) (l : List (Fin d)) :
    G.Reach s (G.walk s l) := by
  induction l generalizing s with
  | nil => exact Reach.refl _
  | cons a l ih =>
      have h1 : G.Reach s (G.step1 s a) := Reach.tail (Reach.refl s) ⟨a, rfl⟩
      exact G.reach_trans h1 (ih _)

