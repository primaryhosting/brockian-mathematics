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

theorem reach_trans {n d : Nat} (G : RotGraph n d) {a b c : Fin n}
    (h1 : G.Reach a b) (h2 : G.Reach b c) : G.Reach a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hadj ih => exact Reach.tail ih hadj

