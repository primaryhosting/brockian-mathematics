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

def vAt {n d : Nat} (G : RotGraph n d) (D : Nat) (hd : 0 < d) (s : Fin n) (j : Nat) : Fin n :=
  G.cwalk hd s (j / (D + 1)) (j % (D + 1))

