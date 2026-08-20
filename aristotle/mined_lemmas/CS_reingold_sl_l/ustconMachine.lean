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

def ustconMachine (n d D : Nat) (hd : 0 < d) : Machine n d where
  Mem := memT n d D
  size := n * (n * ((Tm d D + 1) * (n * 2)))
  card := hasCard_prod (hasCard_fin n)
    (hasCard_prod (hasCard_fin n)
      (hasCard_prod (hasCard_fin _) (hasCard_prod (hasCard_fin n) hasCard_bool)))
  init := fun s t => (s, t, ⟨0, by omega⟩, s, decide (s = t))
  query := qry D hd
  update := upd D
  out := fun m => m.2.2.2.2
  time := Tm d D

/-- The vertex visited at time `j`. -/
