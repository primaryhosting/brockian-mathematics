/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset
open scoped BigOperators

namespace CS

/-! ### Basic probabilistic vocabulary

All probabilities are uniform probabilities over finite types, expressed as expectations
of `{0,1}`-valued indicator functions. -/

/-- The `{0,1}`-valued indicator of a boolean. -/

def nwGen {n m ℓ : ℕ} (S : Fin m → Fin n → Fin ℓ) (f : (Fin n → Bool) → Bool)
    (x : Fin ℓ → Bool) : Fin m → Bool := fun i => f fun k => x (S i k)

/-- `u` depends on at most `d` of its `n` input bits. -/
