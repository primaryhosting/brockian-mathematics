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

def IsNWPredictor {n m : ℕ} (d : ℕ) (D : (Fin m → Bool) → Bool) (t : ℕ)
    (g : (Fin n → Bool) → Bool) : Prop :=
  ∃ (u : Fin m → (Fin n → Bool) → Bool) (w : Fin m → Bool) (b : Bool),
    (∀ j, IsJunta d (u j)) ∧
    ∀ z, g z = xor b (D fun j => if (j : ℕ) < t then u j z else w j)

/-- The `t`-th hybrid distribution: the first `t` output bits come from the generator,
the remaining ones are uniformly random. -/
