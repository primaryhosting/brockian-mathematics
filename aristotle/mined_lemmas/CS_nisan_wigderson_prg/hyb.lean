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

def hyb {n m ℓ : ℕ} (S : Fin m → Fin n → Fin ℓ) (f : (Fin n → Bool) → Bool) (t : ℕ)
    (x : Fin ℓ → Bool) (y : Fin m → Bool) : Fin m → Bool :=
  fun i => if (i : ℕ) < t then nwGen S f x i else y i

/-- Probability that `D` accepts the `t`-th hybrid. -/
