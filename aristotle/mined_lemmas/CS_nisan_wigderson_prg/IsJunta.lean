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

def IsJunta {n : ℕ} (d : ℕ) (u : (Fin n → Bool) → Bool) : Prop :=
  ∃ T : Finset (Fin n), T.card ≤ d ∧
    ∀ z z' : Fin n → Bool, (∀ k ∈ T, z k = z' k) → u z = u z'

/-- The class of *next-bit predictors* arising from the distinguisher `D` in the
Nisan–Wigderson argument at hybrid step `t`: a predictor is obtained by feeding `D` with
`d`-juntas of the input `z` in the first `t` coordinates, hard-wired advice bits in the
remaining coordinates, and possibly negating the output. -/
