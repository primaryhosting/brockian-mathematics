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

noncomputable def glue {n ℓ : ℕ} (σ : Fin n → Fin ℓ) (z : Fin n → Bool) (x0 : Fin ℓ → Bool) :
    Fin ℓ → Bool :=
  fun i => if h : ∃ k, σ k = i then z h.choose else x0 i

/-! ### Auxiliary lemmas -/

