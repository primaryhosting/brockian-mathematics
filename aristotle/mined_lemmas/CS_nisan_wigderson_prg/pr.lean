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

noncomputable def pr {α : Type*} [Fintype α] (p : α → Bool) : ℝ := 𝔼 a, ind (p a)

/-! ### The Nisan–Wigderson generator -/

/-- The Nisan–Wigderson generator built from a combinatorial design `S` (given by `m` injective
maps `Fin n → Fin ℓ`, i.e. `m` subsets of size `n` of the `ℓ` seed bits) and a hard function
`f : (Fin n → Bool) → Bool`.  On seed `x` it outputs the `m` bits `f (x restricted to Sᵢ)`. -/
