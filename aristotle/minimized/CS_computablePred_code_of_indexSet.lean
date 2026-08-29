/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- The index set of a semantic property `P` of partial functions: the set of natural
numbers `n` such that the partial recursive function computed by the `n`-th code
satisfies `P`. -/

def indexSet (P : (ℕ →. ℕ) → Prop) : Set ℕ :=
  {n : ℕ | P (eval (Denumerable.ofNat Code n))}

/-- If the index set of a semantic property is decidable, then so is the property viewed
as a property of codes. -/
