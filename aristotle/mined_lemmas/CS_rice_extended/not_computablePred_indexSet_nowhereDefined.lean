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

set_option autoImplicit false

namespace CS

open Nat.Partrec.Code

/-- The index set of a property `P` of partial functions: the set of natural numbers `n`
such that the partial function computed by the `n`-th program satisfies `P`.

This is a *semantic* (extensional) set by construction: membership of `n` depends only on the
partial function `eval (ofNat Code n)` computed by the program with index `n`, not on the
program itself. -/

theorem not_computablePred_indexSet_nowhereDefined :
    ¬ ComputablePred (fun n : ℕ => n ∈ indexSet fun u : ℕ →. ℕ => ∀ m, ¬ (u m).Dom) :=
  rice_extended _ Nat.Partrec.none Nat.Partrec.zero (fun _ h => h.elim)
    (fun h => h 0 trivial)

end CS

