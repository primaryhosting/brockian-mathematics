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

theorem partrec_eval (c : Code) : Nat.Partrec (eval c) :=
  Partrec.nat_iff.1 (eval_part.comp (Computable.const c) Computable.id)

/-- **Rice's theorem, dichotomy form.** The index set of a property `P` of partial functions
is recursive if and only if `P` is trivial on the partial recursive functions, i.e. it holds
of all of them or of none of them. -/
