/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Statement: The set of indices of a nontrivial semantic property is not recursive (Rice).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib.Computability.Halting

/-!
## Rice's theorem, extended form

We work with `Nat.Partrec.Code`, Mathlib's type of indices (codes) for partial recursive
functions `ℕ →. ℕ`, where `Code.eval : Code → (ℕ →. ℕ)` is the universal evaluation map.

A set `C` of codes is *semantic* if membership depends only on the partial function
computed, and *nontrivial* if it is neither empty nor everything.  Rice's theorem says
that such a `C` is never recursive.

The main theorem `CS.rice_extended` is proved directly from Kleene's recursion (fixed
point) theorem, and we then derive several extended forms: the complement is not
recursive either, the index-set formulation for a property of partial functions, and
the concrete instance that halting on a fixed input is undecidable.
-/

namespace CS

open Nat.Partrec (Code)

/-- A set of codes is *semantic* (extensional) when membership depends only on the
partial function computed by the code, not on the code itself. -/

theorem rice_extended_index_set (P : (ℕ →. ℕ) → Prop)
    (hf : ∃ cf : Code, P cf.eval) (hg : ∃ cg : Code, ¬ P cg.eval) :
    ¬ ComputablePred (fun c : Code => P c.eval) := by
  refine rice_extended {c : Code | P c.eval} (fun cf cg h => by simp only [Set.mem_setOf_eq, h])
    ⟨hf, hg⟩

/-- There is a code for the everywhere-undefined partial function. -/
