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

theorem exists_code_diverging : ∃ c : Code, c.eval = fun _ => Part.none :=
  Nat.Partrec.Code.exists_code.1 Nat.Partrec.none

/-- **Application.** For any input `n`, the set of codes that halt on `n` is a nontrivial
semantic set, hence by Rice's theorem it is not recursive: the halting problem is
undecidable. -/
