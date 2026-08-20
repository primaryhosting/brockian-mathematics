import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib
import Brockian.SierpinskiCovering

/-!
# Sierpiński numbers: Mathlib-flavoured restatement

`Brockian/SierpinskiCovering.lean` must be import-free (its mandated header comment has to
precede everything, and Lean requires `import` to come first), so it develops the covering
argument using only the core `Nat` API.  Here we restate its conclusions with the usual
Mathlib vocabulary: `Nat.Prime`, `Odd`, and `Set.Infinite`.
-/

namespace Brockian.SierpinskiCovering

/-- A composite number is not prime. -/

theorem setOf_isSierpinskiNumber_infinite : {k : ℕ | IsSierpinskiNumber k}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨k, hk, hks⟩ := SierpinskiProblem N
  exact absurd (hN hks) (by omega)

end Brockian.SierpinskiCovering

/-!
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no `import` line): Lean 4 requires every `import`
command to precede all other syntax, including module doc comments, so the mandated header
above forces the development to rely only on the automatically available `Init` prelude.
A Mathlib-flavoured restatement (with `Nat.Prime`, `Odd` and `Set.Infinite`) is provided in
`Brockian/SierpinskiMathlib.lean`, which imports this module.
-/

namespace Brockian.SierpinskiCovering

/-- `IsComposite N` means `N` has a nontrivial divisor; in particular `N` is not prime. -/
