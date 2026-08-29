import Mathlib

/-!
# Regular expressions define regular languages

This file proves the "easy" direction of Kleene's theorem: the language matched by a regular
expression is accepted by some DFA with finitely many states (`Language.IsRegular`).

The proof goes through the Myhill–Nerode characterisation
`Language.isRegular_iff_finite_range_leftQuotient`: a language is regular iff it has finitely
many left quotients.
-/

open Language Computability

namespace Kleene

variable {α : Type*}

/-- The union of a family of languages, as a language. -/

theorem isRegular_matches' (P : RegularExpression α) : P.matches'.IsRegular := by
  induction P with
  | zero => simpa using isRegular_zero
  | epsilon => simpa using isRegular_one
  | char a => simpa [RegularExpression.matches'] using isRegular_singleton a
  | plus P Q hP hQ => simpa [RegularExpression.matches'] using hP.add hQ
  | comp P Q hP hQ => simpa [RegularExpression.matches'] using isRegular_mul hP hQ
  | star P hP => simpa [RegularExpression.matches'] using isRegular_kstar hP

end Kleene

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

