import Mathlib

/-!
# Konig Lt
Category: Frontier — Set Theory
Target: Infinity.konig_lt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

universe u v

namespace Infinity

/-- Key intermediate lemma: a pointwise strict inequality between two cardinal-valued
families yields a strict inequality between the sum of the first family and the product
of the second one.  This is the content of König's theorem, packaged so that the final
statement follows immediately. -/
theorem konig_lt_aux {ι : Type u} (a b : ι → Cardinal.{v})
    (h : ∀ i, a i < b i) : Cardinal.sum a < Cardinal.prod b :=
  Cardinal.sum_lt_prod a b h

/-- **König's theorem** (strict sum-vs-product form): if `a i < b i` for every index `i`,
then `Cardinal.sum a < Cardinal.prod b`. -/
theorem konig_lt {ι : Type u} {a b : ι → Cardinal.{v}}
    (h : ∀ i, a i < b i) : Cardinal.sum a < Cardinal.prod b :=
  konig_lt_aux a b h

end Infinity

