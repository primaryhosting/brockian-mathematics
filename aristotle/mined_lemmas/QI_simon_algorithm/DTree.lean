import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
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

namespace QI

/-! ## The Boolean cube as an `𝔽₂`-vector space -/

/-- `n`-bit strings, viewed as the elementary abelian 2-group `(ℤ/2)ⁿ`;
addition is bitwise XOR. -/
abbrev V (n : ℕ) : Type := Fin n → ZMod 2


lemma DTree.run_congr {n : ℕ} {d : ℕ} (T : DTree n d) (f g : V n → V n)
    (h : ∀ x ∈ T.queries f, g x = f x) : T.run g = T.run f :=
  (DTree.run_queries_congr T f g h).2

/-- `f` is two-to-one with hidden shift `s`. -/
