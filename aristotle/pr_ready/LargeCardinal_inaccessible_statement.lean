/-!
# Inaccessible Statement
Category: Frontier Wave 2 (deeper machinery)
Target: LargeCardinal.inaccessible_statement
Statement: Define an inaccessible-cardinal predicate as a Lean Prop (a cardinal kappa that is uncountable, regular, and a strong limit) and prove ONLY its well-formedness / self-equivalence: define Inaccessible (k : Cardinal) : Prop := Cardinal.aleph0 < k AND k.IsRegular AND (forall c, c < k -> 2^c < k); then prove (exists k, Inaccessible k) <-> (exists k, Inaccessible k). Existence of inaccessibles is IN...
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace LargeCardinal

/-- A cardinal `k` is *inaccessible* if it is uncountable, regular, and a strong limit. -/
def Inaccessible (k : Cardinal.{0}) : Prop :=
  Cardinal.aleph0 < k ∧ k.IsRegular ∧ ∀ c : Cardinal.{0}, c < k → 2 ^ c < k

/-- Well-formedness of the inaccessible-cardinal statement: the assertion that an inaccessible
cardinal exists is equivalent to itself.  (Existence of inaccessible cardinals is independent
of ZFC and is *not* asserted here.) -/
theorem inaccessible_statement :
    (∃ k : Cardinal.{0}, Inaccessible k) ↔ (∃ k : Cardinal.{0}, Inaccessible k) :=
  Iff.rfl

end LargeCardinal

