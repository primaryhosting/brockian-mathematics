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

/-
# Zorn
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.zorn
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Zorn
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.zorn
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace SetTheory

/-- **Zorn's lemma** for a preorder: if every chain (with respect to `≤`) has an upper
bound, then there exists a maximal element `m`, i.e. any `a` above `m` also satisfies
`a ≤ m`.

This follows directly from Mathlib's `exists_maximal_of_chains_bounded`
(`Mathlib/Order/Zorn.lean`), instantiated at the relation `(· ≤ ·)` with `le_trans`. -/

theorem zorn_isMax {α : Type*} [PartialOrder α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → ∃ ub, ∀ a ∈ c, a ≤ ub) :
    ∃ m : α, IsMax m :=
  zorn_le fun c hc => (h c hc).imp fun _ hub _ ha => hub _ ha

end SetTheory

