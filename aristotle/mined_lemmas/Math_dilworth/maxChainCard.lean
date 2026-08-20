/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

variable {α : Type*} [Fintype α] [PartialOrder α]

open Classical in
/-- `chainHeight x` is the largest cardinality of a chain all of whose elements are `≤ x`. -/

noncomputable def maxChainCard (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  (Finset.univ : Finset (Finset α)).sup
    (fun s => if IsChain (· ≤ ·) (s : Set α) then s.card else 0)

/-- In a finite partial order there really is a longest chain, so the hypothesis of
`Math.dilworth` is always satisfiable. -/
