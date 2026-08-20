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

namespace Math

open Finset

/-- The finite intersection `t.inf' h A` of the sets `A i` for `i ∈ t` is indeed
`{a | ∀ i ∈ t, a ∈ A i}`. -/

theorem mem_inf'_iff {ι α : Type*} [DecidableEq α] {t : Finset ι} (h : t.Nonempty)
    (A : ι → Finset α) (a : α) : a ∈ t.inf' h A ↔ ∀ i ∈ t, a ∈ A i := by
  simp [Finset.mem_inf']

/-- **Inclusion-exclusion principle**:
`|⋃_{i ∈ s} A i| = ∑_{∅ ≠ S ⊆ s} (-1)^(|S|+1) |⋂_{i ∈ S} A i|`.

The sum ranges over all subsets `t` of the index set `s`; the empty subset contributes `0`,
and a nonempty subset `t` contributes `(-1)^(|t|+1) * |⋂_{i ∈ t} A i|`, where the intersection
is `t.inf' h A` (see `Math.mem_inf'_iff`). -/
