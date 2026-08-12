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

namespace CS

/-- **Pigeonhole for hash functions**: any hash function from a finite type with
`n + 1` elements to a finite type with `n` elements has a collision, i.e. two
distinct inputs mapping to the same output. -/
theorem pigeonhole_hash {Keys Buckets : Type*} [Fintype Keys] [Fintype Buckets]
    {n : ℕ} (hK : Fintype.card Keys = n + 1) (hB : Fintype.card Buckets = n)
    (hash : Keys → Buckets) :
    ∃ a b : Keys, a ≠ b ∧ hash a = hash b := by
  have hlt : Fintype.card Buckets < Fintype.card Keys := by omega
  obtain ⟨a, b, hab, h⟩ := Fintype.exists_ne_map_eq_of_card_lt hash hlt
  exact ⟨a, b, hab, h⟩

end CS

