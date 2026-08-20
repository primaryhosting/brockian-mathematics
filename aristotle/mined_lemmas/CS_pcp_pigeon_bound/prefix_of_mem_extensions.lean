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

/-- The finite set of all binary words (lists of booleans) of length `n`. -/

theorem prefix_of_mem_extensions {N : ℕ} {w l : List Bool} (hl : l ∈ extensions N w) :
    w <+: l := by
  simp only [extensions, Finset.mem_image] at hl
  obtain ⟨u, _, rfl⟩ := hl
  exact List.prefix_append w u

/-- **Kraft's inequality.**  For any finite prefix-free binary code `S` (a finite set of
binary words no one of which is a proper prefix of another), the sum of `2 ^ (-ℓ)` over the
codeword lengths `ℓ` is at most `1`. -/
