/-
# Plunnecke Ruzsa Shadow
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.plunnecke_ruzsa_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Plunnecke Ruzsa Shadow
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.plunnecke_ruzsa_shadow
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

namespace AdditiveComb

/-- Difference sets of integers: `#(C - B) = #(B - C)`, since one is the pointwise
negation of the other. -/
theorem card_sub_comm (B C : Finset ℤ) : (C - B).card = (B - C).card := by
  rw [← Finset.card_neg (B - C)]
  congr 1
  ext x
  simp [Finset.mem_sub]

/-- **Ruzsa's triangle inequality** (the engine of the Plünnecke–Ruzsa theorem):
for finite nonempty sets `A`, `B`, `C` of integers,
`#(A - C) * #B ≤ #(A - B) * #(B - C)`.

The nonemptiness hypotheses are stated as requested, but turn out to be unnecessary:
the inequality holds for all finite sets. -/
theorem plunnecke_ruzsa_shadow (A B C : Finset ℤ)
    (_hA : A.Nonempty) (_hB : B.Nonempty) (_hC : C.Nonempty) :
    (A - C).card * B.card ≤ (A - B).card * (B - C).card := by
  have h := Finset.ruzsa_triangle_inequality_sub_sub_sub A B C
  rwa [card_sub_comm B C] at h

end AdditiveComb

