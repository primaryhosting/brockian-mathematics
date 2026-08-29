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

/-- Difference sets of integers have the same cardinality when the roles of the two
sets are exchanged: `|B - C| = |C - B|`, since negation is a bijection between them. -/
theorem card_sub_comm_int (B C : Finset ℤ) : (B - C).card = (C - B).card := by
  refine Finset.card_bij (fun x _ => -x) ?_ ?_ ?_
  · intro a ha
    obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_sub.1 ha
    exact Finset.mem_sub.2 ⟨c, hc, b, hb, by ring⟩
  · intro a _ b _ h
    exact neg_injective h
  · intro a ha
    obtain ⟨c, hc, b, hb, rfl⟩ := Finset.mem_sub.1 ha
    exact ⟨b - c, Finset.mem_sub.2 ⟨b, hb, c, hc, rfl⟩, by ring⟩

/-- **Ruzsa's triangle inequality** (the engine of the Plünnecke–Ruzsa inequality):
for finite sets `A`, `B`, `C` of integers,
`|A - C| * |B| ≤ |A - B| * |B - C|`.

The nonemptiness hypotheses `hA`, `hB`, `hC` are kept because they are part of the
requested statement, but the inequality holds for arbitrary finite sets. -/
theorem plunnecke_ruzsa_shadow (A B C : Finset ℤ)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) :
    (A - C).card * B.card ≤ (A - B).card * (B - C).card := by
  have h := Finset.ruzsa_triangle_inequality_sub_sub_sub A B C
  rwa [← card_sub_comm_int B C] at h

end AdditiveComb

