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

/-- Auxiliary: in an additive commutative group, the difference set `B - C` has the same
cardinality as `C - B`, since negation is a bijection between them. -/
theorem card_sub_comm (B C : Finset ℤ) : (C - B).card = (B - C).card := by
  classical
  refine Finset.card_bij (fun x _ => -x) ?_ ?_ ?_
  · rintro x hx
    obtain ⟨c, hc, b, hb, rfl⟩ := Finset.mem_sub.1 hx
    exact Finset.mem_sub.2 ⟨b, hb, c, hc, by ring⟩
  · intro x _ y _ h
    simpa using congrArg Neg.neg h
  · intro y hy
    obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_sub.1 hy
    exact ⟨c - b, Finset.mem_sub.2 ⟨c, hc, b, hb, rfl⟩, by ring⟩

/-- **Ruzsa's triangle inequality** for finite sets of integers: for finite (possibly empty)
sets `A`, `B`, `C` of integers,
`|A - C| * |B| ≤ |A - B| * |B - C|`.
The nonemptiness hypotheses on `A`, `B`, `C` are stated as requested but are not needed. -/
theorem plunnecke_ruzsa_shadow (A B C : Finset ℤ)
    (_hA : A.Nonempty) (_hB : B.Nonempty) (_hC : C.Nonempty) :
    (A - C).card * B.card ≤ (A - B).card * (B - C).card := by
  have h := Finset.ruzsa_triangle_inequality_sub_sub_sub A B C
  rwa [card_sub_comm B C] at h

end AdditiveComb

