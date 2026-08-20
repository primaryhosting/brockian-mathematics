/-!
# Plunnecke Ruzsa Shadow
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.plunnecke_ruzsa_shadow
Statement: Ruzsa triangle inequality (the engine of Plunnecke-Ruzsa): for finite nonempty sets A B C of integers, (A - C).card * B.card <= (A - B).card * (B - C).card. Prove the Ruzsa triangle inequality. (Use Mathlib's Finset.card_sub_mul_le_card_sub_mul_card_sub or ruzsa_triangle if present.)
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

namespace AdditiveComb

/-- Difference sets are equicardinal up to swapping the order of the operands:
`|B - C| = |C - B|`, since `x ↦ -x` is a bijection between the two. -/
theorem card_sub_comm (B C : Finset ℤ) : (B - C).card = (C - B).card := by
  refine Finset.card_bij (fun x _ => -x) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_sub] at ha ⊢
    obtain ⟨b, hb, c, hc, rfl⟩ := ha
    exact ⟨c, hc, b, hb, by ring⟩
  · intro a _ b _ h
    simpa using h
  · intro a ha
    refine ⟨-a, ?_, by ring⟩
    simp only [Finset.mem_sub] at ha ⊢
    obtain ⟨c, hc, b, hb, rfl⟩ := ha
    exact ⟨b, hb, c, hc, by ring⟩

/-- **Ruzsa's triangle inequality** (the engine of the Plünnecke–Ruzsa inequality):
for finite nonempty sets `A`, `B`, `C` of integers,
`|A - C| * |B| ≤ |A - B| * |B - C|`.

This is Mathlib's `Finset.ruzsa_triangle_inequality_sub_sub_sub` (the additive version of
`Finset.ruzsa_triangle_inequality_div_div_div`), combined with `|C - B| = |B - C|`.
The nonemptiness hypotheses are not needed. -/
theorem plunnecke_ruzsa_shadow (A B C : Finset ℤ) (_hA : A.Nonempty) (_hB : B.Nonempty)
    (_hC : C.Nonempty) : (A - C).card * B.card ≤ (A - B).card * (B - C).card := by
  have h := Finset.ruzsa_triangle_inequality_sub_sub_sub A B C
  rwa [card_sub_comm B C]

end AdditiveComb

