import Mathlib

/-!
# Plunnecke Ruzsa Shadow
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.plunnecke_ruzsa_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` to be the very first command of a file, so the required
-- header comment is placed immediately after the single `import Mathlib` line.

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

/-- Difference sets are swapped by negation: `B - C = -(C - B)`. -/
lemma sub_eq_neg_sub_swap (B C : Finset ℤ) : B - C = -(C - B) := by
  ext x
  simp [Finset.mem_sub]

/-- Difference sets of swapped arguments have the same cardinality. -/
lemma card_sub_comm (B C : Finset ℤ) : (B - C).card = (C - B).card := by
  rw [sub_eq_neg_sub_swap B C, Finset.card_neg]

/-- **Ruzsa's triangle inequality** (the engine of the Plünnecke–Ruzsa inequality):
for finite sets `A`, `B`, `C` of integers,
`|A - C| * |B| ≤ |A - B| * |B - C|`.

The nonemptiness hypotheses are stated because the problem statement asks for nonempty sets,
but the inequality holds unconditionally, so they are not used in the proof.

The core step is Mathlib's `Finset.ruzsa_triangle_inequality_sub_sub_sub`
(the additive version of `Finset.ruzsa_triangle_inequality_div_div_div`), combined with
`card_sub_comm` to rewrite `|C - B|` as `|B - C|`. -/
theorem plunnecke_ruzsa_shadow (A B C : Finset ℤ)
    (_hA : A.Nonempty) (_hB : B.Nonempty) (_hC : C.Nonempty) :
    (A - C).card * B.card ≤ (A - B).card * (B - C).card := by
  have h := Finset.ruzsa_triangle_inequality_sub_sub_sub A B C
  rwa [← card_sub_comm B C] at h

end AdditiveComb

