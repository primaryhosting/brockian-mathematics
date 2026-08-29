/-
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
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

namespace Brockian

/-- A finite set of integers `H` (thought of as a tuple of shifts `h₁ < ⋯ < h_k`) is
*admissible* if for every prime `p` the elements of `H` do not cover all residue classes
modulo `p`; equivalently, some residue class mod `p` is missed by `H`.  This is the
classical admissibility condition from the Hardy–Littlewood prime `k`-tuple conjecture. -/

theorem AdmissibilityKTupleK4 (H : Finset ℤ) (hH : H.card = 4) :
    Admissible H ↔
      ((∃ a : ZMod 2, ∀ h ∈ H, (h : ZMod 2) ≠ a) ∧ (∃ a : ZMod 3, ∀ h ∈ H, (h : ZMod 3) ≠ a)) := by
  constructor
  · intro hadm
    exact ⟨hadm 2 Nat.prime_two, hadm 3 Nat.prime_three⟩
  · rintro ⟨h2, h3⟩ p hp
    rcases eq_or_ne p 2 with rfl | hp2
    · exact h2
    rcases eq_or_ne p 3 with rfl | hp3
    · exact h3
    refine missesResidue_of_card_lt H p hp ?_
    rw [hH]
    have h2le := hp.two_le
    have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
    omega

/-- The classical admissible `4`-tuple `(0, 2, 6, 8)`. -/
