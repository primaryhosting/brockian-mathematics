/-
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
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

/-- A finite set of natural numbers is *admissible* when, for every prime `p`, its elements
omit at least one residue class modulo `p`.  This is exactly the classical condition under
which the singular series attached to the tuple is non-zero. -/

lemma exists_avoided_residue_of_two_lt {p : ℕ} (hp : p.Prime) (hp3 : 2 < p) (x y : ℕ) :
    ∃ a : ZMod p, (x : ZMod p) ≠ a ∧ (y : ZMod p) ≠ a := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hcard : ({(x : ZMod p), (y : ZMod p)} : Finset (ZMod p)).card < Finset.univ.card := by
    have h1 : ({(x : ZMod p), (y : ZMod p)} : Finset (ZMod p)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    have h2 : (Finset.univ : Finset (ZMod p)).card = p := by
      simp [ZMod.card]
    omega
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨a, ?_, ?_⟩ <;> intro h <;> apply ha <;> simp [← h]

/-- Elements of an admissible set all have the same parity. -/
