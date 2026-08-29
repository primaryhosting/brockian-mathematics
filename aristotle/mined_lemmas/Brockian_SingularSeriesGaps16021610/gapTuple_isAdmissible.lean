/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
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

/-- `H` covers all residue classes modulo `p`. -/

theorem gapTuple_isAdmissible : IsAdmissible gapTuple := by
  intro p hp hcov
  have hle : p ≤ 4 := gapTuple_card ▸ card_le_of_coversAllResidues hcov
  have hp2 : 2 ≤ p := hp.two_le
  have key : ∀ q : ℕ, (∃ h ∈ gapTuple, h % q = 1) → q = 2 ∨ q = 3 → False := by
    intro q hq hq23
    obtain ⟨h, hmem, hh⟩ := hq
    simp only [gapTuple, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hq23 with rfl | rfl <;> rcases hmem with rfl | rfl | rfl | rfl <;> omega
  have h1 : ∃ h ∈ gapTuple, h % p = 1 := hcov 1 (by omega)
  interval_cases p
  · exact key 2 h1 (Or.inl rfl)
  · exact key 3 h1 (Or.inr rfl)
  · exact absurd hp (by decide)

/-- The even numbers of the range `[1602, 1610]`. -/
