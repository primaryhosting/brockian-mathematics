import Mathlib

/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
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

/-- The residues modulo `p` covered by the tuple `H`. -/

theorem admissible_iff_singularFactor_ne_zero (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → singularFactor H p ≠ 0 := by
  constructor
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hcard : (coveredResidues H p).card < p := card_coveredResidues_lt_iff.mpr (hH p hp)
    have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
    intro hzero
    rw [singularFactor, sub_eq_zero, eq_div_iff (ne_of_gt hp0), one_mul] at hzero
    have : (coveredResidues H p).card = p := by exact_mod_cast hzero.symm
    omega
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    refine card_coveredResidues_lt_iff.mp ?_
    have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
    have hle : (coveredResidues H p).card ≤ p := by
      simpa [ZMod.card] using Finset.card_le_univ (coveredResidues H p)
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      refine hH p hp ?_
      rw [singularFactor, h, div_self (ne_of_gt hp0), sub_self]

/-- The residues covered by an arithmetic progression tuple. -/
