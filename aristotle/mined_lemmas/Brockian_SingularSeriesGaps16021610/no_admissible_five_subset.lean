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

theorem no_admissible_five_subset (H : Finset ℕ) (hsub : H ⊆ Finset.Icc 1602 1610)
    (hcard : H.card = 5) : ¬ IsAdmissible H := by
  intro hadm
  by_cases hmix : (∃ x ∈ H, x % 2 = 0) ∧ (∃ y ∈ H, y % 2 = 1)
  · -- both parities occur, so `H` covers all residues mod `2`
    obtain ⟨⟨x, hx, hx2⟩, ⟨y, hy, hy2⟩⟩ := hmix
    refine hadm 2 (by norm_num) ?_
    intro r hr
    interval_cases r
    · exact ⟨x, hx, hx2⟩
    · exact ⟨y, hy, hy2⟩
  · -- all elements have the same parity
    rw [not_and_or] at hmix
    push_neg at hmix
    rcases hmix with hodd | heven
    · -- every element is odd: at most four such numbers in the range
      have hsub' : H ⊆ ({1603, 1605, 1607, 1609} : Finset ℕ) := by
        intro x hx
        have h1 := Finset.mem_Icc.mp (hsub hx)
        have h2 := hodd x hx
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have := Finset.card_le_card hsub'
      rw [hcard] at this
      revert this
      decide
    · -- every element is even: `H` is exactly the five even numbers
      have hsub' : H ⊆ evens := by
        intro x hx
        have h1 := Finset.mem_Icc.mp (hsub hx)
        have h2 := heven x hx
        simp only [evens, Finset.mem_insert, Finset.mem_singleton]
        omega
      have hEq : H = evens :=
        Finset.eq_of_subset_of_card_le hsub' (by rw [hcard, evens_card])
      exact evens_not_admissible (hEq ▸ hadm)

/-- **Singular Series Gaps 16021610.**

Inside the gap range `[1602, 1610]` (nine consecutive integers) the tuple
`{1602, 1604, 1608, 1610}` is admissible — its singular series is non-zero — it has four
elements, and no five-element subset of the range is admissible.  Hence `4` is the exact
maximal size of an admissible tuple contained in `[1602, 1610]`. -/
