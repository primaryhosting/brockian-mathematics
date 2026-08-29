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
def CoversAllResidues (H : Finset ℕ) (p : ℕ) : Prop :=
  ∀ r < p, ∃ h ∈ H, h % p = r

/-- A finite set of integers is *admissible* if for every prime `p` it misses at least one
residue class modulo `p`.  This is exactly the condition for the singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p)(1 - 1/p)^{-|H|}` to be non-zero. -/
def IsAdmissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ CoversAllResidues H p

/-- Covering all residues mod `p` forces `p ≤ |H|`. -/
theorem card_le_of_coversAllResidues {H : Finset ℕ} {p : ℕ}
    (h : CoversAllResidues H p) : p ≤ H.card := by
  have hsub : Finset.range p ⊆ H.image (fun x => x % p) := by
    intro r hr
    obtain ⟨x, hx, hxr⟩ := h r (Finset.mem_range.mp hr)
    exact Finset.mem_image.2 ⟨x, hx, hxr⟩
  calc p = (Finset.range p).card := (Finset.card_range p).symm
    _ ≤ (H.image (fun x => x % p)).card := Finset.card_le_card hsub
    _ ≤ H.card := Finset.card_image_le

/-- The concrete tuple inside the gap range `[1602, 1610]`. -/
def gapTuple : Finset ℕ := {1602, 1604, 1608, 1610}

theorem gapTuple_card : gapTuple.card = 4 := by decide

theorem gapTuple_subset : gapTuple ⊆ Finset.Icc 1602 1610 := by
  intro x hx
  simp only [gapTuple, Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [Finset.mem_Icc]
  rcases hx with h | h | h | h <;> omega

/-- The tuple `{1602, 1604, 1608, 1610}` (diameter 8) is admissible. -/
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
private def evens : Finset ℕ := {1602, 1604, 1606, 1608, 1610}

private theorem evens_card : evens.card = 5 := by decide

/-- The set of all five even numbers in `[1602, 1610]` is not admissible: it covers all
residues modulo `3`. -/
private theorem evens_not_admissible : ¬ IsAdmissible evens := by
  intro hadm
  refine hadm 3 (by norm_num) ?_
  intro r hr
  interval_cases r
  · exact ⟨1602, by decide, by norm_num⟩
  · exact ⟨1606, by decide, by norm_num⟩
  · exact ⟨1604, by decide, by norm_num⟩

/-- No `5`-element subset of the gap range `[1602, 1610]` is admissible. -/
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
theorem SingularSeriesGaps16021610 :
    gapTuple ⊆ Finset.Icc 1602 1610 ∧ gapTuple.card = 4 ∧ IsAdmissible gapTuple ∧
      ∀ H ⊆ Finset.Icc 1602 1610, H.card = 5 → ¬ IsAdmissible H :=
  ⟨gapTuple_subset, gapTuple_card, gapTuple_isAdmissible,
    fun H hsub hcard => no_admissible_five_subset H hsub hcard⟩

end Brockian

