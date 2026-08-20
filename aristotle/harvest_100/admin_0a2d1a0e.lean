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

namespace Brockian

/-- A finite set of non-negative integers `H` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuple conjecture) if for every prime `p` the elements of `H`
do not cover all residue classes modulo `p`.  Equivalently, the local factor of the
singular series `𝔖(H)` attached to `H` is non-zero at every prime. -/
def IsAdmissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r < p, ∀ h ∈ H, h % p ≠ r

/-- Large primes never obstruct admissibility: if `p` exceeds the size of `H`, then the
residues of `H` modulo `p` cannot exhaust the `p` residue classes.

The counting step is `Finset.card_le_card_of_injOn`-style reasoning packaged as
`Finset.card_image_le` together with `Finset.exists_mem_notMem_of_card_lt_card`. -/
theorem exists_missing_residue_of_card_lt {H : Finset ℕ} {p : ℕ} (hp : H.card < p) :
    ∃ r < p, ∀ h ∈ H, h % p ≠ r := by
  have hsub : H.image (· % p) ⊆ Finset.range p := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨h, _, rfl⟩ := hx
    exact Finset.mem_range.2 (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) hp))
  have hcard : (H.image (· % p)).card < (Finset.range p).card := by
    calc (H.image (· % p)).card ≤ H.card := Finset.card_image_le
    _ < p := hp
    _ = (Finset.range p).card := (Finset.card_range p).symm
  obtain ⟨r, hr, hr'⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨r, Finset.mem_range.1 hr, ?_⟩
  intro h hh hmod
  exact hr' (Finset.mem_image.2 ⟨h, hh, hmod⟩)

/-- The `5`-tuple `{0, 2, 6, 8, 12}` is admissible: it is a prime constellation pattern of
diameter `12`. -/
theorem isAdmissible_zero_two_six_eight_twelve :
    IsAdmissible ({0, 2, 6, 8, 12} : Finset ℕ) := by
  intro p hp
  rcases lt_or_ge p 6 with h | h
  · interval_cases p <;> revert hp <;> decide
  · have h6 : ({0, 2, 6, 8, 12} : Finset ℕ).card < 6 := by decide
    exact exists_missing_residue_of_card_lt (h6.trans_le h)

/-- The admissible gap range: the tuple `{0, 2, 6, 8, 12}` has `5` elements, minimum `0`,
maximum `12`, and hence diameter `12`. -/
theorem gap_range_zero_two_six_eight_twelve :
    ({0, 2, 6, 8, 12} : Finset ℕ).card = 5 ∧
      ({0, 2, 6, 8, 12} : Finset ℕ).max' ⟨0, by decide⟩ -
        ({0, 2, 6, 8, 12} : Finset ℕ).min' ⟨0, by decide⟩ = 12 := by
  constructor
  · decide
  · have hmax : ({0, 2, 6, 8, 12} : Finset ℕ).max' ⟨0, by decide⟩ = 12 := by
      apply le_antisymm
      · exact Finset.max'_le _ _ _ (by decide)
      · exact Finset.le_max' _ _ (by decide)
    have hmin : ({0, 2, 6, 8, 12} : Finset ℕ).min' ⟨0, by decide⟩ = 0 := Nat.le_zero.1
      (Finset.min'_le _ _ (by decide))
    rw [hmax, hmin]

/-- **Singular Series Gaps 16021610.**

`{0, 2, 6, 8, 12}` is an admissible `5`-tuple (every prime misses at least one residue
class), it has exactly `5` elements, and its gap range (diameter) is `12`. -/
theorem SingularSeriesGaps16021610 :
    IsAdmissible ({0, 2, 6, 8, 12} : Finset ℕ) ∧
      ({0, 2, 6, 8, 12} : Finset ℕ).card = 5 ∧
      ({0, 2, 6, 8, 12} : Finset ℕ).max' ⟨0, by decide⟩ -
        ({0, 2, 6, 8, 12} : Finset ℕ).min' ⟨0, by decide⟩ = 12 :=
  ⟨isAdmissible_zero_two_six_eight_twelve, gap_range_zero_two_six_eight_twelve⟩

end Brockian

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

