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

/-- A finite set of nonnegative integer offsets (a "gap pattern") is *admissible* if for
every prime `p` the offsets fail to cover all residue classes modulo `p`.  Equivalently,
the singular series `𝔖(H) = ∏_p (1 - ν_H(p)/p)(1 - 1/p)^{-|H|}` attached to `H` in the
Hardy–Littlewood prime `k`-tuple conjecture is nonzero. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- Pigeonhole: a pattern with fewer elements than `p` cannot cover all residues mod `p`. -/
theorem exists_missing_residue_of_card_lt
    (H : Finset ℕ) (p : ℕ) (hp : p.Prime) (hc : H.card < p) :
    ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard :
      (H.image (fun n : ℕ => (n : ZMod p))).card < (Finset.univ : Finset (ZMod p)).card := by
    calc (H.image (fun n : ℕ => (n : ZMod p))).card ≤ H.card := Finset.card_image_le
      _ < p := hc
      _ = Fintype.card (ZMod p) := (ZMod.card p).symm
      _ = (Finset.univ : Finset (ZMod p)).card := rfl
  obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨r, fun h hh hEq => hr (Finset.mem_image.2 ⟨h, hh, hEq⟩)⟩

/-- Admissibility only has to be checked at the primes `p ≤ |H|`. -/
theorem admissible_of_small_primes (H : Finset ℕ)
    (h : ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r) :
    Admissible H := by
  intro p hp
  rcases lt_or_ge H.card p with hc | hc
  · exact exists_missing_residue_of_card_lt H p hp hc
  · exact h p hp hc

/-- The sextuple pattern `{0, 4, 6, 10, 12, 16}` of diameter `16`. -/
def gapPattern1240 : Finset ℕ := {0, 4, 6, 10, 12, 16}

/-- The octuple pattern `{0, 2, 6, 8, 12, 18, 20, 26}` of diameter `26`. -/
def gapPattern1250 : Finset ℕ := {0, 2, 6, 8, 12, 18, 20, 26}

theorem admissible_gapPattern1240 : Admissible gapPattern1240 := by
  apply admissible_of_small_primes
  intro p hp hple
  have hcard : gapPattern1240.card = 6 := by decide
  rw [hcard] at hple
  have h2 := hp.two_le
  interval_cases p <;> first
    | exact absurd hp (by decide)
    | (unfold gapPattern1240; decide)

theorem admissible_gapPattern1250 : Admissible gapPattern1250 := by
  apply admissible_of_small_primes
  intro p hp hple
  have hcard : gapPattern1250.card = 8 := by decide
  rw [hcard] at hple
  have h2 := hp.two_le
  interval_cases p <;> first
    | exact absurd hp (by decide)
    | (unfold gapPattern1250; decide)

/-- **Singular Series Gaps 12401250.**  Two new admissible gap patterns: the sextuple
`{0, 4, 6, 10, 12, 16}` (diameter `16`) and the octuple `{0, 2, 6, 8, 12, 18, 20, 26}`
(diameter `26`) are both admissible, so the associated singular series are nonzero and
the Hardy–Littlewood conjecture predicts infinitely many prime constellations of each
shape. -/
theorem SingularSeriesGaps12401250 :
    Admissible gapPattern1240 ∧ gapPattern1240.card = 6 ∧
      Admissible gapPattern1250 ∧ gapPattern1250.card = 8 :=
  ⟨admissible_gapPattern1240, by decide, admissible_gapPattern1250, by decide⟩

end Brockian

