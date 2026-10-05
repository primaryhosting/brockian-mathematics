import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
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

/-- A finite set of integers is *admissible* (in the Hardy–Littlewood sense) if for every
prime `p` it fails to cover all residue classes modulo `p`.  Equivalently, the singular
series attached to the tuple is nonzero. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- If a tuple has fewer elements than `p`, it cannot cover all residues mod `p`. -/
theorem exists_missed_residue_of_card_lt (p : ℕ) (hp : p.Prime) (H : Finset ℤ)
    (hcard : H.card < p) : ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) := by
    intro r _
    obtain ⟨h, hH, hr⟩ := hcon r
    exact Finset.mem_image.mpr ⟨h, hH, hr⟩
  have h1 : (Fintype.card (ZMod p)) ≤ (H.image (fun h : ℤ => (h : ZMod p))).card := by
    simpa [Finset.card_univ] using Finset.card_le_card hsub
  have h2 : (H.image (fun h : ℤ => (h : ZMod p))).card ≤ H.card := Finset.card_image_le
  rw [ZMod.card p] at h1
  omega

/-- Two-element tuples are admissible at every odd prime. -/
theorem admissible_pair_of_even (d : ℤ) (hd : Even d) : Admissible {0, d} := by
  intro p hp
  rcases eq_or_ne p 2 with rfl | hp2
  · have hd2 : ((d : ℤ) : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd d 2).mpr (by exact_mod_cast hd.two_dvd)
    refine ⟨1, ?_⟩
    intro h hh
    have hcases : h = 0 ∨ h = d := by simpa using hh
    rcases hcases with h1 | h1 <;> rw [h1]
    · simp only [Int.cast_zero]; decide
    · rw [hd2]; decide
  · refine exists_missed_residue_of_card_lt p hp _ ?_
    have hcard : ({0, d} : Finset ℤ).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    have hp2' := hp.two_le
    have : 3 ≤ p := by omega
    omega

/-- Odd gaps are never admissible: `{0, d}` covers both classes mod `2`. -/
theorem not_admissible_pair_of_odd (d : ℤ) (hd : ¬ Even d) : ¬ Admissible {0, d} := by
  intro hA
  obtain ⟨r, hr⟩ := hA 2 Nat.prime_two
  have h0 : ((0 : ℤ) : ZMod 2) ≠ r := hr 0 (by simp)
  have hdc : ((d : ℤ) : ZMod 2) ≠ r := hr d (by simp)
  have hodd : ((d : ℤ) : ZMod 2) = 1 := by
    rw [Int.not_even_iff_odd] at hd
    obtain ⟨k, hk⟩ := hd
    rw [hk]
    push_cast
    rw [show ((2 : ZMod 2) * (k : ZMod 2)) = 0 by
      rw [show (2 : ZMod 2) = 0 by decide]; ring]
    ring
  simp only [Int.cast_zero] at h0
  rw [hodd] at hdc
  have hall : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hall r with hr0 | hr1
  · exact h0 hr0.symm
  · exact hdc hr1.symm

/-- **Singular series gaps in the range 1350–1360.**

For every gap `d` with `1350 ≤ d ≤ 1360`, the pair `{0, d}` is admissible (equivalently, its
singular series is positive) exactly when `d` is even; and the three-element tuple
`{0, 1350, 1360}` is admissible. -/
theorem SingularSeriesGaps13501360 :
    (∀ d : ℕ, 1350 ≤ d → d ≤ 1360 → (Admissible {0, (d : ℤ)} ↔ Even d)) ∧
      Admissible {0, 1350, 1360} := by
  constructor
  · intro d _ _
    constructor
    · intro hA
      by_contra hodd
      exact not_admissible_pair_of_odd (d : ℤ) (by
        rw [Int.even_coe_nat]; exact hodd) hA
    · intro hd
      exact admissible_pair_of_even (d : ℤ) (by rwa [Int.even_coe_nat])
  · intro p hp
    by_cases hbig : 5 ≤ p
    · refine exists_missed_residue_of_card_lt p hp _ ?_
      have : ({0, 1350, 1360} : Finset ℤ).card ≤ 3 := by
        apply le_trans (Finset.card_insert_le _ _)
        have : ({1350, 1360} : Finset ℤ).card ≤ 2 :=
          le_trans (Finset.card_insert_le _ _) (by simp)
        omega
      omega
    · have hp2 := hp.two_le
      interval_cases p
      · refine ⟨1, ?_⟩
        intro h hh
        have : h = 0 ∨ h = 1350 ∨ h = 1360 := by simpa using hh
        rcases this with rfl | rfl | rfl <;> decide +kernel
      · refine ⟨2, ?_⟩
        intro h hh
        have : h = 0 ∨ h = 1350 ∨ h = 1360 := by simpa using hh
        rcases this with rfl | rfl | rfl <;> decide +kernel
      · exact absurd hp (by decide)

end Brockian

