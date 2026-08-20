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

/-
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Brockian

/-- A finite set of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture / singular series) if for every prime `p` it fails to
cover all residue classes modulo `p`. -/
def IsAdmissible (S : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ s ∈ S, (s : ZMod p) ≠ r

/-- Pigeonhole: a set of integers with fewer than `p` elements misses a residue mod `p`. -/
lemma exists_residue_not_covered {S : Finset ℤ} {p : ℕ} (hp : p.Prime) (h : S.card < p) :
    ∃ r : ZMod p, ∀ s ∈ S, (s : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ S.image (fun s : ℤ => (s : ZMod p)) := by
    intro r _
    obtain ⟨s, hs, hsr⟩ := hcon r
    exact Finset.mem_image.mpr ⟨s, hs, hsr⟩
  have hcard : (Fintype.card (ZMod p)) ≤ S.card := by
    calc (Fintype.card (ZMod p)) = (Finset.univ : Finset (ZMod p)).card := by
            simp [Finset.card_univ]
      _ ≤ (S.image (fun s : ℤ => (s : ZMod p))).card := Finset.card_le_card hsub
      _ ≤ S.card := Finset.card_image_le
  rw [ZMod.card p] at hcard
  omega

/-- An arithmetic progression of length `k` and common difference `d` is admissible
as soon as every prime `p ≤ k` divides `d`. -/
lemma isAdmissible_arithmeticProgression (t d : ℤ) (k : ℕ)
    (hd : ∀ p : ℕ, p.Prime → p ≤ k → (p : ℤ) ∣ d) :
    IsAdmissible ((Finset.range k).image (fun i : ℕ => t + d * (i : ℤ))) := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hpk : p ≤ k
  · refine ⟨(t : ZMod p) + 1, ?_⟩
    intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    have hd0 : ((d : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mpr (hd p hp hpk)
    have : ((t + d * (i : ℤ) : ℤ) : ZMod p) = (t : ZMod p) := by
      push_cast [hd0]
      ring
    rw [this]
    intro hcontra
    have : (0 : ZMod p) = 1 := by linear_combination hcontra
    exact zero_ne_one this
  · refine exists_residue_not_covered hp ?_
    have h1 : ((Finset.range k).image (fun i : ℕ => t + d * (i : ℤ))).card ≤ k := by
      calc ((Finset.range k).image (fun i : ℕ => t + d * (i : ℤ))).card
          ≤ (Finset.range k).card := Finset.card_image_le
        _ = k := Finset.card_range k
    omega

/-- The primorial-style modulus: the product of all primes below `n`. -/
def primesBelowProd (n : ℕ) : ℕ := ∏ p ∈ (Finset.range n).filter Nat.Prime, p

lemma primesBelowProd_pos (n : ℕ) : 0 < primesBelowProd n := by
  refine Finset.prod_pos ?_
  intro p hp
  exact (Finset.mem_filter.mp hp).2.pos

lemma dvd_primesBelowProd {n p : ℕ} (hp : p.Prime) (hpn : p < n) :
    p ∣ primesBelowProd n :=
  Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpn, hp⟩)

/-- **Singular Series Gaps 7280.**
There is a positive common difference `d` such that *every* arithmetic progression
of length `7280` with difference `d` is an admissible `7280`-tuple: it consists of
`7280` distinct integers and, for each prime `p`, omits at least one residue class
modulo `p`.  This extends the family of known admissible gap ranges to length `7280`. -/
theorem SingularSeriesGaps7280 :
    ∃ d : ℤ, 0 < d ∧ ∀ t : ℤ,
      ((Finset.range 7280).image (fun i : ℕ => t + d * (i : ℤ))).card = 7280 ∧
      IsAdmissible ((Finset.range 7280).image (fun i : ℕ => t + d * (i : ℤ))) := by
  refine ⟨(primesBelowProd 7280 : ℤ), ?_, ?_⟩
  · exact_mod_cast primesBelowProd_pos 7280
  · intro t
    have hdpos : (0 : ℤ) < (primesBelowProd 7280 : ℤ) := by
      exact_mod_cast primesBelowProd_pos 7280
    constructor
    · rw [Finset.card_image_of_injective _ ?_, Finset.card_range]
      intro i j hij
      have hmul : (primesBelowProd 7280 : ℤ) * (i : ℤ) = (primesBelowProd 7280 : ℤ) * (j : ℤ) := by
        linarith [hij]
      have := mul_left_cancel₀ (ne_of_gt hdpos) hmul
      exact_mod_cast this
    · refine isAdmissible_arithmeticProgression t _ 7280 ?_
      intro p hp hple
      have hplt : p < 7280 := by
        rcases lt_or_eq_of_le hple with h | h
        · exact h
        · exfalso
          rw [h] at hp
          norm_num at hp
      exact_mod_cast Int.natCast_dvd_natCast.mpr (dvd_primesBelowProd hp hplt)

end Brockian

#print axioms Brockian.SingularSeriesGaps7280

