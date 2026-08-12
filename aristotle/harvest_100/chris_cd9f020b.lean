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

namespace Brockian

/-- A finite set of integers is *admissible* (in the sense of the prime `k`-tuples
conjecture) if for every prime `p` it fails to cover all residue classes modulo `p`. -/
def Admissible (S : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ s ∈ S, (s : ZMod p) ≠ r

/-- The odd-prime Euler product occurring in the Hardy–Littlewood singular series for the
prime pair `(n, n + h)`:  `∏_{p ∣ h, p odd} (p - 1)/(p - 2)` when `h` is a nonzero even
number, and `0` otherwise (the singular series vanishes for odd gaps). -/
noncomputable def singularSeries (h : ℕ) : ℝ :=
  if Even h ∧ h ≠ 0 then
    ∏ p ∈ h.primeFactors.filter (fun p => p ≠ 2), ((p : ℝ) - 1) / ((p : ℝ) - 2)
  else 0

/-- For even `h`, the gap `h` reduces to `0` modulo `2`. -/
lemma cast_two_of_even {h : ℕ} (he : Even h) : ((h : ℤ) : ZMod 2) = 0 := by
  obtain ⟨k, hk⟩ := he
  subst hk
  push_cast
  ring_nf
  simp
  right
  rfl

/-- For odd `h`, the gap `h` reduces to `1` modulo `2`. -/
lemma cast_two_of_odd {h : ℕ} (ho : Odd h) : ((h : ℤ) : ZMod 2) = 1 := by
  obtain ⟨k, hk⟩ := ho
  subst hk
  push_cast
  ring_nf
  simp
  right
  rfl

/-- Modulo an odd prime, a two-element set of residues always misses a class. -/
lemma exists_avoiding_residue (p : ℕ) [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) (x : ZMod p) :
    ∃ r : ZMod p, r ≠ 0 ∧ r ≠ x := by
  have hcard : ({(0 : ZMod p), x} : Finset (ZMod p)).card < Fintype.card (ZMod p) := by
    have h1 : ({(0 : ZMod p), x} : Finset (ZMod p)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    have h2 : Fintype.card (ZMod p) = p := ZMod.card p
    omega
  obtain ⟨r, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (by simpa using hcard : _ < (Finset.univ : Finset (ZMod p)).card)
  exact ⟨r, by simp at hr; tauto, by simp at hr; tauto⟩

/-- The pair `{0, h}` is admissible exactly when the gap `h` is even. -/
theorem admissible_pair_iff_even (h : ℕ) :
    Admissible ({0, (h : ℤ)} : Finset ℤ) ↔ Even h := by
  constructor
  · intro H
    rcases Nat.even_or_odd h with he | ho
    · exact he
    · exfalso
      obtain ⟨r, hr⟩ := H 2 Nat.prime_two
      have h0 : ((0 : ℤ) : ZMod 2) ≠ r := hr 0 (by simp)
      have h1 : (((h : ℤ)) : ZMod 2) ≠ r := hr _ (by simp)
      rw [cast_two_of_odd ho] at h1
      simp only [Int.cast_zero] at h0
      fin_cases r <;> simp_all
  · intro he p hp
    haveI := Fact.mk hp
    rcases eq_or_ne p 2 with rfl | hp2
    · refine ⟨1, ?_⟩
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · simp only [Int.cast_zero]
        exact zero_ne_one
      · rw [cast_two_of_even he]
        exact zero_ne_one
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      obtain ⟨r, hr0, hrh⟩ := exists_avoiding_residue p hp3 ((h : ℤ) : ZMod p)
      refine ⟨r, ?_⟩
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · simpa using (Ne.symm hr0)
      · exact Ne.symm hrh

/-- The singular series of a nonzero even gap is strictly positive. -/
theorem singularSeries_pos_of_even {h : ℕ} (he : Even h) (hh : h ≠ 0) :
    0 < singularSeries h := by
  rw [singularSeries, if_pos ⟨he, hh⟩]
  refine Finset.prod_pos ?_
  intro p hp
  simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp
  obtain ⟨⟨hpp, _, _⟩, hp2⟩ := hp
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  have hp3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  apply div_pos <;> linarith

/-- The singular series vanishes for odd gaps. -/
theorem singularSeries_eq_zero_of_odd {h : ℕ} (ho : Odd h) : singularSeries h = 0 := by
  rw [singularSeries, if_neg]
  rintro ⟨he, -⟩
  exact (Nat.not_even_iff_odd.mpr ho) he

/-- **Admissible gap ranges 1240–1250.**  For every gap `h` with `1240 ≤ h ≤ 1250`, the pair
`{0, h}` is admissible if and only if `h` is even, and this happens exactly when the
Hardy–Littlewood singular series for the gap `h` is positive (it vanishes otherwise).

(The upper bound `h ≤ 1250` is kept because the statement is about the range 1240–1250, but
the proof only uses `1240 ≤ h` — indeed the underlying equivalences hold for all `h`.) -/
theorem SingularSeriesGaps12401250 :
    ∀ h : ℕ, 1240 ≤ h → h ≤ 1250 →
      (Admissible ({0, (h : ℤ)} : Finset ℤ) ↔ Even h) ∧
      (0 < singularSeries h ↔ Even h) ∧
      (¬ Even h → singularSeries h = 0) := by
  intro h h1 _
  have hh : h ≠ 0 := by omega
  refine ⟨admissible_pair_iff_even h, ⟨?_, ?_⟩, ?_⟩
  · intro hpos
    by_contra hodd
    rw [singularSeries_eq_zero_of_odd (Nat.not_even_iff_odd.mp hodd)] at hpos
    exact lt_irrefl 0 hpos
  · intro he
    exact singularSeries_pos_of_even he hh
  · intro hodd
    exact singularSeries_eq_zero_of_odd (Nat.not_even_iff_odd.mp hodd)

end Brockian

