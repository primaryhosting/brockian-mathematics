/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian

/-- `H` is an *admissible* tuple of integers: for every prime `p` there is a residue class
mod `p` which is avoided by every element of `H`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ H, ¬ ((p : ℤ) ∣ (x - (r : ℤ)))

/-- `nu H p` is the number of residue classes mod `p` occupied by the elements of `H`. -/
noncomputable def nu (H : Finset ℤ) (p : ℕ) : ℕ :=
  ((Finset.range p).filter (fun r : ℕ => ∃ x ∈ H, ((p : ℤ) ∣ (x - (r : ℤ))))).card

/-- The local factor at the prime `p` of the Hardy–Littlewood singular series of `H`,
namely `(1 - ν_H(p)/p) * (1 - 1/p)^{-|H|}`. -/
noncomputable def localFactor (H : Finset ℤ) (p : ℕ) : ℝ :=
  (1 - (nu H p : ℝ) / (p : ℝ)) * (1 - 1 / (p : ℝ)) ^ (-(H.card : ℤ))

/-- The truncation of the singular series of `H` to the primes below `N`. -/
noncomputable def singularSeriesPartial (H : Finset ℤ) (N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range N).filter Nat.Prime, localFactor H p

/-- For an admissible tuple, strictly fewer than `p` residue classes mod `p` are occupied. -/
theorem nu_lt_of_admissible {H : Finset ℤ} (hH : Admissible H) {p : ℕ} (hp : p.Prime) :
    nu H p < p := by
  obtain ⟨r, hrp, hr⟩ := hH p hp
  have hsub : ((Finset.range p).filter
      (fun r : ℕ => ∃ x ∈ H, ((p : ℤ) ∣ (x - (r : ℤ))))) ⊂ Finset.range p := by
    refine Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.mpr ⟨r, ?_, ?_⟩
    · exact Finset.mem_range.mpr hrp
    · simp only [Finset.mem_filter, Finset.mem_range, not_and]
      intro _
      push_neg
      intro x hx
      exact hr x hx
  have := Finset.card_lt_card hsub
  simpa [nu] using this

/-- Every local factor of the singular series of an admissible tuple is positive. -/
theorem localFactor_pos {H : Finset ℤ} (hH : Admissible H) {p : ℕ} (hp : p.Prime) :
    0 < localFactor H p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h1 : 0 < 1 - (nu H p : ℝ) / (p : ℝ) := by
    have : (nu H p : ℝ) < (p : ℝ) := by exact_mod_cast nu_lt_of_admissible hH hp
    have := (div_lt_one hp0).mpr this
    linarith
  have h2 : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one hp0]; linarith
    linarith
  exact mul_pos h1 (zpow_pos h2 _)

/-- Every truncation of the singular series of an admissible tuple is positive. -/
theorem singularSeriesPartial_pos {H : Finset ℤ} (hH : Admissible H) (N : ℕ) :
    0 < singularSeriesPartial H N := by
  refine Finset.prod_pos ?_
  intro p hp
  exact localFactor_pos hH (Finset.mem_filter.mp hp).2

/-- A gap `d` which is even gives an admissible pair `{0, d}`. -/
theorem admissible_pair_of_even {d : ℕ} (hd : Even d) :
    Admissible ({0, (d : ℤ)} : Finset ℤ) := by
  intro p hp
  rcases eq_or_lt_of_le hp.two_le with h2 | h3
  · -- p = 2 : take the residue class 1
    refine ⟨1, by omega, ?_⟩
    intro x hx
    have hp2 : p = 2 := h2.symm
    subst hp2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    obtain ⟨k, hk⟩ := hd
    rcases hx with rfl | rfl
    · decide
    · intro hdvd
      rw [hk] at hdvd
      push_cast at hdvd
      omega
  · -- p ≥ 3 : one of the residue classes 1, 2 is free
    by_cases hd1 : (p : ℤ) ∣ ((d : ℤ) - 1)
    · refine ⟨2, by omega, ?_⟩
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · intro hdvd
        have : (p : ℤ) ∣ 2 := by
          simpa using hdvd.neg_right
        have := Int.le_of_dvd (by norm_num) this
        have : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast h3
        omega
      · intro hdvd
        have : (p : ℤ) ∣ (((d : ℤ) - 1) - ((d : ℤ) - 2)) := dvd_sub hd1 hdvd
        norm_num at this
        have hp1 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) this
        have : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast h3
        omega
    · refine ⟨1, by omega, ?_⟩
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · intro hdvd
        have : (p : ℤ) ∣ 1 := by simpa using hdvd.neg_right
        have hp1 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) this
        have : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast h3
        omega
      · exact hd1

/-- An odd gap `d` never gives an admissible pair `{0, d}`: the prime `2` is obstructed. -/
theorem not_admissible_pair_of_odd {d : ℕ} (hd : Odd d) :
    ¬ Admissible ({0, (d : ℤ)} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr2, hr⟩ := h 2 Nat.prime_two
  obtain ⟨k, hk⟩ := hd
  interval_cases r
  · exact hr 0 (by simp) (by simp)
  · refine hr (d : ℤ) (by simp) ?_
    rw [hk]
    push_cast
    omega

/-- Admissibility of the pair `{0, d}` is exactly evenness of the gap `d`. -/
theorem admissible_pair_iff_even (d : ℕ) :
    Admissible ({0, (d : ℤ)} : Finset ℤ) ↔ Even d := by
  constructor
  · intro h
    by_contra hodd
    exact not_admissible_pair_of_odd (Nat.odd_iff.mpr (Nat.not_even_iff.mp hodd)) h
  · exact admissible_pair_of_even

/-- **The admissible gap range 1450–1460.**
Among the gaps `d` with `1450 ≤ d ≤ 1460`, the admissible ones (i.e. those for which the
pair `{0, d}` is an admissible tuple) are exactly `1450, 1452, 1454, 1456, 1458, 1460`;
and for each such gap every truncation of the Hardy–Littlewood singular series of `{0, d}`
is positive. -/
theorem SingularSeriesGaps14501460 :
    ((Finset.Icc 1450 1460).filter
        (fun d : ℕ => Admissible ({0, (d : ℤ)} : Finset ℤ))
      = ({1450, 1452, 1454, 1456, 1458, 1460} : Finset ℕ)) ∧
    (∀ d ∈ ({1450, 1452, 1454, 1456, 1458, 1460} : Finset ℕ), ∀ N : ℕ,
      0 < singularSeriesPartial ({0, (d : ℤ)} : Finset ℤ) N) := by
  constructor
  · ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
      admissible_pair_iff_even, Nat.even_iff]
    omega
  · intro d hd N
    refine singularSeriesPartial_pos (admissible_pair_of_even ?_) N
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rw [Nat.even_iff]
    omega

end Brockian

