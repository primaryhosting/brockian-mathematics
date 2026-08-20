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
