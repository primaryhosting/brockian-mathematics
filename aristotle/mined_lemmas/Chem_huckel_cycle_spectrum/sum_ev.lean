/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Polynomial Matrix SimpleGraph Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma sum_ev (m : Fin n) : ∑ k : Fin n, ev (k * m) = if m = 0 then (n : ℂ) else 0 := by
  have h : ∀ k : Fin n, ev (k * m) = ev m ^ (k : ℕ) := fun k => ev_mul k m
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun j => ev m ^ j) n]
  by_cases hm : m = 0
  · subst hm
    simp [ev_zero]
  · rw [if_neg hm, geom_sum_eq, ev_pow_card]
    · simp
    · intro hcon
      exact hm ((ev_eq_one_iff m).1 hcon)

