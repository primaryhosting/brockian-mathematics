/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex

/-- The adjacency matrix of the cycle graph `C₇`, indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `7`. -/

theorem huckel_C7 (l : ℂ) :
    (∃ v : ZMod 7 → ℂ, v ≠ 0 ∧ C7adj.mulVec v = l • v) ↔
      ∃ k : Fin 7, l = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 7) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨v, hv, heq⟩
    -- the eigenvalue equation, entrywise
    have key : ∀ j : ZMod 7, v (j - 1) + v (j + 1) = l * v j := by
      intro j
      rw [← C7adj_mulVec, heq, Pi.smul_apply, smul_eq_mul]
    have h0 := key 0
    have h1 := key 1
    have h2 := key 2
    have h3 := key 3
    have h4 := key 4
    have h5 := key 5
    have h6 := key 6
    rw [show (0 : ZMod 7) - 1 = 6 from by decide, show (0 : ZMod 7) + 1 = 1 from by decide] at h0
    rw [show (1 : ZMod 7) - 1 = 0 from by decide, show (1 : ZMod 7) + 1 = 2 from by decide] at h1
    rw [show (2 : ZMod 7) - 1 = 1 from by decide, show (2 : ZMod 7) + 1 = 3 from by decide] at h2
    rw [show (3 : ZMod 7) - 1 = 2 from by decide, show (3 : ZMod 7) + 1 = 4 from by decide] at h3
    rw [show (4 : ZMod 7) - 1 = 3 from by decide, show (4 : ZMod 7) + 1 = 5 from by decide] at h4
    rw [show (5 : ZMod 7) - 1 = 4 from by decide, show (5 : ZMod 7) + 1 = 6 from by decide] at h5
    rw [show (6 : ZMod 7) - 1 = 5 from by decide, show (6 : ZMod 7) + 1 = 0 from by decide] at h6
    -- solve the recurrence in terms of `v 0` and `v 1`
    have e2 : v 2 = l * v 1 - v 0 := by linear_combination h1
    have e3 : v 3 = (l ^ 2 - 1) * v 1 - l * v 0 := by linear_combination h2 + l * e2
    have e4 : v 4 = (l ^ 3 - 2 * l) * v 1 - (l ^ 2 - 1) * v 0 := by
      linear_combination h3 + l * e3 - e2
    have e5 : v 5 = (l ^ 4 - 3 * l ^ 2 + 1) * v 1 - (l ^ 3 - 2 * l) * v 0 := by
      linear_combination h4 + l * e4 - e3
    have e6 : v 6 = (l ^ 5 - 4 * l ^ 3 + 3 * l) * v 1 - (l ^ 4 - 3 * l ^ 2 + 1) * v 0 := by
      linear_combination h5 + l * e5 - e4
    -- the two closing equations
    have E1 : (l ^ 6 - 5 * l ^ 4 + 6 * l ^ 2 - 1) * v 1 = (l ^ 5 - 4 * l ^ 3 + 3 * l + 1) * v 0 := by
      linear_combination (-1 : ℂ) * h6 + e5 - l * e6
    have E2 : (l ^ 5 - 4 * l ^ 3 + 3 * l + 1) * v 1 = (l ^ 4 - 3 * l ^ 2 + l + 1) * v 0 := by
      linear_combination h0 - e6
    -- eliminate
    have P0 : (l ^ 7 - 7 * l ^ 5 + 14 * l ^ 3 - 7 * l - 2) * v 0 = 0 := by
      linear_combination (l ^ 5 - 4 * l ^ 3 + 3 * l + 1) * E1
        - (l ^ 6 - 5 * l ^ 4 + 6 * l ^ 2 - 1) * E2
    have P1 : (l ^ 7 - 7 * l ^ 5 + 14 * l ^ 3 - 7 * l - 2) * v 1 = 0 := by
      linear_combination (l ^ 4 - 3 * l ^ 2 + l + 1) * E1
        - (l ^ 5 - 4 * l ^ 3 + 3 * l + 1) * E2
    have hp : l ^ 7 - 7 * l ^ 5 + 14 * l ^ 3 - 7 * l - 2 = 0 := by
      by_contra hne
      apply hv
      have hv0 : v 0 = 0 := by
        rcases mul_eq_zero.1 P0 with h | h
        · exact absurd h hne
        · exact h
      have hv1 : v 1 = 0 := by
        rcases mul_eq_zero.1 P1 with h | h
        · exact absurd h hne
        · exact h
      have hv2 : v 2 = 0 := by rw [e2, hv0, hv1]; ring
      have hv3 : v 3 = 0 := by rw [e3, hv0, hv1]; ring
      have hv4 : v 4 = 0 := by rw [e4, hv0, hv1]; ring
      have hv5 : v 5 = 0 := by rw [e5, hv0, hv1]; ring
      have hv6 : v 6 = 0 := by rw [e6, hv0, hv1]; ring
      funext j
      fin_cases j <;> assumption
    -- factor the characteristic polynomial
    have hfac : (l - 2) * (l ^ 3 + l ^ 2 - 2 * l - 1) ^ 2 = 0 := by linear_combination hp
    rcases mul_eq_zero.1 hfac with h | h
    · refine ⟨0, ?_⟩
      have hl : l = 2 := by linear_combination h
      rw [hl]
      norm_num
    · have hq : l ^ 3 + l ^ 2 - 2 * l - 1 = 0 := by
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      rw [cubic_factor] at hq
      rcases mul_eq_zero.1 hq with h' | h'
      · rcases mul_eq_zero.1 h' with h'' | h''
        · refine ⟨1, ?_⟩
          rw [show ((1 : Fin 7) : ℕ) = 1 from rfl, two_cos_eq 1, zeta_inv_one]
          linear_combination h''
        · refine ⟨2, ?_⟩
          rw [show ((2 : Fin 7) : ℕ) = 2 from rfl, two_cos_eq 2, zeta_inv_two]
          linear_combination h''
      · refine ⟨3, ?_⟩
        rw [show ((3 : Fin 7) : ℕ) = 3 from rfl, two_cos_eq 3, zeta_inv_three]
        linear_combination h'
  · rintro ⟨k, rfl⟩
    refine ⟨fourierVec (k : ℕ), fourierVec_ne_zero _, ?_⟩
    rw [C7adj_mulVec_fourierVec, two_cos_eq]

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

