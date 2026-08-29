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
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Brockian
namespace GoldbachSchema

/-- The finite set of *Goldbach representations* of `n`: those `p ≤ n` such that both `p`
and `n - p` are prime. -/
def reps (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))

/-- Membership in `reps n` yields an honest decomposition of `n` into two primes. -/
theorem exists_two_primes_of_reps_nonempty {n : ℕ} (h : (reps n).Nonempty) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨p, hp⟩ := h
  simp only [reps, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hp
  exact ⟨p, n - p, hp.2.1, hp.2.2, Nat.add_sub_cancel' hp.1⟩

/-- A *Hardy–Littlewood style lower-bound model* for the Goldbach representation counting
function beyond a threshold: a constant `c > 0` and a threshold `bound ≥ 4` such that every
even `n ≥ bound` has at least `c * n / (log n)^2` representations as a sum of two primes.

This is the "model" hypothesis of the schema; the theorem
`goldbach_beyond_of_model` turns it into the Goldbach conclusion beyond `bound`. -/
structure Model where
  /-- Threshold beyond which the lower bound is asserted. -/
  bound : ℕ
  /-- The implied constant of the lower bound. -/
  const : ℝ
  /-- The threshold is at least `4`. -/
  bound_ge : 4 ≤ bound
  /-- The implied constant is positive. -/
  const_pos : 0 < const
  /-- The counting lower bound, valid for every even `n` beyond the threshold. -/
  lower : ∀ n : ℕ, bound ≤ n → Even n →
    const * (n : ℝ) / (Real.log n) ^ 2 ≤ ((reps n).card : ℝ)

/-- For `4 ≤ n` the analytic lower bound `c * n / (log n)^2` is strictly positive. -/
theorem lower_bound_pos {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 4 ≤ n) :
    0 < c * (n : ℝ) / (Real.log n) ^ 2 := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hsq : 0 < (Real.log n) ^ 2 := by positivity
  have hnum : 0 < c * (n : ℝ) := by nlinarith
  exact div_pos hnum hsq

/-- **Goldbach beyond a threshold, from a counting model.**

If a Hardy–Littlewood style lower-bound model `M` for the number of Goldbach
representations is available, then every even `n ≥ M.bound` really is a sum of two primes.

The statement is unconditional: it carries no ambient hypothesis besides the model data
itself, and its proof uses no additional assumptions. -/
theorem goldbach_beyond_of_model (M : Model) :
    ∀ n : ℕ, M.bound ≤ n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  intro n hn hev
  have h4 : 4 ≤ n := le_trans M.bound_ge hn
  have hpos : 0 < M.const * (n : ℝ) / (Real.log n) ^ 2 := lower_bound_pos M.const_pos h4
  have hcard : (0 : ℝ) < ((reps n).card : ℝ) := lt_of_lt_of_le hpos (M.lower n hn hev)
  have : 0 < (reps n).card := by exact_mod_cast hcard
  exact exists_two_primes_of_reps_nonempty (Finset.card_pos.mp this)

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- Sanity check that the conclusion of the schema is a non-vacuous statement: the Goldbach
property is verified unconditionally for all even `n` with `4 ≤ n ≤ 200`. -/
theorem goldbach_small (n : ℕ) (h4 : 4 ≤ n) (h : n ≤ 200) (hev : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  have hdec : ∀ m ∈ Finset.range 201, 4 ≤ m → m % 2 = 0 →
      ∃ p ∈ Finset.range 201, ∃ q ∈ Finset.range 201,
        Nat.Prime p ∧ Nat.Prime q ∧ p + q = m := by decide
  have hmem : n ∈ Finset.range 201 := Finset.mem_range.mpr (by omega)
  obtain ⟨p, _, q, _, hp, hq, hpq⟩ :=
    hdec n hmem h4 (Nat.even_iff.mp hev)
  exact ⟨p, q, hp, hq, hpq⟩

/-- Combining the schema with the finite verification: a counting model whose threshold is at
most `202` yields the full Goldbach conjecture for all even `n ≥ 4`. -/
theorem goldbach_of_model_of_bound_le (M : Model) (hb : M.bound ≤ 202) (n : ℕ)
    (h4 : 4 ≤ n) (hev : Even n) : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  by_cases h : n ≤ 200
  · exact goldbach_small n h4 h hev
  · refine goldbach_beyond_of_model M n (le_trans hb ?_) hev
    obtain ⟨k, hk⟩ := hev
    omega

end GoldbachSchema
end Brockian

