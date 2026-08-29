/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
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

namespace QI

open Finset

/-- The number of inputs `x` on which the oracle `f` returns `true`. -/

theorem deutsch_jozsa_amplitude {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (IsConstant f → |amplitude f| = 1) ∧ (IsBalanced f → amplitude f = 0) := by
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  constructor
  · intro hconst
    by_cases hex : ∃ x : Fin n → Bool, f x = true
    · obtain ⟨x0, hx0⟩ := hex
      have hall : ∀ x : Fin n → Bool, f x = true := fun x => (hconst x x0).trans hx0
      have hnum : numTrue f = 2 ^ n := by
        unfold numTrue
        rw [Finset.filter_true_of_mem (fun x _ => hall x)]
        simp [Finset.card_univ]
      rw [amplitude_eq, hnum]
      push_cast
      rw [show (1 : ℝ) - 2 * 2 ^ n / 2 ^ n = -1 by field_simp; norm_num]
      simp
    · push_neg at hex
      have hnum : numTrue f = 0 := by
        unfold numTrue
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x _
        simp [hex x]
      rw [amplitude_eq, hnum]
      norm_num
  · intro hbal
    have hnum : 2 * (numTrue f : ℝ) = 2 ^ n := by
      have := congrArg (fun k : ℕ => (k : ℝ)) hbal
      push_cast at this
      exact this
    rw [amplitude_eq, hnum]
    field_simp
    norm_num

/-- **Deutsch–Jozsa.** Running the circuit `H^{⊗n} ∘ Uf ∘ H^{⊗n}` on `|0…0⟩`,
with a *single* query to the oracle for `f`, the amplitude of the all-zeros
measurement outcome has modulus `1` when `f` is constant (so that outcome is
observed with probability one) and is `0` when `f` is balanced (so that outcome
is never observed).  Hence one query and one measurement decide constant vs.
balanced. -/
