/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Statement: Deutsch–Jozsa decides constant-vs-balanced with one query.
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Setup

We model the Deutsch–Jozsa algorithm on `n` qubits with real amplitudes (the algorithm
never leaves the real subspace of the state space).

* Computational basis states of the query register are bit strings `x : Fin n → Bool`.
* `sgn b = (-1)^b` is the phase produced by the phase-kickback oracle.
* `chi x y = (-1)^(x ⬝ y)` is the Walsh character, i.e. the matrix entry of the
  `n`-fold Hadamard transform (up to the global normalisation `2^(n/2)`).

The algorithm is: prepare the uniform superposition `2^(-n/2) ∑ x, |x⟩`, apply the
oracle **once** (this is the only place where `f` is used), obtaining
`2^(-n/2) ∑ x, (-1)^(f x) |x⟩`, apply the Hadamard transform again, and measure.
The resulting amplitude on the basis state `y` is `djAmp f y`, and the probability of
observing `y` is `djProb f y`.
-/

/-- The phase `(-1)^b`. -/

theorem djProb_sum_eq_one {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∑ y : Fin n → Bool, djProb f y = 1 := by
  classical
  have hpow : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  have step1 : ∀ y : Fin n → Bool, djProb f y
      = (((2 : ℝ) ^ n)⁻¹) ^ 2 * ∑ x : Fin n → Bool, ∑ x' : Fin n → Bool,
          (sgn (f x) * sgn (f x')) * (chi x y * chi x' y) := by
    intro y
    rw [djProb, djAmp, mul_pow, sq_sum_expand]
  have swap : ∑ y : Fin n → Bool, ∑ x : Fin n → Bool, ∑ x' : Fin n → Bool,
        (sgn (f x) * sgn (f x')) * (chi x y * chi x' y)
      = ∑ x : Fin n → Bool, ∑ x' : Fin n → Bool, ∑ y : Fin n → Bool,
        (sgn (f x) * sgn (f x')) * (chi x y * chi x' y) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  have inner : ∀ x x' : Fin n → Bool,
      (∑ y : Fin n → Bool, (sgn (f x) * sgn (f x')) * (chi x y * chi x' y))
        = (sgn (f x) * sgn (f x')) * (if x = x' then (2 : ℝ) ^ n else 0) := by
    intro x x'
    rw [← Finset.mul_sum, sum_chi_mul_chi]
  have inner2 : ∀ x : Fin n → Bool,
      (∑ x' : Fin n → Bool, (sgn (f x) * sgn (f x')) * (if x = x' then (2 : ℝ) ^ n else 0))
        = (2 : ℝ) ^ n := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp [sgn_sq]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ x) h
  simp only [step1]
  rw [← Finset.mul_sum, swap]
  simp only [inner, inner2]
  rw [Finset.sum_const, Finset.card_univ, card_bool_pow, nsmul_eq_mul]
  field_simp
  push_cast
  ring

/-! ## Balanced and constant are mutually exclusive -/

