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

theorem djAmp_eq_circuit {n : ℕ} (f : (Fin n → Bool) → Bool) :
    djAmp f = hadamard (oracle f (hadamard (initState : (Fin n → Bool) → ℝ))) := by
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
  have hs : Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt ((2 : ℝ) ^ n) = (2 : ℝ) ^ n :=
    Real.mul_self_sqrt hnn
  funext y
  have hstep1 : hadamard (initState : (Fin n → Bool) → ℝ)
      = fun _ : Fin n → Bool => (Real.sqrt ((2 : ℝ) ^ n))⁻¹ := by
    funext z
    rw [hadamard]
    rw [Finset.sum_eq_single (fun _ => false)]
    · simp [initState, chi_zero_left]
    · intro b _ hb
      simp [initState, hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hstep1]
  simp only [oracle, hadamard, djAmp]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have : ((2 : ℝ) ^ n)⁻¹
      = (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * (Real.sqrt ((2 : ℝ) ^ n))⁻¹ := by
    rw [← mul_inv, hs]
  rw [this]
  ring

/-! ## The amplitude at the all-zero outcome -/

