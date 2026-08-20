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

lemma djAmp_zero_of_balanced {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : IsBalanced f) :
    djAmp f (fun _ => false) = 0 := by
  classical
  rw [djAmp_zero]
  set T : Finset (Fin n → Bool) := {x : Fin n → Bool | f x = true} with hT
  have hsplit : ∑ x : Fin n → Bool, sgn (f x)
      = ∑ x ∈ T, sgn (f x) + ∑ x ∈ Tᶜ, sgn (f x) := by
    rw [Finset.sum_add_sum_compl]
  have hT1 : ∀ x ∈ T, sgn (f x) = (-1 : ℝ) := by
    intro x hx
    have : f x = true := by simpa [hT] using hx
    simp [this, sgn]
  have hT2 : ∀ x ∈ Tᶜ, sgn (f x) = (1 : ℝ) := by
    intro x hx
    have hx' : x ∉ T := Finset.mem_compl.mp hx
    have : f x = false := by simpa [hT, Bool.not_eq_true] using hx'
    simp [this, sgn]
  have h1 : ∑ x ∈ T, sgn (f x) = -(T.card : ℝ) := by
    rw [Finset.sum_congr rfl hT1, Finset.sum_const]
    simp
  have h2 : ∑ x ∈ Tᶜ, sgn (f x) = (Tᶜ.card : ℝ) := by
    rw [Finset.sum_congr rfl hT2, Finset.sum_const]
    simp
  have hcard : (Tᶜ.card : ℝ) = (T.card : ℝ) := by
    have hc : Tᶜ.card = Fintype.card (Fin n → Bool) - T.card := Finset.card_compl T
    have hle : T.card ≤ Fintype.card (Fin n → Bool) := Finset.card_le_univ T
    have h2n : 2 * T.card = 2 ^ n := hf
    have : Tᶜ.card = T.card := by
      rw [hc, card_bool_pow]
      omega
    rw [this]
  rw [hsplit, h1, h2, hcard]
  ring

/-! ## Normalisation: the probabilities sum to `1` -/

