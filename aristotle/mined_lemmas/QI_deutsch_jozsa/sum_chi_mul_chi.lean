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

lemma sum_chi_mul_chi {n : ℕ} (x x' : Fin n → Bool) :
    ∑ y : Fin n → Bool, chi x y * chi x' y = if x = x' then (2 : ℝ) ^ n else 0 := by
  have h1 : ∀ y : Fin n → Bool,
      chi x y * chi x' y = ∏ i, (sgn (x i && y i) * sgn (x' i && y i)) := by
    intro y
    rw [chi, chi, ← Finset.prod_mul_distrib]
  have h2 : ∑ y : Fin n → Bool, ∏ i, (sgn (x i && y i) * sgn (x' i && y i))
      = ∏ i, ∑ b : Bool, (sgn (x i && b) * sgn (x' i && b)) := by
    rw [Finset.prod_univ_sum]
    exact (Fintype.sum_equiv (Equiv.refl _) _ _ (fun y => rfl)).symm
  have h3 : ∀ i : Fin n, (∑ b : Bool, (sgn (x i && b) * sgn (x' i && b)))
      = if x i = x' i then (2 : ℝ) else 0 := by
    intro i
    rcases hx : x i with _ | _ <;> rcases hx' : x' i with _ | _ <;>
      norm_num [sgn]
  simp only [h1, h2, h3]
  by_cases hxx : x = x'
  · subst hxx
    simp
  · rw [if_neg hxx]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-! ## The circuit: Hadamard, one oracle query, Hadamard -/

/-- The `n`-fold Hadamard transform acting on real amplitude vectors. -/
