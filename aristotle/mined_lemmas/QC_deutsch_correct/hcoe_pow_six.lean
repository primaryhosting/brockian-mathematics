/-
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
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

/-!
## Deutsch's algorithm

A two–qubit state is modelled as an amplitude function `Bool → Bool → ℂ`, where the first
argument is the query register and the second the answer register.

The algorithm is:

* prepare `|0⟩|1⟩`;
* apply a Hadamard gate to each qubit;
* apply the oracle `U_f : |x⟩|y⟩ ↦ |x⟩|y ⊕ f x⟩` **once**;
* apply a Hadamard gate to the first qubit;
* measure the first qubit.

`QC.prob0 f` is the probability of observing `0` in the first register.  The theorem
`QC.deutsch_correct` says that this probability is `1` exactly when `f` is constant and `0`
exactly when `f` is balanced, so a single oracle query decides constant vs balanced.
-/

namespace QC

/-- The sign `(-1)^b`. -/

lemma hcoe_pow_six : hcoe ^ 6 = 1 / 8 := by
  calc hcoe ^ 6 = (hcoe ^ 2) ^ 3 := by ring
    _ = 1 / 8 := by rw [hcoe_sq]; norm_num

/-- Sanity check: the final state is a unit vector, i.e. the measurement probabilities
sum to one. -/
