/-
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The no-deleting theorem states that, given two copies of an unknown quantum state,
there is no unitary evolution that deletes one of the copies (sending it to a fixed
"blank" state) while leaving the ancilla in a fixed final state.

We model a qubit by `EuclideanSpace ℂ (Fin 2)`, an ancilla by `EuclideanSpace ℂ α`
for an arbitrary finite index type `α`, and the tensor product of state vectors by
`QI.tens` (the Kronecker product of coordinate vectors, which is the standard
concrete model of the tensor product of finite-dimensional Hilbert spaces).

A unitary is modelled as a `ℂ`-linear isometric equivalence `U`.  The key facts used
are that `U` preserves inner products and that the inner product is multiplicative
with respect to `tens`.
-/

namespace QI

open scoped ComplexConjugate

/-- The Kronecker (tensor) product of two finite-dimensional state vectors. -/

theorem inner_tens {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a c : EuclideanSpace ℂ ι) (b d : EuclideanSpace ℂ κ) :
    inner ℂ (tens a b) (tens c d) = inner ℂ a c * inner ℂ b d := by
  rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply, Finset.sum_mul_sum,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [tens, RCLike.inner_apply, map_mul]
  ring

/-- For a unit vector `x`, `⟪x, x⟫ = 1`. -/
