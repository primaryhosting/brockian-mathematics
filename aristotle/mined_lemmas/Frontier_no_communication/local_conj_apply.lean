/-
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment because Lean 4 requires every
-- `import` command to precede any module docstring; the identical header is
-- repeated as the module docstring immediately after the imports.)

import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Kronecker
open scoped Matrix

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

namespace Frontier

/-- The partial trace over the first ("Alice") tensor factor of a bipartite system
with Hilbert space `ℂ^ιA ⊗ ℂ^ιB`: states are matrices indexed by `ιA × ιB`, and
`ptraceLeft ρ` is the reduced state seen by Bob. -/

lemma local_conj_apply {ιA ιB : Type*} [Fintype ιA] [Fintype ιB] [DecidableEq ιB]
    (K : Matrix ιA ιA ℂ) (rho : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (a a' : ιA) (b b' : ιB) :
    ((K ⊗ₖ (1 : Matrix ιB ιB ℂ)) * rho * (K ⊗ₖ (1 : Matrix ιB ιB ℂ))ᴴ) (a, b) (a', b')
      = ∑ c : ιA, ∑ e : ιA, K a c * rho (c, b) (e, b') * (starRingEnd ℂ) (K a' e) := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ← Finset.univ_product_univ, Finset.sum_product,
    mul_ite, ite_mul, mul_zero, zero_mul, mul_one, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, apply_ite (star : ℂ → ℂ), star_zero, starRingEnd_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The core computation: summing the Kraus terms and tracing out Alice's factor
collapses, thanks to the completeness relation `∑ i, (K i)ᴴ * (K i) = 1`, to the
partial trace of the original state. -/
