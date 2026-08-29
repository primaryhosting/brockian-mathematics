/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- comment and is repeated as the module docstring below.)

import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open scoped ComplexConjugate

variable {m n : ℕ}

/-- The amplitude matrix of a bipartite pure state, i.e. its coordinates in the product basis. -/

lemma psi_eq_sum_evecs (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (p : Fin m) (q : Fin n) :
    ψ (p, q) = ∑ j, evecs ψ j p * wcoef ψ j q := by
  set b := evecs ψ with hb
  set x : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun p => ψ (p, q)) with hx
  have h := congrArg (fun y : EuclideanSpace ℂ (Fin m) => y p) (b.sum_repr' x)
  simp only at h
  have hxp : x p = ψ (p, q) := rfl
  rw [← hxp, ← h, WithLp.ofLp_sum]
  simp only [Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, hx, wcoef, hb]
  rw [mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun p' _ => mul_comm _ _

