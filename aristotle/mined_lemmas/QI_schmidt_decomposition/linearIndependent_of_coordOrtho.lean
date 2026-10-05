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

lemma linearIndependent_of_coordOrtho {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : ι → (Fin m → ℂ))
    (h : ∀ i j, ∑ p, conj (v i p) * v j p = if i = j then (1 : ℂ) else 0) :
    LinearIndependent ℂ v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h2 := congrArg (fun w : Fin m → ℂ => ∑ p, conj (v j p) * w p) hg
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero] at h2
  have h3 : ∑ p, conj (v j p) * (∑ i, g i * v i p) = ∑ i, g i * ∑ p, conj (v j p) * v i p := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring
  rw [h3] at h2
  simp only [h j] at h2
  simpa using h2

