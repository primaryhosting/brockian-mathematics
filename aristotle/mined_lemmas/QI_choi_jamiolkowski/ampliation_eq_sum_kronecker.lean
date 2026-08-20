/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

open Matrix
open scoped Kronecker MatrixOrder

variable {n m : ℕ}

/-- The Choi matrix of a linear map `Φ` between matrix algebras:
`C = ∑ i j, E i j ⊗ Φ (E i j)`, i.e. `C (i, a) (j, b) = Φ (E i j) a b`. -/

lemma ampliation_eq_sum_kronecker
    (A : Fin n × Fin m → Matrix (Fin m) (Fin n) ℂ)
    (hA : ∀ X : Matrix (Fin n) (Fin n) ℂ, Φ X = ∑ r, A r * X * (A r)ᴴ)
    (k : ℕ) (M : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ) :
    ampliation Φ k M
      = ∑ r, ((1 : Matrix (Fin k) (Fin k) ℂ) ⊗ₖ A r) * M
          * (((1 : Matrix (Fin k) (Fin k) ℂ) ⊗ₖ A r))ᴴ := by
  ext x y
  obtain ⟨p, a⟩ := x
  obtain ⟨q, b⟩ := y
  simp only [ampliation, Matrix.of_apply, hA, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ite_mul, one_mul, zero_mul]
  refine Finset.sum_congr rfl fun r₁ _ => Finset.sum_congr rfl fun r₂ _ => ?_
  rw [Finset.sum_eq_single_of_mem q (Finset.mem_univ q)]
  · simp [Finset.sum_ite_eq]
  · intro t _ ht
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [Ne.symm ht]

/-- A map with a Kraus representation is completely positive. -/
