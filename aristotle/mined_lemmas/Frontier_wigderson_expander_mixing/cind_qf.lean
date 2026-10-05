import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

section

variable {V : Type*} [Fintype V]

/-- The bilinear form `xᵀ A y` associated to a weight matrix `A`. -/

lemma cind_qf (S : Finset V) (hn : (Fintype.card V : ℝ) ≠ 0) :
    qf (cind S) = (S.card : ℝ) - (S.card : ℝ) ^ 2 / (Fintype.card V : ℝ) := by
  have key : ∀ i : V, (cind S i) ^ 2
      = indf S i * (1 - 2 * ((S.card : ℝ) / (Fintype.card V : ℝ)))
        + ((S.card : ℝ) / (Fintype.card V : ℝ)) ^ 2 := by
    intro i
    simp only [cind, indf, onev, mul_one]
    split <;> ring
  simp only [qf, key]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_indf, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp
  ring

