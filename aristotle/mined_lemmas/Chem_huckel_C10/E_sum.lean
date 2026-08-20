import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
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

namespace Chem

attribute [local instance] Fin.instCommRing

/-! ### A primitive 10-th root of unity -/

/-- The primitive 10-th root of unity `exp (2πi/10)`. -/

lemma E_sum (d : Fin 10) : ∑ k : Fin 10, E (d * k) = if d = 0 then 10 else 0 := by
  have h : ∀ k : Fin 10, E (d * k) = (E d) ^ (k : ℕ) := fun k => E_mul d k
  rw [Finset.sum_congr rfl (fun k _ => h k)]
  rw [Fin.sum_univ_eq_sum_range (fun i => (E d) ^ i) 10]
  by_cases hd : d = 0
  · subst hd
    simp [E_zero]
  · have h1 : E d ≠ 1 := fun hc => hd ((E_eq_one_iff d).mp hc)
    have h10 : (E d) ^ 10 = 1 := by
      rw [E, ← pow_mul, mul_comm, pow_mul, zeta_pow_ten, one_pow]
    rw [geom_sum_eq h1, h10, sub_self, zero_div, if_neg hd]

/-! ### The matrices -/

/-- Adjacency matrix of the cycle graph `C₁₀`. -/
