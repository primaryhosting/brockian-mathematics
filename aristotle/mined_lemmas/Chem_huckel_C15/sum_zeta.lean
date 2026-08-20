import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
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

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 15-th root of unity. -/

lemma sum_zeta (d : Fin 15) :
    (∑ l : Fin 15, zeta (l * d)) = if d = 0 then (15 : ℂ) else 0 := by
  by_cases hd : d = 0
  · subst hd
    simp [zeta]
  · simp only [hd, if_false]
    have hstep : (∑ l : Fin 15, zeta (l * d)) = ∑ i ∈ Finset.range 15, zeta d ^ i := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => zeta d ^ i) 15]
      exact Finset.sum_congr rfl fun l _ => zeta_mul l d
    have hpow : zeta d ^ (15 : ℕ) = 1 := by
      rw [zeta, ← pow_mul, mul_comm, pow_mul, om_pow_15, one_pow]
    have hmul : (∑ i ∈ Finset.range 15, zeta d ^ i) * (zeta d - 1) = 0 := by
      rw [geom_sum_mul, hpow, sub_self]
    have hne : zeta d - 1 ≠ 0 := sub_ne_zero_of_ne (zeta_ne_one hd)
    rw [hstep]
    exact (mul_eq_zero.mp hmul).resolve_right hne

