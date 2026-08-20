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

import Mathlib

/-!
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat

namespace Brockian.GoldbachSchema

open Finset Complex

/-- The primes below `n`, i.e. the support of the spectral model at level `n`. -/

theorem sum_zeta_pow (n : ℕ) (hn : n ≠ 0) (k : ℕ) :
    ∑ j ∈ Finset.range n, zeta n ^ (k * j) = if n ∣ k then (n : ℂ) else 0 := by
  by_cases h : n ∣ k
  · simp only [h, if_true]
    have hone : ∀ j ∈ Finset.range n, zeta n ^ (k * j) = 1 := by
      intro j _
      rw [pow_mul, (zeta_pow_eq_one_iff hn k).2 h, one_pow]
    rw [Finset.sum_congr rfl hone]
    simp
  · simp only [h, if_false]
    have hne : zeta n ^ k ≠ 1 := fun hc => h ((zeta_pow_eq_one_iff hn k).1 hc)
    have hgeom : ∑ j ∈ Finset.range n, (zeta n ^ k) ^ j
        = ((zeta n ^ k) ^ n - 1) / (zeta n ^ k - 1) := geom_sum_eq hne n
    rw [show ∑ j ∈ Finset.range n, zeta n ^ (k * j) = ∑ j ∈ Finset.range n, (zeta n ^ k) ^ j from
      Finset.sum_congr rfl (fun j _ => by rw [pow_mul]), hgeom, ← pow_mul, mul_comm k n, pow_mul,
      (zeta_isPrimitiveRoot hn).pow_eq_one, one_pow]
    simp

/-! ### The spectral identity -/

/-- The circle-method identity: the spectral main term counts ordered Goldbach
representations exactly. -/
