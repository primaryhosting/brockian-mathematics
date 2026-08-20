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

namespace Chem

open Polynomial

/-- The Hückel matrix of benzene (in units where the Coulomb integral `α` is `0` and the
resonance integral `β` is `1`): the adjacency matrix of the cycle graph `C₆`. -/

theorem prod_cos_expand :
    ∏ k ∈ Finset.range 6, (X - C (2 * Real.cos (2 * Real.pi * k / 6))) =
      (X : ℝ[X]) ^ 6 - 6 * X ^ 4 + 9 * X ^ 2 - 4 := by
  have e0 : Real.cos (2 * Real.pi * (0 : ℕ) / 6) = 1 := by norm_num
  have e1 : Real.cos (2 * Real.pi * (1 : ℕ) / 6) = 1 / 2 := by
    rw [show (2 * Real.pi * ((1 : ℕ) : ℝ) / 6) = Real.pi / 3 by push_cast; ring,
      Real.cos_pi_div_three]
  have e2 : Real.cos (2 * Real.pi * (2 : ℕ) / 6) = -(1 / 2) := by
    rw [show (2 * Real.pi * ((2 : ℕ) : ℝ) / 6) = Real.pi - Real.pi / 3 by push_cast; ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  have e3 : Real.cos (2 * Real.pi * (3 : ℕ) / 6) = -1 := by
    rw [show (2 * Real.pi * ((3 : ℕ) : ℝ) / 6) = Real.pi by push_cast; ring, Real.cos_pi]
  have e4 : Real.cos (2 * Real.pi * (4 : ℕ) / 6) = -(1 / 2) := by
    rw [show (2 * Real.pi * ((4 : ℕ) : ℝ) / 6) = Real.pi + Real.pi / 3 by push_cast; ring,
      Real.cos_add, Real.cos_pi_div_three]
    simp
  have e5 : Real.cos (2 * Real.pi * (5 : ℕ) / 6) = 1 / 2 := by
    rw [show (2 * Real.pi * ((5 : ℕ) : ℝ) / 6) = 2 * Real.pi - Real.pi / 3 by push_cast; ring,
      Real.cos_sub, Real.cos_pi_div_three]
    simp
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one, e0, e1, e2, e3, e4, e5]
  norm_num [Polynomial.C_neg, map_ofNat]
  ring

/-- **Hückel theory for benzene (`C₆`), characteristic polynomial form.**
The characteristic polynomial of the adjacency matrix of the cycle graph `C₆` factors as
`∏_{k=0}^{5} (X - 2·cos(2πk/6))`, i.e. the eigenvalues, with multiplicity, are
`2·cos(2πk/6)` for `k = 0, …, 5`. -/
