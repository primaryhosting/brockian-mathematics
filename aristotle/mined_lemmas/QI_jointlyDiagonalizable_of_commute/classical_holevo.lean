import Mathlib
import RequestProject.Holevo

/-!
# Simultaneous diagonalization of a commuting family of Hermitian matrices

The main result `QI.jointlyDiagonalizable_of_commute` shows that a family of pairwise commuting
Hermitian matrices is diagonal in a common orthonormal basis, i.e. satisfies
`QI.JointlyDiagonalizable`.
-/

open Matrix LinearMap
open scoped Function

namespace QI

variable {n X : Type*} [Fintype n] [DecidableEq n]


theorem classical_holevo (p : X → ℝ) (lam : X → I → ℝ) (A : Y → I → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hlam : ∀ x i, 0 ≤ lam x i)
    (hA : ∀ y i, 0 ≤ A y i) (hAcol : ∀ i, ∑ y, A y i = 1) :
    shannonEntropy (fun y => ∑ x, p x * (∑ i, A y i * lam x i))
        - ∑ x, p x * shannonEntropy (fun y => ∑ i, A y i * lam x i)
      ≤ shannonEntropy (fun i => ∑ x, p x * lam x i) - ∑ x, p x * shannonEntropy (lam x) := by
  rw [← mutualInfo_eq_sum_relEntropy, ← mutualInfo_eq_sum_relEntropy]
  refine Finset.sum_le_sum fun x _ => ?_
  rcases eq_or_lt_of_le (hp x) with hpx | hpx
  · simp [← hpx]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hpx)
  have habs : ∀ i, (∑ x', p x' * lam x' i) = 0 → lam x i = 0 := by
    intro i hi
    have hnn : ∀ x' ∈ (Finset.univ : Finset X), 0 ≤ p x' * lam x' i :=
      fun x' _ => mul_nonneg (hp x') (hlam x' i)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hi x (Finset.mem_univ x)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (ne_of_gt hpx)
    · exact h
  have key := relEntropy_channel_le (lam x) (fun i => ∑ x', p x' * lam x' i) A
    (hlam x) (fun i => Finset.sum_nonneg fun x' _ => mul_nonneg (hp x') (hlam x' i))
    habs hA hAcol
  have hfun : (fun y => ∑ x', p x' * ∑ i, A y i * lam x' i)
      = fun y => ∑ i, A y i * ∑ x', p x' * lam x' i := by
    funext y
    have h1 : ∀ x', p x' * (∑ i, A y i * lam x' i) = ∑ i, p x' * (A y i * lam x' i) :=
      fun x' => Finset.mul_sum _ _ _
    rw [Finset.sum_congr rfl fun x' _ => h1 x', Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x' _ => by ring
  rw [hfun]
  exact key

end QI

import Mathlib
import RequestProject.ClassicalInfo
import RequestProject.Holevo
import RequestProject.SimulDiag

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

