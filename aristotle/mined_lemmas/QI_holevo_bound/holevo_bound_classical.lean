import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
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

open Finset

/-! ### Classical entropies -/

/-- Shannon entropy of a probability vector, in nats. -/

theorem holevo_bound_classical {ι Z Y : Type*} [Fintype ι] [Fintype Z] [Fintype Y]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (r : ι → Z → ℝ) (hr0 : ∀ i z, 0 ≤ r i z)
    (E : Y → Z → ℝ) (hE0 : ∀ y z, 0 ≤ E y z) (hE1 : ∀ z, ∑ y, E y z = 1)
    (rbar : Z → ℝ) (hrb : ∀ z, rbar z = ∑ j, p j * r j z) :
    ∑ i, ∑ y, p i * ((∑ z, r i z * E y z) *
        Real.log ((∑ z, r i z * E y z) / (∑ j, p j * (∑ z, r j z * E y z))))
      ≤ shannonEntropy rbar - ∑ i, p i * shannonEntropy (r i) := by
  have hrbar0 : ∀ z, 0 ≤ rbar z := by
    intro z
    rw [hrb z]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hp0 j) (hr0 j z)
  have hwbar : ∀ y : Y, (∑ j, p j * (∑ z, r j z * E y z)) = ∑ z, rbar z * E y z := by
    intro y
    simp only [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro z _
    rw [← Finset.sum_mul, ← hrb z]
  have main : ∀ i : ι, p i * (∑ y, (∑ z, r i z * E y z) *
      Real.log ((∑ z, r i z * E y z) / (∑ z, rbar z * E y z)))
      ≤ p i * relEntropy (r i) rbar := by
    intro i
    rcases eq_or_lt_of_le (hp0 i) with hpi | hpi
    · rw [← hpi]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hpi)
      exact relEntropy_channel_le (r i) rbar E (hr0 i) hrbar0
        (by
          intro z hz
          by_contra hne
          have hz' : 0 < r i z := lt_of_le_of_ne (hr0 i z) (Ne.symm hne)
          have hpos : 0 < rbar z := by
            rw [hrb z]
            refine lt_of_lt_of_le (mul_pos hpi hz') ?_
            exact Finset.single_le_sum (f := fun j => p j * r j z)
              (fun j _ => mul_nonneg (hp0 j) (hr0 j z)) (Finset.mem_univ i)
          exact absurd hz (ne_of_gt hpos))
        hE0 hE1
  calc ∑ i, ∑ y, p i * ((∑ z, r i z * E y z) *
        Real.log ((∑ z, r i z * E y z) / (∑ j, p j * (∑ z, r j z * E y z))))
      = ∑ i, p i * (∑ y, (∑ z, r i z * E y z) *
          Real.log ((∑ z, r i z * E y z) / (∑ z, rbar z * E y z))) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro y _
        rw [hwbar y]
    _ ≤ ∑ i, p i * relEntropy (r i) rbar := Finset.sum_le_sum (fun i _ => main i)
    _ = shannonEntropy rbar - ∑ i, p i * shannonEntropy (r i) :=
        chi_eq_sum_relEntropy p hp0 r hr0 rbar hrb

/-! ### The quantum setting -/

section Quantum

open Matrix Polynomial
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The density matrix of a state which is diagonal in a fixed orthonormal basis, with
spectrum `r`. -/
