/-
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset Complex

variable {n : ℕ}

/-- Auxiliary: the derivative of the (constant) squared norm of a normalized state vanishes. -/
lemma norm_deriv_zero {n : ℕ} (psi : ℝ → Fin n → ℂ) (dpsi : Fin n → ℂ) (l : ℝ)
    (hpsid : ∀ i, HasDerivAt (fun t => psi t i) (dpsi i) l)
    (hnorm : ∀ t : ℝ, ∑ i, (starRingEnd ℂ) (psi t i) * psi t i = 1) :
    ∑ i, ((starRingEnd ℂ) (dpsi i) * psi l i + (starRingEnd ℂ) (psi l i) * dpsi i) = 0 := by
  have hd : HasDerivAt (fun t => ∑ i, (starRingEnd ℂ) (psi t i) * psi t i)
      (∑ i, ((starRingEnd ℂ) (dpsi i) * psi l i + (starRingEnd ℂ) (psi l i) * dpsi i)) l := by
    apply HasDerivAt.fun_sum
    intro i _
    exact ((hpsid i).star).mul (hpsid i)
  have hc : HasDerivAt (fun t => ∑ i, (starRingEnd ℂ) (psi t i) * psi t i) 0 l := by
    have : (fun t => ∑ i, (starRingEnd ℂ) (psi t i) * psi t i) = fun _ : ℝ => (1 : ℂ) :=
      funext hnorm
    rw [this]
    exact hasDerivAt_const l 1
  exact hd.unique hc

/-- **Hellmann–Feynman theorem** (finite-dimensional form).

Let `H i j t` be the entries of a family of Hermitian matrices depending on a real parameter `t`,
let `psi t` be a normalized eigenvector of `H · · t` with real eigenvalue `E t`, and suppose all
data are differentiable at `l`, with `dH i j` the derivative of the entries, `dpsi` the derivative
of the state and `dE` the derivative of the eigenvalue.  Then

`dE/dλ = ⟪ψ, (dH/dλ) ψ⟫`. -/
theorem hellmann_feynman {n : ℕ} (H : Fin n → Fin n → ℝ → ℂ) (dH : Fin n → Fin n → ℂ)
    (psi : ℝ → Fin n → ℂ) (dpsi : Fin n → ℂ) (E : ℝ → ℝ) (dE : ℝ) (l : ℝ)
    (hHerm : ∀ (t : ℝ) (i j : Fin n), H i j t = (starRingEnd ℂ) (H j i t))
    (hHd : ∀ i j, HasDerivAt (H i j) (dH i j) l)
    (hpsid : ∀ i, HasDerivAt (fun t => psi t i) (dpsi i) l)
    (hEd : HasDerivAt E dE l)
    (heig : ∀ (t : ℝ) (i : Fin n), ∑ j, H i j t * psi t j = (E t : ℂ) * psi t i)
    (hnorm : ∀ t : ℝ, ∑ i, (starRingEnd ℂ) (psi t i) * psi t i = 1) :
    (dE : ℂ) = ∑ i, ∑ j, (starRingEnd ℂ) (psi l i) * dH i j * psi l j := by
  -- The Rayleigh quotient `F t = ⟪ψ t, H t ψ t⟫` equals `E t`.
  set F : ℝ → ℂ := fun t => ∑ i, ∑ j, (starRingEnd ℂ) (psi t i) * H i j t * psi t j with hF
  have hFE : F = fun t => ((E t : ℝ) : ℂ) := by
    funext t
    have : F t = ∑ i, (starRingEnd ℂ) (psi t i) * ∑ j, H i j t * psi t j := by
      simp [hF, Finset.mul_sum, mul_assoc]
    rw [this]
    simp only [heig t]
    rw [show (∑ i, (starRingEnd ℂ) (psi t i) * ((E t : ℂ) * psi t i))
        = (E t : ℂ) * ∑ i, (starRingEnd ℂ) (psi t i) * psi t i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
    rw [hnorm t, mul_one]
  -- Differentiate the Rayleigh quotient.
  have hFd : HasDerivAt F
      (∑ i, ∑ j, ((starRingEnd ℂ) (dpsi i) * H i j l * psi l j
        + (starRingEnd ℂ) (psi l i) * dH i j * psi l j
        + (starRingEnd ℂ) (psi l i) * H i j l * dpsi j)) l := by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    have h1 : HasDerivAt (fun t => (starRingEnd ℂ) (psi t i) * H i j t)
        ((starRingEnd ℂ) (dpsi i) * H i j l + (starRingEnd ℂ) (psi l i) * dH i j) l :=
      ((hpsid i).star).mul (hHd i j)
    have h2 := h1.mul (hpsid j)
    convert h2 using 1
    ring
  have hEd' : HasDerivAt F (((dE : ℝ) : ℂ)) l := by
    rw [hFE]
    exact (hEd.ofReal_comp)
  have hkey := hFd.unique hEd'
  -- Split the derivative into three pieces.
  rw [← hkey]
  have hsplit : ∀ i : Fin n, ∑ j, ((starRingEnd ℂ) (dpsi i) * H i j l * psi l j
        + (starRingEnd ℂ) (psi l i) * dH i j * psi l j
        + (starRingEnd ℂ) (psi l i) * H i j l * dpsi j)
      = (∑ j, (starRingEnd ℂ) (dpsi i) * H i j l * psi l j)
        + (∑ j, (starRingEnd ℂ) (psi l i) * dH i j * psi l j)
        + (∑ j, (starRingEnd ℂ) (psi l i) * H i j l * dpsi j) := by
    intro i
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- First piece : `E * ∑ conj(dψ i) ψ i`
  have hA : ∑ i, ∑ j, (starRingEnd ℂ) (dpsi i) * H i j l * psi l j
      = (E l : ℂ) * ∑ i, (starRingEnd ℂ) (dpsi i) * psi l i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∑ j, (starRingEnd ℂ) (dpsi i) * H i j l * psi l j
        = (starRingEnd ℂ) (dpsi i) * ∑ j, H i j l * psi l j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, heig l i]; ring
  -- Third piece : `E * ∑ conj(ψ i) dψ i`, using hermiticity.
  have hC : ∑ i, ∑ j, (starRingEnd ℂ) (psi l i) * H i j l * dpsi j
      = (E l : ℂ) * ∑ i, (starRingEnd ℂ) (psi l i) * dpsi i := by
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hrow : ∑ i, (starRingEnd ℂ) (psi l i) * H i j l
        = (starRingEnd ℂ) (∑ i, H j i l * psi l i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← hHerm l i j]
      ring
    have : ∑ i, (starRingEnd ℂ) (psi l i) * H i j l * dpsi j
        = (∑ i, (starRingEnd ℂ) (psi l i) * H i j l) * dpsi j := by
      rw [Finset.sum_mul]
    rw [this, hrow, heig l j, map_mul, Complex.conj_ofReal]
    ring
  rw [hA, hC]
  have hzero := norm_deriv_zero psi dpsi l hpsid hnorm
  rw [Finset.sum_add_distrib] at hzero
  have : (E l : ℂ) * ∑ i, (starRingEnd ℂ) (dpsi i) * psi l i
      + (E l : ℂ) * ∑ i, (starRingEnd ℂ) (psi l i) * dpsi i = 0 := by
    rw [← mul_add, hzero, mul_zero]
  linear_combination this

end Phys

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

