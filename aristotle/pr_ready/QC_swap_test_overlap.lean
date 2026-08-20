/-!
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Statement: The SWAP test accepts two states with probability (1+|⟨ψ|φ⟩|²)/2.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Finset Complex

variable {n : ℕ}

/-- The state of the swap-test register: one control qubit (`Fin 2`) together with two
`n`-dimensional systems, described by its amplitude function. -/
abbrev State (n : ℕ) := Fin 2 × Fin n × Fin n → ℂ

/-- Hadamard gate acting on the control qubit. -/
noncomputable def hadamardControl (v : State n) : State n := fun p =>
  if p.1 = 0 then (v (0, p.2) + v (1, p.2)) / (Real.sqrt 2 : ℝ)
  else (v (0, p.2) - v (1, p.2)) / (Real.sqrt 2 : ℝ)

/-- Controlled-SWAP gate: swaps the two `n`-dimensional systems when the control is `1`. -/
def cswap (v : State n) : State n := fun p =>
  if p.1 = 0 then v (0, p.2.1, p.2.2) else v (1, p.2.2, p.2.1)

/-- Initial state `|0⟩ ⊗ |ψ⟩ ⊗ |φ⟩`. -/
def initState (psi phi : Fin n → ℂ) : State n := fun p =>
  if p.1 = 0 then psi p.2.1 * phi p.2.2 else 0

/-- The state of the register at the end of the swap test circuit
(Hadamard, controlled swap, Hadamard on the control qubit). -/
noncomputable def swapTestFinal (psi phi : Fin n → ℂ) : State n :=
  hadamardControl (cswap (hadamardControl (initState psi phi)))

/-- Probability that the swap test accepts, i.e. that the control qubit is measured in `|0⟩`. -/
noncomputable def acceptProb (psi phi : Fin n → ℂ) : ℝ :=
  ∑ i, ∑ j, ‖swapTestFinal psi phi (0, i, j)‖ ^ 2

/-- The overlap `⟨ψ|φ⟩`. -/
noncomputable def overlap (psi phi : Fin n → ℂ) : ℂ := ∑ i, (starRingEnd ℂ) (psi i) * phi i

/-- Amplitude of the accepted branch: `(ψᵢφⱼ + ψⱼφᵢ)/2`. -/
theorem swapTestFinal_zero (psi phi : Fin n → ℂ) (i j : Fin n) :
    swapTestFinal psi phi (0, i, j) = (psi i * phi j + psi j * phi i) / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    simp
  simp only [swapTestFinal, hadamardControl, cswap, initState]
  norm_num
  field_simp
  rw [sq, h2]
  ring

/-- **Swap test.** For normalized states `ψ` and `φ`, the swap test accepts with
probability `(1 + |⟨ψ|φ⟩|²)/2`. -/
theorem swap_test_overlap (psi phi : Fin n → ℂ)
    (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) (hphi : ∑ i, ‖phi i‖ ^ 2 = 1) :
    acceptProb psi phi = (1 + ‖overlap psi phi‖ ^ 2) / 2 := by
  have expand : acceptProb psi phi
      = (∑ i, ∑ j, (normSq (psi i * phi j) + normSq (psi j * phi i)
          + 2 * ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re)) / 4 := by
    rw [acceptProb, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [swapTestFinal_zero, Complex.sq_norm, ← Complex.normSq_add]
    rw [normSq_div]
    norm_num
  -- first two terms
  have hsq : ∀ z : ℂ, normSq z = ‖z‖ ^ 2 := fun z => (Complex.sq_norm z).symm
  have h1 : (∑ i, ∑ j, normSq (psi i * phi j)) = 1 := by
    simp only [hsq, norm_mul, mul_pow, ← Finset.mul_sum, hpsi, hphi, mul_one]
  have h2 : (∑ i, ∑ j, normSq (psi j * phi i)) = 1 := by
    simp only [hsq, norm_mul, mul_pow, ← Finset.sum_mul, hpsi, hphi, one_mul]
  have h3 : (∑ i, ∑ j, ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re)
      = ‖overlap psi phi‖ ^ 2 := by
    have hprod : ∀ i : Fin n, ∀ j : Fin n,
        (psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)
          = ((starRingEnd ℂ) (phi i) * psi i) * ((starRingEnd ℂ) (psi j) * phi j) := by
      intro i j; simp only [map_mul]; ring
    have hconj : (∑ i, (starRingEnd ℂ) (phi i) * psi i)
        = (starRingEnd ℂ) (overlap psi phi) := by
      simp [overlap, map_sum, mul_comm]
    calc (∑ i, ∑ j, ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re)
        = ((∑ i, ∑ j, (psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re) := by
          simp [Complex.re_sum]
      _ = (((∑ i, (starRingEnd ℂ) (phi i) * psi i)
            * (∑ j, (starRingEnd ℂ) (psi j) * phi j)).re) := by
          rw [Finset.sum_mul_sum]
          simp only [hprod]
      _ = ‖overlap psi phi‖ ^ 2 := by
          rw [hconj]
          show ((starRingEnd ℂ) (overlap psi phi) * overlap psi phi).re = _
          rw [← Complex.normSq_eq_conj_mul_self]
          simp [Complex.sq_norm]
  rw [expand]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, h2, h3]
  ring

end QC

#print axioms QC.swap_test_overlap

