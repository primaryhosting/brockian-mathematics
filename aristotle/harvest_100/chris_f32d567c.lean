/-
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
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

namespace QC

open Finset

/-- A (pure) state of an `n`-level quantum system is a unit vector in `ℂ^n`, i.e. a
function `Fin n → ℂ` whose squared amplitudes sum to `1`. -/
def IsState {n : ℕ} (psi : Fin n → ℂ) : Prop := ∑ i, ‖psi i‖ ^ 2 = 1

/-- The overlap (inner product) `⟪ψ, φ⟫ = ∑ i, conj (ψ i) * φ i` of two states. -/
noncomputable def overlap {n : ℕ} (psi phi : Fin n → ℂ) : ℂ := ∑ i, (starRingEnd ℂ) (psi i) * phi i

/-- The product state `ψ ⊗ φ` of the two registers, as a vector indexed by pairs. -/
def prodState {n : ℕ} (psi phi : Fin n → ℂ) : Fin n × Fin n → ℂ := fun p => psi p.1 * phi p.2

/-- The SWAP operator on the two registers. -/
def swapOp {n : ℕ} (Psi : Fin n × Fin n → ℂ) : Fin n × Fin n → ℂ := fun p => Psi (p.2, p.1)

/-- The acceptance probability of the SWAP test on the input `ψ ⊗ φ`.

The SWAP test applies a Hadamard gate to an ancilla qubit prepared in `|0⟩`, then a
controlled-SWAP on the two registers, then a second Hadamard, and measures the ancilla.
The ancilla-outcome-`0` (accept) branch carries the unnormalised two-register vector
`(Ψ + SWAP Ψ)/2`, i.e. the projection of `Ψ` onto the symmetric subspace, so the
acceptance probability is the squared norm of that vector. -/
noncomputable def swapTestAccept {n : ℕ} (psi phi : Fin n → ℂ) : ℝ :=
  ∑ p : Fin n × Fin n,
    ‖(prodState psi phi p + swapOp (prodState psi phi) p) / 2‖ ^ 2

/-- Auxiliary algebraic identity: the expansion of the symmetrised squared norm. -/
private lemma sum_sym_expand {n : ℕ} (psi phi : Fin n → ℂ) :
    ∑ i, ∑ j, ((psi i * phi j + psi j * phi i) * (starRingEnd ℂ) (psi i * phi j + psi j * phi i))
      = 2 * ((∑ i, psi i * (starRingEnd ℂ) (psi i)) * (∑ j, phi j * (starRingEnd ℂ) (phi j)))
        + 2 * (overlap psi phi * (starRingEnd ℂ) (overlap psi phi)) := by
  have key : ∀ i j : Fin n,
      ((psi i * phi j + psi j * phi i) * (starRingEnd ℂ) (psi i * phi j + psi j * phi i))
        = (psi i * (starRingEnd ℂ) (psi i)) * (phi j * (starRingEnd ℂ) (phi j))
          + (psi i * (starRingEnd ℂ) (phi i)) * ((starRingEnd ℂ) (psi j) * phi j)
          + ((starRingEnd ℂ) (psi i) * phi i) * (psi j * (starRingEnd ℂ) (phi j))
          + (psi j * (starRingEnd ℂ) (psi j)) * (phi i * (starRingEnd ℂ) (phi i)) := by
    intro i j
    simp only [map_add, map_mul]
    ring
  simp only [overlap, map_sum]
  simp only [key, map_mul, Complex.conj_conj]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- **Swap test overlap.**  For two pure states `ψ` and `φ` of an `n`-level system, the SWAP
test accepts with probability `(1 + |⟪ψ, φ⟫|²)/2`. -/
theorem swap_test_overlap {n : ℕ} (psi phi : Fin n → ℂ)
    (hpsi : IsState psi) (hphi : IsState phi) :
    swapTestAccept psi phi = (1 + ‖overlap psi phi‖ ^ 2) / 2 := by
  -- Recast the two normalisation conditions as complex identities.
  have hpsiC : (∑ i, psi i * (starRingEnd ℂ) (psi i)) = 1 := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) hpsi
    simp only [Complex.ofReal_sum, Complex.ofReal_one] at h
    push_cast at h
    simpa [Complex.mul_conj'] using h
  have hphiC : (∑ i, phi i * (starRingEnd ℂ) (phi i)) = 1 := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) hphi
    simp only [Complex.ofReal_sum, Complex.ofReal_one] at h
    push_cast at h
    simpa [Complex.mul_conj'] using h
  -- It suffices to check the identity after casting to `ℂ`.
  apply Complex.ofReal_injective
  have hsum : ((swapTestAccept psi phi : ℝ) : ℂ)
      = (∑ i, ∑ j, ((psi i * phi j + psi j * phi i)
          * (starRingEnd ℂ) (psi i * phi j + psi j * phi i))) / 4 := by
    simp only [swapTestAccept, prodState, swapOp, Complex.ofReal_sum, Finset.sum_div]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := Complex.mul_conj' ((psi i * phi j + psi j * phi i) / 2)
    dsimp only
    push_cast
    rw [← h]
    simp only [map_div₀, map_ofNat]
    ring
  rw [hsum, sum_sym_expand psi phi, hpsiC, hphiC]
  push_cast
  rw [← Complex.mul_conj' (overlap psi phi)]
  ring

end QC

