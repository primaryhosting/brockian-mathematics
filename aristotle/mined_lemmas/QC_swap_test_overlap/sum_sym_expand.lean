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
