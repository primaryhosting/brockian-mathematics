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
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain block comment; it is repeated verbatim below.)

import Mathlib

/-!
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open scoped ComplexConjugate

variable {n : ℕ}

/-- A (pure) state of an `n`-level system, given by its amplitude vector. -/
abbrev State (n : ℕ) := Fin n → ℂ

/-- The amplitude vector of the tensor product `ψ ⊗ φ` of two states. -/

lemma sum_antisymmetrized (ψ φ : State n) :
    ∑ p : Fin n × Fin n, ((ψ p.1 * φ p.2 - ψ p.2 * φ p.1) / 2) *
        conj ((ψ p.1 * φ p.2 - ψ p.2 * φ p.1) / 2)
      = ((∑ i, ψ i * conj (ψ i)) * (∑ j, φ j * conj (φ j))
          - (∑ i, conj (ψ i) * φ i) * (∑ j, ψ j * conj (φ j))) / 2 := by
  set A : Fin n → Fin n → ℂ := fun i j => (ψ i * conj (ψ i)) * (φ j * conj (φ j)) with hA
  set B : Fin n → Fin n → ℂ := fun i j => (φ i * conj (ψ i)) * (ψ j * conj (φ j)) with hB
  have hcommA : ∑ i, ∑ j, A j i = ∑ i, ∑ j, A i j := Finset.sum_comm
  have hcommB : ∑ i, ∑ j, B j i = ∑ i, ∑ j, B i j := Finset.sum_comm
  have step1 : ∑ p : Fin n × Fin n, ((ψ p.1 * φ p.2 - ψ p.2 * φ p.1) / 2) *
        conj ((ψ p.1 * φ p.2 - ψ p.2 * φ p.1) / 2)
      = ∑ i, ∑ j, ((A i j + A j i - B i j - B j i) / 4) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hA, hB, map_div₀, map_sub, map_mul, Complex.conj_ofNat]
    ring
  have step2 : ∑ i, ∑ j, ((A i j + A j i - B i j - B j i) / 4)
      = ((∑ i, ∑ j, A i j) + (∑ i, ∑ j, A j i) - (∑ i, ∑ j, B i j) - (∑ i, ∑ j, B j i)) / 4 := by
    simp only [← Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  have hprodA : (∑ i, ψ i * conj (ψ i)) * (∑ j, φ j * conj (φ j)) = ∑ i, ∑ j, A i j := by
    rw [Finset.sum_mul_sum]
  have hprodB : (∑ i, conj (ψ i) * φ i) * (∑ j, ψ j * conj (φ j)) = ∑ i, ∑ j, B i j := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      simp only [hB]; ring
  rw [step1, step2, hcommA, hcommB, hprodA, hprodB]
  ring

/-- The swap test rejects with probability `(1 - |⟨ψ|φ⟩|²)/2`. -/
