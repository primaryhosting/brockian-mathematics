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
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ComplexConjugate Finset

namespace QC

variable {n : ℕ}

/-- A pure state of an `n`-level quantum register. -/
abbrev Reg (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- A state of the full swap-test system: one ancilla qubit together with two
`n`-level registers.  We record it as its amplitude function. -/
abbrev SysState (n : ℕ) := Fin 2 × (Fin n × Fin n) → ℂ

/-- The Hadamard gate acting on the ancilla qubit. -/

lemma sum_antisymmetrised (ψ φ : Reg n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    ∑ x : Fin n × Fin n,
      (ψ.ofLp x.1 * φ.ofLp x.2 - ψ.ofLp x.2 * φ.ofLp x.1) *
        conj (ψ.ofLp x.1 * φ.ofLp x.2 - ψ.ofLp x.2 * φ.ofLp x.1)
      = 2 - 2 * ((inner ℂ ψ φ : ℂ) * conj (inner ℂ ψ φ : ℂ)) := by
  have hc := inner_eq_sum ψ φ
  have hcc : conj (inner ℂ ψ φ : ℂ) = ∑ i, ψ.ofLp i * conj (φ.ofLp i) := by
    rw [hc, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, Complex.conj_conj, mul_comm]
  have expand : ∀ i j : Fin n,
      (ψ.ofLp i * φ.ofLp j - ψ.ofLp j * φ.ofLp i) *
        conj (ψ.ofLp i * φ.ofLp j - ψ.ofLp j * φ.ofLp i)
      = (ψ.ofLp i * conj (ψ.ofLp i)) * (φ.ofLp j * conj (φ.ofLp j))
        + (ψ.ofLp i * conj (φ.ofLp i)) * (-(conj (ψ.ofLp j) * φ.ofLp j))
        + (conj (ψ.ofLp i) * φ.ofLp i) * (-(ψ.ofLp j * conj (φ.ofLp j)))
        + (φ.ofLp i * conj (φ.ofLp i)) * (ψ.ofLp j * conj (ψ.ofLp j)) := by
    intro i j
    simp only [map_sub, map_mul]
    ring
  rw [Fintype.sum_prod_type]
  simp only [expand, Finset.sum_add_distrib, ← Finset.sum_mul_sum, Finset.sum_neg_distrib]
  rw [sum_mul_conj_self ψ hψ, sum_mul_conj_self φ hφ, ← hc, ← hcc]
  ring

/-- **Swap test.** For unit vectors `ψ` and `φ`, the swap test accepts (the ancilla is
measured to be `0`) with probability `(1 + |⟨ψ, φ⟩|²)/2`. -/
