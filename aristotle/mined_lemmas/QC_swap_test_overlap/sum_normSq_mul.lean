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

/-!
# The SWAP test

We model the SWAP test circuit explicitly.  A pure state of a finite-dimensional
system with basis indexed by `ι` is a vector `psi : ι → ℂ` with `∑ i, ‖psi i‖ ^ 2 = 1`.

The circuit acts on one ancilla qubit together with two copies of the system,
i.e. on vectors indexed by `Fin 2 × ι × ι`:

* the input is `|0⟩ ⊗ |psi⟩ ⊗ |phi⟩`;
* a Hadamard gate is applied to the ancilla;
* a controlled-SWAP exchanges the two system registers when the ancilla is `1`;
* a Hadamard gate is applied to the ancilla again;
* the ancilla is measured, and the test *accepts* when the outcome is `0`.

The main result `QC.swap_test_overlap` states that the acceptance probability is
`(1 + |⟨psi|phi⟩| ^ 2) / 2`.
-/

namespace QC

variable {ι : Type*} [Fintype ι]

/-- The Hermitian inner product `⟨psi|phi⟩ = ∑ i, conj (psi i) * phi i`. -/

lemma sum_normSq_mul (psi phi : ι → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) (hphi : ∑ i, ‖phi i‖ ^ 2 = 1) :
    ∑ i, ∑ j, Complex.normSq (psi i * phi j) = 1 := by
  have h : ∑ i, ∑ j, Complex.normSq (psi i * phi j)
      = (∑ i, Complex.normSq (psi i)) * ∑ j, Complex.normSq (phi j) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Complex.normSq_mul _ _
  rw [h]
  simp only [Complex.normSq_eq_norm_sq]
  rw [hpsi, hphi, one_mul]

