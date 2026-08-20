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

lemma sum_cross (psi phi : ι → ℂ) :
    ∑ i, ∑ j, ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re = ‖overlap psi phi‖ ^ 2 := by
  have key : ∑ i, ∑ j, ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i))
      = (starRingEnd ℂ) (overlap psi phi) * overlap psi phi := by
    have h1 : (starRingEnd ℂ) (overlap psi phi) = ∑ i, psi i * (starRingEnd ℂ) (phi i) := by
      simp only [overlap, map_sum, map_mul, Complex.conj_conj]
    rw [h1, overlap, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul]
    ring
  calc ∑ i, ∑ j, ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re
      = (∑ i, ∑ j, ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i))).re := by
        simp [Complex.re_sum]
    _ = ‖overlap psi phi‖ ^ 2 := by
        rw [key, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          Complex.ofReal_re]

/-- **The SWAP test.**  If `psi` and `phi` are unit vectors, the SWAP test accepts with
probability `(1 + |⟨psi|phi⟩| ^ 2) / 2`. -/
