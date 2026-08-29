/-
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QPhys

/-- **Pauli exclusion principle (antisymmetry form).**

A two-fermion state is described by a map `psi : ι → ι → V` assigning to each pair of
single-particle labels `i j` an amplitude in a complex vector space `V`, subject to the
antisymmetry (exchange) condition `psi i j = - psi j i`.

If the two fermions occupy the *same* single-particle state `i`, the amplitude vanishes:
`psi i i = 0`.  Equivalently (contrapositive): a nonzero amplitude forces the two
single-particle states to be distinguishable. -/
theorem pauli_exclusion_antisym {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (psi : ι → ι → V) (hanti : ∀ i j, psi i j = -psi j i) (i : ι) :
    psi i i = 0 := by
  have h : psi i i = -psi i i := hanti i i
  have h2 : (2 : ℂ) • psi i i = 0 := by
    have : psi i i + psi i i = 0 := by
      nth_rewrite 2 [h]
      exact add_neg_cancel _
    calc (2 : ℂ) • psi i i = psi i i + psi i i := by
          rw [two_smul]
      _ = 0 := this
  have h2' : (2 : ℂ) ≠ 0 := two_ne_zero
  exact (smul_eq_zero.mp h2).resolve_left h2'

/-- Contrapositive form: if a two-fermion antisymmetric amplitude is nonzero for the pair
`(i, j)`, then the two single-particle states are distinct. -/
theorem pauli_exclusion_ne_of_ne_zero {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (psi : ι → ι → V) (hanti : ∀ i j, psi i j = -psi j i) {i j : ι}
    (h : psi i j ≠ 0) : i ≠ j := by
  rintro rfl
  exact h (pauli_exclusion_antisym psi hanti i)

/-- The two-particle Slater determinant built from single-particle orbitals `f` and `g`. -/
def slater {ι : Type*} (f g : ι → ℂ) (i j : ι) : ℂ := f i * g j - f j * g i

/-- The Slater determinant is antisymmetric under exchange of the two particles. -/
theorem slater_antisym {ι : Type*} (f g : ι → ℂ) (i j : ι) :
    slater f g i j = -slater f g j i := by
  simp only [slater]; ring

/-- Pauli exclusion for a Slater determinant: the amplitude for both fermions to occupy the
same single-particle state vanishes. -/
theorem slater_diag_eq_zero {ι : Type*} (f g : ι → ℂ) (i : ι) :
    slater f g i i = 0 :=
  pauli_exclusion_antisym (slater f g) (slater_antisym f g) i

end QPhys

