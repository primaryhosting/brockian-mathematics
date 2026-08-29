/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command, so the header above is written as a
-- plain block comment rather than a `/-!` module docstring.)

import Mathlib

open scoped BigOperators
open scoped Matrix

namespace QI

/-! ## The 9-qubit register

We label the nine qubits by `Site = Fin 3 × Fin 3`: the first coordinate is the *block*
(one of three three-qubit repetition blocks) and the second the position inside the block.
A computational basis state is a bit string `Bits = Site → ZMod 2`, and a state vector is
its amplitude function `Amp = Bits → ℂ`.
-/

abbrev Site : Type := Fin 3 × Fin 3

abbrev Bits : Type := Site → ZMod 2

abbrev Amp : Type := Bits → ℂ

/-- The Hermitian inner product `⟪u, v⟫ = ∑_b conj (u b) * v b`. -/

theorem shor_all_Z_is_logical_flip : ipf zeroL ((Umat 0 allOnes).mulVec oneL) = 1 := by
  rw [ipf_Umat_zero, G_zeroL_oneL_formula]
  have h1 : ∀ c : Fin 3 → ZMod 2, sgn (dot allOnes (rep c) + lw (rep c)) = 1 := by
    intro c
    rw [dot_allOnes_rep, CharTwo.add_self_eq_zero, sgn_zero]
  have hcard : Fintype.card (Fin 3 → ZMod 2) = 8 := by decide
  simp only [h1, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  rw [kappa_sq]
  norm_num

end QI

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

