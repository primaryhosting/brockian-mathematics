/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not permit a module
-- docstring before the `import` commands.)

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Setup

The state space of `7` qubits is modelled as the space of complex-valued functions on
`Vec := Fin 7 → ZMod 2`, the set of the `2^7` computational basis labels, with the
standard hermitian inner product `ip`.  Linear operators are `Matrix Vec Vec ℂ` acting
by `Matrix.mulVec`.
-/

/-- Computational basis labels for 7 qubits. -/
abbrev Vec := Fin 7 → ZMod 2

/-- The `𝔽₂`-bilinear form on `Vec`. -/

lemma ip_pauli (a1 b1 a2 b2 u w : Vec) (hA : wt (a1 + a2) ≤ 2) (hB : wt (b1 + b2) ≤ 2)
    (hu : u = 0 ∨ u = allOnes) (hw : w = 0 ∨ w = allOnes) :
    ip ((pauli a1 b1).mulVec (psi u)) ((pauli a2 b2).mulVec (psi w))
      = if a1 = a2 ∧ b1 = b2 ∧ u = w then 8 else 0 := by
  have hpt : ∀ x : Vec,
      (starRingEnd ℂ) ((pauli a1 b1).mulVec (psi u) (x + a1))
          * ((pauli a2 b2).mulVec (psi w) (x + a1))
        = chi (dotp b2 (a1 + a2))
            * (chi (dotp (b1 + b2) x) * psi u x * psi w (x + (a1 + a2))) := by
    intro x
    rw [pauli_mulVec, pauli_mulVec, vec_add_cancel, add_assoc x a1 a2, map_mul, chi_conj,
      psi_conj, dotp_add_right b2 x (a1 + a2), chi_add, dotp_add_left, chi_add]
    ring
  unfold ip
  rw [sum_shift _ a1]
  simp only [hpt]
  rw [← Finset.mul_sum, core (a1 + a2) (b1 + b2) u w hA hB hu hw]
  simp only [vec_add_eq_zero_iff]
  by_cases h : a1 = a2 ∧ b1 = b2 ∧ u = w
  · obtain ⟨rfl, rfl, rfl⟩ := h
    rw [if_pos ⟨rfl, rfl, rfl⟩, vec_add_self, dotp_zero, chi_zero, one_mul]
  · rw [if_neg h, mul_zero]

/-! ## Sesquilinearity of the inner product -/

