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

lemma ip_pauli_code (i j : Fin 7) (s1 t1 s2 t2 : ZMod 2) (f g : Vec → ℂ)
    (hf : codeVec f) (hg : codeVec g) :
    ip ((pauli (unit i s1) (unit i t1)).mulVec f) ((pauli (unit j s2) (unit j t2)).mulVec g)
      = (if unit i s1 = unit j s2 ∧ unit i t1 = unit j t2 then 1 else 0) * ip f g := by
  obtain ⟨α, β, rfl⟩ := hf
  obtain ⟨γ, δ, rfl⟩ := hg
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, ip_add_left, ip_add_right,
    ip_smul_left, ip_smul_right]
  rw [ip_pauli_unit i j s1 t1 s2 t2 0 0 (Or.inl rfl) (Or.inl rfl),
      ip_pauli_unit i j s1 t1 s2 t2 0 allOnes (Or.inl rfl) (Or.inr rfl),
      ip_pauli_unit i j s1 t1 s2 t2 allOnes 0 (Or.inr rfl) (Or.inl rfl),
      ip_pauli_unit i j s1 t1 s2 t2 allOnes allOnes (Or.inr rfl) (Or.inr rfl),
      ip_psi 0 0 (Or.inl rfl) (Or.inl rfl), ip_psi 0 allOnes (Or.inl rfl) (Or.inr rfl),
      ip_psi allOnes 0 (Or.inr rfl) (Or.inl rfl),
      ip_psi allOnes allOnes (Or.inr rfl) (Or.inr rfl)]
  rw [if_neg zero_ne_allOnes, if_neg (Ne.symm zero_ne_allOnes), if_pos rfl, if_pos rfl]
  by_cases hP : unit i s1 = unit j s2 ∧ unit i t1 = unit j t2
  · rw [if_pos hP,
      if_pos (show unit i s1 = unit j s2 ∧ unit i t1 = unit j t2 ∧ (0 : Vec) = 0 from
        ⟨hP.1, hP.2, rfl⟩),
      if_pos (show unit i s1 = unit j s2 ∧ unit i t1 = unit j t2 ∧ allOnes = allOnes from
        ⟨hP.1, hP.2, rfl⟩),
      if_neg (fun h => (Ne.symm zero_ne_allOnes) h.2.2),
      if_neg (fun h => zero_ne_allOnes h.2.2)]
    ring
  · rw [if_neg hP, if_neg (fun h => hP ⟨h.1, h.2.1⟩), if_neg (fun h => hP ⟨h.1, h.2.1⟩),
      if_neg (fun h => hP ⟨h.1, h.2.1⟩), if_neg (fun h => hP ⟨h.1, h.2.1⟩)]
    ring

/-! ## Pauli decomposition of an arbitrary single-qubit operator -/

