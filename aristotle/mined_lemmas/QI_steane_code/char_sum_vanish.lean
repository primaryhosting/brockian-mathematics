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

lemma char_sum_vanish (b u : Vec) (hb : wt b ≤ 2) (hb0 : b ≠ 0) :
    (∑ x : Vec, chi (dotp b x) * psi u x) = 0 := by
  have hex : ∃ j, dotp (Hrow j) b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hb0 (C1_min_dist b hb h)
  obtain ⟨j, hj⟩ := hex
  set c : Vec := Hrow j with hcdef
  have hc2 : inC2 c := Hrow_mem_C2 j
  have hbc : dotp b c = 1 := by
    have : dotp b c = dotp (Hrow j) b := by rw [hcdef, dotp_comm]
    rw [this]
    revert hj
    generalize dotp (Hrow j) b = z
    revert z
    decide
  have key : ∀ x : Vec, chi (dotp b (x + c)) * psi u (x + c)
      = -(chi (dotp b x) * psi u x) := by
    intro x
    rw [dotp_add_right, hbc, chi_add, psi_shift hc2,
      (by rw [chi, if_neg (by decide : ¬((1 : ZMod 2) = 0))] : chi 1 = -1)]
    ring
  have h1 : (∑ x : Vec, chi (dotp b x) * psi u x)
      = -(∑ x : Vec, chi (dotp b x) * psi u x) := by
    conv_lhs => rw [sum_shift (fun x => chi (dotp b x) * psi u x) c]
    simp only [key, Finset.sum_neg_distrib]
  have h2 : (2 : ℂ) * (∑ x : Vec, chi (dotp b x) * psi u x) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact h

/-- The fundamental character sum computation for the Steane code. -/
