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

lemma core (a b u w : Vec) (ha : wt a ≤ 2) (hb : wt b ≤ 2)
    (hu : u = 0 ∨ u = allOnes) (hw : w = 0 ∨ w = allOnes) :
    (∑ x : Vec, chi (dotp b x) * psi u x * psi w (x + a))
      = if a = 0 ∧ b = 0 ∧ u = w then 8 else 0 := by
  by_cases hc : inC2 (a + (u + w))
  · have huw : u = w := by
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
      · rfl
      · exact absurd (by simpa using hc) (coset_min_dist a ha)
      · exact absurd (by simpa using hc) (coset_min_dist a ha)
      · rfl
    subst huw
    have ha0 : a = 0 := by
      refine C2_min_dist a ha ?_
      rwa [vec_add_self, add_zero] at hc
    subst ha0
    by_cases hb0 : b = 0
    · subst hb0
      simp only [dotp, Pi.zero_apply, zero_mul, Finset.sum_const_zero, chi_zero, one_mul,
        add_zero]
      simp only [psi_mul_self]
      simpa using sum_psi u
    · simp only [add_zero, mul_assoc, psi_mul_self]
      rw [char_sum_vanish b u hb hb0]
      rw [if_neg]
      rintro ⟨-, h, -⟩
      exact hb0 h
  · have hzero : ∀ x : Vec, chi (dotp b x) * psi u x * psi w (x + a) = 0 := by
      intro x
      by_cases h1 : inC2 (x + u)
      · by_cases h2 : inC2 ((x + a) + w)
        · exfalso
          apply hc
          rw [add_assoc] at h2
          have h3 : inC2 ((x + u) + (x + (a + w))) := inC2_add h1 h2
          rwa [vec_id1] at h3
        · rw [show psi w (x + a) = 0 from by unfold psi; rw [if_neg h2], mul_zero]
      · rw [show psi u x = 0 from by unfold psi; rw [if_neg h1]]
        ring
    rw [Finset.sum_congr rfl (fun x _ => hzero x), Finset.sum_const_zero]
    rw [if_neg]
    rintro ⟨rfl, rfl, rfl⟩
    exact hc (by rw [vec_add_self, add_zero]; exact inC2_zero)

/-! ## Inner products of Pauli-corrupted logical states -/

