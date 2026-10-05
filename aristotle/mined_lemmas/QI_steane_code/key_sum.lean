/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the
-- header above is a plain block comment; it is repeated verbatim as the module
-- docstring immediately after the import.)

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## The classical ingredients: the `[7,4,3]` Hamming code and its dual -/

/-- A binary register of 7 bits.  Also used to index the computational basis of the
7-qubit Hilbert space. -/
abbrev Reg := Fin 7 → ZMod 2

/-- The `𝔽₂`-bilinear form used both for parity checks and for Pauli phases. -/

lemma key_sum (a b : Reg) (i j : Bool) (ha : wt a ≤ 2) (hb : wt b ≤ 2) :
    (∑ v : Reg, (sgnZ (dotp b v) : ℂ) * (psiF i v * psiF j (v + a)))
      = if a = 0 ∧ b = 0 ∧ i = j then 8 else 0 := by
  by_cases ha0 : a = 0
  · by_cases hij : i = j
    · subst ha0; subst hij
      simp only [add_zero, psiF_mul_self]
      -- sum over the coset of the character
      have step1 : (∑ v : Reg, (sgnZ (dotp b v) : ℂ) * psiF i v)
          = ∑ v ∈ cosetOf i, (sgnZ (dotp b v) : ℂ) := by
        unfold psiF
        rw [← Finset.sum_filter_ne_zero]
        rw [Finset.sum_congr rfl (fun v _ => rfl)]
        classical
        have : ∀ v : Reg, (sgnZ (dotp b v) : ℂ) * (if v ∈ cosetOf i then 1 else 0)
            = if v ∈ cosetOf i then (sgnZ (dotp b v) : ℂ) else 0 := by
          intro v; split <;> simp
        simp only [this]
        rw [Finset.sum_filter_ne_zero]
        rw [Finset.sum_ite_mem]
        simp
      rw [step1]
      have hinj : Set.InjOn (fun u => u + shiftv i) Sfin := by
        intro x _ y _ hxy
        simpa using add_right_cancel hxy
      rw [cosetOf, Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
      have hd : ∀ u : Reg, (sgnZ (dotp b (u + shiftv i)) : ℂ)
          = (sgnZ (dotp b (shiftv i)) : ℂ) * (sgnZ (dotp b u) : ℂ) := by
        intro u
        rw [dotp_add_right, sgnZ_add]
        push_cast
        ring
      simp only [hd]
      rw [← Finset.mul_sum]
      by_cases hb0 : b = 0
      · subst hb0
        simp only [dotp_zero_left, sgnZ_zero]
        rw [Finset.sum_const]
        simp [Sfin_card]
      · have : (∑ u ∈ Sfin, (sgnZ (dotp b u) : ℂ)) = ((∑ u ∈ Sfin, sgnZ (dotp b u) : ℤ) : ℂ) := by
          push_cast; ring
        rw [this, character_sum_zero b hb hb0]
        simp [hb0]
    · have : ∀ v : Reg, (sgnZ (dotp b v) : ℂ) * (psiF i v * psiF j (v + a)) = 0 := by
        intro v
        rw [psiF_mul_shift_eq_zero a i j ha (Or.inr hij) v, mul_zero]
      simp [this, hij]
  · have : ∀ v : Reg, (sgnZ (dotp b v) : ℂ) * (psiF i v * psiF j (v + a)) = 0 := by
      intro v
      rw [psiF_mul_shift_eq_zero a i j ha (Or.inl ha0) v, mul_zero]
    simp [this, ha0]

