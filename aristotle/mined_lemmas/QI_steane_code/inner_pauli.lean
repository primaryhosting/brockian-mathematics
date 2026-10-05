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

lemma inner_pauli (a₁ b₁ a₂ b₂ : Reg) (i j : Bool)
    (ha : wt (a₁ + a₂) ≤ 2) (hb : wt (b₁ + b₂) ≤ 2) :
    ⟪pauliLM a₁ b₁ (psi i), pauliLM a₂ b₂ (psi j)⟫_ℂ
      = (sgnZ (dotp (b₁ + b₂) a₁) : ℂ) *
          (if a₁ + a₂ = 0 ∧ b₁ + b₂ = 0 ∧ i = j then 8 else 0) := by
  have hip : ⟪pauliLM a₁ b₁ (psi i), pauliLM a₂ b₂ (psi j)⟫_ℂ
      = ∑ v : Reg, star (pauliLM a₁ b₁ (psi i) v) * (pauliLM a₂ b₂ (psi j) v) := by
    rw [PiLp.inner_apply]; simp [RCLike.inner_apply, mul_comm]
  rw [hip]
  have hterm : ∀ v : Reg, star (pauliLM a₁ b₁ (psi i) v) * (pauliLM a₂ b₂ (psi j) v)
      = (sgnZ (dotp (b₁ + b₂) v) : ℂ) * (psiF i (v + a₁) * psiF j (v + a₂)) := by
    intro v
    simp only [pauliLM_apply, psi_apply, star_mul']
    rw [dotp_add_left, sgnZ_add]
    have h1 : star ((sgnZ (dotp b₁ v) : ℂ)) = ((sgnZ (dotp b₁ v) : ℂ)) := by
      simp
    rw [psiF_real, h1]
    push_cast
    ring
  simp only [hterm]
  -- reindex `v ↦ v + a₁`
  have hre : (∑ v : Reg, (sgnZ (dotp (b₁ + b₂) v) : ℂ) * (psiF i (v + a₁) * psiF j (v + a₂)))
      = ∑ w : Reg, (sgnZ (dotp (b₁ + b₂) (w + a₁)) : ℂ) *
          (psiF i w * psiF j (w + (a₁ + a₂))) := by
    refine (Fintype.sum_equiv (Equiv.addRight a₁) _ _ ?_).symm
    intro w
    simp only [Equiv.coe_addRight]
    have e1 : w + a₁ + a₁ = w := by rw [add_assoc, add_self_reg, add_zero]
    have e2 : w + a₁ + a₂ = w + (a₁ + a₂) := add_assoc w a₁ a₂
    rw [e1, e2]
  rw [hre]
  have hfac : ∀ w : Reg, (sgnZ (dotp (b₁ + b₂) (w + a₁)) : ℂ) *
      (psiF i w * psiF j (w + (a₁ + a₂)))
      = (sgnZ (dotp (b₁ + b₂) a₁) : ℂ) *
        ((sgnZ (dotp (b₁ + b₂) w) : ℂ) * (psiF i w * psiF j (w + (a₁ + a₂)))) := by
    intro w
    rw [dotp_add_right, sgnZ_add]
    push_cast
    ring
  simp only [hfac]
  rw [← Finset.mul_sum, key_sum (a₁ + a₂) (b₁ + b₂) i j ha hb]

/-! ## Support bookkeeping for single-qubit errors -/

