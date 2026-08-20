import Mathlib
import RequestProject.Main

/-!
# A concrete model for the canonical commutation relation

This file shows that the hypotheses of `QPhys.heisenberg_uncertainty` are *consistent* with a
nonzero `ℏ`: we build the (algebraic) Fock space of finitely supported sequences `ℕ →₀ ℂ`
with the Bargmann inner product `⟪eₘ, eₙ⟫ = n! δₘₙ`, the annihilation and creation operators,
and the resulting position and momentum operators `X`, `P`, which are symmetric and satisfy
`X P - P X = i` (i.e. `ℏ = 1`).
-/

open scoped ComplexConjugate InnerProductSpace
open Finsupp

namespace QPhys

/-! ## The Bargmann inner product on `ℕ →₀ ℂ` -/

/-- The Bargmann inner product: `⟪f, g⟫ = ∑ₙ conj (f n) * g n * n!`. -/

lemma inner_annih_left (f g : ℕ →₀ ℂ) : ⟪annih f, g⟫_ℂ = ⟪f, creat g⟫_ℂ := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | single n d =>
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add f₁ f₂ h₁ h₂ => simp [map_add, h₁, h₂]
      | single m c =>
          rw [annih_single, creat_single, inner_fock, inner_fock, fockInner_single_right,
            fockInner_single_right]
          rcases m with _ | k
          · simp
          · simp only [Nat.add_sub_cancel, Finsupp.single_apply]
            by_cases hnk : n = k
            · subst hnk
              rw [Nat.factorial_succ]
              simp only [if_true, map_mul, Complex.conj_natCast]
              push_cast
              ring
            · rw [if_neg (by omega), if_neg (by omega)]
              simp

/-- `annih` is the adjoint of `creat`. -/
