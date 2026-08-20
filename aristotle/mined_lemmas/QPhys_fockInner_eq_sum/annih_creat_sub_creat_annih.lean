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

lemma annih_creat_sub_creat_annih (f : ℕ →₀ ℂ) : annih (creat f) - creat (annih f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ =>
      simp only [map_add]
      rw [show annih (creat f₁) + annih (creat f₂) - (creat (annih f₁) + creat (annih f₂))
            = (annih (creat f₁) - creat (annih f₁)) + (annih (creat f₂) - creat (annih f₂)) by
          abel, h₁, h₂]
  | single n c =>
      rw [creat_single, annih_single, annih_single, creat_single]
      rcases n with _ | k
      · simp
      · simp only [Nat.add_sub_cancel]
        rw [← Finsupp.single_sub]
        congr 1
        push_cast
        ring

/-! ## Position and momentum -/

/-- Position operator `X = a + a†`. -/
