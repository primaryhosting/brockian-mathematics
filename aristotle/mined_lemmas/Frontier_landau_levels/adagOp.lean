/-
# Landau Levels — a concrete model
A Fock-space realization of the ladder-operator hypotheses used in
`Frontier.landau_levels`, showing that they are consistent and that every
level `ℏ ω_c (n + 1/2)` really occurs.
-/

import Mathlib
import RequestProject.LandauLevels

namespace Frontier.Fock

/-! ### The inner product on finitely supported sequences -/

/-- The Fock inner product on finitely supported complex sequences. -/

noncomputable def adagOp : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) where
  toFun := adagFun
  map_add' x y := by
    ext m
    by_cases h : m = 0 <;>
      simp only [adagFun_apply, Finsupp.add_apply, h, if_true, if_false, mul_add, add_zero]
  map_smul' r x := by
    ext m
    by_cases h : m = 0
    · simp [adagFun_apply, h]
    · simp only [adagFun_apply, Finsupp.smul_apply, RingHom.id_apply, smul_eq_mul, h, if_false]
      ring

