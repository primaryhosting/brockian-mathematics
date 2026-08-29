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

noncomputable def aOp : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) where
  toFun := aFun
  map_add' x y := by
    ext m; simp only [aFun_apply, Finsupp.add_apply, mul_add]
  map_smul' r x := by
    ext m
    simp only [aFun_apply, Finsupp.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- The creation operator as a linear map. -/
