import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

/-!
# Landau levels

A charged particle of mass `m` and charge `q` moving in the plane in a uniform magnetic field `B`
perpendicular to the plane has energy spectrum `ℏ ω_c (n + 1/2)`, where `ω_c = q B / m` is the
cyclotron frequency.

We work in the Landau gauge `A = (0, B x)`, so that the Hamiltonian is

  `H = (1/(2m)) ( (-iℏ ∂ₓ)² + (-iℏ ∂_y - q B x)² )`
    `= (1/(2m)) ( -ℏ² ∂ₓ² - ℏ² ∂_y² + 2iℏ q B x ∂_y + q²B²x² )`,

which is `Frontier.landauH` below.

The eigenfunctions are `exp (i k y)` times a shifted Hermite function of `x`
(`Frontier.landauState`), and `Frontier.landau_levels` states that these are eigenfunctions of
`landauH` with eigenvalue `ℏ (qB/m) (n + 1/2)`.
-/

namespace Frontier

open Polynomial

/-! ### Hermite polynomial preliminaries -/

/-- The derivative of the (probabilists') Hermite polynomial: `He_{n+1}' = (n+1) He_n`. -/

theorem landauState_ne_zero (q B hbar k : ℝ) (hq : 0 < q) (hB : 0 < B) (hhbar : 0 < hbar)
    (n : ℕ) : ∃ x y : ℝ, landauState q B hbar k n x y ≠ 0 := by
  have hHe : ∃ y : ℝ, He n y ≠ 0 := by
    by_contra h
    push_neg at h
    have hp : ((hermite n).map (Int.castRingHom ℝ)) ≠ 0 := ((hermite_monic n).map _).ne_zero
    apply hp
    apply Polynomial.funext
    intro y
    simpa [He, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using h y
  obtain ⟨y0, hy0⟩ := hHe
  have hb : 0 < landauB q B hbar := Real.sqrt_pos.mpr (by positivity)
  refine ⟨landauCentre q B hbar k + y0 / landauB q B hbar, 0, ?_⟩
  have hx : landauB q B hbar *
      (landauCentre q B hbar k + y0 / landauB q B hbar - landauCentre q B hbar k) = y0 := by
    field_simp
    ring
  simp only [landauState, hx]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  simpa [hFun, Real.exp_ne_zero] using hy0

end Frontier

