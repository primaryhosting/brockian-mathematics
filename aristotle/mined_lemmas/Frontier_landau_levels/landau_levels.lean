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

set_option grind.warning false

namespace Frontier

open Polynomial

/-! ## Physicists' Hermite polynomials -/

/-- The physicists' Hermite polynomials, defined by `H₀ = 1` and
`H_{n+1} = 2X H_n - H_n'`. -/

theorem landau_levels (m hbar q B k : ℝ) (n : ℕ) (hm : m ≠ 0) (hhbar : 0 < hbar)
    (hqB : 0 < q * B) :
    landauH m hbar q B (landauPsi hbar q B n k) =
      fun x y => ((hbar * omegaC m q B * (n + 1 / 2) : ℝ) : ℂ) * landauPsi hbar q B n k x y := by
  have hQ : q * B ≠ 0 := ne_of_gt hqB
  have hhb : hbar ≠ 0 := ne_of_gt hhbar
  have hc : (Real.sqrt (q * B / hbar)) ^ 2 = q * B / hbar :=
    Real.sq_sqrt (le_of_lt (div_pos hqB hhbar))
  have h1 : ∀ x : ℝ,
      HasDerivAt (fun s : ℝ => oscFun n (Real.sqrt (q * B / hbar) * (s - hbar * k / (q * B))))
        (Real.sqrt (q * B / hbar) *
          gfun (hermiteQ n) (Real.sqrt (q * B / hbar) * (x - hbar * k / (q * B)))) x :=
    fun x => hasDerivAt_gfun_affine (hermiteP n) _ _ x
  have h2 : ∀ x : ℝ,
      HasDerivAt (fun s : ℝ => Real.sqrt (q * B / hbar) *
          gfun (hermiteQ n) (Real.sqrt (q * B / hbar) * (s - hbar * k / (q * B))))
        (Real.sqrt (q * B / hbar) * (Real.sqrt (q * B / hbar) *
          gfun (derivative (hermiteQ n) - X * hermiteQ n)
            (Real.sqrt (q * B / hbar) * (x - hbar * k / (q * B))))) x :=
    fun x => (hasDerivAt_gfun_affine (hermiteQ n) _ _ x).const_mul _
  have hpsi : landauPsi hbar q B n k = fun x y : ℝ => Complex.exp (Complex.I * k * y) *
      (((fun s : ℝ => oscFun n (Real.sqrt (q * B / hbar) * (s - hbar * k / (q * B)))) x : ℝ) : ℂ) :=
    rfl
  funext x y
  rw [hpsi]
  simp only [landauH, piX_sq_sep hbar k _ _ _ h1 h2, piY_sep]
  rw [gfun_hermiteQ_deriv]
  simp only [omegaC]
  push_cast
  have hCsq : ((Real.sqrt (q * B / hbar) : ℝ) : ℂ) ^ 2 = ((q : ℂ) * B) / (hbar : ℂ) := by
    rw [← Complex.ofReal_pow, hc]; push_cast; ring
  have halg := landau_alg (m : ℂ) (hbar : ℂ) ((q : ℂ) * B)
    ((Real.sqrt (q * B / hbar) : ℝ) : ℂ)
    ((oscFun n (Real.sqrt (q * B / hbar) * (x - hbar * k / (q * B))) : ℝ) : ℂ)
    (Complex.exp (Complex.I * k * y)) (n : ℂ) (k : ℂ) (x : ℂ)
    (by exact_mod_cast hm) (by exact_mod_cast hhb) (by exact_mod_cast hQ) hCsq
  linear_combination halg

/-- The Landau eigenstates are genuinely nonzero, so `landau_levels` really exhibits
`ℏ ω_c (n + 1/2)` as an eigenvalue. -/
