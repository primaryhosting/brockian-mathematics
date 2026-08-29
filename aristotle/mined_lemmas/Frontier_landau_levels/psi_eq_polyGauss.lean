/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the header above is a plain block
-- comment; the same text is repeated below as the module docstring.)

import Mathlib

/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Polynomial

/-! ### Hermite polynomials: the Hermite differential equation

Mathlib provides `Polynomial.hermite : ℕ → ℤ[X]` (the *probabilists'* Hermite polynomials)
together with `Polynomial.hermite_succ`, but not the Hermite ODE, which we derive here. -/

/-- The Hermite differential equation `He_n'' = X * He_n' - n * He_n`. -/

theorem psi_eq_polyGauss (hbar m om x0 : ℝ) (hh : 0 < hbar) (hm : 0 < m) (ho : 0 < om)
    (n : ℕ) (ell : ℝ) (hell : ell = Real.sqrt (hbar / (m * om)))
    (psi : ℝ → ℝ)
    (hpsi : ∀ x, psi x = Polynomial.aeval (Real.sqrt 2 * (x - x0) / ell) (hermite n)
      * Real.exp (-((x - x0) ^ 2 / (2 * ell ^ 2)))) :
    ∃ a b : ℝ, a ≠ 0 ∧ a ^ 2 = 4 * b ∧ b = m * om / (2 * hbar) ∧
      psi = polyGauss (hermiteR n) a b x0 := by
  have hpos : 0 < hbar / (m * om) := by positivity
  have hell0 : 0 < ell := by rw [hell]; exact Real.sqrt_pos.mpr hpos
  have hell2 : ell ^ 2 = hbar / (m * om) := by rw [hell, Real.sq_sqrt hpos.le]
  refine ⟨Real.sqrt 2 / ell, 1 / (2 * ell ^ 2), ?_, ?_, ?_, ?_⟩
  · have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    positivity
  · rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
    norm_num
  · rw [hell2]; field_simp
  · funext s
    rw [hpsi s]
    simp only [polyGauss]
    rw [hermiteR_eval,
      show Real.sqrt 2 / ell * (s - x0) = Real.sqrt 2 * (s - x0) / ell from by ring,
      show 1 / (2 * ell ^ 2) * (s - x0) ^ 2 = (s - x0) ^ 2 / (2 * ell ^ 2) from by ring]

/-- **Harmonic oscillator spectrum.**  With `ℓ = √(ħ/(mω))` the oscillator length, the
function `ψ_n(x) = He_n(√2 (x-x₀)/ℓ) exp(-(x-x₀)²/(2ℓ²))` is an eigenfunction of the
Hamiltonian `-ħ²/(2m) d²/dx² + ½ m ω² (x-x₀)²` with eigenvalue `ħω(n + ½)`. -/
