/-
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the mandated
-- header above is written as an ordinary block comment; its text is unchanged.)

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-! ## Definitions -/

/-- The **Unruh temperature** `T = ℏ a / (2 π c k_B)` associated with proper acceleration `a`. -/

theorem planck_of_detailed_balance (hbar kB T ω : ℝ) (hne : Real.exp (hbar * ω / (kB * T)) ≠ 1)
    (n : ℝ) (hn : 1 + n ≠ 0) (hbal : n / (1 + n) = Real.exp (-(hbar * ω / (kB * T)))) :
    n = bosePlanck hbar kB T ω := by
  set E := hbar * ω / (kB * T) with hE
  have hexp : Real.exp E ≠ 0 := Real.exp_ne_zero E
  rw [Real.exp_neg, inv_eq_one_div, div_eq_div_iff hn hexp] at hbal
  have h2 : n * (Real.exp E - 1) = 1 := by linear_combination hbal
  have hd : Real.exp E - 1 ≠ 0 := sub_ne_zero_of_ne hne
  rw [bosePlanck, ← hE, eq_div_iff hd]
  exact h2

/-! ## Main theorem -/

/--
**The Unruh effect.**

An observer moving with constant proper acceleration `a` through the Minkowski vacuum
perceives a thermal bath at the *Unruh temperature*

`T = ℏ a / (2 π c k_B)`.

The statement below packages the derivation:

1. `rindlerT`, `rindlerX` describe a worldline parametrized by proper time
   (four-velocity of constant norm `c`) with constant proper acceleration `a`;
2. the Minkowski interval between two points of that worldline depends only on the
   proper-time separation `Δτ`, and equals `(4c⁴/a²) sinh²(aΔτ/2c)`;
3. this expression, analytically continued in `Δτ`, is periodic in imaginary proper time
   with period `ℏ/(k_B T)`, and `ℏ/(k_B T)` is the *smallest* positive such period —
   this is the KMS condition, which identifies `T` as the temperature of the state;
4. the resulting Boltzmann factor is `exp(-2πcω/a) = exp(-ℏω/(k_B T))`, and detailed balance
   with this factor forces the Planck spectrum `n(ω) = 1/(exp(ℏω/(k_B T)) - 1)`;
5. and the temperature so determined is `T = ℏ a / (2 π c k_B)`.
-/
