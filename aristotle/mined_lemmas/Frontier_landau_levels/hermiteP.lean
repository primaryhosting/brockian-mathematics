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

noncomputable def hermiteP : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => 2 * X * hermiteP n - derivative (hermiteP n)

/-- Hermite's differential equation `H_n'' - 2X H_n' + 2n H_n = 0`, together with the
derivative formula `H_{n+1}' = 2(n+1) H_n`. -/
