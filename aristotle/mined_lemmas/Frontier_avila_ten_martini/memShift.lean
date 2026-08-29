/-
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ)` -/

/-- The complex Hilbert space `ℓ²(ℤ)`, on which the almost Mathieu operator acts. -/
abbrev Hl2 := lp (fun _ : ℤ => ℂ) 2

/-- Auxiliary: the real exponent attached to `p = 2`. -/

theorem memShift (k : ℤ) (u : Hl2) : Memℓp (fun n : ℤ => (u : ℤ → ℂ) (n + k)) 2 := by
  apply memℓp_gen
  exact (Equiv.addRight k).summable_iff.2 ((lp.memℓp u).summable (p := 2) (by norm_num))

/-- The shift `(S_k u)(n) = u(n + k)` as a linear map on `ℓ²(ℤ)`. -/
