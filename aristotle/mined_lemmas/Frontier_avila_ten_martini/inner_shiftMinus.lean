import Mathlib

/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

open scoped ComplexConjugate InnerProductSpace ENNReal NNReal

/-- The Hilbert space `ℓ²(ℤ)` of square-summable complex sequences indexed by `ℤ`. -/
abbrev L2Z : Type := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial L2Z := by
  refine ⟨lp.single 2 (0:ℤ) (1:ℂ), 0, ?_⟩
  intro h
  have := congrFun (congrArg (fun x : L2Z => (x : ℤ → ℂ)) h) 0
  simp [lp.single_apply] at this

/-- Membership of a "weighted shift" sequence in `ℓ²(ℤ)`. -/

theorem inner_shiftMinus (x y : L2Z) : ⟪shiftMinus x, y⟫_ℂ = ⟪x, shiftPlus y⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum,
    ← (Equiv.addRight (-1:ℤ)).tsum_eq (fun n : ℤ => ⟪x n, (shiftPlus y) n⟫_ℂ)]
  refine tsum_congr fun n => ?_
  simp [sub_eq_add_neg]

