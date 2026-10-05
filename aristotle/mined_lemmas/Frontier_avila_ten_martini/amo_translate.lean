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

theorem amo_translate (lam alpha theta : ℝ) :
    amo lam alpha (theta + alpha) = shiftPlus * amo lam alpha theta * shiftMinus := by
  ext u n
  simp only [ContinuousLinearMap.mul_apply, shiftPlus_apply, shiftMinus_apply, amo_apply,
    amoPotential_translate, show ∀ m : ℤ, m + 1 + 1 - 1 = m + 1 from fun m => by ring,
    show ∀ m : ℤ, m + 1 - 1 = m from fun m => by ring]

/-- The (real) spectrum of the almost Mathieu operator. -/
