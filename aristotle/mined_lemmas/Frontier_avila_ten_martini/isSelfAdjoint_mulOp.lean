/-
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ, ℂ)` -/

/-- The Hilbert space `ℓ²(ℤ, ℂ)` on which the almost Mathieu operator acts. -/
abbrev H2 := ℓ²(ℤ, ℂ)

instance : Nontrivial H2 := by
  refine ⟨lp.single 2 (0 : ℤ) (1 : ℂ), 0, ?_⟩
  intro h
  have : (lp.single 2 (0 : ℤ) (1 : ℂ) : ℤ → ℂ) 0 = (0 : H2) 0 := by rw [h]
  simp [lp.single_apply] at this

/-! ## Shift operators -/


lemma isSelfAdjoint_mulOp (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) :
    IsSelfAdjoint (mulOp v C hv) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr (fun n => ?_)
  simp only [RCLike.inner_apply]
  show (g : ℤ → ℂ) n * (starRingEnd ℂ) ((v n : ℂ) * (f : ℤ → ℂ) n)
      = ((v n : ℂ) * (g : ℤ → ℂ) n) * (starRingEnd ℂ) ((f : ℤ → ℂ) n)
  rw [map_mul, Complex.conj_ofReal]
  ring

/-- The almost Mathieu operator is self-adjoint. -/
