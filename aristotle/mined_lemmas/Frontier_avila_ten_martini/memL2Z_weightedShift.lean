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

theorem memL2Z_weightedShift (w : ℤ → ℂ) (e : ℤ ≃ ℤ) (C : ℝ) (hw : ∀ n, ‖w n‖ ≤ C)
    (f : L2Z) : Memℓp (fun n : ℤ => w n * f (e n)) 2 := by
  set t : ℝ := (2 : ℝ≥0∞).toReal with ht_def
  have ht : (0:ℝ) < t := by norm_num [ht_def]
  have hC : 0 ≤ C := (norm_nonneg _).trans (hw 0)
  have hsum : Summable fun n : ℤ => ‖f n‖ ^ t := (lp.memℓp f).summable ht
  have hcomp : Summable fun n : ℤ => ‖f (e n)‖ ^ t := (e.summable_iff).mpr hsum
  refine memℓp_gen (Summable.of_nonneg_of_le (fun n => by positivity) ?_
    (hcomp.mul_left (C ^ t)))
  intro n
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  gcongr
  exact hw n

/-- The defining norm bound for the weighted shift. -/
