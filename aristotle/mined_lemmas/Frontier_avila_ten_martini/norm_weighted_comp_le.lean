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

## Contents

* `Frontier.amo`: the almost Mathieu operator `H_{lam, alpha, theta}` on `ℓ²(ℤ)`, constructed as
  a bounded operator from a general bounded weighted composition operator.
* `Frontier.amo_isSelfAdjoint`: it is selfadjoint.
* `Frontier.amoSpectrum`: its spectrum, as a subset of `ℝ`; it is nonempty, compact and contained
  in `[-(2 + 2|lam|), 2 + 2|lam|]`.
* `Frontier.IsCantorSet`: nonempty, compact, perfect and totally disconnected subsets of `ℝ`.
* `Frontier.avila_ten_martini`: the Ten Martini statement, reduced (with a Lean-checked proof) to
  the two analytic inputs of the Avila–Jitomirskaya theorem, namely that the spectrum has no
  isolated points and that all spectral gaps are open.
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## The Hilbert space `ℓ²(ℤ)` and weighted shift operators -/

/-- The Hilbert space `ℓ²(ℤ)` of square-summable complex sequences indexed by `ℤ`. -/
abbrev L2Z := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial L2Z := by
  refine ⟨lp.single 2 (0:ℤ) (1:ℂ), 0, ?_⟩
  intro h
  have hval := congrArg (fun f : L2Z => (f : ℤ → ℂ) 0) h
  simp at hval


theorem norm_weighted_comp_le (w : ℤ → ℂ) (C : ℝ) (hC : ∀ n, ‖w n‖ ≤ C) (e : ℤ ≃ ℤ) (u : L2Z) :
    ‖(⟨fun n => w n * u (e n), memℓp_weighted_comp w C hC e u⟩ : L2Z)‖ ≤ C * ‖u‖ := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (w 0)) (hC 0)
  have hp : (0:ℝ) < (2:ℝ≥0∞).toReal := by norm_num
  have hu : Summable (fun n : ℤ => ‖(u : ℤ → ℂ) n‖ ^ (2:ℝ)) := by
    simpa using lp.memℓp u |>.summable (by norm_num)
  have hu2 : Summable (fun n : ℤ => ‖(u : ℤ → ℂ) (e n)‖ ^ (2:ℝ)) := hu.comp_injective e.injective
  have hf : Summable (fun n : ℤ => ‖w n * (u : ℤ → ℂ) (e n)‖ ^ (2:ℝ)) := by
    simpa [ENNReal.toReal_ofNat] using (memℓp_weighted_comp w C hC e u).summable hp
  set A := ∑' n : ℤ, ‖(u : ℤ → ℂ) n‖ ^ (2:ℝ) with hA
  have hA0 : 0 ≤ A := tsum_nonneg (fun n => by positivity)
  have key : ∑' n : ℤ, ‖w n * (u : ℤ → ℂ) (e n)‖ ^ (2:ℝ) ≤ C ^ 2 * A := by
    have h1 : ∑' n : ℤ, ‖w n * (u : ℤ → ℂ) (e n)‖ ^ (2:ℝ)
        ≤ ∑' n : ℤ, C ^ 2 * ‖(u : ℤ → ℂ) (e n)‖ ^ (2:ℝ) := by
      refine Summable.tsum_mono hf (hu2.mul_left _) (fun n => ?_)
      simp only [norm_mul, rpow_two, mul_pow]
      have h2 : ‖w n‖ ^ 2 ≤ C ^ 2 := by nlinarith [norm_nonneg (w n), hC n]
      nlinarith [sq_nonneg ‖(u : ℤ → ℂ) (e n)‖]
    calc _ ≤ ∑' n : ℤ, C ^ 2 * ‖(u : ℤ → ℂ) (e n)‖ ^ (2:ℝ) := h1
      _ = C ^ 2 * ∑' n : ℤ, ‖(u : ℤ → ℂ) (e n)‖ ^ (2:ℝ) := tsum_mul_left
      _ = C ^ 2 * A := by rw [hA, e.tsum_eq (fun n => ‖(u : ℤ → ℂ) n‖ ^ (2:ℝ))]
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  simp only [ENNReal.toReal_ofNat]
  have h3 : (∑' n : ℤ, ‖w n * (u : ℤ → ℂ) (e n)‖ ^ (2:ℝ)) ^ (1/(2:ℝ)) ≤ (C ^ 2 * A) ^ (1/(2:ℝ)) :=
    Real.rpow_le_rpow (tsum_nonneg fun n => by positivity) key (by norm_num)
  refine le_trans h3 ?_
  rw [Real.mul_rpow (by positivity) hA0]
  gcongr
  rw [← Real.rpow_natCast C 2, ← Real.rpow_mul hC0]
  norm_num

/-- The bounded operator `u ↦ (n ↦ w n * u (e n))` on `ℓ²(ℤ)`, for a weight `w` bounded by `C`
and a bijection `e` of the index set. -/
