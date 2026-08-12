/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The character `x ↦ e^{2πi k x}` on the circle `ℝ / ℤ`. -/
noncomputable def torusChar (k : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * x))

/-- A trigonometric polynomial on the circle with frequencies in `s` and coefficients `c`. -/
noncomputable def trigPoly (s : Finset ℤ) (c : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ s, c k * torusChar k x

/-- The formal solution of the homological (small–divisor) equation
`u (x + ω) - u x = f x` for `f = trigPoly s c`. -/
noncomputable def homSol (ω : ℝ) (s : Finset ℤ) (c : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ s, (c k / (torusChar k ω - 1)) * torusChar k x

lemma torusChar_add (k : ℤ) (x y : ℝ) :
    torusChar k (x + y) = torusChar k x * torusChar k y := by
  unfold torusChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_torusChar (k : ℤ) (x : ℝ) : ‖torusChar k x‖ = 1 := by
  unfold torusChar
  rw [Complex.norm_exp]
  norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im]

lemma torusChar_periodic (k : ℤ) (x : ℝ) : torusChar k (x + 1) = torusChar k x := by
  rw [torusChar_add]
  have : torusChar k 1 = 1 := by
    unfold torusChar
    rw [Complex.exp_eq_one_iff]
    exact ⟨k, by push_cast; ring⟩
  rw [this, mul_one]

/-- Small divisors do not vanish: for an irrational frequency `ω` and a nonzero
frequency `k`, `e^{2πi k ω} ≠ 1`. -/
lemma torusChar_ne_one {ω : ℝ} (hω : Irrational ω) {k : ℤ} (hk : k ≠ 0) :
    torusChar k ω ≠ 1 := by
  intro hcon
  rw [torusChar, Complex.exp_eq_one_iff] at hcon
  obtain ⟨n, hn⟩ := hcon
  have hI : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  push_cast at hn
  have h2 : (k : ℂ) * (ω : ℂ) = (n : ℂ) := by
    apply mul_left_cancel₀ hI
    linear_combination hn
  have h3 : (k : ℝ) * ω = (n : ℝ) := by exact_mod_cast h2
  exact (Irrational.intCast_mul hω hk).ne_int n h3

/-- **Solution of the homological equation.** For an irrational frequency `ω` and a
zero-mean trigonometric polynomial `f = trigPoly s c` (zero mean is encoded by
`0 ∉ s`), the function `homSol ω s c` solves `u (x + ω) - u x = f x`. -/
theorem homological_equation {ω : ℝ} (hω : Irrational ω) {s : Finset ℤ} (hs : (0 : ℤ) ∉ s)
    (c : ℤ → ℂ) (x : ℝ) :
    homSol ω s c (x + ω) - homSol ω s c x = trigPoly s c x := by
  unfold homSol trigPoly
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk0 : k ≠ 0 := fun h => hs (h ▸ hk)
  have hne : torusChar k ω - 1 ≠ 0 := sub_ne_zero.mpr (torusChar_ne_one hω hk0)
  rw [torusChar_add]
  field_simp

/-- **KAM theorem (persistence of invariant tori), trigonometric-polynomial case.**

Consider the integrable skew system `R (x, y) = (x + ω, y)` on the phase space
`ℝ × ℂ` (with `x` an angle variable on the circle `ℝ / ℤ` and `y` an action-type
variable), whose invariant tori are the circles `{y = a}`, each carrying the linear
flow with frequency `ω`.

Perturb it to `F (x, y) = (x + ω, y + ε * f x)`, where `f = trigPoly s c` is a
zero-mean trigonometric polynomial (`0 ∉ s`) and `ε` is the size of the perturbation.

If `ω` is irrational (a nonresonance condition making all small divisors
`e^{2πi k ω} - 1` nonzero), then the invariant tori persist: there is a periodic
"torus deformation" `U`, of size `O(‖ε‖)`, such that the change of variables
`H (x, y) = (x, y + U x)` conjugates the integrable system to the perturbed one,
`F ∘ H = H ∘ R`, and consequently each deformed torus `{y = a + U x}` is invariant
under `F`, with the induced dynamics on it the rigid rotation `x ↦ x + ω`. -/
theorem kam_theorem (ω : ℝ) (hω : Irrational ω) (s : Finset ℤ) (hs : (0 : ℤ) ∉ s)
    (c : ℤ → ℂ) (ε : ℂ)
    (F : ℝ × ℂ → ℝ × ℂ) (hF : ∀ p, F p = (p.1 + ω, p.2 + ε * trigPoly s c p.1))
    (R : ℝ × ℂ → ℝ × ℂ) (hR : ∀ p, R p = (p.1 + ω, p.2)) :
    ∃ (U : ℝ → ℂ) (H : ℝ × ℂ → ℝ × ℂ),
      -- `H` is a change of variables deforming the tori `{y = a}` into `{y = a + U x}`
      (∀ p, H p = (p.1, p.2 + U p.1)) ∧
      -- the deformation is a function on the circle
      (∀ x, U (x + 1) = U x) ∧
      -- and it is of size `O(‖ε‖)`, so the tori are only slightly displaced
      (∀ x, ‖U x‖ ≤ ‖ε‖ * ∑ k ∈ s, ‖c k / (torusChar k ω - 1)‖) ∧
      -- conjugacy of the integrable system to the perturbed one
      (∀ p, F (H p) = H (R p)) ∧
      -- each deformed torus is invariant under the perturbed map,
      -- and the dynamics on it is the rotation by `ω`
      (∀ a : ℂ, ∀ p : ℝ × ℂ, p.2 = a + U p.1 → (F p).2 = a + U (F p).1 ∧ (F p).1 = p.1 + ω) := by
  refine ⟨fun x => ε * homSol ω s c x, fun p => (p.1, p.2 + ε * homSol ω s c p.1),
    fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro x
    unfold homSol
    simp only [torusChar_periodic]
  · intro x
    rw [norm_mul]
    gcongr
    unfold homSol
    calc ‖∑ k ∈ s, (c k / (torusChar k ω - 1)) * torusChar k x‖
        ≤ ∑ k ∈ s, ‖(c k / (torusChar k ω - 1)) * torusChar k x‖ := norm_sum_le _ _
      _ = ∑ k ∈ s, ‖c k / (torusChar k ω - 1)‖ := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [norm_mul, norm_torusChar, mul_one]
  · intro p
    rw [hF, hR]
    have h := homological_equation hω hs c p.1
    have h2 : ε * homSol ω s c (p.1 + ω) - ε * homSol ω s c p.1 = ε * trigPoly s c p.1 := by
      rw [← mul_sub, h]
    simp only [Prod.mk.injEq, true_and]
    linear_combination -h2
  · intro a p hp
    rw [hF]
    have h := homological_equation hω hs c p.1
    refine ⟨?_, rfl⟩
    simp only [hp]
    have h2 : ε * homSol ω s c (p.1 + ω) - ε * homSol ω s c p.1 = ε * trigPoly s c p.1 := by
      rw [← mul_sub, h]
    linear_combination -h2

end Frontier

#print axioms Frontier.kam_theorem

