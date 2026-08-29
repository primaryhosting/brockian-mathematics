import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well of width `L`:
`Eₙ = n²π²ℏ²/(2mL²)`. -/

lemma sol_form_pos {k : ℝ} (hk : 0 < k) {f f' f'' : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt f (f' x) x) (h2 : ∀ x, HasDerivAt f' (f'' x) x)
    (heq : ∀ x, f'' x = k ^ 2 * f x) (hf0 : f 0 = 0) :
    ∀ x, f x = (f' 0 / k) * Real.sinh (k * x) := by
  set B := f' 0 / k with hB
  set g : ℝ → ℝ := fun x => f x - B * Real.sinh (k * x) with hg
  set g' : ℝ → ℝ := fun x => f' x - B * (Real.cosh (k * x) * k) with hg'
  set g'' : ℝ → ℝ := fun x => f'' x - B * (Real.sinh (k * x) * k * k) with hg''
  have hd1 : ∀ x, HasDerivAt g (g' x) x := fun x =>
    (h1 x).sub (((hasDerivAt_lin k x).sinh).const_mul B)
  have hd2 : ∀ x, HasDerivAt g' (g'' x) x := by
    intro x
    have hc : HasDerivAt (fun y => Real.cosh (k * y) * k) (Real.sinh (k * x) * k * k) x := by
      have h := ((hasDerivAt_lin k x).cosh).mul_const k
      convert h using 1
    exact (h2 x).sub (hc.const_mul B)
  have hgeq : ∀ x, g'' x = k ^ 2 * g x := by
    intro x
    simp only [hg, hg'']
    rw [heq x]; ring
  have hg0 : g 0 = 0 := by simp [hg, hf0]
  have hg'0 : g' 0 = 0 := by
    have hc : f' 0 / k * k = f' 0 := div_mul_cancel₀ _ (ne_of_gt hk)
    simp only [hg', hB, mul_zero, Real.cosh_zero, one_mul, hc, sub_self]
  have hz := ode_unique_nonneg (k := k) hd1 hd2 hgeq hg0 hg'0
  intro x
  have hx := hz x
  simp only [hg] at hx
  linarith

/-- Solutions of `ψ'' = 0` vanishing at `0` are linear. -/
