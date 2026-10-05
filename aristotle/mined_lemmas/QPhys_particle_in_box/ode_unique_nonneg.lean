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

lemma ode_unique_nonneg {k : ℝ} {g g' g'' : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt g (g' x) x) (h2 : ∀ x, HasDerivAt g' (g'' x) x)
    (heq : ∀ x, g'' x = k ^ 2 * g x) (hg0 : g 0 = 0) (hg'0 : g' 0 = 0) :
    ∀ x, g x = 0 := by
  -- `u x = (g' x + k g x)·e^{-kx}` has vanishing derivative, hence vanishes identically.
  have hu : ∀ x, HasDerivAt (fun y => (g' y + k * g y) * Real.exp (-k * y)) 0 x := by
    intro x
    have hA : HasDerivAt (fun y => g' y + k * g y) (g'' x + k * g' x) x :=
      (h2 x).add ((h1 x).const_mul k)
    have hB : HasDerivAt (fun y => Real.exp (-k * y)) (Real.exp (-k * x) * (-k)) x :=
      (hasDerivAt_lin (-k) x).exp
    have h3 := hA.mul hB
    have hE : (g'' x + k * g' x) * Real.exp (-k * x)
        + (g' x + k * g x) * (Real.exp (-k * x) * (-k)) = 0 := by
      rw [heq x]; ring
    rw [hE] at h3
    exact h3
  have hu0 : ∀ x, g' x + k * g x = 0 := by
    intro x
    have h := const_of_hasDerivAt_zero hu x
    have h0 : (g' x + k * g x) * Real.exp (-k * x) = 0 := by rw [h, hg0, hg'0]; simp
    exact (mul_eq_zero.mp h0).resolve_right (Real.exp_ne_zero _)
  -- `v x = g x · e^{kx}` then also has vanishing derivative.
  have hv : ∀ x, HasDerivAt (fun y => g y * Real.exp (k * y)) 0 x := by
    intro x
    have hB : HasDerivAt (fun y => Real.exp (k * y)) (Real.exp (k * x) * k) x :=
      (hasDerivAt_lin k x).exp
    have h3 := (h1 x).mul hB
    have hE : g' x * Real.exp (k * x) + g x * (Real.exp (k * x) * k) = 0 := by
      have h4 := hu0 x
      nlinarith [Real.exp_pos (k * x)]
    rw [hE] at h3
    exact h3
  intro x
  have h := const_of_hasDerivAt_zero hv x
  have h0 : g x * Real.exp (k * x) = 0 := by rw [h, hg0]; simp
  exact (mul_eq_zero.mp h0).resolve_right (Real.exp_ne_zero _)

/-- Uniqueness for `g'' = -k² g` (`k ≠ 0`) with vanishing initial data, via the conserved
energy `g'² + k² g²`. -/
