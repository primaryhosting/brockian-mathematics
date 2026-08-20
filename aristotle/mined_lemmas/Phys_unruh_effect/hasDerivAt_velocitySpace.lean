import Mathlib

/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Statement: State the Unruh temperature T = ℏa/(2πck) seen by a uniformly accelerated observer.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- The physical constants entering the Unruh formula: the reduced Planck constant `hbar`,
the speed of light `c` and Boltzmann's constant `kB`, all positive. -/
structure Constants where
  hbar : ℝ
  c : ℝ
  kB : ℝ
  hbar_pos : 0 < hbar
  c_pos : 0 < c
  kB_pos : 0 < kB

variable (C : Constants)

/-- The **Unruh temperature** `T = ℏ a / (2 π c k_B)` associated with proper acceleration `a`. -/

lemma hasDerivAt_velocitySpace {a : ℝ} (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => C.c * Real.sinh (a * τ / C.c)) (a * Real.cosh (a * τ / C.c)) τ := by
  have hc : C.c ≠ 0 := ne_of_gt C.c_pos
  have h : HasDerivAt (fun τ : ℝ => a * τ / C.c) (a / C.c) τ := by
    simpa [mul_comm, mul_div_assoc] using
      ((hasDerivAt_id τ).const_mul a).div_const C.c
  have := (h.sinh).const_mul C.c
  have hEq : C.c * (Real.cosh (a * τ / C.c) * (a / C.c)) = a * Real.cosh (a * τ / C.c) := by
    field_simp
  simpa [hEq] using this

end Basic

/-- **The Unruh effect.**

For a uniformly accelerated observer with proper acceleration `a > 0`, moving on the Rindler
worldline `t(τ) = (c/a) sinh (aτ/c)`, `x(τ) = (c²/a) cosh (aτ/c)`, the following hold.

1. The worldline is parametrised by proper time: its four-velocity `(t', x')` has Minkowski
   norm `c² t'² - x'² = c²`.
2. Its four-acceleration `(t'', x'')` is spacelike with invariant magnitude `a`, i.e.
   `x''² - c² t''² = a²`.
3. Continued to complex proper time, the worldline is periodic in imaginary proper time with
   period `2 π c / a` — the hallmark of a thermal (KMS) state.
4. This periodicity is exactly the thermal period `ℏ / (k_B T)` for the **Unruh temperature**
   `T = ℏ a / (2 π c k_B)`, which is positive.
5. Equivalently, the Boltzmann factor at temperature `T` is `exp (-2 π c E / (ℏ a))` for every
   energy `E`: the accelerated observer sees a thermal bath at temperature `T`.
-/
