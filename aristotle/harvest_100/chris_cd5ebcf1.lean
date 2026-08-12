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
noncomputable def unruhTemperature (a : ℝ) : ℝ :=
  C.hbar * a / (2 * Real.pi * C.c * C.kB)

/-- Time coordinate of the worldline of a uniformly accelerated (Rindler) observer,
parametrised by proper time `τ`: `t(τ) = (c/a) sinh (a τ / c)`. -/
noncomputable def worldlineTime (a τ : ℝ) : ℝ := (C.c / a) * Real.sinh (a * τ / C.c)

/-- Space coordinate of the worldline of a uniformly accelerated (Rindler) observer,
parametrised by proper time `τ`: `x(τ) = (c²/a) cosh (a τ / c)`. -/
noncomputable def worldlineSpace (a τ : ℝ) : ℝ := (C.c ^ 2 / a) * Real.cosh (a * τ / C.c)

/-- Analytic continuation of the time coordinate of the worldline to complex proper time. -/
noncomputable def worldlineTimeC (a : ℝ) (τ : ℂ) : ℂ :=
  ((C.c : ℂ) / a) * Complex.sinh ((a : ℂ) * τ / C.c)

/-- Analytic continuation of the space coordinate of the worldline to complex proper time. -/
noncomputable def worldlineSpaceC (a : ℝ) (τ : ℂ) : ℂ :=
  ((C.c : ℂ) ^ 2 / a) * Complex.cosh ((a : ℂ) * τ / C.c)

section Basic

variable {C}

lemma cosh_two_pi_I : Complex.cosh (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
  rw [Complex.cosh_mul_I, Complex.cos_two_pi]

lemma sinh_two_pi_I : Complex.sinh (2 * (Real.pi : ℂ) * Complex.I) = 0 := by
  rw [Complex.sinh_mul_I, Complex.sin_two_pi, zero_mul]

/-- The four-velocity of the accelerated worldline: `t'(τ) = cosh (a τ / c)`. -/
lemma hasDerivAt_worldlineTime {a : ℝ} (ha : a ≠ 0) (τ : ℝ) :
    HasDerivAt (worldlineTime C a) (Real.cosh (a * τ / C.c)) τ := by
  have hc : C.c ≠ 0 := ne_of_gt C.c_pos
  have h : HasDerivAt (fun τ : ℝ => a * τ / C.c) (a / C.c) τ := by
    simpa [mul_comm, mul_div_assoc] using
      ((hasDerivAt_id τ).const_mul a).div_const C.c
  have := (h.sinh).const_mul (C.c / a)
  have hEq : C.c / a * (Real.cosh (a * τ / C.c) * (a / C.c)) = Real.cosh (a * τ / C.c) := by
    field_simp
  simpa [worldlineTime, hEq] using this

/-- The four-velocity of the accelerated worldline: `x'(τ) = c sinh (a τ / c)`. -/
lemma hasDerivAt_worldlineSpace {a : ℝ} (ha : a ≠ 0) (τ : ℝ) :
    HasDerivAt (worldlineSpace C a) (C.c * Real.sinh (a * τ / C.c)) τ := by
  have hc : C.c ≠ 0 := ne_of_gt C.c_pos
  have h : HasDerivAt (fun τ : ℝ => a * τ / C.c) (a / C.c) τ := by
    simpa [mul_comm, mul_div_assoc] using
      ((hasDerivAt_id τ).const_mul a).div_const C.c
  have := (h.cosh).const_mul (C.c ^ 2 / a)
  have hEq : C.c ^ 2 / a * (Real.sinh (a * τ / C.c) * (a / C.c))
      = C.c * Real.sinh (a * τ / C.c) := by
    field_simp
  simpa [worldlineSpace, hEq] using this

/-- The four-acceleration: `t''(τ) = (a/c) sinh (a τ / c)`. -/
lemma hasDerivAt_velocityTime {a : ℝ} (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.cosh (a * τ / C.c)) ((a / C.c) * Real.sinh (a * τ / C.c)) τ := by
  have h : HasDerivAt (fun τ : ℝ => a * τ / C.c) (a / C.c) τ := by
    simpa [mul_comm, mul_div_assoc] using
      ((hasDerivAt_id τ).const_mul a).div_const C.c
  simpa [mul_comm] using h.cosh

/-- The four-acceleration: `x''(τ) = a cosh (a τ / c)`. -/
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
theorem unruh_effect (C : Constants) (a : ℝ) (ha : 0 < a) :
    -- (1) unit-normalised four-velocity (proper-time parametrisation)
    (∀ τ : ℝ, HasDerivAt (worldlineTime C a) (Real.cosh (a * τ / C.c)) τ ∧
        HasDerivAt (worldlineSpace C a) (C.c * Real.sinh (a * τ / C.c)) τ ∧
        C.c ^ 2 * Real.cosh (a * τ / C.c) ^ 2 - (C.c * Real.sinh (a * τ / C.c)) ^ 2
          = C.c ^ 2) ∧
    -- (2) the proper acceleration of the worldline has invariant magnitude `a`
    (∀ τ : ℝ,
        HasDerivAt (fun σ : ℝ => Real.cosh (a * σ / C.c))
          ((a / C.c) * Real.sinh (a * τ / C.c)) τ ∧
        HasDerivAt (fun σ : ℝ => C.c * Real.sinh (a * σ / C.c))
          (a * Real.cosh (a * τ / C.c)) τ ∧
        (a * Real.cosh (a * τ / C.c)) ^ 2
            - C.c ^ 2 * ((a / C.c) * Real.sinh (a * τ / C.c)) ^ 2 = a ^ 2) ∧
    -- (3) periodicity in imaginary proper time with period `2 π c / a`
    (∀ τ : ℂ, worldlineTimeC C a (τ + Complex.I * (2 * Real.pi * C.c / a))
          = worldlineTimeC C a τ ∧
        worldlineSpaceC C a (τ + Complex.I * (2 * Real.pi * C.c / a))
          = worldlineSpaceC C a τ) ∧
    -- (4) the Unruh temperature and the KMS relation `ℏ / (k_B T) = 2 π c / a`
    unruhTemperature C a = C.hbar * a / (2 * Real.pi * C.c * C.kB) ∧
    0 < unruhTemperature C a ∧
    C.hbar / (C.kB * unruhTemperature C a) = 2 * Real.pi * C.c / a ∧
    -- (5) the thermal Boltzmann factor seen by the accelerated observer
    (∀ E : ℝ, Real.exp (-E / (C.kB * unruhTemperature C a))
        = Real.exp (-(2 * Real.pi * C.c * E) / (C.hbar * a))) := by
  have hc : C.c ≠ 0 := ne_of_gt C.c_pos
  have ha' : a ≠ 0 := ne_of_gt ha
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hcpos := C.c_pos
  have hkBpos := C.kB_pos
  have hT : 0 < unruhTemperature C a := by
    have : 0 < 2 * Real.pi * C.c * C.kB := by positivity
    exact div_pos (mul_pos C.hbar_pos ha) this
  refine ⟨?_, ?_, ?_, rfl, hT, ?_, ?_⟩
  · intro τ
    refine ⟨hasDerivAt_worldlineTime ha' τ, hasDerivAt_worldlineSpace ha' τ, ?_⟩
    have h := Real.cosh_sq_sub_sinh_sq (a * τ / C.c)
    nlinarith [h]
  · intro τ
    refine ⟨hasDerivAt_velocityTime τ, hasDerivAt_velocitySpace τ, ?_⟩
    have h := Real.cosh_sq_sub_sinh_sq (a * τ / C.c)
    field_simp
    nlinarith [h]
  · intro τ
    have hstep : (a : ℂ) * (τ + Complex.I * (2 * Real.pi * C.c / a)) / C.c
        = (a : ℂ) * τ / C.c + 2 * (Real.pi : ℂ) * Complex.I := by
      have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha'
      have hcc : (C.c : ℂ) ≠ 0 := by exact_mod_cast hc
      field_simp
    constructor
    · simp only [worldlineTimeC, hstep, Complex.sinh_add, cosh_two_pi_I, sinh_two_pi_I]
      ring
    · simp only [worldlineSpaceC, hstep, Complex.cosh_add, cosh_two_pi_I, sinh_two_pi_I]
      ring
  · have hkB : C.kB ≠ 0 := ne_of_gt C.kB_pos
    have hhbar : C.hbar ≠ 0 := ne_of_gt C.hbar_pos
    unfold unruhTemperature
    field_simp
  · intro E
    congr 1
    unfold unruhTemperature
    have hkB : C.kB ≠ 0 := ne_of_gt C.kB_pos
    have hhbar : C.hbar ≠ 0 := ne_of_gt C.hbar_pos
    field_simp

end Phys

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

