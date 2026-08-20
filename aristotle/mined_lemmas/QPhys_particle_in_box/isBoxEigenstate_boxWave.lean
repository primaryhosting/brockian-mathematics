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

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well of width `L`:
`E_n = n² π² ℏ² / (2 m L²)`. -/

theorem isBoxEigenstate_boxWave {hbar m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    {n : ℕ} (hn : 1 ≤ n) :
    IsBoxEigenstate hbar m L (boxEnergy hbar m L n) (boxWave L n) (boxWaveD1 L n)
      (boxWaveD2 L n) := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hm' : m ≠ 0 := ne_of_gt hm
  refine ⟨hasDerivAt_boxWave L n, hasDerivAt_boxWaveD1 L n, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [boxWaveD2, boxWave, boxEnergy]
    field_simp
  · simp [boxWave]
  · simp only [boxWave]
    have : (n : ℝ) * Real.pi / L * L = (n : ℝ) * Real.pi := by field_simp
    rw [this, Real.sin_nat_mul_pi]
    ring
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn' : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
    refine ⟨L / (2 * n), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      nlinarith
    · simp only [boxWave]
      have harg : (n : ℝ) * Real.pi / L * (L / (2 * n)) = Real.pi / 2 := by
        field_simp
      rw [harg, Real.sin_pi_div_two, mul_one]
      positivity

/-- Uniqueness for the harmonic oscillator equation `f'' = -k² f` with `f 0 = 0`:
any such solution is `f x = (f'(0)/k) sin (k x)`. -/
