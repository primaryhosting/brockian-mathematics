/-
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The normalized stationary states of the infinite square well of width `L`:
`ψ_n(x) = √(2/L) · sin(nπx/L)`. -/

theorem particle_in_box {hbar m L : ℝ} (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) :
    (∀ n : ℕ, psi L n 0 = 0 ∧ psi L n L = 0) ∧
    (∀ (n : ℕ) (x : ℝ),
      -(hbar ^ 2 / (2 * m)) * deriv (deriv (psi L n)) x = energy hbar m L n * psi L n x) ∧
    (∀ k : ℝ, 0 < k → Real.sin (k * L) = 0 →
      ∃ n : ℕ, 1 ≤ n ∧ hbar ^ 2 * k ^ 2 / (2 * m) = energy hbar m L n) ∧
    (∀ n : ℕ, 1 ≤ n → 0 < energy hbar m L n ∧ energy hbar m L n < energy hbar m L (n + 1)) := by
  have hL' : L ≠ 0 := ne_of_gt hL
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    constructor
    · simp [psi]
    · have : (n : ℝ) * Real.pi * L / L = n * Real.pi := by field_simp
      simp [psi, this, Real.sin_nat_mul_pi]
  · intro n x
    rw [deriv2_psi, energy]
    have : ((n : ℝ) * Real.pi / L) ^ 2 = (n : ℝ) ^ 2 * Real.pi ^ 2 / L ^ 2 := by
      field_simp
    rw [this]
    field_simp
  · intro k hk hsin
    obtain ⟨n, hn, hkn⟩ := wavenumber_quantized hL hk hsin
    refine ⟨n, hn, ?_⟩
    rw [hkn, energy]
    field_simp
  · intro n hn
    have hpi := Real.pi_pos
    have hden : 0 < 2 * m * L ^ 2 := by positivity
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    constructor
    · unfold energy
      apply div_pos _ hden
      have : (0 : ℝ) < (n : ℝ) ^ 2 := by nlinarith
      positivity
    · unfold energy
      push_cast
      gcongr
      nlinarith [Real.pi_pos, sq_nonneg hbar]

end QPhys

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

