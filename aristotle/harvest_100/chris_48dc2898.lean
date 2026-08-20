/-
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QPhys

/-- The `n`-th (unnormalized) stationary state of a particle in an infinite square
well of width `L`: `ψ_n(x) = sin(n π x / L)`. -/
noncomputable def boxWave (L : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x => Real.sin ((n : ℝ) * Real.pi * x / L)

/-- The `n`-th energy level of a particle in an infinite square well of width `L`:
`E_n = n² π² ℏ² / (2 m L²)`. -/
noncomputable def boxEnergy (m hbar L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- Derivative of `x ↦ sin (c * x)`. -/
private lemma deriv_sin_const_mul (c : ℝ) :
    deriv (fun x : ℝ => Real.sin (c * x)) = fun x : ℝ => c * Real.cos (c * x) := by
  funext x
  have h : HasDerivAt (fun x : ℝ => Real.sin (c * x)) (Real.cos (c * x) * (c * 1)) x :=
    (Real.hasDerivAt_sin (c * x)).comp x ((hasDerivAt_id x).const_mul c)
  simpa [mul_comm] using h.deriv

/-- Derivative of `x ↦ c * cos (c * x)`. -/
private lemma deriv_const_mul_cos (c : ℝ) :
    deriv (fun x : ℝ => c * Real.cos (c * x)) = fun x : ℝ => -(c ^ 2 * Real.sin (c * x)) := by
  funext x
  have h : HasDerivAt (fun x : ℝ => c * Real.cos (c * x)) (c * (-Real.sin (c * x) * (c * 1))) x :=
    HasDerivAt.const_mul c ((Real.hasDerivAt_cos (c * x)).comp x ((hasDerivAt_id x).const_mul c))
  have := h.deriv
  rw [this]
  ring

/--
**Particle in a one-dimensional infinite square well of width `L`.**

For a particle of mass `m > 0` in a box `[0, L]` (`L > 0`), the wave function
`ψ_n(x) = sin(n π x / L)` (`n ≥ 1`) satisfies:

* the Dirichlet boundary conditions `ψ_n(0) = ψ_n(L) = 0`;
* `ψ_n` is not identically zero;
* the time-independent Schrödinger equation `-(ℏ²/2m) ψ_n'' = E_n ψ_n` with
  `E_n = n² π² ℏ² / (2 m L²)`;

and, conversely, energy is quantized: any wave number `k > 0` compatible with the
boundary condition `sin (k L) = 0` yields an energy `ℏ² k² / (2m)` of the form `E_j`
for some integer `j ≥ 1`.
-/
theorem particle_in_box (m hbar L : ℝ) (hm : 0 < m) (hL : 0 < L) (n : ℕ) (hn : 1 ≤ n) :
    boxWave L n 0 = 0 ∧ boxWave L n L = 0 ∧
    (∃ x, boxWave L n x ≠ 0) ∧
    (∀ x : ℝ, -(hbar ^ 2 / (2 * m)) * deriv (deriv (boxWave L n)) x
        = boxEnergy m hbar L n * boxWave L n x) ∧
    (∀ k : ℝ, 0 < k → Real.sin (k * L) = 0 →
        ∃ j : ℕ, 1 ≤ j ∧ hbar ^ 2 * k ^ 2 / (2 * m) = boxEnergy m hbar L j) := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hm' : m ≠ 0 := ne_of_gt hm
  set c : ℝ := (n : ℝ) * Real.pi / L with hc
  have hfun : boxWave L n = fun x : ℝ => Real.sin (c * x) := by
    funext x
    simp only [boxWave, hc]
    ring_nf
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [boxWave]
  · have hLL : (n : ℝ) * Real.pi * L / L = (n : ℝ) * Real.pi := by
      field_simp
    simp [boxWave, hLL, Real.sin_nat_mul_pi]
  · refine ⟨L / (2 * n), ?_⟩
    have hval : c * (L / (2 * (n : ℝ))) = Real.pi / 2 := by
      rw [hc]; field_simp
    rw [hfun]
    show Real.sin (c * (L / (2 * (n : ℝ)))) ≠ 0
    rw [hval]
    simp
  · intro x
    rw [hfun, deriv_sin_const_mul, deriv_const_mul_cos]
    have hcsq : c ^ 2 = (n : ℝ) ^ 2 * Real.pi ^ 2 / L ^ 2 := by
      rw [hc]; field_simp
    simp only [boxEnergy, hcsq]
    field_simp
  · intro k hk hsin
    obtain ⟨j, hj⟩ := Real.sin_eq_zero_iff.mp hsin
    have hjpos : (0 : ℝ) < (j : ℝ) * Real.pi := by
      rw [hj]; positivity
    have hjpos' : (0 : ℤ) < j := by
      by_contra h
      push_neg at h
      have hle : ((j : ℝ)) ≤ 0 := by exact_mod_cast h
      nlinarith [Real.pi_pos]
    refine ⟨j.toNat, by omega, ?_⟩
    have hcast : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hjpos'.le
    have hk' : k = (j : ℝ) * Real.pi / L := by
      field_simp
      linarith [hj]
    rw [boxEnergy, hcast, hk']
    field_simp

end QPhys

