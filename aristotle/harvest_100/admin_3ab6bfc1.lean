import Mathlib
/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real

namespace QPhys

/-- The (unnormalized) stationary state of a particle in an infinite square well
of width `L`: `ψₙ(x) = sin (n π x / L)`. -/
noncomputable def psi (L : ℝ) (n : ℕ) (x : ℝ) : ℝ := Real.sin ((n : ℝ) * π / L * x)

/-- The energy levels of a particle of mass `m` in an infinite square well of width `L`:
`Eₙ = n² π² ℏ² / (2 m L²)`. -/
noncomputable def energy (hbar m L : ℝ) (n : ℕ) : ℝ :=
    (n : ℝ) ^ 2 * π ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

lemma hasDerivAt_sin_mul (k x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (k * y)) (k * Real.cos (k * x)) x := by
  have h : HasDerivAt (fun y : ℝ => k * y) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  simpa [mul_comm] using (Real.hasDerivAt_sin (k * x)).comp x h

lemma hasDerivAt_cos_mul (k x : ℝ) :
    HasDerivAt (fun y : ℝ => k * Real.cos (k * y)) (-(k ^ 2 * Real.sin (k * x))) x := by
  have h : HasDerivAt (fun y : ℝ => k * y) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have := ((Real.hasDerivAt_cos (k * x)).comp x h).const_mul k
  convert this using 1
  ring

lemma deriv_psi (L : ℝ) (n : ℕ) :
    deriv (psi L n) = fun x => ((n : ℝ) * π / L) * Real.cos ((n : ℝ) * π / L * x) := by
  funext x
  exact (hasDerivAt_sin_mul ((n : ℝ) * π / L) x).deriv

lemma deriv2_psi (L : ℝ) (n : ℕ) (x : ℝ) :
    deriv (deriv (psi L n)) x = -(((n : ℝ) * π / L) ^ 2 * psi L n x) := by
  rw [deriv_psi]
  exact (hasDerivAt_cos_mul ((n : ℝ) * π / L) x).deriv

/-- **Particle in a box.**  For a particle of mass `m > 0` confined to an infinite square
well of width `L > 0`:

* the states `ψₙ(x) = sin (n π x / L)` vanish at both walls `x = 0` and `x = L`;
* each `ψₙ` solves the time-independent Schrödinger equation
  `-(ℏ²/2m) ψₙ'' = Eₙ ψₙ` with `Eₙ = n² π² ℏ² / (2 m L²)`;
* the states are nontrivial (`ψₙ` is not identically zero) for `n ≥ 1`;
* conversely, the boundary condition quantizes the wave number: any `k > 0` with
  `sin (k L) = 0` is of the form `k = j π / L` for some integer `j ≥ 1`, and the
  corresponding energy `ℏ² k² / (2m)` is exactly `E_j`.  Hence the admissible energies
  are precisely the `Eₙ`, `n ≥ 1`. -/
theorem particle_in_box (hbar m L : ℝ) (hm : 0 < m) (hL : 0 < L) (n : ℕ) (hn : 1 ≤ n) :
    psi L n 0 = 0 ∧ psi L n L = 0 ∧
    (∀ x : ℝ, -(hbar ^ 2 / (2 * m)) * deriv (deriv (psi L n)) x
        = energy hbar m L n * psi L n x) ∧
    psi L n (L / (2 * n)) ≠ 0 ∧
    (∀ k : ℝ, 0 < k → Real.sin (k * L) = 0 →
        ∃ j : ℕ, 1 ≤ j ∧ k = (j : ℝ) * π / L ∧
          hbar ^ 2 * k ^ 2 / (2 * m) = energy hbar m L j) := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine ⟨by simp [psi], ?_, ?_, ?_, ?_⟩
  · have : (n : ℝ) * π / L * L = (n : ℝ) * π := by field_simp
    simp [psi, this, Real.sin_nat_mul_pi]
  · intro x
    rw [deriv2_psi, energy]
    have : ((n : ℝ) * π / L) ^ 2 = (n : ℝ) ^ 2 * π ^ 2 / L ^ 2 := by
      field_simp
    rw [this]
    field_simp
  · have hx : (n : ℝ) * π / L * (L / (2 * n)) = π / 2 := by
      field_simp
    simp [psi, hx]
  · intro k hk hsin
    rw [Real.sin_eq_zero_iff] at hsin
    obtain ⟨j, hj⟩ := hsin
    have hjpos : 0 < j := by
      by_contra h
      push_neg at h
      have hjr : (j : ℝ) ≤ 0 := by exact_mod_cast h
      have : (j : ℝ) * π ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hjr Real.pi_pos.le
      rw [hj] at this
      nlinarith
    lift j to ℕ using hjpos.le with j' hj'
    have hjR : (j' : ℝ) * π = k * L := by exact_mod_cast hj
    have hk' : k = (j' : ℝ) * π / L := by
      field_simp
      linarith [hjR]
    refine ⟨j', by exact_mod_cast hjpos, hk', ?_⟩
    rw [energy, hk']
    field_simp

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

