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

/-- The `n`-th stationary state of the infinite square well of width `L`:
`ψ_n(x) = sin (n π x / L)` (unnormalized). -/
noncomputable def psi (L : ℝ) (n : ℕ) (x : ℝ) : ℝ := Real.sin (n * Real.pi * x / L)

/-- The `n`-th energy level of the infinite square well of width `L` for a particle of
mass `m`: `E_n = n² π² ℏ² / (2 m L²)`. -/
noncomputable def E (hbar m L : ℝ) (n : ℕ) : ℝ :=
    (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

section Derivatives

variable (c : ℝ)

lemma hasDerivAt_sin_mul (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (c * y)) (c * Real.cos (c * x)) x := by
  have h : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  simpa [mul_comm] using (Real.hasDerivAt_sin (c * x)).comp x h

lemma deriv_sin_mul :
    deriv (fun y : ℝ => Real.sin (c * y)) = fun x => c * Real.cos (c * x) := by
  funext x
  exact (hasDerivAt_sin_mul c x).deriv

lemma hasDerivAt_cos_mul (x : ℝ) :
    HasDerivAt (fun y : ℝ => c * Real.cos (c * y)) (-(c ^ 2) * Real.sin (c * x)) x := by
  have h : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  have hc : HasDerivAt (fun y : ℝ => Real.cos (c * y)) (-Real.sin (c * x) * c) x :=
    (Real.hasDerivAt_cos (c * x)).comp x h
  have := hc.const_mul c
  convert this using 1
  ring

/-- Second derivative of `x ↦ sin (c x)`. -/
lemma deriv2_sin_mul :
    deriv (deriv fun y : ℝ => Real.sin (c * y)) = fun x => -(c ^ 2) * Real.sin (c * x) := by
  rw [deriv_sin_mul]
  funext x
  exact (hasDerivAt_cos_mul c x).deriv

end Derivatives

lemma psi_eq (L : ℝ) (n : ℕ) : psi L n = fun x => Real.sin ((n * Real.pi / L) * x) := by
  funext x
  simp only [psi]
  ring_nf

/-- The wave function satisfies the second-order equation `ψ'' = -(nπ/L)² ψ`. -/
lemma deriv2_psi (L : ℝ) (n : ℕ) :
    deriv (deriv (psi L n)) = fun x => -((n * Real.pi / L) ^ 2) * psi L n x := by
  rw [psi_eq]
  exact deriv2_sin_mul _

/-- **Particle in a box.**  For the infinite square well of width `L > 0` and a particle of
mass `m > 0`, the state `ψ_n(x) = sin (n π x / L)` (with `n ≥ 1`):

* vanishes at both walls `x = 0` and `x = L` (the infinite-well boundary conditions);
* is not identically zero;
* solves the time-independent Schrödinger equation `-(ℏ²/2m) ψ'' = E ψ` inside the well
  with energy `E = E_n = n² π² ℏ² / (2 m L²)`.
-/
theorem particle_in_box (hbar m L : ℝ) (hL : 0 < L) (hm : 0 < m) (n : ℕ) (hn : 1 ≤ n) :
    (psi L n 0 = 0 ∧ psi L n L = 0) ∧
    (∃ x, 0 < x ∧ x < L ∧ psi L n x ≠ 0) ∧
    (∀ x, -(hbar ^ 2 / (2 * m)) * deriv (deriv (psi L n)) x
        = E hbar m L n * psi L n x) := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn' : (0:ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  refine ⟨⟨by simp [psi], ?_⟩, ?_, ?_⟩
  · -- ψ_n(L) = sin (n π) = 0
    have : (n : ℝ) * Real.pi * L / L = (n : ℝ) * Real.pi := by
      field_simp
    simp [psi, this, Real.sin_nat_mul_pi]
  · -- ψ_n is nonzero at x = L / (2n)
    refine ⟨L / (2 * n), by positivity, ?_, ?_⟩
    · rw [div_lt_iff₀ (by positivity)]
      nlinarith
    · have h : (n : ℝ) * Real.pi * (L / (2 * n)) / L = Real.pi / 2 := by
        field_simp
      simp [psi, h]
  · intro x
    rw [deriv2_psi]
    have : -(hbar ^ 2 / (2 * m)) * (-(((n : ℝ) * Real.pi / L) ^ 2))
        = E hbar m L n := by
      simp only [E, div_pow, mul_pow]
      field_simp
    rw [← this]
    ring

/-- **Energy quantization.**  For a wave number `k > 0`, the state `x ↦ sin (k x)` obeys the
boundary condition at the far wall (`sin (k L) = 0`) exactly when `k = n π / L` for some
`n ≥ 1`; equivalently, the admissible energies `ℏ² k² / (2 m)` are exactly the
`E_n = n² π² ℏ² / (2 m L²)`. -/
theorem energy_quantization (m L : ℝ) (hL : 0 < L) (k : ℝ) (hk : 0 < k) :
    Real.sin (k * L) = 0 ↔ ∃ n : ℕ, 1 ≤ n ∧ k = n * Real.pi / L := by
  constructor
  · intro h
    rw [Real.sin_eq_zero_iff] at h
    obtain ⟨z, hz⟩ := h
    have hzpos : 0 < (z : ℝ) := by
      by_contra hc
      push_neg at hc
      have : (z : ℝ) * Real.pi ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc Real.pi_pos.le
      nlinarith
    have hz1 : 1 ≤ z := by exact_mod_cast hzpos
    refine ⟨z.toNat, ?_, ?_⟩
    · omega
    · have hcast : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
        have hz0 : (0:ℤ) ≤ z := by omega
        exact_mod_cast congrArg (fun t : ℤ => (t : ℝ)) (Int.toNat_of_nonneg hz0)
      rw [hcast, eq_div_iff hL.ne']
      exact hz.symm
  · rintro ⟨n, hn, rfl⟩
    have : (n : ℝ) * Real.pi / L * L = (n : ℝ) * Real.pi := by field_simp
    rw [this, Real.sin_nat_mul_pi]

/-- The admissible energies, written out: if `k = n π / L` then `ℏ² k² / (2 m) = E_n`. -/
theorem energy_of_wavenumber (hbar m L : ℝ) (hL : 0 < L) (hm : 0 < m) (n : ℕ) :
    hbar ^ 2 * ((n : ℝ) * Real.pi / L) ^ 2 / (2 * m) = E hbar m L n := by
  simp only [E, div_pow, mul_pow]
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

