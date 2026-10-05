/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Gaussian derivative computations -/

/-- First derivative of a Gaussian `x ↦ exp (c * x ^ 2)`. -/
lemma deriv_gauss (c : ℝ) :
    deriv (fun x : ℝ => Real.exp (c * x ^ 2)) = fun x : ℝ => 2 * c * x * Real.exp (c * x ^ 2) := by
  funext x
  have h : HasDerivAt (fun x : ℝ => Real.exp (c * x ^ 2))
      (Real.exp (c * x ^ 2) * (c * (2 * x ^ 1))) x :=
    (((hasDerivAt_pow 2 x).const_mul c).exp)
  have := h.deriv
  rw [this]; ring

/-- Second derivative of a Gaussian `x ↦ exp (c * x ^ 2)`. -/
lemma deriv2_gauss (c : ℝ) :
    deriv (deriv (fun x : ℝ => Real.exp (c * x ^ 2)))
      = fun x : ℝ => (2 * c + 4 * c ^ 2 * x ^ 2) * Real.exp (c * x ^ 2) := by
  rw [deriv_gauss]
  funext x
  have hg : HasDerivAt (fun x : ℝ => Real.exp (c * x ^ 2))
      (Real.exp (c * x ^ 2) * (c * (2 * x ^ 1))) x :=
    (((hasDerivAt_pow 2 x).const_mul c).exp)
  have hl : HasDerivAt (fun x : ℝ => 2 * c * x) (2 * c) x := by
    simpa using ((hasDerivAt_id x).const_mul (2 * c))
  have h : HasDerivAt (fun y : ℝ => 2 * c * y * Real.exp (c * y ^ 2))
      (2 * c * Real.exp (c * x ^ 2) + 2 * c * x * (Real.exp (c * x ^ 2) * (c * (2 * x ^ 1)))) x :=
    hl.mul hg
  rw [h.deriv]; ring

/-- First derivative of `x ↦ x * exp (c * x ^ 2)`. -/
lemma deriv_xgauss (c : ℝ) :
    deriv (fun x : ℝ => x * Real.exp (c * x ^ 2))
      = fun x : ℝ => (1 + 2 * c * x ^ 2) * Real.exp (c * x ^ 2) := by
  funext x
  have hg : HasDerivAt (fun x : ℝ => Real.exp (c * x ^ 2))
      (Real.exp (c * x ^ 2) * (c * (2 * x ^ 1))) x :=
    (((hasDerivAt_pow 2 x).const_mul c).exp)
  have h : HasDerivAt (fun y : ℝ => y * Real.exp (c * y ^ 2))
      (1 * Real.exp (c * x ^ 2) + x * (Real.exp (c * x ^ 2) * (c * (2 * x ^ 1)))) x :=
    (hasDerivAt_id x).mul hg
  rw [h.deriv]; ring

/-- Second derivative of `x ↦ x * exp (c * x ^ 2)`. -/
lemma deriv2_xgauss (c : ℝ) :
    deriv (deriv (fun x : ℝ => x * Real.exp (c * x ^ 2)))
      = fun x : ℝ => (6 * c * x + 4 * c ^ 2 * x ^ 3) * Real.exp (c * x ^ 2) := by
  rw [deriv_xgauss]
  funext x
  have hg : HasDerivAt (fun x : ℝ => Real.exp (c * x ^ 2))
      (Real.exp (c * x ^ 2) * (c * (2 * x ^ 1))) x :=
    (((hasDerivAt_pow 2 x).const_mul c).exp)
  have hl : HasDerivAt (fun x : ℝ => 1 + 2 * c * x ^ 2) (2 * c * (2 * x ^ 1)) x := by
    simpa using (((hasDerivAt_pow 2 x).const_mul (2 * c)).const_add 1)
  have h : HasDerivAt (fun y : ℝ => (1 + 2 * c * y ^ 2) * Real.exp (c * y ^ 2))
      (2 * c * (2 * x ^ 1) * Real.exp (c * x ^ 2)
        + (1 + 2 * c * x ^ 2) * (Real.exp (c * x ^ 2) * (c * (2 * x ^ 1)))) x :=
    hl.mul hg
  rw [h.deriv]; ring

/-! ## The Landau problem

A particle of mass `m` and charge `q` in a uniform magnetic field `B` (say along the `z`-axis)
moves, after separation of variables in the Landau gauge, according to a one-dimensional
harmonic oscillator with the cyclotron frequency `ω_c = q * B / m`:
`H ψ = -(ℏ² / (2 m)) ψ'' + (1/2) m ω_c² x² ψ`.
Its spectrum is `E n = ℏ ω_c (n + 1/2)`.
-/

/-- The cyclotron frequency `ω_c = q B / m` of a particle of charge `q` and mass `m`
in a uniform magnetic field of strength `B`. -/
noncomputable def cyclotronFreq (q B m : ℝ) : ℝ := q * B / m

/-- The `n`-th Landau level energy `E n = ℏ ω_c (n + 1/2)`. -/
noncomputable def landauEnergy (hbar omega : ℝ) (n : ℕ) : ℝ := hbar * omega * (n + 1 / 2)

/-- The effective (reduced) Landau Hamiltonian: a harmonic oscillator at the cyclotron
frequency. -/
noncomputable def landauH (m omega hbar : ℝ) (psi : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(hbar ^ 2 / (2 * m)) * deriv (deriv psi) x + (1 / 2) * m * omega ^ 2 * x ^ 2 * psi x

/-- The Landau ground state (lowest Landau level orbital) `ψ₀ x = exp (-m ω x² / (2 ℏ))`. -/
noncomputable def landauState0 (m omega hbar : ℝ) : ℝ → ℝ :=
  fun x => Real.exp (-(m * omega) / (2 * hbar) * x ^ 2)

/-- The first excited Landau state `ψ₁ x = x * exp (-m ω x² / (2 ℏ))`. -/
noncomputable def landauState1 (m omega hbar : ℝ) : ℝ → ℝ :=
  fun x => x * Real.exp (-(m * omega) / (2 * hbar) * x ^ 2)

/-- `ψ₀` is an eigenfunction of the Landau Hamiltonian with eigenvalue `ℏ ω_c / 2`. -/
lemma landauH_state0 (m omega hbar : ℝ) (hm : m ≠ 0) (hbar0 : hbar ≠ 0) (x : ℝ) :
    landauH m omega hbar (landauState0 m omega hbar) x
      = landauEnergy hbar omega 0 * landauState0 m omega hbar x := by
  unfold landauH landauState0 landauEnergy
  rw [deriv2_gauss]
  field_simp
  ring

/-- `ψ₁` is an eigenfunction of the Landau Hamiltonian with eigenvalue `3 ℏ ω_c / 2`. -/
lemma landauH_state1 (m omega hbar : ℝ) (hm : m ≠ 0) (hbar0 : hbar ≠ 0) (x : ℝ) :
    landauH m omega hbar (landauState1 m omega hbar) x
      = landauEnergy hbar omega 1 * landauState1 m omega hbar x := by
  unfold landauH landauState1 landauEnergy
  rw [deriv2_xgauss]
  field_simp
  ring

/-- **Landau levels.**  For a particle of mass `m > 0` and charge `q` in a uniform magnetic
field `B`, with cyclotron frequency `ω_c = q B / m`, the energy levels are
`E n = ℏ ω_c (n + 1/2)`:

* consecutive levels are equally spaced by `ℏ ω_c`;
* the ground state `ψ₀ x = exp (-m ω_c x² / (2ℏ))` solves the stationary Schrödinger equation
  with energy `E 0 = ℏ ω_c / 2`;
* the first excited state `ψ₁ x = x ψ₀ x` solves it with energy `E 1 = 3 ℏ ω_c / 2`.
-/
theorem landau_levels (q B m hbar : ℝ) (hm : 0 < m) (hbar0 : 0 < hbar) :
    ∀ omega : ℝ, omega = cyclotronFreq q B m →
      (∀ n : ℕ, landauEnergy hbar omega n = hbar * omega * (n + 1 / 2)) ∧
      (∀ n : ℕ, landauEnergy hbar omega (n + 1) - landauEnergy hbar omega n = hbar * omega) ∧
      (∀ x : ℝ, landauH m omega hbar (landauState0 m omega hbar) x
          = landauEnergy hbar omega 0 * landauState0 m omega hbar x) ∧
      (∀ x : ℝ, landauH m omega hbar (landauState1 m omega hbar) x
          = landauEnergy hbar omega 1 * landauState1 m omega hbar x) := by
  intro omega _
  refine ⟨fun n => rfl, fun n => ?_, fun x => landauH_state0 m omega hbar hm.ne' hbar0.ne' x,
    fun x => landauH_state1 m omega hbar hm.ne' hbar0.ne' x⟩
  unfold landauEnergy
  push_cast
  ring

end Frontier

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

