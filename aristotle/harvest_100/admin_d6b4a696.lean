/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Statement: State the Bekenstein bound S ≤ 2πkRE/ℏc.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Note: Lean 4 requires `import` to be the first command in a file, so this header is written as a
plain block comment `/- ... -/` rather than a module docstring `/-! ... -/`; the text is otherwise
exactly as specified.
-/

import Mathlib

open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Phys

/-- The Bekenstein bound `2 π k R E / (ℏ c)` on the entropy of a system of energy `E`
contained in a sphere of radius `R`. -/
noncomputable def bekensteinBound (k hbar c R E : ℝ) : ℝ :=
  2 * Real.pi * k * R * E / (hbar * c)

/-- The Schwarzschild radius `2 G M / c ^ 2` of a body of mass `M`. -/
noncomputable def schwarzschildRadius (G c M : ℝ) : ℝ := 2 * G * M / c ^ 2

/-- The Bekenstein–Hawking entropy `k A c ^ 3 / (4 G ℏ)` of a Schwarzschild black hole of
mass `M`, written out in terms of `M` (its horizon area being `A = 4 π (2 G M / c ^ 2) ^ 2`). -/
noncomputable def bhEntropy (k hbar c G M : ℝ) : ℝ := 4 * Real.pi * k * G * M ^ 2 / (hbar * c)

/-- The horizon area of a Schwarzschild black hole of mass `M`. -/
noncomputable def horizonArea (G c M : ℝ) : ℝ := 4 * Real.pi * (schwarzschildRadius G c M) ^ 2

/-- The Bekenstein–Hawking entropy is indeed `k A c ^ 3 / (4 G ℏ)` with `A` the horizon area. -/
theorem bhEntropy_eq_area_formula {k hbar c G M : ℝ} (hc : c ≠ 0) (hG : G ≠ 0) :
    bhEntropy k hbar c G M = k * horizonArea G c M * c ^ 3 / (4 * G * hbar) := by
  unfold bhEntropy horizonArea schwarzschildRadius
  field_simp
  ring

/-- A Schwarzschild black hole saturates the Bekenstein bound: its entropy equals
`2 π k R E / (ℏ c)` for `R` its Schwarzschild radius and `E = M c ^ 2` its energy. -/
theorem bhEntropy_eq_bekensteinBound {k hbar c G M : ℝ} (hc : c ≠ 0) :
    bhEntropy k hbar c G M
      = bekensteinBound k hbar c (schwarzschildRadius G c M) (M * c ^ 2) := by
  unfold bhEntropy bekensteinBound schwarzschildRadius
  field_simp
  ring

/-- The mass increment delivered to a black hole of mass `M` when a body of energy `E` and
radius `R`, first lowered quasi-statically to proper distance `R` from the horizon, is dropped
in: the redshift factor there is `R / (2 R_s)` with `R_s = 2 G M / c ^ 2`, so the energy
delivered at infinity is `E R c ^ 2 / (4 G M)`, i.e. a mass `E R / (4 G M)`. -/
noncomputable def deliveredMass (G M R E : ℝ) : ℝ := E * R / (4 * G * M)

/-- The Bekenstein–Hawking entropy is differentiable in the mass, with derivative
`8 π k G M / (ℏ c)`. -/
theorem hasDerivAt_bhEntropy (k hbar c G M : ℝ) :
    HasDerivAt (bhEntropy k hbar c G) (8 * Real.pi * k * G * M / (hbar * c)) M := by
  have h : HasDerivAt (fun M : ℝ => M ^ 2) (2 * M) M := by
    simpa using (hasDerivAt_pow 2 M)
  have hfun : bhEntropy k hbar c G = fun x : ℝ => (4 * Real.pi * k * G) * x ^ 2 / (hbar * c) := by
    funext x; simp [bhEntropy]
  rw [hfun]
  have h' := (h.const_mul (4 * Real.pi * k * G)).div_const (hbar * c)
  convert h' using 1
  ring

/-- The derivative of the black-hole entropy with respect to mass. -/
theorem deriv_bhEntropy (k hbar c G M : ℝ) :
    deriv (bhEntropy k hbar c G) M = 8 * Real.pi * k * G * M / (hbar * c) :=
  (hasDerivAt_bhEntropy k hbar c G M).deriv

/-- **The Bekenstein bound.**

A system of energy `E` fitting inside a sphere of radius `R` has entropy at most
`2 π k R E / (ℏ c)`.

Following Bekenstein's derivation, the physical input is the generalized second law: when the
system is lowered to the horizon of a Schwarzschild black hole of mass `M` and dropped in, the
black hole's entropy must increase by at least the entropy `S` lost from the exterior, i.e.
`S ≤ (d S_BH / d M) (M) * ΔM`, where `ΔM = E R / (4 G M)` is the mass delivered.  Given that
law, the bound `S ≤ 2 π k R E / (ℏ c)` is an exact identity: all reference to the auxiliary
black hole (its mass `M` and Newton's constant `G`) cancels. -/
theorem bekenstein_bound {k hbar c G M R E S : ℝ} (hG : G ≠ 0) (hM : M ≠ 0)
    (hGSL : S ≤ deriv (bhEntropy k hbar c G) M * deliveredMass G M R E) :
    S ≤ bekensteinBound k hbar c R E := by
  refine hGSL.trans_eq ?_
  rw [deriv_bhEntropy]
  unfold deliveredMass bekensteinBound
  field_simp
  ring

/-- The Bekenstein bound is saturated: for every choice of the parameters there is a system
whose entropy exactly attains the generalized-second-law estimate, and it equals the bound.
In particular the hypothesis of `Phys.bekenstein_bound` is not vacuous. -/
theorem bekenstein_bound_sharp {k hbar c G M R E : ℝ} (hG : G ≠ 0) (hM : M ≠ 0) :
    ∃ S : ℝ, S = deriv (bhEntropy k hbar c G) M * deliveredMass G M R E ∧
      S = bekensteinBound k hbar c R E := by
  refine ⟨deriv (bhEntropy k hbar c G) M * deliveredMass G M R E, rfl, ?_⟩
  rw [deriv_bhEntropy]
  unfold deliveredMass bekensteinBound
  field_simp
  ring

end Phys

