import Mathlib

/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Pointwise

namespace Chem

/-- The intensive state variables of a system with `C` chemical components distributed over
`P` phases: temperature, pressure, and the `C` mole fractions of each of the `P` phases,
i.e. `2 + P * C` real variables. -/
abbrev StateVars (C P : ℕ) : Type := Fin (2 + P * C) → ℝ

/-- The equilibrium constraints on the intensive variables: one normalization condition
`∑ mole fractions = 1` per phase (`P` equations) together with the equality of the chemical
potential of each component across consecutive phases (`C * (P - 1)` equations). -/
abbrev Constraints (C P : ℕ) : Type := Fin (P + C * (P - 1)) → ℝ

/-- Number of variables minus number of constraints, computed in `ℤ`. -/
theorem variables_sub_constraints (C P : ℕ) (hP : 1 ≤ P) :
    ((2 + P * C : ℕ) : ℤ) - ((P + C * (P - 1) : ℕ) : ℤ) = (C : ℤ) - (P : ℤ) + 2 := by
  obtain ⟨Q, rfl⟩ := Nat.exists_eq_add_of_le hP
  push_cast [Nat.add_sub_cancel_left]
  ring

/-- The number of constraints never exceeds the number of variables when the constraint map
is surjective; equivalently `P ≤ C + 2`. -/
theorem phases_le (C P : ℕ) (hP : 1 ≤ P) (L : StateVars C P →ₗ[ℝ] Constraints C P)
    (hL : Function.Surjective L) : P ≤ C + 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.mpr hL] at h
  simp only [finrank_top, Module.finrank_fin_fun] at h
  obtain ⟨Q, rfl⟩ := Nat.exists_eq_add_of_le hP
  simp only [Nat.add_sub_cancel_left] at h
  nlinarith [h, Nat.zero_le (Module.finrank ℝ (LinearMap.ker L))]

/-- **Gibbs phase rule.**  For a system of `C` components in `P ≥ 1` phases the intensive state
is described by `2 + P * C` variables (temperature, pressure and the mole fractions in every
phase), subject to `P + C * (P - 1)` independent equilibrium constraints (normalization of the
mole fractions in each phase and equality of the chemical potentials across the phases).
If the constraint map `L` is linear and independent (surjective), the space of admissible
variations — the direction space of the affine set of equilibrium states — has dimension

`F = C - P + 2`. -/
theorem gibbs_phase_rule (C P : ℕ) (hP : 1 ≤ P) (L : StateVars C P →ₗ[ℝ] Constraints C P)
    (hL : Function.Surjective L) :
    (Module.finrank ℝ (LinearMap.ker L) : ℤ) = (C : ℤ) - (P : ℤ) + 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.mpr hL] at h
  simp only [finrank_top, Module.finrank_fin_fun] at h
  have h' : ((P + C * (P - 1) : ℕ) : ℤ) + (Module.finrank ℝ (LinearMap.ker L) : ℤ)
      = ((2 + P * C : ℕ) : ℤ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) h
  have := variables_sub_constraints C P hP
  linarith

/-- Non-vacuity: whenever `1 ≤ P ≤ C + 2` an independent (surjective) linear constraint map of
the required shape does exist. -/
theorem exists_surjective_constraints (C P : ℕ) (hP : 1 ≤ P) (hPC : P ≤ C + 2) :
    ∃ L : StateVars C P →ₗ[ℝ] Constraints C P, Function.Surjective L := by
  have hle : P + C * (P - 1) ≤ 2 + P * C := by
    obtain ⟨Q, rfl⟩ := Nat.exists_eq_add_of_le hP
    simp only [Nat.add_sub_cancel_left]
    have : (1 + Q) * C = C * Q + C := by ring
    omega
  refine ⟨LinearMap.funLeft ℝ ℝ (Fin.castLE hle), ?_⟩
  exact LinearMap.funLeft_surjective_of_injective ℝ ℝ _ (Fin.castLE_injective hle)

/-- The set of equilibrium states, i.e. the solutions of the constraint equations `L x = b`,
is an affine subset whose difference set is exactly the kernel of `L`. -/
theorem solution_vsub_solution (C P : ℕ) (L : StateVars C P →ₗ[ℝ] Constraints C P)
    (hL : Function.Surjective L) (b : Constraints C P) :
    {x : StateVars C P | L x = b} -ᵥ {x : StateVars C P | L x = b}
      = (LinearMap.ker L : Set (StateVars C P)) := by
  obtain ⟨x₀, hx₀⟩ := hL b
  ext v
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    simp only [Set.mem_setOf_eq] at hx hy
    simp [LinearMap.mem_ker, vsub_eq_sub, map_sub, hx, hy]
  · intro hv
    refine ⟨x₀ + v, ?_, x₀, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, map_add, hx₀]
      simpa [LinearMap.mem_ker] using congrArg (fun w => b + w) (LinearMap.mem_ker.mp hv)
    · simpa using hx₀
    · simp [vsub_eq_sub]

/-- **Gibbs phase rule, affine form.**  The affine set of equilibrium states
`{x | L x = b}` has affine dimension `F = C - P + 2`. -/
theorem gibbs_phase_rule_affine (C P : ℕ) (hP : 1 ≤ P) (L : StateVars C P →ₗ[ℝ] Constraints C P)
    (hL : Function.Surjective L) (b : Constraints C P) :
    (Module.finrank ℝ (vectorSpan ℝ {x : StateVars C P | L x = b}) : ℤ)
      = (C : ℤ) - (P : ℤ) + 2 := by
  have hspan : vectorSpan ℝ {x : StateVars C P | L x = b} = LinearMap.ker L := by
    rw [vectorSpan_def, solution_vsub_solution C P L hL b, Submodule.span_eq]
  rw [hspan]
  exact gibbs_phase_rule C P hP L hL

end Chem

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

