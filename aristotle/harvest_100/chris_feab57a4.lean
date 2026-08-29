/-
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
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

set_option grind.warning false

namespace Chem

/-- The number of intensive state variables describing a heterogeneous system with
`C` chemical components distributed over `P` phases: temperature and pressure, plus,
for each phase, the `C - 1` independent mole fractions of that phase (the last one is
fixed by the requirement that the mole fractions of a phase sum to `1`). -/
def gibbsVariables (C P : ℕ) : ℕ := 2 + P * (C - 1)

/-- The number of independent equilibrium conditions: for each of the `C` components,
its chemical potential must agree across the `P` phases, giving `P - 1` independent
equations per component. -/
def gibbsConstraints (C P : ℕ) : ℕ := C * (P - 1)

/-- **Gibbs' phase rule**, as an affine-dimension count.

The intensive state of a system of `C` components in `P` phases is described by
`gibbsVariables C P = 2 + P * (C - 1)` real variables, subject to the
`gibbsConstraints C P = C * (P - 1)` equilibrium conditions expressed by a linear map
`f`.  If these conditions are independent (i.e. `f` is surjective), then the solution
set is the linear subspace `ker f`, whose dimension — the number of degrees of freedom
`F` — satisfies `F + P = C + 2`, that is, `F = C - P + 2`. -/
theorem gibbs_phase_rule (C P : ℕ) (hC : 1 ≤ C) (hP : 1 ≤ P)
    (f : (Fin (gibbsVariables C P) → ℝ) →ₗ[ℝ] (Fin (gibbsConstraints C P) → ℝ))
    (hf : Function.Surjective f) :
    Module.finrank ℝ (LinearMap.ker f) + P = C + 2 := by
  have hrank : Module.finrank ℝ (LinearMap.range f) = gibbsConstraints C P := by
    rw [LinearMap.range_eq_top.mpr hf]
    simp
  have key := LinearMap.finrank_range_add_finrank_ker f
  rw [hrank, Module.finrank_fin_fun] at key
  obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
  obtain ⟨p, rfl⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
  simp only [gibbsVariables, gibbsConstraints, Nat.add_sub_cancel] at key
  have key2 : c * p + p + Module.finrank ℝ (LinearMap.ker f) = 2 + (c * p + c) := by
    have h1 : (c + 1) * p = c * p + p := by ring
    have h2 : (p + 1) * c = c * p + c := by ring
    rw [h1, h2] at key
    exact key
  clear key hrank
  omega

/-- The phase rule in its familiar signed form: over the integers, the number of
degrees of freedom equals `C - P + 2`. -/
theorem gibbs_phase_rule_int (C P : ℕ) (hC : 1 ≤ C) (hP : 1 ≤ P)
    (f : (Fin (gibbsVariables C P) → ℝ) →ₗ[ℝ] (Fin (gibbsConstraints C P) → ℝ))
    (hf : Function.Surjective f) :
    (Module.finrank ℝ (LinearMap.ker f) : ℤ) = (C : ℤ) - (P : ℤ) + 2 := by
  have h := gibbs_phase_rule C P hC hP f hf
  omega

/-- The hypotheses of `gibbs_phase_rule` are not vacuous: whenever `1 ≤ C`, `1 ≤ P`
and `P ≤ C + 2` (the physically meaningful range, in which the number of equilibrium
conditions does not exceed the number of variables), an independent system of
equilibrium conditions — i.e. a surjective linear map — does exist. -/
theorem exists_surjective_gibbs_constraints (C P : ℕ) (hC : 1 ≤ C) (hP : 1 ≤ P)
    (hPC : P ≤ C + 2) :
    ∃ f : (Fin (gibbsVariables C P) → ℝ) →ₗ[ℝ] (Fin (gibbsConstraints C P) → ℝ),
      Function.Surjective f := by
  have hle : gibbsConstraints C P ≤ gibbsVariables C P := by
    obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
    obtain ⟨p, rfl⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
    simp only [gibbsVariables, gibbsConstraints, Nat.add_sub_cancel]
    have h1 : (c + 1) * p = c * p + p := by ring
    have h2 : (p + 1) * c = c * p + c := by ring
    rw [h1, h2]
    omega
  refine ⟨LinearMap.funLeft ℝ ℝ (Fin.castLE hle), fun y => ?_⟩
  refine ⟨fun j => if h : (j : ℕ) < gibbsConstraints C P then y ⟨j, h⟩ else 0, ?_⟩
  funext i
  simp only [LinearMap.funLeft_apply, Fin.val_castLE, Fin.is_lt, dif_pos]

end Chem

