import Mathlib

/-!
# Ratner
Category: Frontier Math
Target: Math2.ratner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

/-- The homogeneous space `X = G / Γ` for `G = ℝ²` and the lattice `Γ = ℤ²`, i.e. the
two-dimensional torus. -/
abbrev Torus2 : Type := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- The projection `G = ℝ² → X = ℝ²/ℤ²`. -/

lemma lattice_le_ker_proj :
    AddSubgroup.closure {((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))} ≤ proj.ker := by
  rw [AddSubgroup.closure_le]
  rintro p hp
  rcases hp with h | h <;> subst h <;>
    simp [AddMonoidHom.mem_ker, proj, Prod.ext_iff, AddCircle.coe_period]

