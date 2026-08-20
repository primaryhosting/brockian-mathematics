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

lemma flow_mem_orbitSubgroup (v : ℝ × ℝ) (t : ℝ) : flowHom v t ∈ orbitSubgroup v := by
  have : flowHom v t ∈ closure (Set.range (flowHom v)) := subset_closure ⟨t, rfl⟩
  rwa [← coe_orbitSubgroup] at this

/-- No nontrivial integral relation forces the first coordinate to be nonzero and the slope to be
irrational. -/
