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

lemma orbitSubgroup_eq_top (v : ℝ × ℝ)
    (h : ∀ a b : ℤ, (a : ℝ) * v.1 + (b : ℝ) * v.2 = 0 → a = 0 ∧ b = 0) :
    orbitSubgroup v = ⊤ := by
  obtain ⟨hv1, hirr⟩ := irrational_ratio v h
  have hdense : Dense (Set.range (flowHom v)) :=
    Dense.mono (proj_image_lineAddLattice_subset v)
      (dense_image_proj (dense_lineAddLattice v hv1 hirr))
  rw [AddSubgroup.eq_top_iff']
  intro x
  have hx : x ∈ closure (Set.range (flowHom v)) := hdense.closure_eq ▸ Set.mem_univ x
  rw [← coe_orbitSubgroup] at hx
  exact hx

/-- The character of the torus attached to a pair of integers, `(x, y) ↦ a x + b y`. -/
