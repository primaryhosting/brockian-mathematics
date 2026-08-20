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

lemma proj_image_lineAddLattice_subset (v : ℝ × ℝ) :
    proj '' ((lineAddLattice v : AddSubgroup (ℝ × ℝ)) : Set (ℝ × ℝ))
      ⊆ Set.range (flowHom v) := by
  rintro y ⟨p, hp, rfl⟩
  simp only [lineAddLattice, SetLike.mem_coe, AddSubgroup.mem_sup] at hp
  obtain ⟨l, ⟨t, rfl⟩, z, hz, rfl⟩ := hp
  refine ⟨t, ?_⟩
  have hz0 : proj z = 0 := lattice_le_ker_proj hz
  simp [flowHom, hz0]

/-- If the direction `v` satisfies no nontrivial integral linear relation, then the orbit of the
unipotent flow is dense: the orbit closure subgroup is everything. -/
