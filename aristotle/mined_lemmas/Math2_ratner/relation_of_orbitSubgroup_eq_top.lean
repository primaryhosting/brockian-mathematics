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

lemma relation_of_orbitSubgroup_eq_top (v : ℝ × ℝ) (h : orbitSubgroup v = ⊤) (a b : ℤ)
    (hab : (a : ℝ) * v.1 + (b : ℝ) * v.2 = 0) : a = 0 ∧ b = 0 := by
  by_contra hcon
  have hkerclosed : IsClosed ((chi a b).ker : Set Torus2) := by
    rw [AddMonoidHom.coe_ker]
    exact isClosed_singleton.preimage (continuous_chi a b)
  have hle : orbitSubgroup v ≤ (chi a b).ker := by
    refine AddSubgroup.topologicalClosure_minimal _ ?_ hkerclosed
    rintro y ⟨t, rfl⟩
    have hval : chi a b (flowHom v t)
        = (((t * ((a : ℝ) * v.1 + (b : ℝ) * v.2)) : ℝ) : AddCircle (1 : ℝ)) := by
      rw [flowHom_apply_coe, chi_apply]
      ring_nf
    rw [AddMonoidHom.mem_ker, hval, hab, mul_zero]
    simp
  rw [h, top_le_iff] at hle
  have hall : ∀ p : Torus2, chi a b p = 0 := by
    intro p
    have hp : p ∈ (chi a b).ker := by rw [hle]; trivial
    simpa [AddMonoidHom.mem_ker] using hp
  rcases (not_and_or.1 hcon) with ha | hb
  · have hne : (a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
    have hz := hall (((1 / (2 * (a : ℝ)) : ℝ) : AddCircle (1 : ℝ)), ((0 : ℝ) : AddCircle (1 : ℝ)))
    rw [chi_apply] at hz
    have heq : ((a : ℝ) * (1 / (2 * (a : ℝ))) + (b : ℝ) * 0) = 1 / 2 := by field_simp; ring
    rw [heq] at hz
    exact half_ne_zero_addCircle hz
  · have hne : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
    have hz := hall (((0 : ℝ) : AddCircle (1 : ℝ)), ((1 / (2 * (b : ℝ)) : ℝ) : AddCircle (1 : ℝ)))
    rw [chi_apply] at hz
    have heq : ((a : ℝ) * 0 + (b : ℝ) * (1 / (2 * (b : ℝ)))) = 1 / 2 := by field_simp; ring
    rw [heq] at hz
    exact half_ne_zero_addCircle hz

/-- **Ratner's orbit closure theorem** for the unipotent one-parameter flow
`t ↦ x + t·v` on the homogeneous space `X = ℝ²/ℤ²`.

There is a closed, connected subgroup `H ≤ X` containing the acting one-parameter group such that
*every* orbit closure is a coset `x + H` of `H` (in particular every orbit closure is a
homogeneous subspace).  Moreover `H` is all of `X` — i.e. every orbit is dense — exactly when the
direction `v` satisfies no nontrivial integral linear relation. -/
