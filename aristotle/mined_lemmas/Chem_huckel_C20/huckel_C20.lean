/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring `/-! ... -/` before the `import`
line, so the required header appears here as an ordinary block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-! ### The primitive 20-th root of unity and the associated character -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

theorem huckel_C20 :
    spectrum ℂ ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) =
      {z : ℂ | ∃ k : ℕ, k < 20 ∧ z = (2 * Real.cos (2 * Real.pi * k / 20) : ℝ)} := by
  rw [← adjC20_eq_cycleGraph]
  obtain ⟨u, hu⟩ := isUnit_dftMat
  have hconj : adjC20 = (u : Matrix (ZMod 20) (ZMod 20) ℂ) * diagC20
      * ((u⁻¹ : (Matrix (ZMod 20) (ZMod 20) ℂ)ˣ) : Matrix (ZMod 20) (ZMod 20) ℂ) := by
    have h : adjC20 * (u : Matrix (ZMod 20) (ZMod 20) ℂ)
        = (u : Matrix (ZMod 20) (ZMod 20) ℂ) * diagC20 := by
      rw [hu]; exact adj_mul_dft
    rw [← h, mul_assoc, u.mul_inv, mul_one]
  rw [hconj, spectrum.units_conjugate, diagC20, spectrum_diagonal]
  ext z
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, ZMod.val_lt k, by push_cast; ring⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(k : ZMod 20), ?_⟩
    rw [ZMod.val_natCast_of_lt hk]
    push_cast
    ring

/-- The explicit Hückel eigenvectors of `C₂₀`: the `k`-th Fourier mode
`j ↦ exp (2πi jk/20)` is an eigenvector of the adjacency matrix with eigenvalue
`2 cos (2πk/20)`. -/
