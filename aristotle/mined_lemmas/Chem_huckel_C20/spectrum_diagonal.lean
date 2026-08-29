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

lemma spectrum_diagonal (d : ZMod 20 → ℂ) :
    spectrum ℂ (Matrix.diagonal d) = Set.range d := by
  ext l
  rw [spectrum.mem_iff]
  have halg : (algebraMap ℂ (Matrix (ZMod 20) (ZMod 20) ℂ)) l - Matrix.diagonal d
      = Matrix.diagonal (fun k => l - d k) := by
    rw [Matrix.algebraMap_eq_diagonal, ← Matrix.diagonal_sub]
    rfl
  rw [halg, Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero,
    not_not, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, (sub_eq_zero.mp hk).symm⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Finset.mem_univ k, by rw [hk, sub_self]⟩

/-- **Hückel theory for C₂₀.** The adjacency eigenvalues of the cycle graph `C₂₀`
(equivalently, up to the affine transformation `α + βx`, the Hückel MO energies of the
20-membered carbon ring) are exactly `2 cos (2πk/20)` for `k = 0, …, 19`. -/
