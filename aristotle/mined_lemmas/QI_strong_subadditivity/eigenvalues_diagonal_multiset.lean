/-
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` commands to precede any module docstring, so the header above is
repeated as a module docstring below the import.)
-/

import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Real Finset

namespace QI

/-! ## Von Neumann entropy -/

open scoped Classical in
/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix, computed as
`∑ i, negMulLog (λ i)` over the eigenvalues of `ρ`. (Junk value `0` for non-Hermitian input.) -/

theorem eigenvalues_diagonal_multiset {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ)
    (h : (diagonal fun i => ((d i : ℝ) : ℂ)).IsHermitian) :
    Multiset.map h.eigenvalues Finset.univ.val = Multiset.map d Finset.univ.val := by
  have h1 := h.roots_charpoly_eq_eigenvalues
  have h2 : (diagonal fun i => ((d i : ℝ) : ℂ)).charpoly.roots
      = Multiset.map (fun i => ((d i : ℝ) : ℂ)) Finset.univ.val := by
    rw [charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  rw [h1] at h2
  have h3 := congrArg (Multiset.map Complex.re) h2
  simpa [Multiset.map_map, Function.comp_def] using h3

/-- The von Neumann entropy of a matrix that is diagonal with real entries is the Shannon
entropy of its diagonal. -/
