import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Real
open scoped ComplexOrder

namespace QI

/-! ## Von Neumann entropy and reduced density matrices -/

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a matrix, computed as the sum of
`negMulLog` over the eigenvalues.  (Defined to be `0` on non-Hermitian matrices.) -/

theorem vonNeumannEntropy_diagonal {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    vonNeumannEntropy (Matrix.diagonal fun i => (d i : ℂ)) = ∑ i, Real.negMulLog (d i) := by
  have hH : (Matrix.diagonal fun i => (d i : ℂ)).IsHermitian := isHermitian_diagonal_ofReal d
  rw [vonNeumannEntropy, dif_pos hH]
  have h2 := hH.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod,
    show (Multiset.map (fun i => (Polynomial.X - Polynomial.C ((d i : ℂ)))) Finset.univ.val)
      = Multiset.map (fun a => Polynomial.X - Polynomial.C a)
        (Multiset.map (fun i => ((d i : ℝ) : ℂ)) Finset.univ.val) by
          rw [Multiset.map_map]; rfl,
    Polynomial.roots_multiset_prod_X_sub_C] at h2
  have h3 : Multiset.map (fun (x : ℝ) => (x : ℂ)) (Multiset.map hH.eigenvalues Finset.univ.val)
      = Multiset.map (fun (x : ℝ) => (x : ℂ)) (Multiset.map d Finset.univ.val) := by
    rw [Multiset.map_map, Multiset.map_map]
    exact h2.symm
  have h4 : Multiset.map hH.eigenvalues Finset.univ.val = Multiset.map d Finset.univ.val :=
    Multiset.map_injective (fun _ _ hab => Complex.ofReal_injective hab) h3
  calc ∑ i, Real.negMulLog (hH.eigenvalues i)
      = (Multiset.map Real.negMulLog (Multiset.map hH.eigenvalues Finset.univ.val)).sum := by
        rw [Multiset.map_map]; rfl
    _ = (Multiset.map Real.negMulLog (Multiset.map d Finset.univ.val)).sum := by rw [h4]
    _ = ∑ i, Real.negMulLog (d i) := by rw [Multiset.map_map]; rfl

/-! ## The classical (Shannon) strong subadditivity inequality -/

/-- Gibbs' inequality in pointwise form: `u * log (v / u) ≤ v - u`. -/
