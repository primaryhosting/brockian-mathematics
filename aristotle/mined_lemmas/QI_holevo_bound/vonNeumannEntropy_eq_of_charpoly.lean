/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset ComplexOrder

/-! ## Classical information quantities -/

variable {ι X I Y : Type*}

/-- Shannon entropy of a finite (sub)probability vector, `H(p) = -∑ p i log (p i)`. -/

lemma vonNeumannEntropy_eq_of_charpoly {A : Matrix n n ℂ} (hA : A.IsHermitian) (d : n → ℝ)
    (h : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C ((d i : ℂ)))) :
    vonNeumannEntropy A = shannonEntropy d := by
  have hroots : A.charpoly.roots = Multiset.map (fun i => ((d i : ℂ))) Finset.univ.val := by
    rw [h, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have h2 : Multiset.map (fun i => ((hA.eigenvalues i : ℂ))) Finset.univ.val
      = Multiset.map (fun i => ((d i : ℂ))) Finset.univ.val := by
    rw [← hroots, hA.roots_charpoly_eq_eigenvalues]
    rfl
  have h3 : Multiset.map hA.eigenvalues Finset.univ.val = Multiset.map d Finset.univ.val := by
    rw [show (fun i => ((hA.eigenvalues i : ℂ))) = (fun r : ℝ => (r : ℂ)) ∘ hA.eigenvalues from rfl,
      show (fun i => ((d i : ℂ))) = (fun r : ℝ => (r : ℂ)) ∘ d from rfl,
      ← Multiset.map_map, ← Multiset.map_map] at h2
    exact Multiset.map_injective Complex.ofReal_injective h2
  have h4 : ∑ i, Real.negMulLog (hA.eigenvalues i) = ∑ i, Real.negMulLog (d i) := by
    have h5 := congrArg (fun m => (Multiset.map Real.negMulLog m).sum) h3
    simp only [Multiset.map_map] at h5
    rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
    exact h5
  rw [vonNeumannEntropy, dif_pos hA, shannonEntropy, h4]

omit [Fintype n] in
/-- A diagonal matrix with real entries is Hermitian. -/
