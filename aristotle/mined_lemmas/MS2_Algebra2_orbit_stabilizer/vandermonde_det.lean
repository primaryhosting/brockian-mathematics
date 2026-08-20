import Mathlib
namespace MS2.Algebra2

theorem vandermonde_det {n : ℕ} (v : Fin n → ℝ) :
    (Matrix.of (fun (i j : Fin n) => (v i)^(j:ℕ))).det
      = ∏ i ∈ Finset.univ, ∏ j ∈ Finset.univ.filter (· > i), (v j - v i) := by
  have hfil : ∀ i : Fin n, Finset.univ.filter (· > i) = Finset.Ioi i := by
    intro i; ext j; simp
  simp only [hfil]
  exact Matrix.det_vandermonde v
