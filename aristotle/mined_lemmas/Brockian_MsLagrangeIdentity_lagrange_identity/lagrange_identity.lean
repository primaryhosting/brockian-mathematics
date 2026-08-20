import Mathlib
namespace Brockian.MsLagrangeIdentity

/-- Expanding the full double sum of `(aᵢbⱼ − aⱼbᵢ)²`. -/

theorem lagrange_identity {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i, a i ^ 2) * (∑ i, b i ^ 2) - (∑ i, a i * b i) ^ 2
      = ∑ i, ∑ j, (if i < j then (a i * b j - a j * b i) ^ 2 else 0) := by
  have h := sum_symm_eq_two_mul_sum_lt (fun i j => (a i * b j - a j * b i) ^ 2)
    (fun i j => by ring_nf) (fun i => by ring_nf)
  rw [sum_sum_sq_expand a b] at h
  linarith

end Brockian.MsLagrangeIdentity

