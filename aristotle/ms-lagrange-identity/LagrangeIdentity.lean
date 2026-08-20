import Mathlib
namespace Brockian.MsLagrangeIdentity
/-- Lagrange's identity: (∑ aᵢ²)(∑ bᵢ²) − (∑ aᵢbᵢ)² = ∑_{i<j} (aᵢbⱼ − aⱼbᵢ)². -/
theorem lagrange_identity {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i, a i ^ 2) * (∑ i, b i ^ 2) - (∑ i, a i * b i) ^ 2
      = ∑ i, ∑ j, (if i < j then (a i * b j - a j * b i) ^ 2 else 0) := by
  sorry
end Brockian.MsLagrangeIdentity
