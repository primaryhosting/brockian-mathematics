import Mathlib
namespace Brockian.MsLagrangeIdentity

/-- Expanding the full double sum of `(aᵢbⱼ − aⱼbᵢ)²`. -/

private lemma sum_symm_eq_two_mul_sum_lt {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    ∑ i, ∑ j, f i j = 2 * ∑ i, ∑ j, (if i < j then f i j else 0) := by
  have h1 : ∑ i, ∑ j, f i j = ∑ i, ∑ j, (if i < j then f i j else if i > j then f i j else 0) := by
    congr 1 with i
    congr 1 with j
    by_cases hij : i < j <;> by_cases hij' : i > j <;> simp [hij, hij']
    have : i = j := le_antisymm (le_of_not_gt hij') (le_of_not_gt hij)
    simp [this, hdiag j]
  have h2 : ∑ i, ∑ j, (if i < j then f i j else if i > j then f i j else 0) =
            ∑ i, ∑ j, (if i < j then f i j else 0) + ∑ i, ∑ j, (if i > j then f i j else 0) := by
    rw [← Finset.sum_add_distrib]
    congr 1 with i
    rw [← Finset.sum_add_distrib]
    congr 1 with j
    by_cases hij : i < j
    · simp [hij]
      intro hj; exact (lt_asymm hj hij).elim
    · by_cases hij' : i > j
      · simp [hij, hij']
      · simp [hij, hij']
  have h3 : ∑ i, ∑ j, (if i > j then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [← Finset.sum_comm]
    congr 1 with i
    congr 1 with j
    by_cases hij : i < j
    · simp [hsymm i j, hij]
    · simp [hij]
  rw [h1, h2, h3]
  ring

/-- Lagrange's identity: (∑ aᵢ²)(∑ bᵢ²) − (∑ aᵢbᵢ)² = ∑_{i<j} (aᵢbⱼ − aⱼbᵢ)². -/
