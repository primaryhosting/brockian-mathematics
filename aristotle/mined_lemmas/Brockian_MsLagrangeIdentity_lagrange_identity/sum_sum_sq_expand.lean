import Mathlib
namespace Brockian.MsLagrangeIdentity

/-- Expanding the full double sum of `(aᵢbⱼ − aⱼbᵢ)²`. -/

private lemma sum_sum_sq_expand {n : ℕ} (a b : Fin n → ℝ) :
    ∑ i, ∑ j, (a i * b j - a j * b i) ^ 2
      = 2 * ((∑ i, a i ^ 2) * (∑ i, b i ^ 2) - (∑ i, a i * b i) ^ 2) := by
  have expand : ∀ i j : Fin n, (a i * b j - a j * b i) ^ 2 = a i ^ 2 * b j ^ 2 - 2 * a i * a j * b i * b j + a j ^ 2 * b i ^ 2 := by intro i j; ring
  simp_rw [expand]
  simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hmid : ∀ y : Fin n, ∑ x : Fin n, 2 * a x * a y * b x * b y = 2 * (a y * b y) * ∑ i, a i * b i := by
    intro y
    rw [show ∑ x : Fin n, 2 * a x * a y * b x * b y = ∑ i : Fin n, (2 * (a y * b y)) * (a i * b i) by
      apply Finset.sum_congr rfl; intro i _; ring]
    rw [← Finset.mul_sum]
  simp [hmid]
  rw [show ∑ x, a x ^ 2 * ∑ i, b i ^ 2 = (∑ x, a x ^ 2) * ∑ i, b i ^ 2 by rw [Finset.sum_mul]]
  rw [show ∑ x, 2 * (a x * b x) * ∑ i, a i * b i = (∑ i, a i * b i) * ∑ x, 2 * (a x * b x) by
    rw [Finset.mul_sum]; congr 1; ext x; ring]
  rw [pow_two]
  rw [show ∑ x : Fin n, 2 * (a x * b x) = 2 * ∑ x : Fin n, a x * b x by rw [Finset.mul_sum]]
  ring

/-- A symmetric function with vanishing diagonal: the full double sum is twice the
sum over the strictly-increasing pairs. -/
