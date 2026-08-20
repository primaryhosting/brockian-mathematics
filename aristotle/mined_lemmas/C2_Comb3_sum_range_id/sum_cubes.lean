import Mathlib
open Finset
namespace C2.Comb3

/-- Gauss' summation formula: `∑_{i<n} i = n(n-1)/2` (natural division is exact here). -/

theorem sum_cubes (n : ℕ) : ∑ i ∈ range (n+1), i^3 = (∑ i ∈ range (n+1), i)^2 := by
  have hcube : 4 * ∑ i ∈ range (n+1), i^3 = n^2*(n+1)^2 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, Nat.mul_add, ih]; ring
  have hid : (∑ i ∈ range (n+1), i) * 2 = n*(n+1) := by
    simpa [Nat.mul_comm] using Finset.sum_range_id_mul_two (n+1)
  have hsq : 4 * (∑ i ∈ range (n+1), i)^2 = n^2*(n+1)^2 := by
    have : ((∑ i ∈ range (n+1), i) * 2)^2 = (n*(n+1))^2 := by rw [hid]
    calc 4 * (∑ i ∈ range (n+1), i)^2 = ((∑ i ∈ range (n+1), i) * 2)^2 := by ring
      _ = (n*(n+1))^2 := this
      _ = n^2*(n+1)^2 := by ring
  omega

/-- Symmetry of binomial coefficients. -/
