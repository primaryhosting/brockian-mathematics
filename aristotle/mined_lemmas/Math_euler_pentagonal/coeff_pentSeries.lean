import Mathlib

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Math

/-! ## Distinct partitions as finsets of positive integers -/

/-- The finset of all "partitions of `n` into distinct parts", encoded as finsets of
positive integers whose sum is `n`. -/

lemma coeff_pentSeries (n : ℕ) :
    (PowerSeries.coeff n) (1 + ∑' k : ℕ, ((-1 : ℤ⟦X⟧)) ^ (k + 1) *
        (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2)))
      = pentSign n := by
  rw [map_add, PowerSeries.coeff_one,
    summable_pent.map_tsum _ (PowerSeries.WithPiTopology.continuous_coeff ℤ n),
    tsum_eq_sum (s := Finset.range n)
      (fun k hk => coeff_pentTerm_eq_zero (by simpa using hk))]
  simp only [coeff_pentTerm]
  rw [Finset.sum_add_distrib, pentSign, Icc_one_eq_map, Finset.sum_map, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have e1 : ∑ k ∈ Finset.range n, (if (k + 1) * (3 * k + 2) / 2 = n then ((-1 : ℤ)) ^ (k + 1) else 0)
      = ∑ k ∈ Finset.range n,
        (if 2 * n = (k + 1) * (3 * (k + 1) - 1) then ((-1 : ℤ)) ^ (k + 1) else 0) :=
    Finset.sum_congr rfl (fun k _ => if_congr (pent1_iff k n) rfl rfl)
  have e2 : ∑ k ∈ Finset.range n, (if (k + 1) * (3 * k + 4) / 2 = n then ((-1 : ℤ)) ^ (k + 1) else 0)
      = ∑ k ∈ Finset.range n,
        (if 2 * n = (k + 1) * (3 * (k + 1) + 1) then ((-1 : ℤ)) ^ (k + 1) else 0) :=
    Finset.sum_congr rfl (fun k _ => if_congr (pent2_iff k n) rfl rfl)
  rw [e1, e2]
  ring

/-- **Euler's pentagonal number theorem**: as formal power series over `ℤ`,
`∏_{i ≥ 1} (1 - X^i) = 1 + ∑_{a ≥ 1} (-1)^a (X^{a(3a-1)/2} + X^{a(3a+1)/2})`. -/
