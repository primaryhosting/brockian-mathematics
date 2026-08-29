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

lemma summable_pent :
    Summable fun k : ℕ =>
      ((-1 : ℤ⟦X⟧)) ^ (k + 1) *
        (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2)) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  refine summable_of_finite_support ((Set.finite_Iio d).subset (fun k hk => ?_))
  simp only [Function.mem_support] at hk
  simp only [Set.mem_Iio]
  by_contra hcon
  exact hk (coeff_pentTerm_eq_zero (by omega))

