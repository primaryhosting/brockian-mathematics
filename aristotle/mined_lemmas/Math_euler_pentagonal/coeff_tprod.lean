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

lemma coeff_tprod (n : ℕ) :
    (PowerSeries.coeff n) (∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1)))
      = ∑ S ∈ distinctSets n, ((-1 : ℤ)) ^ S.card := by
  have hp : HasProd (fun i : ℕ => (1 - (X : ℤ⟦X⟧) ^ (i + 1)))
      (∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1))) :=
    (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).hasProd
  have hc := ((PowerSeries.WithPiTopology.continuous_coeff ℤ n).tendsto _).comp hp
  refine tendsto_nhds_unique hc ?_
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop (Finset.range n)] with s hs
  exact (coeff_prod_finset s n hs).symm

/-! ### The pentagonal series -/

