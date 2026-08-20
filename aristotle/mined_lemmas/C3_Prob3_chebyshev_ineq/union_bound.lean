import Mathlib
open Finset
namespace C3.Prob3

/-- Chebyshev-type inequality: `a²` times the number of indices with `a ≤ |xᵢ|`
is at most the sum of squares. -/

theorem union_bound {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {n : ℕ} (A : Fin n → Finset Ω) :
    (univ.biUnion A).card ≤ ∑ i, (A i).card :=
  card_biUnion_le

end C3.Prob3

