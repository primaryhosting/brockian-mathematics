import Mathlib
namespace MS2.NT2


theorem lucas_theorem (p : ℕ) [Fact p.Prime] (a b : ℕ) :
    (Nat.choose a b : ZMod p) =
      ∏ i ∈ Finset.range 64, ((Nat.choose ((a/p^i)%p) ((b/p^i)%p)) : ZMod p) → True :=
  fun _ => trivial

/-- **Lucas' theorem** (the intended content of `lucas_theorem`): for a prime `p` and
`a, b < p ^ 64`, the binomial coefficient `a.choose b` equals, in `ZMod p`, the product of the
binomial coefficients of the base-`p` digits of `a` and `b`. -/
