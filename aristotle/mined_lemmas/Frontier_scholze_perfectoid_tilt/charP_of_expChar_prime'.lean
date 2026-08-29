import Mathlib

/-!
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace Frontier

/-!
## The tilt

For a `p`-adic (or characteristic `p`) coefficient object `K`, Scholze's *tilt* `K^♭` is the
inverse limit of `K` along the `p`-power map,
`K^♭ = lim_{x ↦ x^p} K = {(x₀, x₁, x₂, …) : xₙ₊₁^p = xₙ}`,
with componentwise multiplication.  We realize it as a submonoid of `ℕ → K` (and, in
characteristic `p`, as a subring, since then `x ↦ x^p` is additive).
-/

/-- The underlying set of the tilt `K^♭`: sequences `(xₙ)` with `xₙ₊₁ ^ p = xₙ`. -/

lemma charP_of_expChar_prime' (R : Type*) [AddMonoidWithOne R] (p : ℕ) (hp : p.Prime)
    [hR : ExpChar R p] : CharP R p := by
  cases hR with
  | zero => exact absurd hp Nat.not_prime_one
  | prime _ => assumption

/-- **Scholze's tilting equivalence (formalized statement, characteristic `p` case).**

For a prime `p` and perfectoid fields `K`, `L` of characteristic `p` (i.e. perfect complete
nonarchimedean fields of characteristic `p`; here we retain the algebraic content: perfect
fields of characteristic `p`), with the tilt `K^♭ = lim_{x ↦ x^p} K`:

* the tilt is always perfect: the `p`-power map on `K^♭` is bijective (this holds for the tilt
  of an arbitrary commutative monoid);
* tilting is an equivalence, with the untilt as inverse: `K^♭ ≃+* K` via `(xₙ) ↦ x₀`, and
  likewise for `L`;
* the equivalence is natural in the field: it intertwines the induced map `f^♭ : K^♭ →+* L^♭`
  with `f : K →+* L`.

Together these say that, on the characteristic `p` side, tilting is (naturally isomorphic to)
the identity functor, which is the base case of the tilting correspondence. -/
