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

lemma tilt_pow_surjective (p : ℕ) (K : Type*) [CommMonoid K] :
    Function.Surjective (fun x : tiltSubmonoid p K => x ^ p) := by
  rintro ⟨g, hg⟩
  refine ⟨⟨fun n => g (n + 1), fun n => hg (n + 1)⟩, ?_⟩
  apply Subtype.ext
  funext n
  simpa using hg n

/-- **The tilt is perfect.**  The `p`-power map on `K^♭` is bijective for every commutative
monoid `K`. -/
