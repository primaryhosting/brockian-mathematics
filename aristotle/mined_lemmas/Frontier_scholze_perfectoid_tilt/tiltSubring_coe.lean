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

lemma tiltSubring_coe (p : ℕ) (K : Type*) [CommRing K] [ExpChar K p] :
    (tiltSubring p K : Set (ℕ → K)) = tiltSubmonoid p K := rfl

/-!
## The tilt is always perfect

This is the fundamental structural feature of tilting: whatever `K` is, the `p`-power map on
`K^♭` is bijective (its inverse is the shift).
-/

/-- The `p`-power map on the tilt is injective. -/
