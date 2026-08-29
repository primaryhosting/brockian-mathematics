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

@[simp] lemma tiltEquiv_apply (p : ℕ) (K : Type*) [CommRing K] [IsReduced K] [ExpChar K p]
    [PerfectRing K p] (x : tiltSubring p K) : tiltEquiv p K x = (x : ℕ → K) 0 := rfl

/-!
## Functoriality of tilting
-/

/-- The ring homomorphism `(ℕ → K) →+* (ℕ → L)` induced by `f : K →+* L`. -/
