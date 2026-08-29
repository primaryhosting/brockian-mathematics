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

lemma tiltEval_surjective (p : ℕ) (K : Type*) [CommRing K] [ExpChar K p] [PerfectRing K p] :
    Function.Surjective (tiltEval p K) := by
  intro a
  refine ⟨⟨fun n => ((frobeniusEquiv K p).symm)^[n] a, ?_⟩, rfl⟩
  intro n
  have h1 : ((frobeniusEquiv K p).symm)^[n + 1] a
      = (frobeniusEquiv K p).symm (((frobeniusEquiv K p).symm)^[n] a) :=
    Function.iterate_succ_apply' _ _ _
  show ((frobeniusEquiv K p).symm)^[n + 1] a ^ p = ((frobeniusEquiv K p).symm)^[n] a
  rw [h1]
  simp

/-- **Tilting in characteristic `p`.**  For a perfect commutative ring `K` of characteristic `p`
(e.g. a perfectoid field of characteristic `p`), the projection `(xₙ) ↦ x₀` is a ring
isomorphism `K^♭ ≃+* K`. -/
