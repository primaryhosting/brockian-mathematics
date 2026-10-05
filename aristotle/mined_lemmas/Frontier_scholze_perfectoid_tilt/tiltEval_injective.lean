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

lemma tiltEval_injective (p : ℕ) (K : Type*) [CommRing K] [IsReduced K] [ExpChar K p] :
    Function.Injective (tiltEval p K) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  simp only [tiltEval_apply] at h
  have key : ∀ n, f n = g n := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih =>
        have hpow : f (n + 1) ^ p = g (n + 1) ^ p := by rw [hf n, hg n, ih]
        exact frobenius_inj K p (by simpa [frobenius_def] using hpow)
  exact Subtype.ext (funext key)

