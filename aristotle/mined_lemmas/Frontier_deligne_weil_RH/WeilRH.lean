/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Formalization notes

Mathlib (as of the pinned commit) contains no development of étale cohomology, Weil
cohomology theories, or zeta functions of varieties over finite fields, so no existing

def WeilRH (q d : ℕ) (eig : ℕ → Multiset ℂ) : Prop :=
  ∀ w ≤ 2 * d, ∀ a ∈ eig w, ‖a‖ = (q : ℝ) ^ ((w : ℝ) / 2)

/-- A sum over `range (2 * n + 1)` of a function vanishing on odd arguments is the sum
over the even arguments `2 i`, `i ≤ n`. -/
