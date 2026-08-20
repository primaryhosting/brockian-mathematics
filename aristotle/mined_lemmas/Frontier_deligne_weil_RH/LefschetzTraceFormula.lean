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

def LefschetzTraceFormula (N : ℕ → ℕ) (d : ℕ) (eig : ℕ → Multiset ℂ) : Prop :=
  ∀ m, 1 ≤ m → (N m : ℂ) = ∑ w ∈ range (2 * d + 1),
    (-1 : ℂ) ^ w * ((eig w).map (fun a => a ^ m)).sum

/-- The Riemann hypothesis of the Weil conjectures (Deligne): every eigenvalue of the
geometric Frobenius on the `w`-th cohomology group has complex absolute value
`q ^ (w / 2)`. -/
