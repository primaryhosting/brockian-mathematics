/-
# Van Der Waerden
Category: Frontier Math
Target: Math2.van_der_waerden
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Van Der Waerden

Category: Frontier Math

Target: `Math2.van_der_waerden`

Provenance: Aristotle theorem prover (Harmonic)

Any finite coloring of `ℕ` has arbitrarily long monochromatic arithmetic progressions.

The proof is the classical "color focusing" (Graham–Rothschild) double induction:
an outer induction on the length `k` of the progression, and, inside it, an induction on
the number `s` of *focused* progressions with pairwise distinct colors that can be found
in a sufficiently long window.
-/

set_option autoImplicit false

namespace Math2

/-- `HasAP c k N` : the coloring `c` has a monochromatic arithmetic progression of
length `k` (with positive common difference `d < N`) such that even the "next" term
`a + k * d` lies below `N`. -/

theorem fan_all {k r : ℕ} (hW : ∀ m, VDWBound k m) (s : ℕ) :
    ∃ N : ℕ, ∀ c : ℕ → Fin r, HasAP c (k + 1) N ∨ Fan c k s N := by
  induction s with
  | zero => exact fan_zero k r
  | succ n ih => exact fan_step hW ih

/-- A fan with `r` pairwise distinctly colored progressions is impossible for an
`r`-coloring: the focus supplies an `(r+1)`-st color. -/
