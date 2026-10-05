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

theorem fan_zero (k r : ℕ) :
    ∃ N : ℕ, ∀ c : ℕ → Fin r, HasAP c (k + 1) N ∨ Fan c k 0 N := by
  refine ⟨1, fun c => Or.inr ⟨0, fun _ => 0, fun _ => 0, by norm_num, ?_, ?_, ?_⟩⟩ <;> omega

/-- The inductive step for fans: given van der Waerden for progressions of length `k` and
any number of colors, a fan of size `s` can be upgraded to a fan of size `s + 1`, unless a
monochromatic progression of length `k + 1` appears. -/
