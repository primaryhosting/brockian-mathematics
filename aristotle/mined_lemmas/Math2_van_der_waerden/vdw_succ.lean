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

theorem vdw_succ {k : ℕ} (hW : ∀ m, VDWBound k m) (r : ℕ) : VDWBound (k + 1) r := by
  obtain ⟨N, hN⟩ := fan_all (k := k) (r := r) hW r
  refine ⟨N, fun c => ?_⟩
  rcases hN c with h | h
  · exact h
  · exact absurd h (fun hh => fan_card hh)

/-- The finitary van der Waerden theorem: for every length `k` and number of colors `r`
there is an `N` such that every `r`-coloring of `ℕ` has a monochromatic arithmetic
progression of length `k` within `[0, N)`. -/
