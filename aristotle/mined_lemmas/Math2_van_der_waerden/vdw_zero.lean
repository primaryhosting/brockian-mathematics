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

theorem vdw_zero (r : ℕ) : VDWBound 0 r :=
  ⟨2, fun _ => ⟨0, 1, by norm_num, by norm_num, by norm_num, by omega⟩⟩

/-- A fan of size `0` exists trivially. -/
