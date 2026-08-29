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

theorem vdw_bound (k r : ℕ) : VDWBound k r := by
  induction k generalizing r with
  | zero => exact vdw_zero r
  | succ n ih => exact vdw_succ (fun m => ih m) r

/-- **Van der Waerden's theorem.** For any coloring of `ℕ` by finitely many colors and any
`k`, there is a monochromatic arithmetic progression of length `k`: a starting point `a`
and a positive common difference `d` such that `a, a + d, …, a + (k-1) * d` all get the
same color. Since `k` is arbitrary, the monochromatic progressions are arbitrarily long. -/
