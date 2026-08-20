/-
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Archive.Wiedijk100Theorems.AbelRuffini

/-!
# Abel Ruffini Deg 5

The quintic is not solvable by radicals: there is a degree-`5` irreducible polynomial over `ℚ`
whose Galois group is not solvable (indeed its Galois group acts on the five complex roots as the
full symmetric group `S₅`), and hence none of whose complex roots is expressible by radicals.

The witness is `X ^ 5 - 4 * X + 2`, which is Eisenstein at `2` and has exactly three real roots.

The main input is Mathlib's Archive development of the Abel-Ruffini theorem
(`Archive/Wiedijk100Theorems/AbelRuffini.lean`, by Thomas Browning), which provides
`AbelRuffini.gal_Phi`, `AbelRuffini.irreducible_Phi` and `AbelRuffini.complex_roots_Phi`,
together with `solvableByRad.isSolvable'` and `Equiv.Perm.not_solvable` from Mathlib proper.
-/

namespace Math

open Polynomial

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-- The witness polynomial `X ^ 5 - 4 * X + 2 : ℚ[X]`. -/

theorem quinticWitness_eq : quinticWitness = AbelRuffini.Φ ℚ 4 2 := by
  simp [quinticWitness, AbelRuffini.Φ]

/-- **Abel-Ruffini theorem in degree 5.** The general quintic is not solvable by radicals:
the irreducible rational quintic `X ^ 5 - 4 * X + 2` has non-solvable Galois group (its Galois
group acts on the five complex roots as the full symmetric group), and consequently none of its
complex roots -- which exist -- is solvable by radicals over `ℚ`. -/
