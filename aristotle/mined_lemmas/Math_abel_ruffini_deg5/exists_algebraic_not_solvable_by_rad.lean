/-
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The quintic `Φ a b = X ^ 5 - a * X + b` over `ℚ`, for suitable natural numbers `a, b`,
is irreducible with exactly three real roots, hence its Galois group is the full
symmetric group `S₅`, which is not solvable.  Combined with the (already formalized)
direction of Abel–Ruffini stating that an irreducible polynomial with a root solvable
by radicals has solvable Galois group, this shows that the quintic `X ^ 5 - 4 * X + 2`
is not solvable by radicals.

The main external ingredients are
* `solvableByRad.isSolvable'` : an irreducible polynomial with a root that is solvable
  by radicals has solvable Galois group;
* `Polynomial.Gal.galActionHom_bijective_of_prime_degree'` : an irreducible polynomial of
  prime degree with at most three non-real roots has full symmetric Galois group;
* `Equiv.Perm.not_solvable` : the symmetric group on five letters is not solvable.

The development of the auxiliary polynomial `Phi` follows the classical argument and is adapted
from the mathlib archive file `Archive/Wiedijk100Theorems/AbelRuffini.lean` (Apache 2.0,
Thomas Browning), which is not part of the `Mathlib` library itself.
-/

namespace AbelRuffiniDeg5

open Function Polynomial Polynomial.Gal Ideal

open scoped Polynomial

attribute [local instance] splits_ℚ_ℂ

variable (R : Type*) [CommRing R] (a b : ℕ)

/-- The quintic polynomial `X ^ 5 - a * X + b`. -/

theorem exists_algebraic_not_solvable_by_rad :
    ∃ x : ℂ, IsAlgebraic ℚ x ∧ ¬IsSolvableByRad ℚ x := by
  obtain ⟨x, hx⟩ := (IsAlgClosed.splits (Phi ℂ 4 2)).exists_eval_eq_zero (by simp [degree_Phi])
  rw [← map_Phi 4 2 (algebraMap ℚ ℂ), eval_map] at hx
  refine ⟨x, ⟨Phi ℚ 4 2, (monic_Phi 4 2).ne_zero, hx⟩, ?_⟩
  exact not_solvable_by_rad 4 2 2 x hx (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- The general quintic is not solvable by radicals: it is **not** the case that every
complex root of every rational quintic can be expressed by radicals over `ℚ`. -/
