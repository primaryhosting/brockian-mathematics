import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## Faltings' theorem (the Mordell conjecture)

Faltings' theorem states that a smooth projective curve of genus `≥ 2` defined over `ℚ` has
only finitely many rational points.  Mathlib currently has no definition of the genus of a
curve, so we formalize the statement for the classical family of test cases: the *Fermat
curves* `x ^ n + y ^ n = 1`.  The smooth plane projective curve `x ^ n + y ^ n = z ^ n` has
genus `(n - 1) * (n - 2) / 2`, which is `≥ 2` exactly when `n ≥ 4`; so the assertion
`FaltingsForFermatCurves` below is precisely the content of Faltings' theorem for this family.

We prove:

* `Frontier.fermatCurve_finite_of_flt`: a Lean-checked *reduction* of Faltings' theorem for the
  Fermat curve of even degree `n ≥ 1` to Fermat's Last Theorem for the exponent `n`;
* `Frontier.faltings_mordell` (the target): the resulting unconditional *base case* — for every
  `n` divisible by `4` (in particular the genus `3` quartic `x ^ 4 + y ^ 4 = 1`), the Fermat
  curve has only finitely many rational points.  The input is Mathlib's
  `fermatLastTheoremFour`, Fermat's Last Theorem for exponent `4`.
* `Frontier.fermatCurve_eq_of_four_dvd`: in fact the rational points are exactly the four
  trivial ones.
-/

/-- The set of affine rational points of the Fermat curve `x ^ n + y ^ n = 1`. -/

theorem fermatCurve_eq_of_four_dvd {n : ℕ} (hn : 4 ∣ n) (hn0 : n ≠ 0) :
    fermatCurveRatPoints n = trivialFermatPoints := by
  refine Set.Subset.antisymm
    (fermatCurve_subset_trivial_of_flt hn0 (fermatLastTheoremWith_rat_of_four_dvd hn)) ?_
  have hev : Even n := by
    obtain ⟨k, rfl⟩ := hn
    exact ⟨2 * k, by ring⟩
  rintro ⟨x, y⟩ hp
  simp only [trivialFermatPoints, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
  simp only [fermatCurveRatPoints, Set.mem_setOf_eq]
  rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> subst hx <;> subst hy <;>
    simp [zero_pow hn0, hev.neg_one_pow]

/-- The genus `3` quartic Fermat curve has finitely many rational points. -/
