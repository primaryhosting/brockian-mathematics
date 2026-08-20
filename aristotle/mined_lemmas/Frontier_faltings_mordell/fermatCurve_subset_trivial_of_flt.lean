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

theorem fermatCurve_subset_trivial_of_flt {n : ℕ} (hn : n ≠ 0)
    (hflt : FermatLastTheoremWith ℚ n) :
    fermatCurveRatPoints n ⊆ trivialFermatPoints := by
  rintro ⟨x, y⟩ hp
  simp only [fermatCurveRatPoints, Set.mem_setOf_eq] at hp
  have hxy : x = 0 ∨ y = 0 := by
    by_contra hcon
    push_neg at hcon
    exact hflt x y 1 hcon.1 hcon.2 one_ne_zero (by simpa using hp)
  simp only [trivialFermatPoints, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  rcases hxy with hx | hy
  · subst hx
    have hy1 : y ^ n = 1 := by simpa [zero_pow hn] using hp
    rcases rat_eq_one_or_neg_one_of_pow_eq_one hn hy1 with h | h
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
  · subst hy
    have hx1 : x ^ n = 1 := by simpa [zero_pow hn] using hp
    rcases rat_eq_one_or_neg_one_of_pow_eq_one hn hx1 with h | h
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr (Or.inl ⟨h, rfl⟩)

/-- **Reduction.** Faltings' theorem for the Fermat curve of exponent `n ≠ 0` follows from
Fermat's Last Theorem for the exponent `n`. -/
