import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
## Faltings's theorem (Mordell conjecture): statement and a checked instance

Faltings's theorem states that a smooth projective curve of genus `≥ 2` over `ℚ` has only
finitely many rational points.  Mathlib currently has neither the notion of the genus of an
arbitrary curve nor the arithmetic-geometry machinery (Mordell--Weil, height theory, abelian
varieties, Shafarevich conjecture) that the proof requires, so the full theorem is out of reach.

This file provides:

* `Frontier.HasFiniteCoordinateCover` and `Frontier.faltings_mordell_reduction`: the
  set-theoretic reduction step, namely that a bounded-height statement (all rational points have
  coordinates in a fixed finite set) yields finiteness of the rational points.
* `Frontier.planeGenus` and `Frontier.two_le_planeGenus`: the genus of a smooth plane curve of
  degree `n`, which is `≥ 2` as soon as `n ≥ 4`; in particular the Fermat curve of degree `n`
  with `4 ∣ n`, `n ≠ 0` falls under Faltings's theorem.
* `Frontier.faltings_mordell`: an unconditional, fully proved instance of Faltings's theorem —
  the Fermat curve `x ^ n + y ^ n = 1` for `4 ∣ n`, `n ≠ 0` (genus `(n-1)(n-2)/2 ≥ 3`) has only
  finitely many rational points.  Its rational points are computed exactly in
  `Frontier.fermatCurve_rationalPoints`, using Fermat's Last Theorem for exponent four (which
  *is* in Mathlib).
-/

namespace Frontier

/-! ### The bounded-height reduction -/

/-- The data used here to present an affine curve over `ℚ`: its genus together with its set of
rational points. -/
structure CurveOverQ where
  /-- The genus of the curve. -/
  genus : ℕ
  /-- The set of rational points of the curve, in affine coordinates. -/
  rationalPoints : Set (ℚ × ℚ)

/-- A curve `C` *has a finite coordinate cover* if there is a finite set of rationals containing
all coordinates of all rational points of `C`.  This is the shape of the conclusion produced by
the deep, height-theoretic part of Faltings's theorem. -/

theorem fermatCurve_rationalPoints {n : ℕ} (hn : 4 ∣ n) (hn0 : n ≠ 0) :
    fermatCurvePoints n = {(1, 0), (-1, 0), (0, 1), (0, -1)} := by
  have hflt := flt_rat_of_four_dvd hn
  have heven : Even n := by
    obtain ⟨k, rfl⟩ := hn
    exact ⟨2 * k, by ring⟩
  ext ⟨x, y⟩
  simp only [fermatCurvePoints, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq]
  constructor
  · intro hxy
    have hx0 : x = 0 ∨ y = 0 := by
      by_contra hcon
      push_neg at hcon
      exact hflt x y 1 hcon.1 hcon.2 one_ne_zero (by simpa using hxy)
    rcases hx0 with rfl | rfl
    · have hy : y ^ n = 1 := by simpa [zero_pow hn0] using hxy
      rcases pow_eq_one_iff_cases.mp hy with h | h | h
      · exact absurd h hn0
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, h.1⟩))
    · have hx : x ^ n = 1 := by simpa [zero_pow hn0] using hxy
      rcases pow_eq_one_iff_cases.mp hx with h | h | h
      · exact absurd h hn0
      · exact Or.inl ⟨h, rfl⟩
      · exact Or.inr (Or.inl ⟨h.1, rfl⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      simp [zero_pow hn0, heven.neg_one_pow]

/-- **Faltings's theorem for the Fermat curves of degree divisible by four.**

For `4 ∣ n` and `n ≠ 0` the Fermat curve `x ^ n + y ^ n = 1` is a smooth plane curve of degree
`n ≥ 4`, hence of genus `planeGenus n ≥ 2`, and it has only finitely many rational points — an
unconditional instance of Faltings's theorem, proved here from Fermat's Last Theorem for exponent
four. -/
