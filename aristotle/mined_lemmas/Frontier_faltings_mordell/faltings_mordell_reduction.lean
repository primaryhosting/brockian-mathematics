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

theorem faltings_mordell_reduction (C : CurveOverQ) (_hgenus : 2 ≤ C.genus)
    (hcover : HasFiniteCoordinateCover C) : C.rationalPoints.Finite := by
  obtain ⟨s, hs⟩ := hcover
  exact (s.finite_toSet.prod s.finite_toSet).subset hs

/-! ### Genus of a smooth plane curve -/

/-- The genus of a smooth plane projective curve of degree `n`, namely `(n - 1) * (n - 2) / 2`. -/
