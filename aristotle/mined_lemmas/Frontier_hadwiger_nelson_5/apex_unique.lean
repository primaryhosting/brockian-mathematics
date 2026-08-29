import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Basic notions for the Hadwiger–Nelson problem

We identify the Euclidean plane with `ℂ`.  A *proper* 4-colouring is a map
`c : ℂ → Fin 4` such that no two points at distance exactly `1` receive the
same colour.  We phrase the distance condition with `Complex.normSq` (the
squared modulus) so that all verifications stay polynomial.
-/

namespace CNP

open Complex

/-- A proper 4-colouring of the plane. -/

theorem apex_unique {p q r s : ℂ} (hpq : normSq (p - q) = 3)
    (hr1 : normSq (p - r) = 3) (hr2 : normSq (q - r) = 3)
    (hs1 : normSq (p - s) = 3) (hs2 : normSq (q - s) = 3) :
    r = s ∨ r = p + q - s := by
  simp only [normSq_apply, Complex.sub_re, Complex.sub_im] at hpq hr1 hr2 hs1 hs2
  have hA : (r.re - (p.re + q.re) / 2) * ((q.re - p.re) / 2) +
      (r.im - (p.im + q.im) / 2) * ((q.im - p.im) / 2) = 0 := by
    linear_combination hr1 / 4 - hr2 / 4
  have hB : (s.re - (p.re + q.re) / 2) * ((q.re - p.re) / 2) +
      (s.im - (p.im + q.im) / 2) * ((q.im - p.im) / 2) = 0 := by
    linear_combination hs1 / 4 - hs2 / 4
  have hN : (r.re - (p.re + q.re) / 2) ^ 2 + (r.im - (p.im + q.im) / 2) ^ 2 =
      (s.re - (p.re + q.re) / 2) ^ 2 + (s.im - (p.im + q.im) / 2) ^ 2 := by
    linear_combination hr1 / 2 + hr2 / 2 - hs1 / 2 - hs2 / 2
  have hD : ((q.re - p.re) / 2) ^ 2 + ((q.im - p.im) / 2) ^ 2 ≠ 0 := by
    have h : ((q.re - p.re) / 2) ^ 2 + ((q.im - p.im) / 2) ^ 2 = 3 / 4 := by
      linear_combination hpq / 4
    rw [h]; norm_num
  rcases perp_eq_or_neg hA hB hN hD with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · left
    exact Complex.ext (by linarith) (by linarith)
  · right
    refine Complex.ext ?_ ?_
    · simp only [Complex.add_re, Complex.sub_re]; linarith
    · simp only [Complex.add_im, Complex.sub_im]; linarith

end CNP

