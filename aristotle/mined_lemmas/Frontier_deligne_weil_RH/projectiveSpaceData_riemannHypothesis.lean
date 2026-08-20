/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- Cohomological data attached to a smooth projective variety of dimension `dim` over the
finite field `𝔽_q`: for each degree `i` the (multi)set `frobEigenvalues i` of eigenvalues of
the geometric Frobenius acting on the `i`-th étale cohomology group, which vanishes outside
degrees `0, …, 2 dim`.

Étale cohomology is not available in Mathlib, so the cohomological input of the Weil
conjectures is packaged here as data; all statements below are statements about this data. -/
structure WeilData where
  /-- The size of the base field. -/
  q : ℕ
  /-- The base field is a genuine finite field, so it has at least two elements. -/
  one_lt_q : 1 < q
  /-- The dimension of the variety. -/
  dim : ℕ
  /-- The eigenvalues of the geometric Frobenius on the `i`-th cohomology group. -/
  frobEigenvalues : ℕ → Multiset ℂ
  /-- Cohomology vanishes above degree `2 dim`. -/
  vanishing : ∀ i, 2 * dim < i → frobEigenvalues i = 0

namespace WeilData

variable (W : WeilData)

/-- The number of `𝔽_{q^m}`-rational points of the variety, as computed by the
Grothendieck–Lefschetz trace formula
`N_m = ∑_i (-1)^i ∑_j α_{i,j}^m`. -/

theorem projectiveSpaceData_riemannHypothesis (q n : ℕ) (hq : 1 < q) :
    (projectiveSpaceData q n hq).RiemannHypothesis := by
  intro i α hα
  simp only [projectiveSpaceData] at hα ⊢
  by_cases h : Even i ∧ i ≤ 2 * n
  · rw [if_pos h] at hα
    have hαv : α = (q : ℂ) ^ (i / 2) := by simpa using hα
    have hhalf : (i : ℝ) / 2 = ((i / 2 : ℕ) : ℝ) := by
      obtain ⟨k, hk⟩ := h.1
      subst hk
      have h2 : (k + k) / 2 = k := by omega
      rw [h2]
      push_cast
      ring
    rw [hαv, hhalf, Real.rpow_natCast]
    simp
  · rw [if_neg h] at hα
    simp at hα

/-- **Reduction**: the Riemann hypothesis implies the Weil estimate for point counts.  If the
top cohomology is one dimensional with Frobenius eigenvalue `q^dim` (as for a geometrically
connected smooth projective variety), then the number of `𝔽_{q^m}`-points differs from
`q^{m·dim}` by at most `(∑_{i < 2 dim} b_i) · q^{m (dim - 1/2)}`. -/
