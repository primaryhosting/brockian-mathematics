/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace Frontier

/-- Cohomological data attached to a variety over a finite field `𝔽_q`:
the inverse roots (Frobenius eigenvalues) on each cohomology group, together with the
point counts over the extensions `𝔽_{q^m}`, linked by the Grothendieck–Lefschetz trace
formula. -/
structure WeilVariety where
  /-- Cardinality of the base field. -/
  q : ℕ
  /-- The base field has at least two elements. -/
  hq : 2 ≤ q
  /-- Dimension of the variety. -/
  dim : ℕ
  /-- Multiset of inverse roots of Frobenius acting on the `i`-th cohomology group. -/
  frobRoots : ℕ → Multiset ℂ
  /-- `count m` is the number of `𝔽_{q^m}`-rational points. -/
  count : ℕ → ℕ
  /-- Cohomology vanishes above degree `2 * dim`. -/
  vanishing : ∀ i, 2 * dim < i → frobRoots i = 0
  /-- Grothendieck–Lefschetz trace formula. -/
  trace : ∀ m, 1 ≤ m →
    (count m : ℂ) =
      ∑ i ∈ Finset.range (2 * dim + 1),
        (-1) ^ i * (((frobRoots i).map (fun a => a ^ m)).sum)

/-- The Riemann hypothesis for a variety over a finite field: every inverse root of
Frobenius on the `i`-th cohomology group has archimedean absolute value `q ^ (i / 2)`. -/

theorem riemannHypothesis_projectiveSpace (q n : ℕ) (hq : 2 ≤ q) :
    RiemannHypothesis (projectiveSpace q n hq) := by
  intro i hi a ha
  simp only [projectiveSpace] at hi ha ⊢
  by_cases h : i % 2 = 0 ∧ i ≤ 2 * n
  · rw [if_pos h] at ha
    have ha' : a = ((q : ℂ)) ^ (i / 2) := by
      simpa using ha
    subst ha'
    have hq0 : (0:ℝ) ≤ (q : ℝ) := by positivity
    rw [norm_pow, Complex.norm_natCast]
    have hi2 : ((i : ℝ) / 2) = ((i / 2 : ℕ) : ℝ) := by
      obtain ⟨k, hk⟩ : ∃ k, i = 2 * k := ⟨i / 2, by omega⟩
      subst hk
      have : (2 * k) / 2 = k := by omega
      rw [this]
      push_cast
      ring
    rw [hi2, Real.rpow_natCast]
  · rw [if_neg h] at ha
    simp at ha

/-- **Consequence of the Riemann hypothesis**: the point counts of a `d`-dimensional variety
whose top cohomology is one-dimensional with Frobenius eigenvalue `q ^ d` satisfy the
square-root error estimate `|#X(𝔽_{q^m}) - q^{dm}| ≤ B · q^{(2d-1)m/2}`, where `B` is the sum
of the Betti numbers below the top degree. -/
