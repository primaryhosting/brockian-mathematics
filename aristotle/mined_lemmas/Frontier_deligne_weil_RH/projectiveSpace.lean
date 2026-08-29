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

def projectiveSpace (q n : ℕ) (hq : 2 ≤ q) : WeilVariety where
  q := q
  hq := hq
  dim := n
  frobRoots := fun i => if i % 2 = 0 ∧ i ≤ 2 * n then {((q : ℂ)) ^ (i / 2)} else 0
  count := fun m => ∑ k ∈ Finset.range (n + 1), q ^ (k * m)
  vanishing := by
    intro i hi
    have : ¬ (i % 2 = 0 ∧ i ≤ 2 * n) := by omega
    simp [this]
  trace := by
    intro m _
    have hcast : ((∑ k ∈ Finset.range (n + 1), q ^ (k * m) : ℕ) : ℂ)
        = ∑ k ∈ Finset.range (n + 1), ((q : ℂ) ^ (k * m)) := by push_cast; ring
    rw [hcast, ← sum_projective_range q n m]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i ≤ 2 * n := by
      simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi
    by_cases h : i % 2 = 0 <;> simp [h, hi']

/-- The `count` function of `projectiveSpace q n` is the actual number of rational points of
`n`-dimensional projective space over a field with `q ^ m` elements. -/
