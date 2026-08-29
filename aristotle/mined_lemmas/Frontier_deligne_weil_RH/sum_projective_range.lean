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

lemma sum_projective_range (q n m : ℕ) :
    ∑ i ∈ Finset.range (2 * n + 1),
        ((-1 : ℂ)) ^ i * (if i % 2 = 0 then (((q : ℂ) ^ (i / 2)) ^ m) else 0)
      = ∑ k ∈ Finset.range (n + 1), ((q : ℂ) ^ (k * m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by ring
      rw [h, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have h1 : (2 * n + 1) % 2 = 1 := by omega
      have h2 : (2 * n + 1 + 1) % 2 = 0 := by omega
      have h3 : (2 * n + 1 + 1) / 2 = n + 1 := by omega
      rw [h1, h2, h3, Finset.sum_range_succ]
      have hsign : ((-1 : ℂ)) ^ (2 * n + 1 + 1) = 1 := by
        rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul]
        simp
      rw [hsign]
      simp [pow_mul, Finset.sum_range_succ]

end Auxiliary

/-- The Weil data of projective `n`-space over `𝔽_q`: the cohomology is one-dimensional in
each even degree `2k ≤ 2n`, with Frobenius eigenvalue `q ^ k`, and the number of
`𝔽_{q^m}`-points is `1 + q^m + ⋯ + q^{nm}`. -/
