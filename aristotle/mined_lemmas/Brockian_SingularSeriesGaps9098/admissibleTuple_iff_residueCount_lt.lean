/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: the requested header is reproduced verbatim above, but as an ordinary block comment
`/- ... -/` rather than a module docstring `/-! ... -/`, since Lean 4 does not allow a module
docstring to precede the `import` commands.)
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

set_option grind.warning false

namespace Brockian

/-- A finite set of nonnegative integers `H` (a *gap range*, or prime tuple pattern) is
*admissible* when, for every prime `p`, the reductions of the elements of `H` modulo `p`
do not cover all of `ZMod p`.  Equivalently the local factor
`1 - ν_H(p)/p` of the Hardy–Littlewood singular series is strictly positive at every prime,
which is exactly the condition for the singular series `𝔖(H)` to be nonzero. -/

theorem admissibleTuple_iff_residueCount_lt (H : Finset ℕ) :
    AdmissibleTuple H ↔ ∀ p : ℕ, p.Prime → residueCount H p < p := by
  constructor
  · intro hH p hp
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨r, hr⟩ := hH p hp
    have hsub : Finset.image (fun h : ℕ => (h : ZMod p)) H ⊂ Finset.univ := by
      refine Finset.ssubset_univ_iff.mpr ?_
      intro hcon
      have : r ∈ Finset.image (fun h : ℕ => (h : ZMod p)) H := by rw [hcon]; exact Finset.mem_univ r
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp this
      exact hr h hh rfl
    have := Finset.card_lt_card hsub
    simpa [residueCount, ZMod.card] using this
  · intro hH p hp
    haveI : Fact p.Prime := ⟨hp⟩
    have hlt : (Finset.image (fun h : ℕ => (h : ZMod p)) H).card < Fintype.card (ZMod p) := by
      simpa [residueCount, ZMod.card] using hH p hp
    have : ∃ r : ZMod p, r ∉ Finset.image (fun h : ℕ => (h : ZMod p)) H := by
      by_contra hcon
      push_neg at hcon
      have : Finset.univ ⊆ Finset.image (fun h : ℕ => (h : ZMod p)) H := fun r _ => hcon r
      exact absurd (Finset.card_le_card this) (by simpa using hlt)
    obtain ⟨r, hr⟩ := this
    exact ⟨r, fun h hh hcon => hr (Finset.mem_image.mpr ⟨h, hh, hcon⟩)⟩

/-- **Singular Series Gaps 9098.**
Any finite set `H` of primes, each of which exceeds the cardinality of `H`, is an admissible
tuple: no prime `p` has all its residue classes occupied by `H`.

Proof idea: for small primes `p ≤ #H` no element of `H` is divisible by `p` (the elements are
primes larger than `p`), so the class `0` is missed; for large primes `p > #H` there are simply
too few elements to cover the `p` classes. -/
