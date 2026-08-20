import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
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

namespace Brockian

/-- A finite set of shifts `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuple conjecture) if for every prime `p` the residues of `H` modulo `p`
do not cover all of `ℤ/pℤ`.  Equivalently, the local factor of the singular series
attached to `H` is nonzero at every prime. -/

theorem admissible_pair_iff_even {g : ℕ} :
    Admissible ({0, g} : Finset ℕ) ↔ Even g := by
  constructor
  · intro h
    have h2 := h 2 Nat.prime_two
    by_contra hodd
    have hg2 : g % 2 = 1 := Nat.not_even_iff.mp hodd
    have hsub : ({0, 1} : Finset ℕ) ⊆ ({0, g} : Finset ℕ).image (· % 2) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp
      · simp [hg2]
    have hle := Finset.card_le_card hsub
    have hc : ({0, 1} : Finset ℕ).card = 2 := by decide
    omega
  · intro heven p hp
    rcases eq_or_ne p 2 with rfl | hp2
    · have hg2 : g % 2 = 0 := Nat.even_iff.mp heven
      have himg : ({0, g} : Finset ℕ).image (· % 2) = {0} := by
        ext x
        simp [hg2]
      rw [himg]
      simp
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hcard : ({0, g} : Finset ℕ).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      exact lt_of_le_of_lt (Finset.card_image_le.trans hcard) (by omega)

/-- **Singular Series Gaps 1240–1250.**
For every gap `g` in the range `1240 ≤ g ≤ 1250`, the two-element pattern `{0, g}`
is admissible (equivalently, the singular series `𝔖({0,g})` is nonzero) precisely when
`g` is even.  In particular the admissible gaps in this range are exactly
`1240, 1242, 1244, 1246, 1248, 1250`. -/
