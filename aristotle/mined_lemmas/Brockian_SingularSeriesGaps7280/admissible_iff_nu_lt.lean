/-
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Header kept verbatim, but as a plain block comment: Lean 4 forbids module
-- doc comments before `import`.)

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

namespace Brockian

/-- A finite set `H` of natural numbers is *admissible* if, for every prime `p`, the
reductions of the elements of `H` modulo `p` omit at least one residue class.
This is exactly the classical condition guaranteeing that the singular series
`𝔖(H)` attached to the tuple `H` does not vanish. -/

theorem admissible_iff_nu_lt (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → nu H p < p := by
  constructor
  · intro hA p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨r, hr⟩ := hA p hp
    have hsub : H.image (fun h : ℕ => (h : ZMod p)) ⊆ Finset.univ.erase r := by
      intro x hx
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_erase.mpr ⟨hr h hh, Finset.mem_univ _⟩
    have h1 : nu H p ≤ (Finset.univ.erase r).card := Finset.card_le_card hsub
    have h2 : (Finset.univ.erase r : Finset (ZMod p)).card = p - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
    have h3 := hp.pos
    omega
  · intro hnu p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    by_contra hc
    push_neg at hc
    have huniv : H.image (fun h : ℕ => (h : ZMod p)) = Finset.univ := by
      refine Finset.eq_univ_iff_forall.mpr ?_
      intro r
      obtain ⟨h, hh, hcast⟩ := hc r
      exact Finset.mem_image.mpr ⟨h, hh, hcast⟩
    have := hnu p hp
    rw [nu, huniv, Finset.card_univ, ZMod.card] at this
    exact lt_irrefl _ this

/-- **Singular Series Gaps 7280.**

A new family of admissible gap ranges: if every member of a finite set `H` of
natural numbers is a prime exceeding the cardinality of `H`, then `H` is admissible,
i.e. for every prime `p` the reductions of `H` mod `p` miss some residue class.

Consequently the singular series of such a tuple has all local factors nonzero. -/
