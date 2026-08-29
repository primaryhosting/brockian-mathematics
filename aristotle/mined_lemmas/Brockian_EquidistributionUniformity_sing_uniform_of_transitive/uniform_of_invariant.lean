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
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace EquidistributionUniformity

/-- **Invariance forces uniformity.** If a group `G` acts transitively on a finite type `α`
and `w : α → ℝ` is a `G`-invariant weight with total mass `1`, then `w` takes the constant
value `1 / |α|`.  (No positivity assumption on `w` is needed.) -/

theorem uniform_of_invariant {G α : Type*} [Group G] [MulAction G α] [Fintype α]
    (htrans : ∀ a b : α, ∃ g : G, g • a = b)
    (w : α → ℝ) (hinv : ∀ (g : G) (a : α), w (g • a) = w a)
    (hsum : ∑ a, w a = 1) (a : α) : w a = (Fintype.card α : ℝ)⁻¹ := by
  have hconst : ∀ b : α, w b = w a := by
    intro b
    obtain ⟨g, hg⟩ := htrans a b
    rw [← hg, hinv]
  have hmul : (Fintype.card α : ℝ) * w a = 1 := by
    rw [← hsum, Finset.sum_congr rfl (fun b _ => hconst b)]
    simp [Finset.sum_const, Finset.card_univ, mul_comm]
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    have := Fintype.card_pos_iff.mpr ⟨a⟩
    positivity
  field_simp at hmul ⊢
  linarith [hmul]

/-- **Uniqueness of the equidistributed (uniform) invariant law under a transitive action.**

For a transitive action of a group `G` on a finite nonempty type `α`, the set of `G`-invariant
real weights of total mass `1` is the *singleton* consisting of the uniform law
`fun _ => 1 / |α|`.

This is the unconditional form: the hypothesis that the invariant law be uniform is now
discharged, being derived from transitivity alone. -/
