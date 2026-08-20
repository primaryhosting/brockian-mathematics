/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The *local count* of a shift pattern `H` at modulus `n`: the number of residues
`a : ZMod n` for which none of the shifted values `a + h`, `h ∈ H`, vanishes modulo `n`.
For a prime `n = p` this is the quantity `ν_H(p)` occurring in the singular series of the
Hardy–Littlewood prime constellation conjecture. -/

theorem ConstellationLocalCountK3 (n : ℕ) [NeZero n] (h₁ h₂ h₃ : ℤ) :
    localCount {h₁, h₂, h₃} n
        = n - ({-(h₁ : ZMod n), -(h₂ : ZMod n), -(h₃ : ZMod n)} : Finset (ZMod n)).card ∧
      n - 3 ≤ localCount {h₁, h₂, h₃} n ∧ localCount {h₁, h₂, h₃} n ≤ n := by
  have himg : Finset.image (fun h : ℤ => -(h : ZMod n)) {h₁, h₂, h₃}
      = ({-(h₁ : ZMod n), -(h₂ : ZMod n), -(h₃ : ZMod n)} : Finset (ZMod n)) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, (rfl | rfl | rfl), rfl⟩ <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨h₁, by simp⟩, ⟨h₂, by simp⟩, ⟨h₃, by simp⟩]
  have hcount : localCount {h₁, h₂, h₃} n
      = n - ({-(h₁ : ZMod n), -(h₂ : ZMod n), -(h₃ : ZMod n)} : Finset (ZMod n)).card := by
    rw [localCount_eq, himg]
  have hcard : ({-(h₁ : ZMod n), -(h₂ : ZMod n), -(h₃ : ZMod n)} : Finset (ZMod n)).card ≤ 3 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h2 : ({-(h₂ : ZMod n), -(h₃ : ZMod n)} : Finset (ZMod n)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    omega
  exact ⟨hcount, by omega, by omega⟩

/-- The prime case: for `p` prime and three shifts that are pairwise distinct modulo `p`,
the local factor of the `3`-tuple constellation equals `p - 3`. -/
