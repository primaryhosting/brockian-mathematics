/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- The *local count* of a constellation (admissible tuple) with shift set `H`
at the modulus `p`: the number of residue classes `a` mod `p` such that none of
the numbers `a + h`, `h ∈ H`, is divisible by `p`. -/
def localCount (p : ℕ) [NeZero p] (H : Finset ℤ) : ℕ :=
  (Finset.univ.filter (fun a : ZMod p => ∀ h ∈ H, a + (h : ZMod p) ≠ 0)).card

/-- The residues *excluded* by the shift set `H` are exactly the negatives of the
residues of the elements of `H`. -/
lemma forbidden_eq_image (p : ℕ) [NeZero p] (H : Finset ℤ) :
    (Finset.univ.filter (fun a : ZMod p => ¬ ∀ h ∈ H, a + (h : ZMod p) ≠ 0))
      = H.image (fun h : ℤ => -((h : ℤ) : ZMod p)) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, not_forall,
    Classical.not_not]
  constructor
  · rintro ⟨h, hH, hne⟩
    exact ⟨h, hH, by linear_combination -hne⟩
  · rintro ⟨h, hH, hEq⟩
    exact ⟨h, hH, by linear_combination -hEq⟩

/-- The local count equals `p` minus the number of distinct residues of `-H`. -/
lemma localCount_eq_sub (p : ℕ) [NeZero p] (H : Finset ℤ) :
    localCount p H = p - (H.image (fun h : ℤ => -((h : ℤ) : ZMod p))).card := by
  have hcard : (Finset.univ.filter (fun a : ZMod p => ∀ h ∈ H, a + (h : ZMod p) ≠ 0)).card
      + (Finset.univ.filter (fun a : ZMod p => ¬ ∀ h ∈ H, a + (h : ZMod p) ≠ 0)).card
      = (Finset.univ : Finset (ZMod p)).card :=
    Finset.card_filter_add_card_filter_not _
  rw [forbidden_eq_image] at hcard
  have hp : (Finset.univ : Finset (ZMod p)).card = p := by
    simp [ZMod.card p]
  rw [hp] at hcard
  simp only [localCount]
  omega

/-- Main statement: the local constellation count for `k = 3` tuples with shifts
`h₁, h₂, h₃`. -/
theorem ConstellationLocalCountK3 (p : ℕ) [NeZero p] (h₁ h₂ h₃ : ℤ) :
    localCount p {h₁, h₂, h₃}
        = p - ({-(h₁ : ZMod p), -(h₂ : ZMod p), -(h₃ : ZMod p)} : Finset (ZMod p)).card
      ∧ p - 3 ≤ localCount p {h₁, h₂, h₃}
      ∧ localCount p {h₁, h₂, h₃} ≤ p - 1
      ∧ ((h₁ : ZMod p) ≠ (h₂ : ZMod p) → (h₁ : ZMod p) ≠ (h₃ : ZMod p) →
          (h₂ : ZMod p) ≠ (h₃ : ZMod p) → localCount p {h₁, h₂, h₃} = p - 3)
      ∧ (3 < p → 0 < localCount p {h₁, h₂, h₃}) := by
  set S : Finset (ZMod p) :=
    ({-(h₁ : ZMod p), -(h₂ : ZMod p), -(h₃ : ZMod p)} : Finset (ZMod p)) with hS
  have himg : ({h₁, h₂, h₃} : Finset ℤ).image (fun h : ℤ => -((h : ℤ) : ZMod p)) = S := by
    simp [hS, Finset.image_insert]
  have hmain : localCount p {h₁, h₂, h₃} = p - S.card := by
    rw [localCount_eq_sub, himg]
  have hle3 : S.card ≤ 3 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    have : ({-(h₂ : ZMod p), -(h₃ : ZMod p)} : Finset (ZMod p)).card ≤ 2 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      simp
    omega
  have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨-(h₁ : ZMod p), by simp [hS]⟩
  refine ⟨hmain, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro d12 d13 d23
    have hcard : S.card = 3 := by
      have n12 : -(h₁ : ZMod p) ≠ -(h₂ : ZMod p) := fun h => d12 (neg_injective h)
      have n13 : -(h₁ : ZMod p) ≠ -(h₃ : ZMod p) := fun h => d13 (neg_injective h)
      have n23 : -(h₂ : ZMod p) ≠ -(h₃ : ZMod p) := fun h => d23 (neg_injective h)
      rw [hS]
      rw [Finset.card_insert_of_notMem (by simp [n12, n13]),
        Finset.card_insert_of_notMem (by simp [n23]), Finset.card_singleton]
    omega
  · intro hp
    omega

end Brockian

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

