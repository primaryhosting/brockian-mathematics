import Mathlib

/-!
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
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

open MulAction DihedralGroup

/-! ## The action of the dihedral group on the vertices of the regular `n`-gon -/

/-- The symmetry action of `DihedralGroup n` on the vertex set `ZMod n` of the regular `n`-gon:
the rotation `r i` sends a vertex `x` to `x - i`, and the reflection `sr i` sends `x` to `i - x`. -/

theorem ngonChar_sr_of_odd {n : ℕ} (hn : Odd n) (i : ZMod n) :
    ngonChar n (DihedralGroup.sr i) = 1 := by
  have hunit : IsUnit (2 : ZMod n) := by
    have h2 : ((2 : ℕ) : ZMod n) = (2 : ZMod n) := by push_cast; ring
    rw [← h2, ZMod.isUnit_iff_coprime]
    simpa [Nat.coprime_two_left] using hn
  obtain ⟨u, hu⟩ := hunit
  have h : (MulAction.fixedBy (ZMod n) (DihedralGroup.sr i)) = ({(↑u⁻¹ * i)} : Set (ZMod n)) := by
    ext x
    simp only [MulAction.mem_fixedBy, sr_smul, Set.mem_singleton_iff]
    constructor
    · intro hx
      have h2x : (2 : ZMod n) * x = i := by linear_combination -hx
      rw [← hu] at h2x
      rw [← h2x]
      rw [← mul_assoc]
      simp [← Units.val_mul]
    · intro hx
      subst hx
      have : (2 : ZMod n) * ((↑u⁻¹ : ZMod n) * i) = i := by
        rw [← hu, ← mul_assoc]
        simp [← Units.val_mul]
      linear_combination -this
  rw [ngonChar, h]
  simp

/-! ## Burnside's lemma: the trivial character occurs with multiplicity one -/

