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
def ngonSMul {n : ℕ} : DihedralGroup n → ZMod n → ZMod n
  | DihedralGroup.r i, x => x - i
  | DihedralGroup.sr i, x => i - x

/-- The vertex set `ZMod n` of the regular `n`-gon is a `DihedralGroup n`-set. -/
instance ngonMulAction (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  smul := ngonSMul
  one_smul x := by
    show ngonSMul (DihedralGroup.r 0) x = x
    simp [ngonSMul]
  mul_smul := by
    rintro (i | i) (j | j) x <;>
      simp [HSMul.hSMul, SMul.smul, ngonSMul, r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr] <;> ring

@[simp] theorem r_smul {n : ℕ} (i x : ZMod n) : (DihedralGroup.r i) • x = x - i := rfl

@[simp] theorem sr_smul {n : ℕ} (i x : ZMod n) : (DihedralGroup.sr i) • x = i - x := rfl

/-- The dihedral group acts transitively on the vertices of the regular `n`-gon. -/
instance ngonPretransitive (n : ℕ) : MulAction.IsPretransitive (DihedralGroup n) (ZMod n) :=
  ⟨fun x y => ⟨DihedralGroup.r (x - y), by simp⟩⟩

/-! ## The permutation character -/

/-- The permutation character of the vertex representation of `DihedralGroup n`: the value at `g`
is the number of vertices fixed by `g`. -/
noncomputable def ngonChar (n : ℕ) (g : DihedralGroup n) : ℕ :=
  Nat.card (MulAction.fixedBy (ZMod n) g)

theorem ngonChar_r_zero (n : ℕ) : ngonChar n (DihedralGroup.r (0 : ZMod n)) = Nat.card (ZMod n) := by
  have h : (MulAction.fixedBy (ZMod n) (DihedralGroup.r (0 : ZMod n))) = (Set.univ : Set (ZMod n)) := by
    ext x
    simp
  rw [ngonChar, h, Nat.card_congr (Equiv.Set.univ (ZMod n))]

theorem ngonChar_r_of_ne_zero {n : ℕ} {i : ZMod n} (hi : i ≠ 0) :
    ngonChar n (DihedralGroup.r i) = 0 := by
  have h : (MulAction.fixedBy (ZMod n) (DihedralGroup.r i)) = (∅ : Set (ZMod n)) := by
    ext x
    simp [MulAction.mem_fixedBy, sub_eq_self, hi]
  rw [ngonChar, h]
  simp

/-- For odd `n`, every reflection of the regular `n`-gon fixes exactly one vertex. -/
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

theorem ngon_orbits_card (n : ℕ) [NeZero n]
    [Fintype (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n)))] :
    Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n))) = 1 := by
  have hs : Subsingleton (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n))) := by
    constructor
    rintro ⟨a⟩ ⟨b⟩
    refine Quotient.sound ?_
    show (MulAction.orbitRel (DihedralGroup n) (ZMod n)) a b
    rw [MulAction.orbitRel_apply]
    exact (MulAction.mem_orbit_iff).mpr (MulAction.exists_smul_eq (DihedralGroup n) b a)
  exact Fintype.card_eq_one_iff_nonempty_unique.mpr
    ⟨@uniqueOfSubsingleton _ hs (Quotient.mk _ 0)⟩

/-- Burnside's lemma for the vertex action: the total number of fixed points equals the order of
the dihedral group, since the action is transitive. -/
theorem sum_ngonChar (n : ℕ) [NeZero n] :
    ∑ g : DihedralGroup n, ngonChar n g = Fintype.card (DihedralGroup n) := by
  haveI : Fintype (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n))) := Quotient.fintype _
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (DihedralGroup n) (ZMod n)
  rw [ngon_orbits_card n, one_mul] at hburnside
  rw [← hburnside]
  exact Finset.sum_congr rfl fun g _ => Nat.card_eq_fintype_card

/-- **Pentagon Pentagon Character Multiplicity Ext.**

Generalization of the pentagon (`D₅`) computation to arbitrary regular `n`-gons: for every `n ≥ 1`,
the multiplicity of the trivial character in the permutation character `ngonChar n` of the vertex
representation of the dihedral group `DihedralGroup n` — that is, the character inner product
`⟪χ, 1⟫ = |G|⁻¹ ∑_{g ∈ G} χ(g)` — is exactly `1`, because the action on the vertices of the
`n`-gon is transitive (Burnside's lemma,
`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`). -/
theorem PentagonPentagonCharacterMultiplicityExt (n : ℕ) [NeZero n] :
    ((Fintype.card (DihedralGroup n) : ℚ))⁻¹ * ∑ g : DihedralGroup n, (ngonChar n g : ℚ) = 1 := by
  have hcard : (Fintype.card (DihedralGroup n) : ℚ) ≠ 0 := by
    have : 0 < Fintype.card (DihedralGroup n) := Fintype.card_pos
    positivity
  have hsum : ∑ g : DihedralGroup n, (ngonChar n g : ℚ) = (Fintype.card (DihedralGroup n) : ℚ) := by
    rw [← Nat.cast_sum, sum_ngonChar n]
  rw [hsum, inv_mul_cancel₀ hcard]

/-! ## The pentagon case `n = 5` -/

/-- The pentagon instance of the general theorem: the trivial character occurs exactly once in the
vertex permutation character of `D₅`. -/
theorem pentagon_character_multiplicity :
    ((Fintype.card (DihedralGroup 5) : ℚ))⁻¹ * ∑ g : DihedralGroup 5, (ngonChar 5 g : ℚ) = 1 :=
  PentagonPentagonCharacterMultiplicityExt 5

/-- The permutation character of the pentagon: the identity rotation fixes all `5` vertices. -/
theorem pentagon_char_r_zero : ngonChar 5 (DihedralGroup.r (0 : ZMod 5)) = 5 := by
  rw [ngonChar_r_zero]
  simp

/-- The permutation character of the pentagon: a nontrivial rotation fixes no vertex. -/
theorem pentagon_char_r_ne_zero {i : ZMod 5} (hi : i ≠ 0) : ngonChar 5 (DihedralGroup.r i) = 0 :=
  ngonChar_r_of_ne_zero hi

/-- The permutation character of the pentagon: every reflection fixes exactly one vertex. -/
theorem pentagon_char_sr (i : ZMod 5) : ngonChar 5 (DihedralGroup.sr i) = 1 :=
  ngonChar_sr_of_odd (by decide) i

end Brockian

#print axioms Brockian.PentagonPentagonCharacterMultiplicityExt
#print axioms Brockian.pentagon_char_sr
#print axioms Brockian.pentagon_char_r_zero

