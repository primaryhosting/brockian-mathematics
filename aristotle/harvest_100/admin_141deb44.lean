/-
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 does not permit a module docstring `/-! ... -/` before the `import` block, so the
-- required header appears verbatim above as a plain comment and again below as the module
-- docstring.)

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

set_option grind.warning false

namespace Brockian

/-!
## The `n`-gon vertex action of the dihedral group

We realise `DihedralGroup n` as the symmetry group of the regular `n`-gon by letting it act on
the vertex set `ZMod n`.  With Mathlib's multiplication convention

```
r i * r j = r (i + j),  r i * sr j = sr (j - i),  sr i * r j = sr (i + j),  sr i * sr j = r (j - i)
```

the corresponding left action is

```
r i • x = x - i,        sr i • x = i - x.
```

For `n = 5` this is the usual action of the symmetry group of the regular pentagon on its five
vertices; everything below is proved for arbitrary `n`, which is the promised extension.
-/

/-- The action of an element of `DihedralGroup n` on a vertex of the regular `n`-gon. -/
def vertexSMul {n : ℕ} : DihedralGroup n → ZMod n → ZMod n
  | .r i, x => x - i
  | .sr i, x => i - x

instance vertexSMulInstance (n : ℕ) : SMul (DihedralGroup n) (ZMod n) where
  smul := vertexSMul

@[simp]
theorem r_smul {n : ℕ} (i x : ZMod n) : (DihedralGroup.r i) • x = x - i := rfl

@[simp]
theorem sr_smul {n : ℕ} (i x : ZMod n) : (DihedralGroup.sr i) • x = i - x := rfl

/-- The regular `n`-gon vertex action of `DihedralGroup n` on the vertex set `ZMod n`. -/
instance vertexAction (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  one_smul x := sub_zero x
  mul_smul g h x := by
    rcases g with i | i <;> rcases h with j | j <;> simp <;> ring

/-- The vertex action of the dihedral group on the `n`-gon is transitive: any vertex can be
rotated onto any other. -/
instance vertexAction_isPretransitive (n : ℕ) :
    MulAction.IsPretransitive (DihedralGroup n) (ZMod n) where
  exists_smul_eq x y := ⟨DihedralGroup.r (x - y), by simp⟩

/-- The orbit space of the `n`-gon vertex action is a singleton (for `n ≠ 0`). -/
theorem card_vertexOrbits (n : ℕ) [NeZero n] :
    Nat.card (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n)) = 1 := by
  have hne : Nonempty (ZMod n) := ⟨0⟩
  have huniq : Unique (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n)) :=
    ((MulAction.pretransitive_iff_unique_quotient_of_nonempty (DihedralGroup n) (ZMod n)).mp
      inferInstance).some
  letI := huniq
  exact Nat.card_unique

/-!
## The permutation character and the multiplicity of the trivial character
-/

/-- The permutation character of the `n`-gon vertex action: `g` is sent to the number of
vertices that it fixes. -/
noncomputable def vertexCharacter (n : ℕ) (g : DihedralGroup n) : ℕ :=
  Nat.card (MulAction.fixedBy (ZMod n) g)

/-- Sanity check on the permutation character: the identity symmetry fixes all `n` vertices. -/
theorem vertexCharacter_one (n : ℕ) [NeZero n] : vertexCharacter n 1 = n := by
  rw [vertexCharacter, MulAction.fixedBy_one_eq_univ (ZMod n) (DihedralGroup n)]
  simp [Nat.card_eq_fintype_card, ZMod.card n]

/-- **Burnside count for the `n`-gon.**  The total number of (symmetry, fixed vertex) incidences
for the symmetry group of the regular `n`-gon equals the order `2n` of that group. -/
theorem sum_vertexCharacter (n : ℕ) [NeZero n] :
    ∑ g : DihedralGroup n, vertexCharacter n g = 2 * n := by
  classical
  haveI : ∀ g : DihedralGroup n, Fintype (MulAction.fixedBy (ZMod n) g) := fun _ =>
    Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n)) := Fintype.ofFinite _
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (DihedralGroup n) (ZMod n)
  rw [← Nat.card_eq_fintype_card, card_vertexOrbits n, one_mul, DihedralGroup.card] at h
  simpa [vertexCharacter, Nat.card_eq_fintype_card] using h

/-- **Pentagon Pentagon Character Multiplicity Ext.**

Extension of the pentagon (`D₅`) computation to arbitrary regular `n`-gons: for the action of
the dihedral group `DihedralGroup n` on the vertex set `ZMod n` of the regular `n`-gon, the
multiplicity of the trivial character in the permutation character `χ g = #Fix(g)` — that is,
the average number of fixed vertices — equals `1`, since the action is transitive.  Equivalently
`∑ g, #Fix(g) = |DihedralGroup n| = 2n`. -/
theorem PentagonPentagonCharacterMultiplicityExt (n : ℕ) [NeZero n] :
    (Fintype.card (DihedralGroup n) : ℂ)⁻¹ *
        ∑ g : DihedralGroup n, (vertexCharacter n g : ℂ) = 1 := by
  have hsum : ∑ g : DihedralGroup n, (vertexCharacter n g : ℂ) = ((2 * n : ℕ) : ℂ) := by
    rw [← Nat.cast_sum, sum_vertexCharacter n]
  rw [DihedralGroup.card, hsum]
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  push_cast
  field_simp

/-- The original pentagon case `n = 5`: the ten symmetries of the regular pentagon fix ten
vertices in total, so the trivial character occurs exactly once in the vertex permutation
representation. -/
theorem pentagon_sum_vertexCharacter :
    ∑ g : DihedralGroup 5, vertexCharacter 5 g = 10 := by
  simpa using sum_vertexCharacter 5

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

