/-
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

variable {n : ℕ}

/-- The permutation action of the dihedral group `DihedralGroup n` on the `n` vertices of the
regular `n`-gon (labelled by `ZMod n`): the rotation `r i` sends a vertex `x` to `x + i`, and the
reflection `sr i` sends `x` to `-i - x`. -/

theorem sum_vertexCharacter [NeZero n] :
    ∑ g : DihedralGroup n, vertexCharacter n g = 2 * n := by
  let e : ZMod n ⊕ ZMod n ≃ DihedralGroup n :=
    { toFun := Sum.elim DihedralGroup.r DihedralGroup.sr
      invFun := fun g => match g with
        | .r i => Sum.inl i
        | .sr i => Sum.inr i
      left_inv := by rintro (i | i) <;> rfl
      right_inv := by rintro (i | i) <;> rfl }
  have := Fintype.sum_equiv e.symm (fun g => vertexCharacter n g)
    (fun x => vertexCharacter n (e x)) (fun g => by cases g <;> rfl)
  rw [this, Fintype.sum_sum_type]
  simp only [e, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr]
  rw [sum_vertexCharacter_r, sum_vertexCharacter_sr]
  ring

/--
**Pentagon Pentagon Character Multiplicity Ext.**

Generalization of the `D₅`-pentagon computation to arbitrary regular `n`-gons: for every `n ≥ 1`
the vertex permutation character of `DihedralGroup n` sums to `2n = |DihedralGroup n|` over the
group, i.e. by Burnside's formula the trivial representation occurs with multiplicity exactly `1`
in the vertex permutation representation (equivalently, the action on the vertices of the
`n`-gon is transitive).
-/
