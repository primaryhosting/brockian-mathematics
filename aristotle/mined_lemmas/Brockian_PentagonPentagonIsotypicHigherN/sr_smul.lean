/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The `D₅` pentagon results are generalized here to an arbitrary regular `n`-gon.

The dihedral group `DihedralGroup n` acts on the vertex set `ZMod n` of the regular
`n`-gon by rotations (`r i • x = x - i`) and reflections (`sr i • x = i - x`).  This action
is transitive, hence the trivial isotypic component of the associated complex permutation
representation `ZMod n → ℂ` — i.e. the space of invariant vectors — is the line spanned by
the all-ones vector, and in particular is one dimensional.  Specializing `n = 5` recovers
the pentagon statement.
-/

namespace Brockian

open DihedralGroup

/-- The action of the dihedral group of order `2n` on the vertices `ZMod n`
of the regular `n`-gon: `r i` rotates and `sr i` reflects. -/
instance ngonAction (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  smul g x := match g with
    | r i => x - i
    | sr i => i - x
  one_smul x := by change x - 0 = x; ring
  mul_smul g h x := by
    cases g <;> cases h <;> (show _ = _; simp [HSMul.hSMul]; ring)


@[simp] lemma sr_smul (n : ℕ) (i x : ZMod n) : (sr i : DihedralGroup n) • x = i - x := rfl

/-- The dihedral group acts transitively on the vertices of the `n`-gon. -/
instance ngon_pretransitive (n : ℕ) :
    MulAction.IsPretransitive (DihedralGroup n) (ZMod n) :=
  ⟨fun x y => ⟨r (x - y), by rw [r_smul]; ring⟩⟩

/-- The trivial isotypic component (the space of invariant vectors) of the complex
permutation representation of `DihedralGroup n` on the vertices of the regular `n`-gon. -/
