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

def trivialIsotypic (n : ℕ) : Submodule ℂ (ZMod n → ℂ) where
  carrier := {f | ∀ (g : DihedralGroup n) (x : ZMod n), f (g • x) = f x}
  add_mem' := by intro a b ha hb g x; simp [ha g x, hb g x]
  zero_mem' := by intro g x; rfl
  smul_mem' := by intro c a ha g x; simp [ha g x]

/-- **Pentagon → higher `n`-gon.** For every `n`, the trivial isotypic component of the
vertex permutation representation of the dihedral group `DihedralGroup n` is the line
spanned by the all-ones function, and hence has dimension `1`. -/

theorem PentagonPentagonIsotypicHigherN (n : ℕ) :
    trivialIsotypic n = Submodule.span ℂ {Function.const (ZMod n) (1 : ℂ)} ∧
      Module.finrank ℂ (trivialIsotypic n) = 1 := by
  have hspan : trivialIsotypic n = Submodule.span ℂ {Function.const (ZMod n) (1 : ℂ)} := by
    apply le_antisymm
    · intro f hf
      rw [Submodule.mem_span_singleton]
      refine ⟨f 0, ?_⟩
      funext x
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (DihedralGroup n) (0 : ZMod n) x
      simp only [Pi.smul_apply, Function.const_apply, smul_eq_mul, mul_one]
      rw [← hg, hf g 0]
    · rw [Submodule.span_le]
      rintro f rfl g x
      rfl
  refine ⟨hspan, ?_⟩
  rw [hspan]
  apply finrank_span_singleton
  intro h
  have := congrFun h 0
  simp at this

/-- The pentagon case `n = 5`, recovered as a special case. -/
