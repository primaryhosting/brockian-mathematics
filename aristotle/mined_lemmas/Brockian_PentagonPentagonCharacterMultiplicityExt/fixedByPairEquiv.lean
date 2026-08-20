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

/-- The natural action of the dihedral group `DihedralGroup n` on the `n` vertices of a regular
`n`-gon, the vertices being modelled by `ZMod n`.  The rotation `r i` sends a vertex `x` to
`x - i`, and the reflection `sr i` sends `x` to `i - x`. -/

def fixedByPairEquiv (n : ℕ) [NeZero n] (g : DihedralGroup n) :
    MulAction.fixedBy (ZMod n × ZMod n) g ≃
      MulAction.fixedBy (ZMod n) g × MulAction.fixedBy (ZMod n) g where
  toFun p := (⟨p.1.1, by
      have := p.2
      rw [MulAction.mem_fixedBy, Prod.ext_iff] at this
      exact this.1⟩,
    ⟨p.1.2, by
      have := p.2
      rw [MulAction.mem_fixedBy, Prod.ext_iff] at this
      exact this.2⟩)
  invFun q := ⟨(q.1.1, q.2.1), by
      rw [MulAction.mem_fixedBy, Prod.ext_iff]
      exact ⟨q.1.2, q.2.2⟩⟩
  left_inv p := by cases p; rfl
  right_inv q := by cases q; rfl

/-- The permutation character of the diagonal action on ordered pairs of vertices is `χ²`. -/
