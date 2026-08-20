/-
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as the first lines of the file as a plain block comment,
since Lean does not allow a module docstring `/-! ... -/` to precede the `import` line.)

## What is formalised here

* `Math2.IsMinor H G` : the standard *minor model* definition of "`H` is a minor of `G`".
* `Math2.robertson_seymour` : well-quasi-ordering by the minor relation for families of
  finite graphs whose orders are bounded by a fixed `k`.
* `Math2.robertson_seymour_linearForest` : well-quasi-ordering by the minor relation of the
  (infinite, unbounded) class of linear forests, i.e. disjoint unions of paths.  This is
  deduced from Higman's lemma.
* `Math2.robertson_seymour_cycleGraph` : well-quasi-ordering by the minor relation of the
  (infinite, unbounded) class of cycles; here the minors genuinely involve edge
  contractions.
* `Math2.isMinor_refl` and `Math2.IsMinor.trans` : the minor relation is a quasi-order.
* `Math2.RobertsonSeymourWQO` : the statement of the unrestricted Robertson–Seymour theorem,
  recorded as a `Prop`.  It is **not** proved here; the full graph minor theorem is the
  conclusion of the twenty-paper Graph Minors series and is far beyond what is formalised
  in this file.
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

namespace Math2

/-! ## The minor relation -/

/-- `IsMinor H G` says that `H` is a minor of `G`, expressed through a *minor model*:
each vertex `v` of `H` is assigned a branch set `B v ⊆ G`, the branch sets are nonempty,
induce connected subgraphs of `G`, are pairwise disjoint, and whenever `v` and `w` are
adjacent in `H` there is an edge of `G` joining `B v` to `B w`. -/

def linearForestSingletonIso (n : ℕ) : linearForest [n] ≃g SimpleGraph.pathGraph n where
  toFun p := ⟨p.1.2, by have hp := p.2; simpa [lfVertex_fst_eq_zero p] using hp⟩
  invFun k := ⟨(0, k.val), by simp⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (lfVertex_fst_eq_zero p).symm rfl
  right_inv k := by
    apply Fin.ext
    rfl
  map_rel_iff' := by
    intro p q
    rw [SimpleGraph.pathGraph_adj]
    simp only [linearForest]
    constructor
    · intro h
      exact ⟨(lfVertex_fst_eq_zero p).trans (lfVertex_fst_eq_zero q).symm, h⟩
    · rintro ⟨-, h⟩
      exact h

/-- From a domination `l₁ ≤ l₂` of lists of naturals in the sense of Higman's ordering one
extracts a strictly monotone index map matching each entry of `l₁` with a larger entry of
`l₂`. -/
