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

theorem connected_cycleGraph_arc {b m : ℕ} (hmb : m < b) (hb : 2 ≤ b) :
    ((SimpleGraph.cycleGraph b).induce {x : Fin b | m ≤ x.val}).Connected := by
  set S : Set (Fin b) := {x : Fin b | m ≤ x.val} with hS
  have hbase : (⟨m, hmb⟩ : Fin b) ∈ S := by simp [hS]
  haveI : Nonempty ↥S := ⟨⟨⟨m, hmb⟩, hbase⟩⟩
  have key : ∀ k : ℕ, ∀ (x : Fin b) (hx : x ∈ S), x.val = k →
      ((SimpleGraph.cycleGraph b).induce S).Reachable ⟨x, hx⟩ ⟨⟨m, hmb⟩, hbase⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro x hx hxk
      have hxm : m ≤ x.val := hx
      rcases eq_or_lt_of_le hxm with heq | hlt
      · have hxe : x = (⟨m, hmb⟩ : Fin b) := Fin.ext heq.symm
        subst hxe
        exact SimpleGraph.Reachable.refl _
      · have hy : (x.val - 1) < b := by omega
        have hyS : (⟨x.val - 1, hy⟩ : Fin b) ∈ S := by
          show m ≤ x.val - 1
          omega
        have hadj : ((SimpleGraph.cycleGraph b).induce S).Adj ⟨⟨x.val - 1, hy⟩, hyS⟩ ⟨x, hx⟩ :=
          cycleGraph_adj_of_succ _ x (by show x.val - 1 + 1 = x.val; omega) hb
        have hrec := ih (x.val - 1) (by omega) ⟨x.val - 1, hy⟩ hyS rfl
        exact (hadj.symm.reachable).trans hrec
  constructor
  intro x y
  exact (key x.val.val x.val x.2 rfl).trans (key y.val.val y.val y.2 rfl).symm

/-- A cycle of length `a` is a minor of any longer cycle: contract the arc of the long cycle
that lies beyond the first `a - 1` vertices. -/
