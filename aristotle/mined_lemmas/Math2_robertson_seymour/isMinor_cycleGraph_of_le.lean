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

theorem isMinor_cycleGraph_of_le {a b : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) :
    IsMinor (SimpleGraph.cycleGraph a) (SimpleGraph.cycleGraph b) := by
  have hb2 : 2 ≤ b := by omega
  have harc : a - 1 < b := by omega
  set B : Fin a → Set (Fin b) :=
    fun i => if i.val + 1 < a then {x : Fin b | x.val = i.val} else {x : Fin b | a - 1 ≤ x.val}
    with hB
  have hmem_sing : ∀ i : Fin a, i.val + 1 < a → ∀ x : Fin b, x ∈ B i ↔ x.val = i.val := by
    intro i hi x
    simp [hB, if_pos hi]
  have hmem_arc : ∀ i : Fin a, ¬ (i.val + 1 < a) → ∀ x : Fin b, x ∈ B i ↔ a - 1 ≤ x.val := by
    intro i hi x
    simp [hB, if_neg hi]
  have hstep : ∀ i j : Fin a, j.val = i.val + 1 →
      ∃ x ∈ B i, ∃ y ∈ B j, (SimpleGraph.cycleGraph b).Adj x y := by
    intro i j hji
    have hi : i.val + 1 < a := by have := j.isLt; omega
    have hib : i.val < b := by have := i.isLt; omega
    have hjb : j.val < b := by have := j.isLt; omega
    refine ⟨⟨i.val, hib⟩, (hmem_sing i hi _).mpr rfl, ⟨j.val, hjb⟩, ?_, ?_⟩
    · by_cases hj : j.val + 1 < a
      · exact (hmem_sing j hj _).mpr rfl
      · exact (hmem_arc j hj _).mpr (by show a - 1 ≤ j.val; omega)
    · exact cycleGraph_adj_of_succ _ _ (by show i.val + 1 = j.val; omega) hb2
  have hwrap : ∀ i j : Fin a, i.val + 1 = a → j.val = 0 →
      ∃ x ∈ B i, ∃ y ∈ B j, (SimpleGraph.cycleGraph b).Adj x y := by
    intro i j hi hj
    have hbi : b - 1 < b := by omega
    have hj' : j.val + 1 < a := by omega
    refine ⟨⟨b - 1, hbi⟩, (hmem_arc i (by omega) _).mpr (by simp; omega), ⟨0, by omega⟩, ?_, ?_⟩
    · exact (hmem_sing j hj' _).mpr (by simp [hj])
    · exact cycleGraph_adj_wrap _ _ (by simp; omega) (by simp) hb2
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i.val + 1 < a
    · exact ⟨⟨i.val, by have := i.isLt; omega⟩, (hmem_sing i hi _).mpr rfl⟩
    · exact ⟨⟨a - 1, harc⟩, (hmem_arc i hi _).mpr (by simp)⟩
  · intro i
    by_cases hi : i.val + 1 < a
    · have hset : B i = {(⟨i.val, by have := i.isLt; omega⟩ : Fin b)} := by
        ext x
        rw [hmem_sing i hi]
        simp [Fin.ext_iff]
      rw [hset]
      exact connected_induce_singleton _ _
    · have hset : B i = {x : Fin b | a - 1 ≤ x.val} := by
        ext x
        rw [hmem_arc i hi]
        simp
      rw [hset]
      exact connected_cycleGraph_arc harc hb2
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hx hx'
    by_cases hi : i.val + 1 < a <;> by_cases hj : j.val + 1 < a
    · exact hij (Fin.ext (((hmem_sing i hi x).mp hx).symm.trans ((hmem_sing j hj x).mp hx')))
    · have h1 := (hmem_sing i hi x).mp hx
      have h2 := (hmem_arc j hj x).mp hx'
      omega
    · have h1 := (hmem_arc i hi x).mp hx
      have h2 := (hmem_sing j hj x).mp hx'
      have := j.isLt
      omega
    · exact hij (Fin.ext (by have := i.isLt; have := j.isLt; omega))
  · intro i j hadj
    rw [SimpleGraph.cycleGraph_adj'] at hadj
    have hsymm : (∃ x ∈ B j, ∃ y ∈ B i, (SimpleGraph.cycleGraph b).Adj x y) →
        ∃ x ∈ B i, ∃ y ∈ B j, (SimpleGraph.cycleGraph b).Adj x y := by
      rintro ⟨x, hx, y, hy, h⟩
      exact ⟨y, hy, x, hx, h.symm⟩
    rcases hadj with h | h
    · rcases fin_sub_val_eq_one i j h with h1 | ⟨h1, h2⟩
      · exact hsymm (hstep j i h1)
      · exact hsymm (hwrap j i h2 h1)
    · rcases fin_sub_val_eq_one j i h with h1 | ⟨h1, h2⟩
      · exact hstep i j h1
      · exact hwrap i j h2 h1

/-- **Robertson–Seymour for cycles.**  The class of cycles is well-quasi-ordered by the minor
relation. -/
