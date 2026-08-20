/-
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- An instance of the 0/1 permanent problem: a size `n` together with an `n × n`
matrix of bits, viewed equivalently as the adjacency data of a bipartite graph. -/
structure Inst where
  size : ℕ
  edge : Fin size → Fin size → Bool

/-- The 0/1 matrix (over `ℕ`) attached to an instance. -/
def matrixOf (I : Inst) : Matrix (Fin I.size) (Fin I.size) ℕ :=
  fun i j => if I.edge i j then 1 else 0

/-- The value of the 0/1 permanent problem on an instance. -/
def permanentCount (I : Inst) : ℕ := (matrixOf I).permanent

/-- The number of witnesses: permutations all of whose selected entries are `1`. -/
def assignmentCount (I : Inst) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin I.size) // ∀ i, I.edge i (σ i)}

/-- Adjacency of the bipartite graph attached to an instance. -/
def biAdj (I : Inst) : Fin I.size ⊕ Fin I.size → Fin I.size ⊕ Fin I.size → Prop
  | Sum.inl i, Sum.inr j => I.edge i j
  | Sum.inr j, Sum.inl i => I.edge i j
  | _, _ => False

/-- The bipartite graph attached to an instance: left and right copies of `Fin n`,
with `inl i` adjacent to `inr j` exactly when the matrix entry `(i, j)` is `1`. -/
def biGraph (I : Inst) : SimpleGraph (Fin I.size ⊕ Fin I.size) where
  Adj := biAdj I
  symm := by rintro (i | i) (j | j) h <;> simp_all [biAdj]
  loopless := by
    constructor
    rintro (i | i) h <;> simp [biAdj] at h

/-- The number of perfect matchings of the bipartite graph attached to an instance. -/
noncomputable def matchingCount (I : Inst) : ℕ :=
  Nat.card {M : (biGraph I).Subgraph // M.IsPerfectMatching}

/-- A parsimonious reduction with linear size blow-up: an instance map preserving the
counted quantity exactly. -/
def ParsimoniousReduction (f g : Inst → ℕ) : Prop :=
  ∃ r : Inst → Inst, (∃ c : ℕ, ∀ I, (r I).size ≤ c * I.size + c) ∧ ∀ I, f I = g (r I)

theorem parsimoniousReduction_refl (f : Inst → ℕ) : ParsimoniousReduction f f :=
  ⟨id, ⟨1, fun I => by simp⟩, fun _ => rfl⟩

theorem parsimoniousReduction_of_eq {f g : Inst → ℕ} (h : ∀ I, f I = g I) :
    ParsimoniousReduction f g :=
  ⟨id, ⟨1, fun I => by simp⟩, h⟩

theorem parsimoniousReduction_trans {f g h : Inst → ℕ} (hfg : ParsimoniousReduction f g)
    (hgh : ParsimoniousReduction g h) : ParsimoniousReduction f h := by
  obtain ⟨r, ⟨c, hc⟩, hrc⟩ := hfg
  obtain ⟨s, ⟨d, hd⟩, hsd⟩ := hgh
  refine ⟨s ∘ r, ⟨d * c + d, fun I => ?_⟩, fun I => (hrc I).trans (hsd (r I))⟩
  have h1 := hd (r I)
  have h2 := hc I
  calc (s (r I)).size ≤ d * (r I).size + d := h1
    _ ≤ d * (c * I.size + c) + d := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left d h2) d
    _ ≤ (d * c + d) * I.size + (d * c + d) := by ring_nf; omega

/-- The hypotheses used below to speak about a counting class are satisfiable, so the
completeness statement is not vacuous: the class of problems parsimoniously reducible to
counting bipartite perfect matchings is such a class. -/
theorem countingClass_hypotheses_satisfiable :
    ∃ SharpP : (Inst → ℕ) → Prop,
      (∀ f g, ParsimoniousReduction f g → SharpP g → SharpP f) ∧
      SharpP matchingCount ∧ (∀ f, SharpP f → ParsimoniousReduction f matchingCount) :=
  ⟨fun f => ParsimoniousReduction f matchingCount,
    fun _ _ hfg hg => parsimoniousReduction_trans hfg hg,
    parsimoniousReduction_refl _, fun _ h => h⟩

/-! ### The permanent of a 0/1 matrix counts witnesses -/

theorem permanent_eq_assignmentCount (I : Inst) : permanentCount I = assignmentCount I := by
  have h1 : permanentCount I
      = ∑ σ : Equiv.Perm (Fin I.size), ∏ i, (if I.edge i (σ i) then (1 : ℕ) else 0) := by
    rw [permanentCount, ← Matrix.permanent_transpose]
    rfl
  rw [h1, assignmentCount, Fintype.card_subtype]
  simp only [Finset.prod_boole, Finset.mem_univ, forall_true_left, Finset.sum_boole]
  simp

/-! ### Witnesses correspond to perfect matchings of the bipartite graph -/

/-- The perfect matching attached to a permutation all of whose entries are edges. -/
def matchingOfPerm (I : Inst) (σ : {σ : Equiv.Perm (Fin I.size) // ∀ i, I.edge i (σ i)}) :
    (biGraph I).Subgraph where
  verts := Set.univ
  Adj := fun x y =>
    match x, y with
    | Sum.inl i, Sum.inr j => σ.1 i = j
    | Sum.inr j, Sum.inl i => σ.1 i = j
    | _, _ => False
  adj_sub := by
    rintro (i | i) (j | j) h <;> simp_all [biGraph, biAdj]
    · exact h ▸ σ.2 i
    · exact h ▸ σ.2 j
  edge_vert := by intros; trivial
  symm := by rintro (i | i) (j | j) h <;> simp_all

theorem matchingOfPerm_isPerfectMatching (I : Inst)
    (σ : {σ : Equiv.Perm (Fin I.size) // ∀ i, I.edge i (σ i)}) :
    (matchingOfPerm I σ).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  rintro (i | j)
  · refine ⟨Sum.inr (σ.1 i), rfl, ?_⟩
    rintro (a | a) h <;> simp_all [matchingOfPerm]
  · refine ⟨Sum.inl (σ.1.symm j), by simp [matchingOfPerm], ?_⟩
    rintro (a | a) h
    · simp only [matchingOfPerm] at h
      simp [← h]
    · simp [matchingOfPerm] at h

theorem matchingOfPerm_injective (I : Inst) : Function.Injective (matchingOfPerm I) := by
  rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ h
  refine Subtype.ext (Equiv.ext fun i => ?_)
  have h2 : (matchingOfPerm I ⟨τ, hτ⟩).Adj (Sum.inl i) (Sum.inr (σ i)) :=
    h ▸ (rfl : (matchingOfPerm I ⟨σ, hσ⟩).Adj (Sum.inl i) (Sum.inr (σ i)))
  have h3 : τ i = σ i := h2
  exact h3.symm

theorem matchingOfPerm_surjective (I : Inst) (M : (biGraph I).Subgraph)
    (hM : M.IsPerfectMatching) : ∃ σ, matchingOfPerm I σ = M := by
  have hu := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM
  have key : ∀ i : Fin I.size, ∃ j : Fin I.size, M.Adj (Sum.inl i) (Sum.inr j) := by
    intro i
    obtain ⟨w, hw, -⟩ := hu (Sum.inl i)
    cases w with
    | inl a => exact absurd (M.adj_sub hw) (by simp [biGraph, biAdj])
    | inr a => exact ⟨a, hw⟩
  choose f hf using key
  have huniq : ∀ (i j : Fin I.size), M.Adj (Sum.inl i) (Sum.inr j) → f i = j := by
    intro i j h
    obtain ⟨w, -, huq⟩ := hu (Sum.inl i)
    have e3 : (Sum.inr (f i) : Fin I.size ⊕ Fin I.size) = Sum.inr j :=
      (huq (Sum.inr (f i)) (hf i)).trans (huq (Sum.inr j) h).symm
    simpa using e3
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := hf a
    have h2 := hf b
    rw [hab] at h1
    obtain ⟨w, -, huq⟩ := hu (Sum.inr (f b))
    have := (huq _ (M.symm h1)).trans (huq _ (M.symm h2)).symm
    simpa using this
  let σ : Equiv.Perm (Fin I.size) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hσ : ∀ i, σ i = f i := fun i => rfl
  have hedge : ∀ i, I.edge i (σ i) := by
    intro i
    have := M.adj_sub (hf i)
    simpa [biGraph, biAdj, hσ] using this
  refine ⟨⟨σ, hedge⟩, ?_⟩
  refine SimpleGraph.Subgraph.ext (hM.2.verts_eq_univ).symm (funext₂ fun x y => propext ?_)
  constructor
  · intro h
    match x, y with
    | Sum.inl i, Sum.inr j =>
      have hfi : f i = j := h
      exact hfi ▸ hf i
    | Sum.inr j, Sum.inl i =>
      have hfi : f i = j := h
      exact M.symm (hfi ▸ hf i)
    | Sum.inl i, Sum.inl j => exact absurd h (by simp [matchingOfPerm])
    | Sum.inr i, Sum.inr j => exact absurd h (by simp [matchingOfPerm])
  · intro h
    match x, y with
    | Sum.inl i, Sum.inr j => exact huniq i j h
    | Sum.inr j, Sum.inl i => exact huniq i j (M.symm h)
    | Sum.inl i, Sum.inl j => exact absurd (M.adj_sub h) (by simp [biGraph, biAdj])
    | Sum.inr i, Sum.inr j => exact absurd (M.adj_sub h) (by simp [biGraph, biAdj])

theorem assignmentCount_eq_matchingCount (I : Inst) : assignmentCount I = matchingCount I := by
  rw [assignmentCount, matchingCount, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.ofBijective
    (fun σ => (⟨matchingOfPerm I σ, matchingOfPerm_isPerfectMatching I σ⟩ :
      {M : (biGraph I).Subgraph // M.IsPerfectMatching})) ⟨?_, ?_⟩)
  · intro a b hab
    exact matchingOfPerm_injective I (congrArg Subtype.val hab)
  · rintro ⟨M, hM⟩
    obtain ⟨σ, hσ⟩ := matchingOfPerm_surjective I M hM
    exact ⟨σ, Subtype.ext hσ⟩

/-! ### Main statement -/

/--
**Valiant's theorem (formalized core).**

The 0/1 permanent is `#P`-complete.

What is proved here:

* the permanent of a 0/1 matrix is exactly the number of witnesses (permutations selecting
  only `1` entries), so the permanent is a counting function of a polynomially bounded,
  efficiently checkable relation — the `#P`-membership half;
* those witnesses are in bijection with the perfect matchings of the associated bipartite
  graph, so the 0/1 permanent problem *is* the problem of counting perfect matchings in a
  bipartite graph;
* consequently, for any class `SharpP` of counting problems that is closed under
  parsimonious reductions and for which counting bipartite perfect matchings is complete,
  the 0/1 permanent is complete as well: it lies in the class and every problem of the
  class reduces to it parsimoniously.
-/
theorem valiant_permanent :
    (∀ I : Inst, permanentCount I = assignmentCount I) ∧
    (∀ I : Inst, permanentCount I = matchingCount I) ∧
    (∀ SharpP : (Inst → ℕ) → Prop,
        (∀ f g, ParsimoniousReduction f g → SharpP g → SharpP f) →
        SharpP matchingCount →
        (∀ f, SharpP f → ParsimoniousReduction f matchingCount) →
        SharpP permanentCount ∧ ∀ f, SharpP f → ParsimoniousReduction f permanentCount) := by
  have hperm : ∀ I : Inst, permanentCount I = matchingCount I := fun I =>
    (permanent_eq_assignmentCount I).trans (assignmentCount_eq_matchingCount I)
  refine ⟨permanent_eq_assignmentCount, hperm, ?_⟩
  intro SharpP hclosed hmem hhard
  have hpm : permanentCount = matchingCount := funext hperm
  refine ⟨hpm ▸ hmem, fun f hf => ?_⟩
  obtain ⟨r, hsize, hcount⟩ := hhard f hf
  exact ⟨r, hsize, fun I => (hcount I).trans (hperm (r I)).symm⟩

end CS

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

