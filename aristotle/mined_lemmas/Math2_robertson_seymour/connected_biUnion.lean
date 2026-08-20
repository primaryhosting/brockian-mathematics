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

theorem connected_biUnion {W X : Type*} {G : SimpleGraph W} {K : SimpleGraph X}
    (S : Set W) (C : W → Set X)
    (hS : (G.induce S).Connected)
    (hconn : ∀ w, (K.induce (C w)).Connected)
    (hedge : ∀ w w', G.Adj w w' → ∃ x ∈ C w, ∃ y ∈ C w', K.Adj x y) :
    (K.induce (⋃ w ∈ S, C w)).Connected := by
  set T : Set X := ⋃ w ∈ S, C w with hT
  have hsub : ∀ w ∈ S, C w ⊆ T := fun _ hw _ hx => Set.mem_biUnion hw hx
  have key : ∀ (a b : ↥S), (G.induce S).Reachable a b →
      ∀ (x y : X) (_ : x ∈ C a.val) (_ : y ∈ C b.val) (hxT : x ∈ T) (hyT : y ∈ T),
      (K.induce T).Reachable ⟨x, hxT⟩ ⟨y, hyT⟩ := by
    rintro a b ⟨p⟩
    induction p with
    | @nil c =>
        intro x y hx hy hxT hyT
        exact reachable_induce_mono (hsub _ c.2) hx hy hxT hyT ((hconn c.val).preconnected _ _)
    | @cons a c b hac p ih =>
        intro x y hx hy hxT hyT
        obtain ⟨u, hu, v, hv, huv⟩ := hedge a.val c.val hac
        have huT : u ∈ T := hsub _ a.2 hu
        have hvT : v ∈ T := hsub _ c.2 hv
        have r1 : (K.induce T).Reachable ⟨x, hxT⟩ ⟨u, huT⟩ :=
          reachable_induce_mono (hsub _ a.2) hx hu hxT huT ((hconn a.val).preconnected _ _)
        have r2 : (K.induce T).Adj ⟨u, huT⟩ ⟨v, hvT⟩ := huv
        have r3 : (K.induce T).Reachable ⟨v, hvT⟩ ⟨y, hyT⟩ := ih v y hv hy hvT hyT
        exact (r1.trans r2.reachable).trans r3
  obtain ⟨w0⟩ := hS.nonempty
  obtain ⟨x0, hx0⟩ := (hconn w0.val).nonempty
  haveI : Nonempty ↥T := ⟨⟨x0, hsub _ w0.2 hx0⟩⟩
  constructor
  rintro ⟨x, hxT⟩ ⟨y, hyT⟩
  have hxT' := hxT
  have hyT' := hyT
  simp only [hT, Set.mem_iUnion, exists_prop] at hxT' hyT'
  obtain ⟨a, haS, hxa⟩ := hxT'
  obtain ⟨b, hbS, hyb⟩ := hyT'
  exact key ⟨a, haS⟩ ⟨b, hbS⟩ (hS.preconnected _ _) x y hxa hyb _ _

/-- The minor relation is transitive: together with `Math2.isMinor_refl` this makes it a
quasi-order. -/
