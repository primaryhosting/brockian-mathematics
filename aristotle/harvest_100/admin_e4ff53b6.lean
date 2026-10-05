import Mathlib

/-!
# Four Color Statement
Category: Frontier — Moonshot
Target: Frontier.four_color_statement
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

namespace Frontier

open SimpleGraph

/-! ## Minors and planarity -/

/-- `IsMinor H G` says that `H` is a *minor* of `G`: there is a family of pairwise disjoint
"branch sets" `B w ⊆ V`, one for each vertex `w` of `H`, each inducing a connected subgraph
of `G`, such that adjacent vertices of `H` have branch sets joined by an edge of `G`. -/
def IsMinor {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ B : W → Set V,
    (∀ w₁ w₂, w₁ ≠ w₂ → Disjoint (B w₁) (B w₂)) ∧
    (∀ w, (G.induce (B w)).Connected) ∧
    (∀ w₁ w₂, H.Adj w₁ w₂ → ∃ a ∈ B w₁, ∃ b ∈ B w₂, G.Adj a b)

/-- The complete graph `K₅`. -/
abbrev K5 : SimpleGraph (Fin 5) := completeGraph (Fin 5)

/-- The complete bipartite graph `K₃,₃`. -/
abbrev K33 : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)

/-- A graph is *planar* when it has neither `K₅` nor `K₃,₃` as a minor.  By Wagner's theorem this
is equivalent to embeddability in the plane; it is the combinatorial form of planarity used
here. -/
def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ IsMinor K5 G ∧ ¬ IsMinor K33 G

/-- Every graph is a minor of itself (take singleton branch sets). -/
theorem IsMinor.refl {V : Type*} (G : SimpleGraph V) : IsMinor G G := by
  refine ⟨fun v => {v}, ?_, ?_, ?_⟩
  · intro a b hab
    simpa using hab
  · intro v
    haveI : Nonempty ↥({v} : Set V) := ⟨⟨v, rfl⟩⟩
    rw [SimpleGraph.induce_singleton_eq_top]
    exact connected_top
  · intro a b hab
    exact ⟨a, rfl, b, rfl, hab⟩

/-- Minors are inherited from induced subgraphs: a minor of `G.induce s` is a minor of `G`. -/
theorem IsMinor.of_induce {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V} {s : Set V}
    (h : IsMinor H (G.induce s)) : IsMinor H G := by
  obtain ⟨B, hdisj, hconn, hadj⟩ := h
  refine ⟨fun w => Subtype.val '' (B w), ?_, ?_, ?_⟩
  · intro w₁ w₂ hw
    exact Set.disjoint_image_of_injective Subtype.val_injective (hdisj w₁ w₂ hw)
  · intro w
    have hsurj : Function.Surjective
        (fun x : ↥(B w) => (⟨x.val.val, ⟨x.val, x.prop, rfl⟩⟩ : ↥(Subtype.val '' (B w)))) := by
      rintro ⟨v, y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    exact Connected.map (G := (G.induce s).induce (B w)) (H := G.induce (Subtype.val '' (B w)))
      ⟨fun x => ⟨x.val.val, ⟨x.val, x.prop, rfl⟩⟩, fun {_ _} hab => hab⟩ hsurj (hconn w)
  · intro w₁ w₂ hw
    obtain ⟨a, ha, b, hb, hab⟩ := hadj w₁ w₂ hw
    exact ⟨a.val, ⟨a, ha, rfl⟩, b.val, ⟨b, hb, rfl⟩, hab⟩

/-- Planarity is inherited by induced subgraphs. -/
theorem IsPlanar.induce {V : Type*} {G : SimpleGraph V} (hG : IsPlanar G) (s : Set V) :
    IsPlanar (G.induce s) :=
  ⟨fun h => hG.1 (IsMinor.of_induce h), fun h => hG.2 (IsMinor.of_induce h)⟩

/-! ## A compactness (De Bruijn–Erdős) argument -/

/-- **De Bruijn–Erdős**: for `n > 0`, a graph is `n`-colourable as soon as all of its finite
induced subgraphs are.  The proof is a compactness argument in the space of all `Fin n`-valued
vertex labellings. -/
theorem colorable_of_forall_finite_induce {V : Type} (G : SimpleGraph V) (n : ℕ) (hn : 0 < n)
    (h : ∀ s : Finset V, (G.induce (s : Set V)).Colorable n) : G.Colorable n := by
  classical
  letI : TopologicalSpace (Fin n) := ⊥
  haveI : DiscreteTopology (Fin n) := ⟨rfl⟩
  set C : Finset V → Set (V → Fin n) :=
    fun s => {f | ∀ a ∈ s, ∀ b ∈ s, G.Adj a b → f a ≠ f b} with hC
  have hclosed : ∀ s, IsClosed (C s) := by
    intro s
    have hCs : C s = ⋂ a ∈ s, ⋂ b ∈ s, {f : V → Fin n | G.Adj a b → f a ≠ f b} := by
      ext f; simp [hC]
    rw [hCs]
    refine isClosed_biInter fun a _ => isClosed_biInter fun b _ => ?_
    by_cases hab : G.Adj a b
    · have he : {f : V → Fin n | G.Adj a b → f a ≠ f b}
          = (fun f : V → Fin n => (f a, f b)) ⁻¹' {p : Fin n × Fin n | p.1 ≠ p.2} := by
        ext f; simp [hab]
      rw [he]
      exact IsClosed.preimage (by fun_prop) (isClosed_discrete _)
    · have he : {f : V → Fin n | G.Adj a b → f a ≠ f b} = Set.univ := by ext f; simp [hab]
      rw [he]
      exact isClosed_univ
  have hne : ∀ s, (C s).Nonempty := by
    intro s
    obtain ⟨c⟩ := h s
    refine ⟨fun v => if hv : v ∈ s then c ⟨v, by simpa using hv⟩ else ⟨0, hn⟩, ?_⟩
    intro a ha b hb hab
    have ha' : a ∈ (s : Set V) := by simpa using ha
    have hb' : b ∈ (s : Set V) := by simpa using hb
    have hadj : (G.induce (s : Set V)).Adj ⟨a, ha'⟩ ⟨b, hb'⟩ := hab
    simpa [ha, hb] using c.valid hadj
  have hdir : Directed (· ⊇ ·) C := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩ <;> intro f hf a ha b hb hab <;>
      exact hf a (by simp [ha]) b (by simp [hb]) hab
  obtain ⟨f, hf⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hne
    (fun s => (hclosed s).isCompact) hclosed
  simp only [Set.mem_iInter] at hf
  exact ⟨SimpleGraph.Coloring.mk f fun {a b} hab => hf {a, b} a (by simp) b (by simp) hab⟩

/-! ## The four colour statement -/

/-- The four colour statement restricted to finite graphs. -/
def FourColorFinite : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsPlanar G → G.Colorable 4

/-- The four colour statement for arbitrary (possibly infinite) planar graphs. -/
def FourColorAll : Prop :=
  ∀ (V : Type) (G : SimpleGraph V), IsPlanar G → G.Colorable 4

/-- **Four Color Statement (Lean-checked reduction to the finite case).**
Every planar graph — of arbitrary cardinality — is 4-colourable **if and only if** every *finite*
planar graph is 4-colourable.  The substantive direction is a compactness argument
(De Bruijn–Erdős) combined with the fact that planarity, in Wagner's minor-free form, is
inherited by induced subgraphs.  The finite case itself is the Appel–Haken theorem, which is
taken here as the hypothesis `FourColorFinite`. -/
theorem four_color_statement : FourColorFinite ↔ FourColorAll := by
  constructor
  · intro h V G hG
    refine colorable_of_forall_finite_induce G 4 (by norm_num) fun s => ?_
    exact h ↥(s : Set V) (G.induce (s : Set V)) (hG.induce _)
  · intro h V _ G hG
    exact h V G hG

/-- Sanity check that `IsPlanar` is not degenerate: `K₅` is not planar. -/
theorem not_isPlanar_K5 : ¬ IsPlanar K5 := fun h => h.1 (IsMinor.refl K5)

/-- Sanity check that `IsPlanar` is not degenerate: `K₃,₃` is not planar. -/
theorem not_isPlanar_K33 : ¬ IsPlanar K33 := fun h => h.2 (IsMinor.refl K33)

/-- Base case: any graph with at most four vertices is 4-colourable. -/
theorem colorable_four_of_card_le_four {V : Type} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V ≤ 4) : G.Colorable 4 := by
  obtain ⟨f⟩ : Nonempty (V ↪ Fin 4) := Function.Embedding.nonempty_of_card_le (by simpa using hV)
  exact ⟨SimpleGraph.Coloring.mk f fun {a b} hab h => G.ne_of_adj hab (f.injective h)⟩

end Frontier

