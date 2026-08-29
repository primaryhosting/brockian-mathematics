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
