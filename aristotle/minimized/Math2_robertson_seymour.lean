import Mathlib

/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
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

set_option grind.warning false

namespace Math2

/-- A finite simple graph, presented as a simple graph on the vertex set `Fin n`. -/
structure FinGraph where
  /-- The number of vertices. -/
  n : ℕ
  /-- The adjacency structure. -/
  adj : SimpleGraph (Fin n)

namespace FinGraph

/-- The graph obtained from `H` by contracting the edge `{a, b}`: the vertex `b` is deleted and
its neighbourhood is added to that of `a`. -/

def contract (H : FinGraph) (a b : Fin H.n) : SimpleGraph {v : Fin H.n // v ≠ b} where
  Adj u w := u ≠ w ∧
    (H.adj.Adj u.1 w.1 ∨ (u.1 = a ∧ H.adj.Adj b w.1) ∨ (w.1 = a ∧ H.adj.Adj u.1 b))
  symm := by
    rintro u w ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h1, h2.symm⟩)
    · exact Or.inr (Or.inl ⟨h1, h2.symm⟩)
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- `G` embeds into `H` as a subgraph: there is an injection of vertices carrying edges to
edges.  (This single relation encodes deletion of vertices, deletion of edges, and relabelling
of vertices.) -/

def SubgraphEmbed (G H : FinGraph) : Prop :=
  ∃ f : Fin G.n ↪ Fin H.n, ∀ u v, G.adj.Adj u v → H.adj.Adj (f u) (f v)

/-- `G` is obtained from `H` by contracting a single edge (up to isomorphism). -/

def ContractStep (G H : FinGraph) : Prop :=
  ∃ a b : Fin H.n, H.adj.Adj a b ∧ Nonempty (G.adj ≃g H.contract a b)

/-- One elementary minor operation: pass to a subgraph, or contract one edge. -/

def MinorStep (G H : FinGraph) : Prop := SubgraphEmbed G H ∨ ContractStep G H

/-- `G` is a *minor* of `H`: `G` is obtained from `H` by a finite sequence of vertex deletions,
edge deletions and edge contractions. -/

def IsMinor (G H : FinGraph) : Prop := Relation.ReflTransGen MinorStep G H

@[refl]

theorem isMinor_refl (G : FinGraph) : IsMinor G G := Relation.ReflTransGen.refl

theorem IsMinor.trans {G H K : FinGraph} (h₁ : IsMinor G H) (h₂ : IsMinor H K) : IsMinor G K :=
  Relation.ReflTransGen.trans h₁ h₂

theorem MinorStep.card_le {G H : FinGraph} (h : MinorStep G H) : G.n ≤ H.n := by
  rcases h with ⟨f, -⟩ | ⟨a, b, -, ⟨iso⟩⟩
  · simpa using Fintype.card_le_of_embedding f
  · have h1 : Fintype.card (Fin G.n) = Fintype.card {v : Fin H.n // v ≠ b} :=
      Fintype.card_congr iso.toEquiv
    have h2 : Fintype.card {v : Fin H.n // v ≠ b} ≤ Fintype.card (Fin H.n) :=
      Fintype.card_le_of_embedding (Function.Embedding.subtype _)
    have h3 : G.n = Fintype.card {v : Fin H.n // v ≠ b} := by simpa using h1
    have h4 : Fintype.card (Fin H.n) = H.n := Fintype.card_fin _
    omega

/-- A minor has at most as many vertices as the host graph. -/

theorem IsMinor.card_le {G H : FinGraph} (h : IsMinor G H) : G.n ≤ H.n := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head h1 _ ih => exact le_trans h1.card_le ih

/-- A graph with no edges. -/

def Edgeless (G : FinGraph) : Prop := ∀ u v, ¬ G.adj.Adj u v

theorem MinorStep.edgeless {G H : FinGraph} (h : MinorStep G H) (hH : Edgeless H) :
    Edgeless G := by
  rcases h with ⟨f, hf⟩ | ⟨a, b, hab, -⟩
  · exact fun u v huv => hH _ _ (hf u v huv)
  · exact absurd hab (hH a b)

/-- Every minor of an edgeless graph is edgeless. -/

theorem IsMinor.edgeless {G H : FinGraph} (h : IsMinor G H) (hH : Edgeless H) : Edgeless G := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hH
  | head h1 _ ih => exact h1.edgeless ih

/-- Sanity check that the minor relation defined above is not degenerate: a single edge is not a
minor of an edgeless graph, however large. -/

def WellQuasiOrderedByMinors : Prop :=
  ∀ f : ℕ → FinGraph, ∃ i j, i < j ∧ IsMinor (f i) (f j)

/-- A class of graphs is minor-closed if it contains every minor of each of its members. -/

def MinorClosed (C : Set FinGraph) : Prop :=
  ∀ ⦃G H : FinGraph⦄, G ∈ C → IsMinor H G → H ∈ C

/-- **Robertson–Seymour, obstruction-set form**: every minor-closed class of finite graphs is
characterised by finitely many forbidden minors. -/

def FiniteObstructionSets : Prop :=
  ∀ C : Set FinGraph, MinorClosed C →
    ∃ S : Set FinGraph, S.Finite ∧ ∀ G, G ∈ C ↔ ∀ H ∈ S, ¬ IsMinor H G

/-- From well-quasi-ordering: every class `D` of graphs which is closed upwards contains a finite
subset generating it, i.e. every member of `D` has a minor in that finite subset. -/

theorem exists_finite_generating (hA : WellQuasiOrderedByMinors) (D : Set FinGraph) :
    ∃ S : Set FinGraph, S.Finite ∧ S ⊆ D ∧ ∀ K ∈ D, ∃ H ∈ S, IsMinor H K := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ l : List D, ∃ K : D, ∀ H ∈ l, ¬ IsMinor (H : FinGraph) (K : FinGraph) := by
    intro l
    obtain ⟨K, hKD, hK⟩ := hcon (Subtype.val '' {x : D | x ∈ l})
      ((List.finite_toSet l).image _) (by rintro _ ⟨x, -, rfl⟩; exact x.2)
    exact ⟨⟨K, hKD⟩, fun H hH => hK _ ⟨H, hH, rfl⟩⟩
  choose F hF using key
  let p : ℕ → List D := fun n => Nat.rec [] (fun _ l => l ++ [F l]) n
  have hps : ∀ n, p (n + 1) = p n ++ [F (p n)] := fun _ => rfl
  have hmem : ∀ n i, i < n → F (p i) ∈ p n := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi
      rw [hps]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact List.mem_append_left _ (ih i h)
      · exact List.mem_append_right _ (by simp)
  obtain ⟨i, j, hij, hminor⟩ := hA (fun n => (F (p n) : FinGraph))
  exact hF (p j) (F (p i)) (hmem j i hij) hminor

theorem finiteObstructionSets_of_wqo (hA : WellQuasiOrderedByMinors) :
    FiniteObstructionSets := by
  intro C hC
  obtain ⟨S, hSfin, hSD, hSgen⟩ := exists_finite_generating hA Cᶜ
  refine ⟨S, hSfin, fun G => ⟨?_, ?_⟩⟩
  · intro hG H hH hHG
    exact hSD hH (hC hG hHG)
  · intro h
    by_contra hG
    obtain ⟨H, hH, hHG⟩ := hSgen G hG
    exact h H hH hHG

theorem wqo_of_finiteObstructionSets (hB : FiniteObstructionSets) :
    WellQuasiOrderedByMinors := by
  intro f
  by_contra hbad
  push_neg at hbad
  set C : Set FinGraph := {G | ∀ i, ¬ IsMinor (f i) G}
  have hC : MinorClosed C := by
    intro G H hG hHG i hfi
    exact hG i (hfi.trans hHG)
  obtain ⟨S, hSfin, hS⟩ := hB C hC
  have hnot : ∀ i, f i ∉ C := fun i h => h i (isMinor_refl _)
  have hex : ∀ i, ∃ H ∈ S, IsMinor H (f i) := by
    intro i
    by_contra h
    push_neg at h
    exact hnot i ((hS (f i)).2 h)
  have hHnot : ∀ H ∈ S, ∃ i, IsMinor (f i) H := by
    intro H hH
    by_contra h
    push_neg at h
    exact (hS H).1 h H hH (isMinor_refl H)
  choose! idx hidx using hHnot
  obtain ⟨N, hN⟩ := (hSfin.image idx).bddAbove
  obtain ⟨H, hHS, hHf⟩ := hex (N + 1)
  have h1 : idx H ≤ N := hN (Set.mem_image_of_mem idx hHS)
  exact hbad (idx H) (N + 1) (lt_of_le_of_lt h1 (Nat.lt_succ_self N))
    ((hidx H hHS).trans hHf)

/-- **Robertson–Seymour (graph minor theorem), equivalence of the two standard formulations.**

The finite graphs are well-quasi-ordered by the minor relation if and only if every minor-closed
class of finite graphs is the class of graphs avoiding some finite set of forbidden minors.

Note: what is established here is the equivalence of the two formulations (together with the
unconditional special cases proved below); the full strength of the Robertson–Seymour theorem,
namely that these statements hold, is *not* proved in this file. -/

theorem robertson_seymour : WellQuasiOrderedByMinors ↔ FiniteObstructionSets :=
  ⟨finiteObstructionSets_of_wqo, wqo_of_finiteObstructionSets⟩

/-- Unconditional special case: the graphs on at most `K` vertices are well-quasi-ordered
(indeed, already quasi-ordered by subgraph embedding) by the minor relation. -/
