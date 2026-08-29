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

theorem wqo_of_bounded_order (K : ℕ) (f : ℕ → FinGraph) (hf : ∀ i, (f i).n ≤ K) :
    ∃ i j, i < j ∧ IsMinor (f i) (f j) := by
  classical
  set e : ℕ → Fin (K + 1) × (Fin K → Fin K → Bool) := fun i =>
    (⟨(f i).n, Nat.lt_succ_of_le (hf i)⟩,
      fun a b => decide (∃ (ha : (a : ℕ) < (f i).n) (hb : (b : ℕ) < (f i).n),
        (f i).adj.Adj ⟨a, ha⟩ ⟨b, hb⟩)) with he
  have key : ∀ i j : ℕ, e i = e j → IsMinor (f i) (f j) := by
    intro i j hij
    have hn : (f i).n = (f j).n := by
      have := congrArg (fun x => (x.1 : ℕ)) hij
      simpa [he] using this
    have hadj := congrArg Prod.snd hij
    refine isMinor_of_subgraphEmbed ⟨(finCongr hn).toEmbedding, ?_⟩
    intro u v huv
    have hu : (u : ℕ) < K := lt_of_lt_of_le u.isLt (hf i)
    have hv : (v : ℕ) < K := lt_of_lt_of_le v.isLt (hf i)
    have h2 := congrFun (congrFun hadj ⟨u, hu⟩) ⟨v, hv⟩
    simp only [he] at h2
    have h3 : (∃ (ha : (u : ℕ) < (f j).n) (hb : (v : ℕ) < (f j).n),
        (f j).adj.Adj ⟨u, ha⟩ ⟨v, hb⟩) := by
      have h4 : (∃ (ha : (u : ℕ) < (f i).n) (hb : (v : ℕ) < (f i).n),
          (f i).adj.Adj ⟨u, ha⟩ ⟨v, hb⟩) := ⟨u.isLt, v.isLt, by simpa using huv⟩
      have := (decide_eq_decide.mp h2).mp h4
      exact this
    obtain ⟨ha, hb, hadj'⟩ := h3
    simpa [finCongr, Fin.ext_iff] using hadj'
  obtain ⟨i, j, hne, hE⟩ := Finite.exists_ne_map_eq_of_infinite e
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨i, j, h, key i j hE⟩
  · exact ⟨j, i, h, key j i hE.symm⟩

/-- Unconditional special case: any sequence of edgeless graphs (of unbounded size) contains an
earlier member which is a minor of a later one. -/
