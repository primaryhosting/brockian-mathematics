import RequestProject.Counting

/-!
# Soundness of the counting machine

We define an invariant of the states of the counting machine which is satisfied by the
initial state and preserved by every transition, and which guarantees, in the accepting
phase, that no accepting vertex is reachable.
-/

open scoped Classical

namespace CS
namespace IS

open Data

variable (G : Data) (x : List Bool)

/-- The invariant of the inner loop: the vertices counted so far form a set `S` of vertices
`< u` reachable in `i` steps, and the flag correctly records whether one of them witnesses
the reachability of `v` in `i+1` steps. -/

theorem machine_complete (hnoacc : ¬ ∃ q, G.accV q ∧ G.Reachable x q) :
    (machine G).Accepts x := by
  have hn : ¬ ∃ q, G.accV q ∧ G.Rch x G.N q := by
    rintro ⟨q, hq, hqr⟩
    exact hnoacc ⟨q, hq, (Rch_iff_reachable q).1 hqr⟩
  refine ⟨mkA G, rfl, ?_⟩
  show MR G x (startA G) (mkA G)
  have hb : G.cnt x G.N G.N ≤ G.N := cnt_le _ _
  have h0 : startA G = mkO G 0 (G.cnt x 0 G.N) 0 0 := by
    rw [cnt_zero_eq]; rfl
  rw [h0]
  refine Relation.ReflTransGen.trans (round_reach G.N 0 (by omega)) ?_
  have hstep : (machine G).edge x (mkO G G.N (G.cnt x G.N G.N) 0 0)
      (mkF G (G.cnt x G.N G.N) 0 0) := by
    rw [edge_iff]
    refine Or.inr <| Or.inr <| Or.inl ⟨rfl, ?_, rfl, ?_, ?_, ?_⟩
    · mkfin
    · mkfin
    · mkfin
    · mkfin
  refine Relation.ReflTransGen.head hstep ?_
  have h1 : mkF G (G.cnt x G.N G.N) 0 0 = mkF G (G.cnt x G.N G.N) 0 (G.cnt x G.N 0) := by
    rw [cnt_zero_index]
  rw [h1]
  exact final_reach hn rfl G.N 0 (by omega)

end IS
end CS

import RequestProject.Model

/-!
# Bounded reachability in a configuration graph

We work with an abstract configuration graph whose vertices are the natural numbers
`< N` (packaged in the structure `CS.IS.Data`).  `Ed b u v` says that there is an edge from
`u` to `v` when the symbol read at `u` is `b`; the symbol actually read is the one at input
position `pos u`.

`G.Rch x i v` says that `v` is reachable from the start vertex `st0` in at most `i` steps.
The main result of this file is `Data.Rch_iff_reachable`: reachability is the same thing as
reachability in at most `N` steps.
-/

open scoped Classical

namespace CS
namespace IS

/-- An (input dependent) configuration graph on the vertex set `{0, …, N-1}`. -/
structure Data where
  /-- number of vertices -/
  N : ℕ
  /-- the start vertex -/
  st0 : ℕ
  /-- the input position read at a vertex -/
  pos : ℕ → ℕ
  /-- the edge relation, depending on the symbol read at the source vertex -/
  Ed : Option Bool → ℕ → ℕ → Prop
  /-- the accepting vertices -/
  accV : ℕ → Prop
  /-- the start vertex is a vertex -/
  hst0 : st0 < N
  /-- edges only connect vertices -/
  hEd : ∀ b u v, Ed b u v → u < N ∧ v < N

namespace Data

variable (G : Data) (x : List Bool)

/-- The edge relation of the configuration graph on input `x`. -/
