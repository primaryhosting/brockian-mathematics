import Mathlib
import Brockian.ConstellationGateClose
import Brockian.SieveSpectrumDeletion

/-!
# Twin-wheel components have at most three vertices

For a wheel `15 * Q` with `15` coprime to `Q`, the canonical block coordinates identify every
twin-admissible vertex with a surviving site `(b, j) : ZMod Q x Fin 3`. Adjacency preserves `b`.
Consequently every connected component injects into `Fin 3`, so its cardinality is exactly one,
two, or three.

This is the missing component-level form of the modulo-5 run cap. It is stated directly for the
actual graph `ConstellationPaths.G (15 * Q)` consumed by the matrix factorization.
-/

namespace Brockian.ConstellationComponentPaths

open SimpleGraph
open Brockian.ConstellationGraph
open Brockian.ConstellationGraphAcyclic
open Brockian.ConstellationPaths
open Brockian.GraphComponentMatrix
open Brockian.SieveSpectrumBlocks
open Brockian.SieveSpectrumDeletion

noncomputable section

local instance instDecidableEqConnectedComponent (Q : Nat) [NeZero Q] :
    DecidableEq (G (15 * Q)).ConnectedComponent :=
  Classical.decEq _

abbrev WheelVertex (Q : Nat) [NeZero Q] :=
  {a : ZMod (15 * Q) // twinAdm a}

/-- The twin-graph vertex subtype and the deletion module's wheel-site subtype are definitionally
the same predicate. -/
def vertexWheelEquiv (Q : Nat) [NeZero Q] : WheelVertex Q ≃ WheelSite Q :=
  Equiv.refl _

/-- Canonical surviving block coordinates for an actual twin-graph vertex. -/
def vertexBlockEquiv (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :
    WheelVertex Q ≃ BlockSite Q h15 :=
  (vertexWheelEquiv Q).trans (blockSiteEquiv Q h15).symm

/-- The `(block, lane)` coordinate of an actual twin-graph vertex. -/
def blockCoord (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (v : WheelVertex Q) : ZMod Q × Fin 3 :=
  (vertexBlockEquiv Q h15 v).1

def blockBase (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (v : WheelVertex Q) : ZMod Q :=
  (blockCoord Q h15 v).1

def blockLane (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (v : WheelVertex Q) : Fin 3 :=
  (blockCoord Q h15 v).2

theorem blockCoord_injective (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :
    Function.Injective (blockCoord Q h15) := by
  intro v w hvw
  apply (vertexBlockEquiv Q h15).injective
  apply Subtype.ext
  exact hvw

private theorem path3Adj_irrefl (i : Fin 3) : ¬Path3Adj i i := by
  fin_cases i <;> simp [Path3Adj]

/-- The canonical three-lane path used by the block coordinates. -/
abbrev lanePathGraph : SimpleGraph (Fin 3) := SimpleGraph.pathGraph 3

theorem lanePathGraph_adj (i j : Fin 3) :
    lanePathGraph.Adj i j ↔ Path3Adj i j := by
  fin_cases i <;> fin_cases j <;>
    simp [lanePathGraph, SimpleGraph.pathGraph_adj, Path3Adj]

/-- The canonical lane path embeds in the integer line by its lane index. -/
def lanePathGraphEmbedding : lanePathGraph ↪g intLine where
  toFun i := (i.1 : Int)
  inj' := fun _ _ h => Fin.ext (Int.ofNat_inj.mp h)
  map_rel_iff' := by
    intro i j
    rw [intLine_adj, SimpleGraph.pathGraph_adj]
    norm_num
    omega

theorem lanePathGraph_isAcyclic : lanePathGraph.IsAcyclic :=
  intLine_isAcyclic.comap lanePathGraphEmbedding.toHom lanePathGraphEmbedding.injective

private theorem blockSiteMap_vertexBlockEquiv
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) (v : WheelVertex Q) :
    blockSiteMap Q h15 (vertexBlockEquiv Q h15 v) = vertexWheelEquiv Q v := by
  exact (blockSiteEquiv Q h15).apply_symm_apply (vertexWheelEquiv Q v)

/-- Adjacency in the actual twin graph is exactly path adjacency in canonical block coordinates. -/
theorem G_adj_iff_blockAdj
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) (v w : WheelVertex Q) :
    (G (15 * Q)).Adj v w ↔ BlockAdj (blockCoord Q h15 v) (blockCoord Q h15 w) := by
  let x : BlockSite Q h15 := vertexBlockEquiv Q h15 v
  let y : BlockSite Q h15 := vertexBlockEquiv Q h15 w
  have hx : blockSiteMap Q h15 x = vertexWheelEquiv Q v := by
    simpa [x] using blockSiteMap_vertexBlockEquiv Q h15 v
  have hy : blockSiteMap Q h15 y = vertexWheelEquiv Q w := by
    simpa [y] using blockSiteMap_vertexBlockEquiv Q h15 w
  rw [G_adj]
  constructor
  · intro h
    have hwheel : WheelAdj (blockSiteMap Q h15 x).1 (blockSiteMap Q h15 y).1 := by
      rw [hx, hy]
      change WheelAdj (v : ZMod (15 * Q)) (w : ZMod (15 * Q))
      rcases h.1 with hstep | hstep
      · left
        linear_combination hstep
      · right
        linear_combination hstep
    simpa [x, y, blockCoord] using
      (blockSite_wheelAdj_iff Q h15 x y).mp hwheel
  · intro h
    have hblock : BlockAdj x.1 y.1 := by
      simpa [x, y, blockCoord] using h
    have hwheel := (blockSite_wheelAdj_iff Q h15 x y).mpr hblock
    rw [hx, hy] at hwheel
    change WheelAdj (v : ZMod (15 * Q)) (w : ZMod (15 * Q)) at hwheel
    refine ⟨?_, ?_⟩
    · rcases hwheel with hstep | hstep
      · left
        linear_combination hstep
      · right
        linear_combination hstep
    · intro hvw
      have hxy : x.1 = y.1 := by
        have hvw' : v = w := Subtype.ext hvw
        have hcoord := congrArg (vertexBlockEquiv Q h15) hvw'
        exact congrArg Subtype.val hcoord
      have hlane : Path3Adj x.1.2 x.1.2 := by
        simpa [hxy] using hblock.2
      exact path3Adj_irrefl x.1.2 hlane

/-- The block index is constant along every graph walk. -/
theorem blockBase_eq_of_reachable
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) {v w : WheelVertex Q}
    (h : (G (15 * Q)).Reachable v w) :
    blockBase Q h15 v = blockBase Q h15 w := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | @cons u v w huv p ih =>
      exact ((G_adj_iff_blockAdj Q h15 u v).mp huv).1.trans ih

/-- Every connected component embeds into its three possible lane positions. -/
def componentLaneEmbedding
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (c : (G (15 * Q)).ConnectedComponent) :
    ComponentFiber (G (15 * Q)) c ↪ Fin 3 where
  toFun v := blockLane Q h15 v.1
  inj' := by
    intro v w hlane
    apply Subtype.ext
    apply blockCoord_injective Q h15
    apply Prod.ext
    · apply blockBase_eq_of_reachable Q h15
      apply ConnectedComponent.exact
      exact v.2.trans w.2.symm
    · exact hlane

/-- Each actual connected component is an induced subgraph of the canonical three-lane path. -/
def componentLaneGraphEmbedding
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (c : (G (15 * Q)).ConnectedComponent) :
    componentGraph (G (15 * Q)) c ↪g lanePathGraph where
  toFun v := componentLaneEmbedding Q h15 c v
  inj' := (componentLaneEmbedding Q h15 c).injective
  map_rel_iff' := by
    intro v w
    rw [lanePathGraph_adj]
    change Path3Adj (blockLane Q h15 v.1) (blockLane Q h15 w.1) ↔
      (G (15 * Q)).Adj v.1 w.1
    rw [G_adj_iff_blockAdj Q h15]
    have hbase : blockBase Q h15 v.1 = blockBase Q h15 w.1 := by
      apply blockBase_eq_of_reachable Q h15
      apply ConnectedComponent.exact
      exact v.2.trans w.2.symm
    change Path3Adj (blockLane Q h15 v.1) (blockLane Q h15 w.1) ↔
      blockBase Q h15 v.1 = blockBase Q h15 w.1 ∧
        Path3Adj (blockLane Q h15 v.1) (blockLane Q h15 w.1)
    exact ⟨fun h => ⟨hbase, h⟩, And.right⟩

/-- In particular, every actual component is acyclic; this rules out the three-vertex triangle. -/
theorem componentGraph_isAcyclic
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (c : (G (15 * Q)).ConnectedComponent) :
    (componentGraph (G (15 * Q)) c).IsAcyclic :=
  lanePathGraph_isAcyclic.comap (componentLaneGraphEmbedding Q h15 c).toHom
    (componentLaneGraphEmbedding Q h15 c).injective

/-- Every actual twin-wheel component has at most three vertices. -/
theorem component_card_le_three
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (c : (G (15 * Q)).ConnectedComponent) :
    Fintype.card (ComponentFiber (G (15 * Q)) c) ≤ 3 := by
  simpa using Fintype.card_le_of_injective (componentLaneEmbedding Q h15 c)
    (componentLaneEmbedding Q h15 c).injective

/-- Connected-component fibers are nonempty. -/
theorem componentFiber_nonempty {V : Type*} (G' : SimpleGraph V)
    (c : G'.ConnectedComponent) : Nonempty (ComponentFiber G' c) := by
  obtain ⟨v, rfl⟩ := Quot.exists_rep c
  exact ⟨⟨v, rfl⟩⟩

/-- Every actual twin-wheel component has exactly one, two, or three vertices. -/
theorem component_card_cases
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (c : (G (15 * Q)).ConnectedComponent) :
    Fintype.card (ComponentFiber (G (15 * Q)) c) = 1 ∨
      Fintype.card (ComponentFiber (G (15 * Q)) c) = 2 ∨
      Fintype.card (ComponentFiber (G (15 * Q)) c) = 3 := by
  haveI : Nonempty (ComponentFiber (G (15 * Q)) c) := componentFiber_nonempty _ c
  have hpos : 0 < Fintype.card (ComponentFiber (G (15 * Q)) c) := Fintype.card_pos
  have hle := component_card_le_three Q h15 c
  omega

/-- The induced graph on every connected-component fiber is connected. -/
theorem componentGraph_connected {V : Type*} [Fintype V] [DecidableEq V]
    (G' : SimpleGraph V) (c : G'.ConnectedComponent) :
    (componentGraph G' c).Connected := by
  exact c.connected_toSimpleGraph

end

end Brockian.ConstellationComponentPaths
