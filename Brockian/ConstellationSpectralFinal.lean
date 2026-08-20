import Mathlib
import Brockian.ConstellationComponentPaths
import Brockian.ConstellationSpectrumEnvelope
import Brockian.GraphComponentGrouping
import Brockian.SmallConnectedGraphSpectrum

/-!
# Exact component multiplicities and spectrum of the twin-wheel Hamiltonian

For the actual twin-admissible graph on `ZMod (15 * Q)`, every connected component has one, two,
or three vertices. Its Hamiltonian block therefore has the characteristic polynomial of `H1`,
`H2`, or `H3`. Grouping the exact connected-component product gives the full characteristic
polynomial with the actual component multiplicities `n1`, `n2`, and `n3`.

This is a finite, unconditional wheel theorem. It makes no assertion about twin-prime infinitude.
-/

namespace Brockian.ConstellationSpectralFinal

open Polynomial SimpleGraph
open Brockian.ConstellationPaths
open Brockian.ConstellationGateClose
open Brockian.ConstellationComponentPaths
open Brockian.ConstellationSpectrum
open Brockian.ConstellationSpectrumEnvelope
open Brockian.GraphComponentMatrix
open Brockian.GraphComponentGrouping
open Brockian.SmallConnectedGraphSpectrum

noncomputable section

local instance instDecidableEqConnectedComponent (Q : Nat) [NeZero Q] :
    DecidableEq (G (15 * Q)).ConnectedComponent := Classical.decEq _

/-- Actual number of one-vertex components in the twin wheel. -/
def n1 (Q : Nat) [NeZero Q] : Nat :=
  componentCount (G (15 * Q)) 1

/-- Actual number of two-vertex components in the twin wheel. -/
def n2 (Q : Nat) [NeZero Q] : Nat :=
  componentCount (G (15 * Q)) 2

/-- Actual number of three-vertex components in the twin wheel. -/
def n3 (Q : Nat) [NeZero Q] : Nat :=
  componentCount (G (15 * Q)) 3

theorem component_natCard_cases
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (c : (G (15 * Q)).ConnectedComponent) :
    Nat.card (ComponentFiber (G (15 * Q)) c) = 1 ∨
      Nat.card (ComponentFiber (G (15 * Q)) c) = 2 ∨
      Nat.card (ComponentFiber (G (15 * Q)) c) = 3 := by
  simpa only [Nat.card_eq_fintype_card] using component_card_cases Q h15 c

/-- **Explicit component classification.** Every actual connected component is graph-isomorphic
to exactly one of the path graphs on one, two, or three vertices. -/
theorem component_is_P1_or_P2_or_P3
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (c : (G (15 * Q)).ConnectedComponent) :
    Nonempty (componentGraph (G (15 * Q)) c ≃g SimpleGraph.pathGraph 1) ∨
      Nonempty (componentGraph (G (15 * Q)) c ≃g SimpleGraph.pathGraph 2) ∨
      Nonempty (componentGraph (G (15 * Q)) c ≃g SimpleGraph.pathGraph 3) := by
  rcases component_card_cases Q h15 c with h1 | h2 | h3
  · exact Or.inl (nonempty_iso_pathGraph_one _ h1)
  · exact Or.inr (Or.inl
      (nonempty_iso_pathGraph_two _ (componentGraph_connected _ c) h2))
  · exact Or.inr (Or.inr
      (nonempty_iso_pathGraph_three_of_acyclic _ (componentGraph_connected _ c)
        (componentGraph_isAcyclic Q h15 c) h3))

/-- A one-vertex actual component contributes the `H1` factor. -/
theorem component_charpoly_card_one
    (Q : Nat) [NeZero Q] (c : (G (15 * Q)).ConnectedComponent)
    (hc : Fintype.card (ComponentFiber (G (15 * Q)) c) = 1) :
    (shiftedAdjacency (componentGraph (G (15 * Q)) c) (2 : Real)).charpoly =
      H1.charpoly :=
  shiftedAdjacency_charpoly_card_one _ hc

/-- A two-vertex actual component contributes the `H2` factor. -/
theorem component_charpoly_card_two
    (Q : Nat) [NeZero Q] (c : (G (15 * Q)).ConnectedComponent)
    (hc : Fintype.card (ComponentFiber (G (15 * Q)) c) = 2) :
    (shiftedAdjacency (componentGraph (G (15 * Q)) c) (2 : Real)).charpoly =
      H2.charpoly :=
  shiftedAdjacency_charpoly_card_two _ (componentGraph_connected _ c) hc

/-- A three-vertex actual component contributes the `H3` factor. The component's explicit
embedding in the canonical three-lane path supplies the required acyclicity. -/
theorem component_charpoly_card_three
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (c : (G (15 * Q)).ConnectedComponent)
    (hc : Fintype.card (ComponentFiber (G (15 * Q)) c) = 3) :
    (shiftedAdjacency (componentGraph (G (15 * Q)) c) (2 : Real)).charpoly =
      H3.charpoly :=
  shiftedAdjacency_charpoly_card_three_of_acyclic _
    (componentGraph_connected _ c) (componentGraph_isAcyclic Q h15 c) hc

/-- The component-wise Hamiltonian factors regroup exactly according to the actual component
counts `n1`, `n2`, and `n3`. -/
theorem component_charpoly_product
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :
    (∏ c : (G (15 * Q)).ConnectedComponent,
      (shiftedAdjacency (componentGraph (G (15 * Q)) c) (2 : Real)).charpoly) =
      pathBlockCharpoly (n1 Q) (n2 Q) (n3 Q) := by
  rw [pathBlockCharpoly, ← H3_charpoly, ← H2_charpoly, ← H1_charpoly]
  simpa only [n1, n2, n3] using prod_components_eq_three_powers
    (G (15 * Q))
    (Finset.univ : Finset (G (15 * Q)).ConnectedComponent)
    (fun c => Finset.mem_univ c)
    (fun c : (G (15 * Q)).ConnectedComponent =>
      (shiftedAdjacency (componentGraph (G (15 * Q)) c) (2 : Real)).charpoly)
    H1.charpoly H2.charpoly H3.charpoly
    (component_natCard_cases Q h15)
    (fun c hc => component_charpoly_card_one Q c (by
      simpa only [Nat.card_eq_fintype_card] using hc))
    (fun c hc => component_charpoly_card_two Q c (by
      simpa only [Nat.card_eq_fintype_card] using hc))
    (fun c hc => component_charpoly_card_three Q h15 c (by
      simpa only [Nat.card_eq_fintype_card] using hc))

/-- **Exact graph-Hamiltonian characteristic polynomial.** The actual graph operator `2I-A`, not
an assembled surrogate, has the product prescribed by its `P1/P2/P3` component multiplicities. -/
theorem graph_hamiltonian_charpoly
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :
    (graphHamiltonian (15 * Q)).charpoly =
      pathBlockCharpoly (n1 Q) (n2 Q) (n3 Q) := by
  rw [graph_hamiltonian_charpoly_components]
  exact component_charpoly_product Q h15

/-- Expanded form of the exact characteristic polynomial. This exhibits the multiplicities
directly: the `H1`, `H2`, and `H3` factors occur `n1`, `n2`, and `n3` times. -/
theorem graph_hamiltonian_charpoly_explicit
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :
    (graphHamiltonian (15 * Q)).charpoly =
      (X - C 2) ^ n1 Q *
        ((X - C 1) * (X - C 3)) ^ n2 Q *
          ((X - C 2) * (X ^ 2 - C 4 * X + C 2)) ^ n3 Q := by
  simpa only [pathBlockCharpoly] using graph_hamiltonian_charpoly Q h15

/-- Every eigenvalue of the actual twin-wheel Hamiltonian belongs to the five-point alphabet. -/
theorem graph_hamiltonian_spectrum_subset
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) (x : Real)
    (hx : (graphHamiltonian (15 * Q)).charpoly.eval x = 0) :
    x ∈ ({2 - Real.sqrt 2, 1, 2, 3, 2 + Real.sqrt 2} : Set Real) := by
  rw [graph_hamiltonian_charpoly Q h15] at hx
  exact pathBlockCharpoly_root_mem (n1 Q) (n2 Q) (n3 Q) x hx

/-- When both a two-vertex and a three-vertex component occur, the actual graph Hamiltonian has
exactly the full five-point spectral alphabet. -/
theorem graph_hamiltonian_spectrum_iff
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (hn2 : 0 < n2 Q) (hn3 : 0 < n3 Q) (x : Real) :
    (graphHamiltonian (15 * Q)).charpoly.eval x = 0 ↔
      x ∈ ({2 - Real.sqrt 2, 1, 2, 3, 2 + Real.sqrt 2} : Set Real) := by
  rw [graph_hamiltonian_charpoly Q h15]
  exact pathBlockCharpoly_root_iff (n1 Q) (n2 Q) (n3 Q) hn2 hn3 x

/-- The actual vertex count is reconstructed from the three component multiplicities. -/
theorem vertex_count_eq_component_counts
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :
    Fintype.card (WheelVertex Q) = n1 Q + 2 * n2 Q + 3 * n3 Q := by
  simpa only [n1, n2, n3] using
    vertex_card_eq_component_counts (G (15 * Q)) (component_natCard_cases Q h15)

end

end Brockian.ConstellationSpectralFinal
