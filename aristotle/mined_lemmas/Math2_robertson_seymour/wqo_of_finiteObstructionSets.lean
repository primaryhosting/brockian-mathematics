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
