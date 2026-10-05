import Mathlib
/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
A self-contained development of Hall's marriage theorem.

* `Math.hall_exists_injective_iff` : the combinatorial ("system of distinct representatives")
  form, proved from scratch by induction (it does *not* use Mathlib's Hall theorem).
* `Math.halls_marriage` : a bipartite graph has a perfect matching iff Hall's condition holds.
-/

namespace Math

open Finset

section Core

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

omit [DecidableEq ι] in

theorem hall_condition_of_isPerfectMatching {M : G.Subgraph} (hM : M.IsPerfectMatching)
    (s : Set V) : s.ncard ≤ (⋃ v ∈ s, G.neighborSet v).ncard := by
  classical
  have hM' := Subgraph.isPerfectMatching_iff.mp hM
  choose g hg huniq using hM'
  refine Set.ncard_le_ncard_of_injOn g (fun v hv => ?_) (fun a _ b _ hab => ?_) (Set.toFinite _)
  · exact Set.mem_biUnion hv (M.adj_sub (hg v))
  · have ha : M.Adj (g a) a := (hg a).symm
    have hb : M.Adj (g b) b := (hg b).symm
    rw [hab] at ha
    exact ((huniq (g b) a ha).trans (huniq (g b) b hb).symm)

omit [Fintype V] [DecidableEq V] in
/-- From an adjacency-respecting involution one builds a perfect matching. -/
