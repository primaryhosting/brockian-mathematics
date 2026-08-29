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

theorem exists_involutive_of_hall [DecidableRel G.Adj] (hb : G.IsBipartiteWith A B)
    (hall : ∀ s : Set V, s.ncard ≤ (⋃ v ∈ s, G.neighborSet v).ncard) :
    ∃ sigma : V → V, (∀ v, G.Adj v (sigma v)) ∧ ∀ v, sigma (sigma v) = v := by
  classical
  have hfin : ∀ s : Finset V, s.card ≤ (s.biUnion fun v => G.neighborFinset v).card := by
    intro s
    have h := hall ↑s
    have hset : (⋃ v ∈ (↑s : Set V), G.neighborSet v)
        = ↑(s.biUnion fun v => G.neighborFinset v) := by
      ext y
      simp
    rwa [hset, Set.ncard_coe_finset, Set.ncard_coe_finset] at h
  obtain ⟨f, hinj, hmem⟩ :=
    (hall_exists_injective_iff (fun v => G.neighborFinset v)).mpr hfin
  have hadj : ∀ v, G.Adj v (f v) := fun v => (G.mem_neighborFinset v (f v)).mp (hmem v)
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hinj
  set e : V ≃ V := Equiv.ofBijective f hbij with he
  have hef : ∀ v, e v = f v := fun v => rfl
  have hmemAB : ∀ v, v ∈ A ∨ v ∈ B := by
    intro v
    rcases hb.mem_of_adj (hadj v) with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hfA : ∀ v ∈ A, f v ∈ B := fun v hv => hb.mem_of_mem_adj hv (hadj v)
  have hfB : ∀ v ∈ B, f v ∈ A := fun v hv => hb.symm.mem_of_mem_adj hv (hadj v)
  have hnotA : ∀ v ∈ B, v ∉ A := fun v hv hv' => (Set.disjoint_left.mp hb.disjoint hv') hv
  refine ⟨fun v => if v ∈ A then f v else e.symm v, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ A
    · simpa [hv] using hadj v
    · have hvB : v ∈ B := (hmemAB v).resolve_left hv
      have hfe : f (e.symm v) = v := by
        rw [← hef]; exact e.apply_symm_apply v
      have := hadj (e.symm v)
      rw [hfe] at this
      simpa [hv] using this.symm
  · intro v
    by_cases hv : v ∈ A
    · have h1 : f v ∉ A := hnotA _ (hfA v hv)
      simp only [hv, if_true, h1, if_false]
      rw [← hef v, e.symm_apply_apply]
    · have hvB : v ∈ B := (hmemAB v).resolve_left hv
      have hfe : f (e.symm v) = v := by
        rw [← hef]; exact e.apply_symm_apply v
      have hsA : e.symm v ∈ A := by
        rcases hmemAB (e.symm v) with h | h
        · exact h
        · exact absurd (hfe ▸ hfB _ h) hv
      simp only [hv, if_false, hsA, if_true, hfe]

/-- **Hall's marriage theorem** for bipartite graphs: a bipartite graph (on a finite vertex type,
with parts `A` and `B`) has a perfect matching if and only if Hall's condition holds, i.e. every
set of vertices has at least as many neighbours as it has elements. -/
