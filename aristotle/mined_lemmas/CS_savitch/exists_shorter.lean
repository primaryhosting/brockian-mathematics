/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Savitch.Model
import RequestProject.Savitch.Stack

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

`NSPACE f ⊆ DSPACE (f²)`.

Given a nondeterministic machine with at most `2 ^ (c * f n + c)` configurations we build a
deterministic machine which decides, by Savitch's midpoint recursion, whether an accepting
configuration is reachable in the configuration graph.  The deterministic machine stores an
explicit recursion stack of depth `c * f n + c + 2`, each frame holding a constant number of
configurations and indices, hence it has `2 ^ O(f n ^ 2)` configurations.

As a corollary, `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

section Construction

variable (M : NMachine)

/-- The vertices of the configuration graph: the configurations of `M`, together with an extra
sink `none` which is reachable exactly from the accepting configurations.  Thus `M` accepts iff
the sink is reachable from the initial configuration. -/
abbrev Vtx (M : NMachine) (n : ℕ) : Type := Option (M.Conf n)

instance vtxFinite (n : ℕ) : Finite (Vtx M n) := by
  haveI := M.finite n; infer_instance

noncomputable instance vtxFintype (n : ℕ) : Fintype (Vtx M n) := Fintype.ofFinite _

noncomputable instance vtxDecEq (n : ℕ) : DecidableEq (Vtx M n) := Classical.decEq _

/-- An enumeration of the vertices of the configuration graph. -/

theorem exists_shorter [Finite X] {m : ℕ} {u v : X} (h : PathTo adj m u v)
    (hm : Nat.card X ≤ m) : ∃ m' < m, PathTo adj m' u v := by
  classical
  have : Fintype X := Fintype.ofFinite X
  obtain ⟨g, h0, hm', hs⟩ := h
  subst h0; subst hm'
  have hcard : Fintype.card X < Fintype.card (Fin (m + 1)) := by
    have hnc : Nat.card X = Fintype.card X := Nat.card_eq_fintype_card
    simp only [Fintype.card_fin]
    omega
  obtain ⟨i, j, hij, hgij⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (m + 1) => g i) hcard
  have hne : (i : ℕ) ≠ (j : ℕ) := fun hc => hij (Fin.ext hc)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨(i : ℕ) + (m - (j : ℕ)), by omega, ?_⟩
    have hpi : PathTo adj (i : ℕ) (g 0) (g i) := pathTo_prefix hs (by omega)
    have hpj : PathTo adj (m - (j : ℕ)) (g j) (g m) := pathTo_suffix hs (by omega)
    rw [← hgij] at hpj
    exact hpi.concat hpj
  · refine ⟨(j : ℕ) + (m - (i : ℕ)), by omega, ?_⟩
    have hpj : PathTo adj (j : ℕ) (g 0) (g j) := pathTo_prefix hs (by omega)
    have hpi : PathTo adj (m - (i : ℕ)) (g i) (g m) := pathTo_suffix hs (by omega)
    rw [hgij] at hpi
    exact hpj.concat hpi

/-- In a finite digraph, reachability is witnessed by a walk with fewer edges than there are
vertices. -/
