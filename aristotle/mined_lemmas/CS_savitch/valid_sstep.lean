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

theorem valid_sstep {K : ℕ} {s : SState X} (h : Valid K l.length s) :
    Valid K l.length (sstep badj l s) := by
  obtain ⟨stack, ret⟩ := s
  cases stack with
  | nil => exact h
  | cons f rest =>
    obtain ⟨lvl, u, v, mid, ph⟩ := f
    have hlev : LevelsOK K (⟨lvl, u, v, mid, ph⟩ :: rest) := h.levels
    have hmids : ∀ g ∈ (⟨lvl, u, v, mid, ph⟩ :: rest : List (Frame X)), g.mid ≤ l.length := h.mids
    cases ret with
    | none =>
      cases lvl with
      | zero =>
        rw [sstep_base]
        exact ⟨levelsOK_tail hlev, fun g hg => hmids g (List.mem_cons_of_mem _ hg)⟩
      | succ k =>
        cases hmid : l[mid]? with
        | none =>
          rw [sstep_call_none hmid]
          exact ⟨levelsOK_tail hlev, fun g hg => hmids g (List.mem_cons_of_mem _ hg)⟩
        | some m =>
          cases ph with
          | false =>
            rw [sstep_call_some_false hmid]
            refine ⟨⟨rfl, hlev⟩, ?_⟩
            intro g hg
            rcases List.mem_cons.1 hg with rfl | hg'
            · simp
            · exact hmids g hg'
          | true =>
            rw [sstep_call_some_true hmid]
            refine ⟨⟨rfl, hlev⟩, ?_⟩
            intro g hg
            rcases List.mem_cons.1 hg with rfl | hg'
            · simp
            · exact hmids g hg'
    | some r =>
      cases ph with
      | false =>
        cases r with
        | false =>
          rw [sstep_ret_false_false]
          refine ⟨levelsOK_head_mod hlev rfl, ?_⟩
          intro g hg
          rcases List.mem_cons.1 hg with rfl | hg'
          · simp
          · exact hmids g (List.mem_cons_of_mem _ hg')
        | true =>
          rw [sstep_ret_false_true]
          refine ⟨levelsOK_head_mod hlev rfl, ?_⟩
          intro g hg
          rcases List.mem_cons.1 hg with rfl | hg'
          · exact hmids ⟨lvl, u, v, mid, false⟩ (by simp)
          · exact hmids g (List.mem_cons_of_mem _ hg')
      | true =>
        cases r with
        | false =>
          rw [sstep_ret_true_false]
          refine ⟨levelsOK_head_mod hlev rfl, ?_⟩
          intro g hg
          rcases List.mem_cons.1 hg with rfl | hg'
          · simp
          · exact hmids g (List.mem_cons_of_mem _ hg')
        | true =>
          rw [sstep_ret_true_true]
          exact ⟨levelsOK_tail hlev, fun g hg => hmids g (List.mem_cons_of_mem _ hg)⟩

/-- Encoding of a valid configuration by a bounded array of bounded frames; used only to count
configurations. -/
