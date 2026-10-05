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

theorem accepts_ofDMachine (D : DMachine) (x : List Bool) :
    (NMachine.ofDMachine D).Accepts x ↔ D.Accepts x := by
  have hstep : ∀ u v : D.Conf x.length,
      (NMachine.ofDMachine D).stepRel x u v ↔ v = D.stepFun x u := by
    intro u v
    simp [NMachine.stepRel, NMachine.ofDMachine, DMachine.stepFun, eq_comm]
  constructor
  · rintro ⟨c, hc, hacc⟩
    have : Relation.ReflTransGen (fun u v : D.Conf x.length => v = D.stepFun x u)
        (D.start x.length) c := by
      refine Relation.ReflTransGen.mono ?_ hc
      intro u v h
      exact (hstep u v).1 h
    obtain ⟨t, ht⟩ := (reflTransGen_fun _ _ _).1 this
    exact ⟨t, by rw [ht]; exact hacc⟩
  · rintro ⟨t, ht⟩
    refine ⟨(D.stepFun x)^[t] (D.start x.length), ?_, ht⟩
    refine Relation.ReflTransGen.mono ?_ ((reflTransGen_fun (D.stepFun x) _ _).2 ⟨t, rfl⟩)
    intro u v h
    exact (hstep u v).2 h

/-- Deterministic space is contained in nondeterministic space. -/
