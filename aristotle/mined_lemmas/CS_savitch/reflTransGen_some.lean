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

theorem reflTransGen_some (x : List Bool) (u : M.Conf x.length) :
    ∀ w : Vtx M x.length, Relation.ReflTransGen (adjOf (badjT M x)) (some u) w →
      (w = none ∧ ∃ c, Relation.ReflTransGen (M.stepRel x) u c ∧ M.accept x.length c = true) ∨
      (∃ c, w = some c ∧ Relation.ReflTransGen (M.stepRel x) u c) := by
  intro w h
  induction h with
  | refl => exact Or.inr ⟨u, rfl, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    rcases ih with ⟨rfl, -⟩ | ⟨b', rfl, hb'⟩
    · exact absurd hbc (by simp [adjOf, badjT_none])
    · cases c with
      | none =>
        exact Or.inl ⟨rfl, b', hb', by simpa [adjOf, badjT_some_none] using hbc⟩
      | some c' =>
        refine Or.inr ⟨c', rfl, hb'.tail ?_⟩
        simpa [NMachine.stepRel, adjOf, badjT_some_some] using hbc

/-- A computation of `M` lifts to a walk in the extended graph. -/
