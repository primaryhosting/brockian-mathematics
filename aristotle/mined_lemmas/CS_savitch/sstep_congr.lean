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

theorem sstep_congr {b1 b2 : X → X → Bool} {s : SState X}
    (h : ∀ f rest, s.stack = f :: rest → ∀ w, b1 f.u w = b2 f.u w) :
    sstep b1 l s = sstep b2 l s := by
  obtain ⟨stack, ret⟩ := s
  cases stack with
  | nil => rfl
  | cons f rest =>
    obtain ⟨lvl, u, v, mid, ph⟩ := f
    cases ret with
    | none =>
      cases lvl with
      | zero =>
        rw [sstep_base, sstep_base, h ⟨0, u, v, mid, ph⟩ rest rfl v]
      | succ k =>
        cases hmid : l[mid]? with
        | none => rw [sstep_call_none hmid, sstep_call_none hmid]
        | some m =>
          cases ph with
          | false => rw [sstep_call_some_false hmid, sstep_call_some_false hmid]
          | true => rw [sstep_call_some_true hmid, sstep_call_some_true hmid]
    | some r =>
      cases ph <;> cases r <;> simp

/-- The adjacency relation determined by the Boolean adjacency test. -/
