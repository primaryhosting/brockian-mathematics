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

def readBit (x : List Bool) (i : ℕ) : Bool := x[i]?.getD false

/-- A nondeterministic space-bounded machine, presented by its configuration graph. -/
structure NMachine where
  /-- The set of configurations available on inputs of length `n`. -/
  Conf : ℕ → Type
  /-- There are only finitely many configurations. -/
  finite : ∀ n, Finite (Conf n)
  /-- Position of the input head in a given configuration. -/
  head : ∀ n, Conf n → ℕ
  /-- `next n u b v` says that `v` is a possible successor of `u` when the scanned input symbol
  is `b`. -/
  next : ∀ n, Conf n → Bool → Conf n → Bool
  /-- The initial configuration. -/
  start : ∀ n, Conf n
  /-- The accepting configurations. -/
  accept : ∀ n, Conf n → Bool

/-- The one-step relation of a nondeterministic machine on a fixed input. -/
