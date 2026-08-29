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

theorem reach_iff_reflTransGen [Finite X] {k : ℕ} (hk : Nat.card X ≤ 2 ^ k) (u v : X) :
    Reach adj k u v ↔ Relation.ReflTransGen adj u v := by
  constructor
  · intro h
    obtain ⟨m, _, hp⟩ := (reach_iff_exists_pathTo k u v).1 h
    exact hp.reflTransGen
  · intro h
    obtain ⟨m, hm, hp⟩ := exists_short_pathTo h
    exact (reach_iff_exists_pathTo k u v).2 ⟨m, by omega, hp⟩

end Savitch
end CS

import Mathlib

/-!
# A space-bounded machine model

We use the standard "configuration graph" presentation of space bounded computation.

A machine is given, for every input length `n`, by a *finite* set of configurations `Conf n`.
The machine reads its input only through an input head: the position of the head is a function
of the current configuration, and the transition function/relation may depend on the input only
through the symbol currently scanned.  The *space* used by the machine on inputs of length `n`
is (up to a constant factor) `log₂ (Nat.card (Conf n))`, which is how the space classes below
are defined: a machine runs in space `O(s)` if it has at most `2 ^ (c * s n + c)` configurations.

This is the usual abstraction of space-bounded computation by its configuration graph; it is
non-uniform (the configuration graph may depend on `n` in an arbitrary way), which is the
standard setting in which Savitch's argument is a purely graph-theoretic statement about
reachability.
-/

namespace CS

/-- `readBit x i` is the `i`-th symbol of the input word `x`; positions past the end read `false`
(the blank symbol). -/
