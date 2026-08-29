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

theorem savitch_exponent_le (c F : ℕ) :
    (4 * (c * F + c) + 7) * ((c * F + c) + 2) + 2 ≤
      (16 * c ^ 2 + 30 * c + 16) * F ^ 2 + (16 * c ^ 2 + 30 * c + 16) := by
  have h1 : 2 * F ≤ F ^ 2 + 1 := two_mul_le_sq_add_one F
  have h2 : F ≤ F ^ 2 + 1 := by omega
  nlinarith [Nat.zero_le c, Nat.zero_le F, sq_nonneg c, Nat.zero_le (c * F),
    Nat.zero_le (c ^ 2 * F), Nat.zero_le (c ^ 2 * F ^ 2)]

/-! ### The number of configurations of the simulating machine -/

