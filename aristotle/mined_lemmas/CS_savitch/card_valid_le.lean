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

theorem card_valid_le [Finite X] (K N : ℕ) :
    Nat.card {s : SState X // Valid K N s} ≤
      ((K + 1) * Nat.card X * Nat.card X * (N + 1) * 2 + 1) ^ (K + 1) * 3 := by
  have h := Nat.card_le_card_of_injective _ (encodeValid_injective (X := X) K N)
  refine h.trans (le_of_eq ?_)
  rw [Nat.card_prod, Nat.card_fun, Finite.card_option, Finite.card_option]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_bool]
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_bool]
  ring

end Savitch
end CS

