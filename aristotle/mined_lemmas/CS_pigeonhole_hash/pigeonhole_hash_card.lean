import Mathlib
import RequestProject.Main

/-!
# Pigeonhole Hash — generalisation to arbitrary finite types

A Mathlib-based restatement of `CS.pigeonhole_hash` for arbitrary finite key and value
types, derived from the core-library version proved in `RequestProject/Main.lean`.
-/

namespace CS

/-- Any hash function from a set of `n + 1` keys to a set of `n` hash values has a
collision. -/

theorem pigeonhole_hash_card {K V : Type*} [Fintype K] [Fintype V] {n : ℕ}
    (hK : Fintype.card K = n + 1) (hV : Fintype.card V = n) (f : K → V) :
    ∃ a b : K, a ≠ b ∧ f a = f b := by
  -- transport along equivalences `K ≃ Fin (n+1)` and `V ≃ Fin n`
  classical
  obtain ⟨eK⟩ := (Fintype.truncEquivFinOfCardEq (α := K) hK).nonempty
  obtain ⟨eV⟩ := (Fintype.truncEquivFinOfCardEq (α := V) hV).nonempty
  obtain ⟨a, b, hab, hfab⟩ := pigeonhole_hash n (fun i => eV (f (eK.symm i)))
  refine ⟨eK.symm a, eK.symm b, ?_, ?_⟩
  · exact fun h => hab (eK.symm.injective h)
  · exact eV.injective hfab

end CS

/-!
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first commands of a
file, and a module docstring `/-! ... -/` counts as a command. Since the mandated header
above must literally begin the file, this module carries no imports and the proof is
developed from the Lean 4 core library only. A Mathlib-based generalisation to arbitrary
finite types is given in `RequestProject/Card.lean`.
-/

namespace CS

/-- `shrink v x` deletes the value `v` from the range of possible values:
values below `v` are kept, values above `v` are shifted down by one. -/
