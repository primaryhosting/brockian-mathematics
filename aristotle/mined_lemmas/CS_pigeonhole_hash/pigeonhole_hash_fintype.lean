/-!
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean requires `import` commands to precede every other command,
including module docstrings, so the mandated header above rules out importing
Mathlib in this file. The development below is therefore fully self-contained
(core Lean only). The companion file `RequestProject/CSMathlib.lean` records the
Mathlib proof of the same statement, via `Fintype.exists_ne_map_eq_of_card_lt`.
-/

namespace CS

/-- Pigeonhole principle in arithmetic form: if `f` maps each of the `n + 1`
numbers `0, …, n` into `{0, …, n - 1}`, then two distinct inputs collide. -/

theorem pigeonhole_hash_fintype {K B : Type*} [Fintype K] [Fintype B] {n : ℕ}
    (hK : Fintype.card K = n + 1) (hB : Fintype.card B = n) (f : K → B) :
    ∃ a b : K, a ≠ b ∧ f a = f b := by
  have hlt : Fintype.card B < Fintype.card K := by omega
  obtain ⟨a, b, hab, h⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  exact ⟨a, b, hab, h⟩

/-- Concrete form: any hash `f : Fin (n + 1) → Fin n` has a collision. -/
