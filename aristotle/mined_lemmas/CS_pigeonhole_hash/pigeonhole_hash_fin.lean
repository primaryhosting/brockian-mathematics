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

theorem pigeonhole_hash_fin (n : ℕ) (f : Fin (n + 1) → Fin n) :
    ∃ a b : Fin (n + 1), a ≠ b ∧ f a = f b :=
  pigeonhole_hash_fintype (Fintype.card_fin _) (Fintype.card_fin _) f

end CS

