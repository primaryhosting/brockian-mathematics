/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-! ## Graphs presented by neighbour maps -/

variable {n D k : ℕ}

/-- `walk nbr v w j` is the vertex reached from `v` after following the first `j`
directions of the direction sequence `w` in the `D`-regular graph given by the
neighbour map `nbr`. -/

private theorem div_mod_succ (hk : 0 < k) (l : ℕ) :
    (l + 1) % k = (l % k + 1) % k ∧ (l + 1) / k = (l % k + 1) / k + l / k := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < k ∧ l = k * q + r :=
    ⟨l / k, l % k, Nat.mod_lt _ hk, (Nat.div_add_mod l k).symm⟩
  have h1 : (k * q + r) % k = r := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have h2 : (k * q + r) / k = q := by
    rw [Nat.mul_add_div hk, Nat.div_eq_of_lt hr, Nat.add_zero]
  rw [h1, h2]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_assoc, Nat.mul_add_mod]
  · rw [Nat.add_assoc, Nat.mul_add_div hk, Nat.add_comm]

/-- The key invariant: after `l` levels the program is at the vertex reached by following
the `(l % k)` first directions of the `(l / k)`-th direction sequence, and its flag records
whether `t` has been met so far. -/
