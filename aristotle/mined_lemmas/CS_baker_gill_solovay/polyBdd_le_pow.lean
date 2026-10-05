import RequestProject.QueryProg
import RequestProject.Aux

/-!
# An oracle `A` with `P^A = NP^A`

The oracle answers questions about its own relativized nondeterministic
computations.  This is well defined because the query `encodeQ i x t` is *longer*
than any string that can be queried during a computation of cost at most `t` on
input `x`, so the definition can be made by recursion on the length of the query.
-/

namespace CS

open Prog

/-- `AAux n z` is the value of the oracle at `z`, where `n` is the length of `z`;
the recursive calls are only made at strictly shorter strings. -/

theorem polyBdd_le_pow {f : ℕ → ℕ} (hf : PolyBdd f) : ∃ m, ∀ n, f n ≤ (n + 2) ^ m := by
  obtain ⟨c, k, hc⟩ := hf
  refine ⟨k + c, fun n => ?_⟩
  have h1 : c * (n + 1) ^ k ≤ (n + 2) ^ k * (n + 2) ^ c := by
    have e1 : (n + 1) ^ k ≤ (n + 2) ^ k := Nat.pow_le_pow_left (by omega) k
    have e2 : c ≤ (n + 2) ^ c := by
      calc c ≤ 2 ^ c := le_of_lt (Nat.lt_two_pow_self)
        _ ≤ (n + 2) ^ c := Nat.pow_le_pow_left (by omega) c
    calc c * (n + 1) ^ k ≤ (n + 2) ^ c * (n + 2) ^ k := Nat.mul_le_mul e2 e1
      _ = (n + 2) ^ k * (n + 2) ^ c := by ring
  calc f n ≤ c * (n + 1) ^ k := hc n
    _ ≤ (n + 2) ^ k * (n + 2) ^ c := h1
    _ = (n + 2) ^ (k + c) := by rw [pow_add]

/-- The initial configuration on input `x` with guess string `cert`. -/
