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

theorem polyBdd_add {f g : ℕ → ℕ} (hf : PolyBdd f) (hg : PolyBdd g) :
    PolyBdd (fun n => f n + g n) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 + c2, max k1 k2, fun n => ?_⟩
  have e1 : (n + 1) ^ k1 ≤ (n + 1) ^ max k1 k2 :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have e2 : (n + 1) ^ k2 ≤ (n + 1) ^ max k1 k2 :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  calc f n + g n ≤ c1 * (n + 1) ^ k1 + c2 * (n + 1) ^ k2 := Nat.add_le_add (h1 n) (h2 n)
    _ ≤ c1 * (n + 1) ^ max k1 k2 + c2 * (n + 1) ^ max k1 k2 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
    _ = (c1 + c2) * (n + 1) ^ max k1 k2 := by ring

