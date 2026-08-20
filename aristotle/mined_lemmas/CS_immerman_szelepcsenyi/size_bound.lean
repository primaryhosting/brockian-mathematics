import RequestProject.Machine

/-!
# The inductive counting construction

Given a nondeterministic branching program we build, by Immerman and Szelepcsényi's
inductive counting method, a nondeterministic branching program of polynomially larger
size accepting exactly the complementary language.
-/

namespace CS

namespace Compl

variable {n : ℕ} (P : Setup n)

/-! ### The invariant -/

variable (x : Fin n → Bool)

/-- The set of configurations of the original machine reachable in at most `i` steps. -/

lemma size_bound (c k S n : ℕ) (h : S ≤ c * (n + 1) ^ k) :
    10 * (S + 1) ^ 8 ≤ (10 * (c + 1) ^ 8) * (n + 1) ^ (k * 8) := by
  have hp : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have h1 : S + 1 ≤ (c + 1) * (n + 1) ^ k := by
    calc S + 1 ≤ c * (n + 1) ^ k + (n + 1) ^ k := by omega
      _ = (c + 1) * (n + 1) ^ k := by ring
  calc 10 * (S + 1) ^ 8 ≤ 10 * ((c + 1) * (n + 1) ^ k) ^ 8 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 8)
    _ = 10 * (c + 1) ^ 8 * ((n + 1) ^ k) ^ 8 := by rw [mul_pow]; ring
    _ = 10 * (c + 1) ^ 8 * (n + 1) ^ (k * 8) := by rw [← pow_mul]

/-- Nondeterministic logarithmic space is closed under complement. -/
