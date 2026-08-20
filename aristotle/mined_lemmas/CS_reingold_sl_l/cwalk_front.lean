/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (it uses only the Lean 4 core library), so that the
required header comment above can literally be the first thing in the file.
-/

namespace CS

/-! ## Counting -/

/-- `HasCard α N` says that the type `α` embeds into `Fin N`; i.e. `α` has at most `N`
elements, so an element of `α` can be stored in `⌈log₂ N⌉` bits. -/

theorem cwalk_front {n d : Nat} (G : RotGraph n d) (hd : 0 < d) (s : Fin n) (c k : Nat) :
    G.cwalk hd s c (k + 1) = G.cwalk hd (G.step1 s (digitF hd c 0)) (c / d) k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      have hdig : digitF hd (c / d) k = digitF hd c (k + 1) := by
        apply Fin.ext
        show c / d / d ^ k % d = c / d ^ (k + 1) % d
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (d ^ k) d]
      show G.step1 (G.cwalk hd s c (k + 1)) (digitF hd c (k + 1))
          = G.step1 (G.cwalk hd (G.step1 s (digitF hd c 0)) (c / d) k) (digitF hd (c / d) k)
      rw [ih, hdig]

