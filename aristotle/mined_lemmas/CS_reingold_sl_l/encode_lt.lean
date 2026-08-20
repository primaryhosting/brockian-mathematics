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

theorem encode_lt {d : Nat} (hd : 0 < d) (l : List (Fin d)) : encode l < d ^ l.length := by
  induction l with
  | nil => simp [encode]
  | cons a l ih =>
      have ha : a.1 < d := a.2
      have h1 : d * encode l + d ≤ d * d ^ l.length := by
        have h := Nat.mul_le_mul_left d (Nat.succ_le_of_lt ih)
        rw [Nat.mul_succ] at h
        exact h
      have hpow : d ^ (a :: l).length = d * d ^ l.length := by
        simp [List.length_cons, Nat.pow_succ, Nat.mul_comm]
      show a.1 + d * encode l < d ^ (a :: l).length
      rw [hpow]
      omega

