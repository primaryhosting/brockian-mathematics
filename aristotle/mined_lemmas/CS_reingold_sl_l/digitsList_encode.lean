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

theorem digitsList_encode {d : Nat} (hd : 0 < d) (l : List (Fin d)) :
    digitsList hd (encode l) l.length = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have ha : a.1 < d := a.2
      have h0 : digitF hd (encode (a :: l)) 0 = a := by
        apply Fin.ext
        show (a.1 + d * encode l) / d ^ 0 % d = a.1
        rw [Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
      have h1 : encode (a :: l) / d = encode l := by
        show (a.1 + d * encode l) / d = encode l
        rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt ha, Nat.zero_add]
      show digitF hd (encode (a :: l)) 0 :: digitsList hd (encode (a :: l) / d) l.length
          = a :: l
      rw [h0, h1, ih]

/-! ## The algorithm -/

namespace RotGraph

/-- The walk from `s` following the first `k` digits of `c` in base `d` as edge labels. -/
