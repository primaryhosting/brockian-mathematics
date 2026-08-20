import Mathlib
namespace Brockian.MsThue

/-- Pigeonhole step: there are more than `n` pairs `(i, j)` with `0 ≤ i, j ≤ √n`, so two
    distinct such pairs give the same value of `i - a * j` in `ZMod n`. -/

private lemma thue_pigeonhole (n a : ℕ) (hn : 1 < n) :
    ∃ p q : Fin (Nat.sqrt n + 1) × Fin (Nat.sqrt n + 1), p ≠ q ∧
      ((p.1 : ZMod n) - a * (p.2 : ZMod n) = (q.1 : ZMod n) - a * (q.2 : ZMod n)) := by
  -- The number of pairs is `(√n + 1)^2 > n`, the number of values in `ZMod n`.
  haveI : NeZero n := ⟨by omega⟩
  have hcard :
      Fintype.card (ZMod n) < Fintype.card (Fin (Nat.sqrt n + 1) × Fin (Nat.sqrt n + 1)) := by
    simpa [ZMod.card] using Nat.lt_succ_sqrt n
  exact Fintype.exists_ne_map_eq_of_card_lt
    (fun p => (p.1 : ZMod n) - a * (p.2 : ZMod n)) hcard

/-- Thue's lemma: for n > 1 and any a, there exist x, y not both zero with |x|,|y| ≤ √n and
    x ≡ a·y (mod n). -/
