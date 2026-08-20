import Mathlib
namespace MS2.NT2


theorem lucas_theorem_eq (p : ℕ) [Fact p.Prime] (a b : ℕ) (ha : a < p ^ 64) (hb : b < p ^ 64) :
    (Nat.choose a b : ZMod p) =
      ∏ i ∈ Finset.range 64, ((Nat.choose ((a/p^i)%p) ((b/p^i)%p)) : ZMod p) := by
  have h := Choose.choose_modEq_prod_range_choose_nat (p := p) ha hb
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h
  push_cast at h2
  exact h2

