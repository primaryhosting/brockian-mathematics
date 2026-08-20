import Mathlib
namespace Frontier.NTClassics

theorem fermat_little (p : ℕ) (hp : p.Prime) (a : ℤ) : a^p ≡ a [ZMOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : ((a ^ p : ℤ) : ZMod p) = ((a : ℤ) : ZMod p) := by
    push_cast
    exact ZMod.pow_card (a : ZMod p)
  exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp h
