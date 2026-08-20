import Mathlib
namespace MS2.NT2

theorem chinese_remainder (m n : ℕ) (h : Nat.Coprime m n) :
    Nonempty (ZMod (m*n) ≃+* ZMod m × ZMod n) :=
  ⟨ZMod.chineseRemainder h⟩
