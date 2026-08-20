import Mathlib
namespace MS2.NT2


theorem euler_theorem (n : ℕ) (a : ZMod n) (ha : IsUnit a) : a ^ (Nat.totient n) = 1 := by
  obtain ⟨u, rfl⟩ := ha
  rw [← Units.val_pow_eq_pow_val, ZMod.pow_totient u, Units.val_one]

