import Mathlib
namespace MS.Algebra


theorem freshmans_dream (p : ℕ) [Fact p.Prime] (a b : ZMod p) : (a + b) ^ p = a ^ p + b ^ p :=
  add_pow_char a b p

