import Mathlib
namespace Brockian.LteTwo

/-- Auxiliary: the integer form of lifting-the-exponent at `p = 2`, phrased with
`emultiplicity`.  This is exactly `Int.two_pow_sub_pow'` from Mathlib. -/

theorem lte_two {a b n : ℕ} (ha : Odd a) (hb : Odd b) (hab : 4 ∣ (a - b))
    (hlt : b < a) (hn : 0 < n) :
    (a ^ n - b ^ n).factorization 2 = (a - b).factorization 2 + n.factorization 2 := by
  simp only [factorization_two]
  exact padicValNat_two_pow_sub_pow n ha hab hlt hn

end Brockian.LteTwo

