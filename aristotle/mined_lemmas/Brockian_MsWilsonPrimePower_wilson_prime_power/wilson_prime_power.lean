import Mathlib
namespace Brockian.MsWilsonPrimePower

open Finset

/-- If an odd prime power `p ^ k` divides `(a - 1) * (a + 1)`, then it divides one of the two
factors, since `p` cannot divide both `a - 1` and `a + 1`. -/

theorem wilson_prime_power (p k : ℕ) [NeZero (p ^ k)] (hp : p.Prime) (hodd : Odd p) (hk : 0 < k) :
    (∏ u : (ZMod (p ^ k))ˣ, (u : ZMod (p ^ k))) = -1 := by
  have h := congrArg (fun u : (ZMod (p ^ k))ˣ => (u : ZMod (p ^ k)))
    (prod_units_eq_neg_one p k hp hodd)
  simpa [Units.coe_prod] using h

end Brockian.MsWilsonPrimePower

