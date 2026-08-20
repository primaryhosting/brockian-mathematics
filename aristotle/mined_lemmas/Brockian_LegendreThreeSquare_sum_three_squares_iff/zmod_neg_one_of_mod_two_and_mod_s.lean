import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

private lemma zmod_neg_one_of_mod_two_and_mod_s
    (s q : ℕ) (hs : Odd s) (hqodd : Odd q) (hq_mods : (q : ZMod s) = (-1 : ZMod s)) :
    (q : ZMod (2 * s)) = (-1 : ZMod (2 * s)) := by
  classical
  have hcop : Nat.Coprime 2 s := Nat.coprime_two_left.2 hs
  let e : ZMod (2 * s) ≃+* ZMod 2 × ZMod s := ZMod.chineseRemainder hcop
  apply e.injective
  ext
  · -- mod 2 component: `Odd q` ⇒ `q = 1` in `ZMod 2`, and `-1 = 1` in `ZMod 2`.
    have hqZ2 : (q : ZMod 2) = (1 : ZMod 2) := by
      have : q % 2 = 1 := by
        exact Nat.odd_iff.1 hqodd
      -- `q ≡ 1 [MOD 2]` gives equality in `ZMod 2`.
      have : q ≡ 1 [MOD 2] := by
        dsimp [Nat.ModEq]
        simpa [this]
      exact (ZMod.natCast_eq_natCast_iff q 1 2).2 this
    -- `e`'s `fst` projection is definitionally the reduction mod 2.
    simpa [hqZ2]
  · -- mod `s` component: given.
    simpa [hq_mods]

