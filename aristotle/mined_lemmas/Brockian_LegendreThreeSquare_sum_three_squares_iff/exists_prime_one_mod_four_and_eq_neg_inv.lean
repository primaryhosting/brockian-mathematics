import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma exists_prime_one_mod_four_and_eq_neg_inv
    (n r : ℕ) (hn : Odd n) (hr : IsUnit (r : ZMod n)) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ (q : ZMod n) = - (r : ZMod n)⁻¹ := by
  classical
  have hn0 : n ≠ 0 := by
    intro h0; subst h0
    simpa using hn

  -- Combine the two congruence conditions into a single residue class modulo `4*n`.
  have hcop2 : Nat.Coprime 2 n := Nat.coprime_two_left.2 hn
  have hcop4 : Nat.Coprime 4 n := by
    have : Nat.Coprime (2 ^ 2) n :=
      (Nat.coprime_pow_left_iff (n := 2) (by decide : 0 < 2) 2 n).2 hcop2
    simpa using this

  let a0 : ZMod n := - (r : ZMod n)⁻¹
  let e : ZMod (4 * n) ≃+* ZMod 4 × ZMod n := ZMod.chineseRemainder hcop4
  let a : ZMod (4 * n) := e.symm (1, a0)

  have ha0 : IsUnit a0 := by
    -- `r` unit ⇒ `r⁻¹` unit ⇒ `-(r⁻¹)` unit
    rcases hr with ⟨u, hu⟩
    have hinv : IsUnit ((r : ZMod n)⁻¹) := by
      refine ⟨u⁻¹, ?_⟩
      -- `↑(u⁻¹) = (↑u)⁻¹`
      have : ((↑(u⁻¹) : ZMod n)) = ((u : (ZMod n)ˣ) : ZMod n)⁻¹ := by simp
      simpa [hu] using this
    simpa [a0] using hinv.neg

  have ha_pair : IsUnit ((1 : ZMod 4), a0) := by
    rcases ha0 with ⟨u0, hu0⟩
    refine ⟨
      { val := ((1 : ZMod 4), (u0 : ZMod n))
        inv := ((1 : ZMod 4), (↑(u0⁻¹) : ZMod n))
        val_inv := by ext <;> simp
        inv_val := by ext <;> simp }, ?_⟩
    simpa [hu0]

  have ha : IsUnit a := by
    simpa [a] using (e.symm.toRingHom.isUnit_map ha_pair)

  -- Apply Dirichlet: infinitely many primes in the residue class `a (mod 4*n)`.
  have hQ0 : (4 * n) ≠ 0 := Nat.mul_ne_zero (by decide) hn0
  haveI : NeZero (4 * n) := ⟨hQ0⟩
  obtain ⟨q, _hq_gt, hq_prime, hq_eq⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 4 * n) (a := a) ha 0

  -- Project back to `ZMod 4` and `ZMod n` to read off the two conditions.
  have hpair : e (q : ZMod (4 * n)) = ((1 : ZMod 4), a0) := by
    have := congrArg e hq_eq
    simpa [a] using this

  have hq_mod4 : (q : ZMod 4) = 1 := by
    have := congrArg Prod.fst hpair
    simpa [e] using this
  have hq_modn : (q : ZMod n) = a0 := by
    have := congrArg Prod.snd hpair
    simpa [e] using this

  have hq_mod4_nat : q % 4 = 1 := by
    have : (q : ZMod 4).val = (1 : ZMod 4).val := congrArg ZMod.val hq_mod4
    simpa [ZMod.val_natCast] using this

  refine ⟨q, hq_prime, hq_mod4_nat, ?_⟩
  simpa [a0] using hq_modn

/-- Existence of the Ankeny prime `q`. -/
