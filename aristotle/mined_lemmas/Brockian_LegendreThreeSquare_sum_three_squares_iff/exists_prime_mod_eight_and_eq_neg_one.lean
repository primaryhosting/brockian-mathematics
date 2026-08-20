import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma exists_prime_mod_eight_and_eq_neg_one
    (s : ℕ) (hs : Odd s) (a8 : ℕ) (ha8 : a8 = 1 ∨ a8 = 5) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 8 = a8 ∧ (q : ZMod s) = (-1 : ZMod s) := by
  classical
  have hs0 : s ≠ 0 := by
    intro h0; subst h0
    simpa using hs

  -- CRT between `ZMod 8` and `ZMod s` (since `s` is odd).
  have hcop2 : Nat.Coprime 2 s := Nat.coprime_two_left.2 hs
  have hcop8 : Nat.Coprime 8 s := by
    -- `8 = 2^3`
    simpa [pow_succ] using (hcop2.pow_left 3)
  let e : ZMod (8 * s) ≃+* ZMod 8 × ZMod s := ZMod.chineseRemainder hcop8

  let a : ZMod (8 * s) := e.symm (a8, (-1 : ZMod s))

  have ha_unit8 : IsUnit (a8 : ZMod 8) := by
    rcases ha8 with rfl | rfl
    · simpa using (isUnit_one : IsUnit (1 : ZMod 8))
    · -- `5` is a unit modulo `8`.
      -- (This is a finite-ring fact; `decide` can discharge it.)
      have : IsUnit (5 : ZMod 8) := by decide
      simpa using this

  have ha_pair : IsUnit ((a8 : ZMod 8), (-1 : ZMod s)) := by
    -- `IsUnit` in a product ring is componentwise.
    have hneg1 : IsUnit (-1 : ZMod s) := by simpa using (isUnit_neg (1 : ZMod s))
    exact (Prod.isUnit_iff).2 ⟨ha_unit8, hneg1⟩

  have ha_unit : IsUnit a := by
    simpa [a] using (e.symm.toRingHom.isUnit_map ha_pair)

  -- Apply Dirichlet: there exist primes in the residue class `a (mod 8*s)`.
  have hQ0 : (8 * s) ≠ 0 := Nat.mul_ne_zero (by decide) hs0
  haveI : NeZero (8 * s) := ⟨hQ0⟩
  obtain ⟨q, _hq_gt, hq_prime, hq_eq⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 8 * s) (a := a) ha_unit 0

  -- Project back to `ZMod 8` and `ZMod s`.
  have hpair : e (q : ZMod (8 * s)) = ((a8 : ZMod 8), (-1 : ZMod s)) := by
    have := congrArg e hq_eq
    simpa [a] using this

  have hq_mod8 : (q : ZMod 8) = a8 := by
    have := congrArg Prod.fst hpair
    simpa [e] using this
  have hq_mods : (q : ZMod s) = (-1 : ZMod s) := by
    have := congrArg Prod.snd hpair
    simpa [e] using this

  have hq_mod8_nat : q % 8 = a8 := by
    have : (q : ZMod 8).val = (a8 : ZMod 8).val := congrArg ZMod.val hq_mod8
    -- `a8` is already < 8 (since we restrict to 1 or 5).
    rcases ha8 with rfl | rfl
    · simpa [ZMod.val_natCast] using this
    · simpa [ZMod.val_natCast] using this

  exact ⟨q, hq_prime, hq_mod8_nat, hq_mods⟩

/-!
### Even squarefree residues (`2` and `6` mod `8`)

For the Q₁ route (`q*x^2 + y^2 + n*z^2 = n*q`) we need:
- an odd prime `q` with `q ≡ -1 (mod n)`, and
- a square root `b` of `-n` modulo `q` (i.e. `b^2 ≡ -n [ZMOD q]`).

When `n` is squarefree and even, we write `n = 2*s` with `s` odd. The prime choice lemma
`exists_prime_mod_eight_and_eq_neg_one` gives `q ≡ -1 (mod s)` and a controlled residue `q % 8`.

The Jacobi-symbol computation is then a short invariant:
\[
J(n \mid q) = J(2 \mid q)\,J(s \mid q),
\]
and `J(s|q)` is controlled via reciprocity from `q ≡ -1 (mod s)` (so `J(q|s)=J(-1|s)`).

Choosing `q % 8 = 1` (resp. `5`) makes `J(2|q)` equal `1` (resp. `-1`), which cancels the
`J(-1|s)` value when `s % 4 = 1` (resp. `3`). This forces `J(-n|q)=1`, hence `-n` is a square mod `q`.
-/

