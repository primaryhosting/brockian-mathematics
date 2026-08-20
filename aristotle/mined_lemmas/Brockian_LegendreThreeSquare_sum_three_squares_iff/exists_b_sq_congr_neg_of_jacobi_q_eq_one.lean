import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma exists_b_sq_congr_neg_of_jacobi_q_eq_one
    (n q : ℕ) (hn : Odd n) (hq : Nat.Prime q) (hq1 : q % 4 = 1)
    (hJ_q : J((q : ℤ) | n) = (1 : ℤ)) :
    ∃ b : ℤ, b^2 ≡ - (n : ℤ) [ZMOD (2 * q)] := by
  classical

  have hq_odd : Odd q := by
    -- `q % 4 = 1` rules out `q = 2`, hence `q` is odd.
    have hq_ne2 : q ≠ 2 := by
      intro hq2; subst hq2
      simp at hq1
    exact hq.odd_of_ne_two hq_ne2

  have hcop2q : Nat.Coprime 2 q := Nat.coprime_two_left.2 hq_odd

  -- Step 1: Reciprocity transfers `J(q|n)=1` to `J(n|q)=1` since `q % 4 = 1`.
  have hJ_nq : J((n : ℤ) | q) = (1 : ℤ) := by
    have := jacobiSym.quadratic_reciprocity_one_mod_four (a := q) (b := n) hq1 hn
    -- `this : J(q|n) = J(n|q)`
    simpa using (this ▸ hJ_q)

  -- Step 2: Turn `J(-n | q) = 1` into an actual square root in `ZMod q`.
  haveI : Fact q.Prime := ⟨hq⟩
  have hJ_negn : J(-(n : ℤ) | q) = 1 := by
    -- `J(-n|q) = χ₄ q * J(n|q)`; for `q % 4 = 1`, `χ₄ q = 1`.
    have hχ4 : ZMod.χ₄ q = (1 : ℤ) := ZMod.χ₄_nat_one_mod_four hq1
    calc
      J(-(n : ℤ) | q) = ZMod.χ₄ q * J((n : ℤ) | q) := jacobiSym.neg (a := (n : ℤ)) (hb := hq_odd)
      _ = 1 := by simp [hχ4, hJ_nq]

  have hsq_q : IsSquare (-(n : ZMod q)) := by
    -- `ZMod.isSquare_of_jacobiSym_eq_one` returns `IsSquare ((-(n:ℤ)) : ZMod q)`;
    -- rewrite the integer cast using `Int.cast_neg` / `Int.cast_natCast`.
    simpa [Int.cast_neg, Int.cast_natCast] using
      (ZMod.isSquare_of_jacobiSym_eq_one (p := q) (a := (-(n : ℤ))) hJ_negn)
  rcases hsq_q with ⟨r, hr⟩

  -- Step 3: Lift the square root mod `q` to a square root mod `2*q` via CRT.
  have hnZ2 : (n : ZMod 2) = (1 : ZMod 2) := by
    have : n % 2 = 1 := by
      -- `Odd n` forces `n % 2 = 1`.
      exact (Nat.odd_iff.1 hn)
    have : n ≡ 1 [MOD 2] := by
      dsimp [Nat.ModEq]
      simpa [this]
    exact (ZMod.natCast_eq_natCast_iff n 1 2).2 this

  have hmod2 : ((1 : ZMod 2) ^ 2) = (-(n : ZMod 2)) := by
    -- In `ZMod 2`, `n = 1` and `-1 = 1`.
    simp [hnZ2]

  let e : ZMod (2 * q) ≃+* ZMod 2 × ZMod q := ZMod.chineseRemainder hcop2q
  let bZ : ZMod (2 * q) := e.symm ((1 : ZMod 2), r)

  have hbZ : bZ ^ 2 = (-(n : ℤ) : ZMod (2 * q)) := by
    apply e.injective
    ext
    · -- mod 2 component
      have : ((1 : ZMod 2) ^ 2) = (-(n : ZMod 2)) := hmod2
      simpa [bZ] using this
    · -- mod q component
      -- `hr : -(n : ZMod q) = r*r`.
      have : (r ^ 2) = (-(n : ZMod q)) := by
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hr.symm
      -- cast `-(n : ZMod q)` as `((-(n : ℤ)) : ZMod q)` to match `e`'s component.
      simpa [bZ, Int.cast_neg, Int.cast_natCast] using this

  -- Convert the equality in `ZMod (2*q)` into an `Int.ModEq` witness.
  rcases ZMod.intCast_surjective bZ with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  have hbZ' : ((b : ZMod (2 * q)) ^ 2) = (-(n : ℤ) : ZMod (2 * q)) := by simpa [hb] using hbZ
  exact (ZMod.intCast_eq_intCast_iff (b ^ 2) (-(n : ℤ)) (2 * q)).1 (by
    simpa [Int.cast_pow, pow_two] using hbZ')

/-- A “next unlocked piece” for `n % 4 = 1` (so `n % 8 = 1` or `5`):

Pick a prime `q ≡ 1 (mod 4)` with `q ≡ -1 (mod n)` (i.e. `q = -1` in `ZMod n`).
Then `J(q|n) = J(-1|n) = 1`, so the back-half lemma produces `b^2 ≡ -n [ZMOD 2q]`.

This does *not* finish the `t % 8 = 1,5` cases on its own (the Minkowski layer is still
specialized to `2q` in the quadratic form), but it gives us a clean interface:

- “front half”: pick `q` in a residue class (Dirichlet),
- “Jacobi half”: conclude `J(q|n)=1`,
- “back half”: produce the `b` congruence we need for a lattice construction. -/
