import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma exists_even_q1_data_two_mod_eight
    (n : ℕ) (hn2 : n % 8 = 2) (_hn_sq : Squarefree n) :
    ∃ q : ℕ, ∃ b : ℤ,
      Nat.Prime q ∧ q % 4 = 1 ∧ Nat.Coprime n q ∧
      (q : ℤ) ≡ (-1 : ℤ) [ZMOD (n : ℤ)] ∧
      b ^ 2 ≡ - (n : ℤ) [ZMOD (q : ℤ)] := by
  classical
  -- write `n = 2*s` with `s` odd (forced by `n % 8 = 2`)
  have hn_even : n % 2 = 0 := by omega
  have hs_odd : Odd (n / 2) := by
    have : (n / 2) % 2 = 1 := by omega
    exact Nat.odd_iff.2 this
  have hs4 : (n / 2) % 4 = 1 := by omega

  obtain ⟨q, hq_prime, hq8, hq_mods⟩ :=
    exists_prime_mod_eight_and_eq_neg_one (s := (n / 2)) hs_odd 1 (Or.inl rfl)
  have hq1 : q % 4 = 1 := by omega
  have hq_odd : Odd q := by
    have : q % 2 = 1 := by omega
    exact Nat.odd_iff.2 this

  -- lift `q ≡ -1 (mod n/2)` to `q ≡ -1 (mod n)`.
  have hq_modZMod : (q : ZMod n) = (-1 : ZMod n) := by
    -- Avoid rewriting the modulus by equality (which is brittle for `ZMod`).
    -- Instead show `n ∣ q+1`, which is equivalent to `q = -1` in `ZMod n`.
    have hn_eq : n = 2 * (n / 2) :=
      (Nat.two_mul_div_two_of_even (Nat.even_iff.2 hn_even)).symm
    have hs_dvd : (n / 2) ∣ q + 1 := by
      have : (q : ZMod (n / 2)) + 1 = 0 := by
        rw [hq_mods]
        simp
      have : ((q + 1 : ℕ) : ZMod (n / 2)) = 0 := by
        simpa [Nat.cast_add, Nat.cast_one] using this
      exact (ZMod.natCast_eq_zero_iff (q + 1) (n / 2)).1 this
    have h2_dvd : 2 ∣ q + 1 := by
      have : (q + 1) % 2 = 0 := by omega
      exact Nat.dvd_iff_mod_eq_zero.mpr this
    have hcop : Nat.Coprime 2 (n / 2) := Nat.coprime_two_left.2 hs_odd
    have hn_dvd : n ∣ q + 1 := by
      -- `2*(n/2) ∣ q+1` and `n = 2*(n/2)`.
      have hmul : 2 * (n / 2) ∣ q + 1 := hcop.mul_dvd_of_dvd_of_dvd h2_dvd hs_dvd
      exact hn_eq.symm ▸ hmul
    -- turn `n ∣ q+1` into equality in `ZMod n`
    have : ((q + 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff (q + 1) n).2 hn_dvd
    -- `q + 1 = 0` ⇒ `q = -1`
    have : (q : ZMod n) = (-1 : ZMod n) := by
      -- From `(q+1)=0`, add `(-1)` to both sides.
      have h1 : (q : ZMod n) + 1 = 0 := by
        simpa [Nat.cast_add, Nat.cast_one] using this
      have := congrArg (fun t : ZMod n => t + (-1)) h1
      -- `(q+1)+(-1) = q` and `0+(-1) = -1`
      simpa [add_assoc] using this
    simpa using this

  have hqunit : IsUnit (q : ZMod n) := by
    -- `q = -1` in `ZMod n`, and `-1` is a unit.
    simpa [hq_modZMod] using (isUnit_neg (1 : ZMod n))
  have hnq : Nat.Coprime n q :=
    (ZMod.isUnit_iff_coprime q n).1 (by simpa using hqunit) |> Nat.coprime_comm.1

  have hq_mod : (q : ℤ) ≡ (-1 : ℤ) [ZMOD (n : ℤ)] := by
    -- convert the `ZMod` equality into an `Int.ModEq`.
    have : ((q : ℤ) : ZMod n) = ((-1 : ℤ) : ZMod n) := by
      -- `(-1 : ZMod n)` is definitional `(((-1:ℤ)) : ZMod n)`.
      simpa using hq_modZMod
    exact (ZMod.intCast_eq_intCast_iff (q : ℤ) (-1 : ℤ) n).1 this

  -- Jacobi bookkeeping to show `J(-n|q)=1`.
  have hJ2 : J(2 | q) = (1 : ℤ) := by
    calc
      J(2 | q) = ZMod.χ₈ q := jacobiSym.at_two hq_odd
      _ = (1 : ℤ) := by
        have hred : ZMod.χ₈ q = ZMod.χ₈ (q % 8 : ℕ) := by
          simpa using (ZMod.χ₈_nat_mod_eight q)
        have hval : ZMod.χ₈ (1 : ℕ) = (1 : ℤ) := by decide
        simpa [hred, hq8] using hval

  have hJq_s : J((q : ℤ) | (n / 2)) = (1 : ℤ) := by
    have hs_odd' : Odd (n / 2) := hs_odd
    have hq_mod_sZ : (q : ℤ) ≡ (-1 : ℤ) [ZMOD ((n / 2 : ℕ) : ℤ)] := by
      have : ((q : ℤ) : ZMod (n / 2)) = ((-1 : ℤ) : ZMod (n / 2)) := by
        simpa using hq_mods
      exact (ZMod.intCast_eq_intCast_iff (q : ℤ) (-1 : ℤ) (n / 2)).1 this
    have : J((q : ℤ) | (n / 2)) = J(-1 | (n / 2)) := by
      refine jacobiSym.mod_left' (a₁ := (q : ℤ)) (a₂ := (-1 : ℤ)) (b := (n / 2)) ?_
      simpa using hq_mod_sZ.eq
    have hJ_neg_one : J(-1 | (n / 2)) = (1 : ℤ) := by
      calc
        J(-1 | (n / 2)) = ZMod.χ₄ (n / 2 : ℕ) := jacobiSym.at_neg_one hs_odd'
        _ = (1 : ℤ) := ZMod.χ₄_nat_one_mod_four hs4
    simpa [hJ_neg_one] using this

  have hJs_q : J(((n / 2 : ℕ) : ℤ) | q) = (1 : ℤ) := by
    have hs_odd' : Odd (n / 2) := hs_odd
    have := jacobiSym.quadratic_reciprocity_one_mod_four (a := q) (b := (n / 2)) hq1 hs_odd'
    simpa using (this ▸ hJq_s)

  have hJ_nq : J((n : ℤ) | q) = (1 : ℤ) := by
    have hn2Z : (n : ℤ) = (2 : ℤ) * ((n / 2 : ℕ) : ℤ) := by
      have hn2n : n = 2 * (n / 2) := (Nat.two_mul_div_two_of_even (Nat.even_iff.2 hn_even)).symm
      exact_mod_cast hn2n
    have hmul :
        J((2 : ℤ) * ((n / 2 : ℕ) : ℤ) | q) = J(2 | q) * J(((n / 2 : ℕ) : ℤ) | q) :=
      jacobiSym.mul_left (2 : ℤ) ((n / 2 : ℕ) : ℤ) q
    calc
      J((n : ℤ) | q) = J((2 : ℤ) * ((n / 2 : ℕ) : ℤ) | q) := by
        rw [hn2Z]
      _ = J(2 | q) * J(((n / 2 : ℕ) : ℤ) | q) := by simpa using hmul
      _ = 1 := by
        -- Avoid `simp` rewriting `↑(n/2)` into `↑n/2` (Int division).
        rw [hJ2, hJs_q]
        simp

  have hJ_negn : J(-(n : ℤ) | q) = 1 := by
    have hχ4 : ZMod.χ₄ q = (1 : ℤ) := ZMod.χ₄_nat_one_mod_four hq1
    calc
      J(-(n : ℤ) | q) = ZMod.χ₄ q * J((n : ℤ) | q) := jacobiSym.neg (a := (n : ℤ)) (hb := hq_odd)
      _ = 1 := by simp [hχ4, hJ_nq]

  obtain ⟨b, hb⟩ := exists_b_sq_congr_neg_mod_q_of_jacobi n q hq_prime hJ_negn
  exact ⟨q, b, hq_prime, hq1, hnq, hq_mod, hb⟩

