import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma ankeny_even_padicValNat_of_mem_primeFactors_q1
    {n q K p : ℕ} {x y z b : ℤ}
    (hq1 : q % 4 = 1)
    (hq_prime : Nat.Prime q)
    (hq_mod : (q : ℤ) ≡ (-1 : ℤ) [ZMOD (n : ℤ)])
    (hn_sq : Squarefree n)
    (hK_eq : (K : ℤ) = (n : ℤ) - x ^ 2)
    (h_eqK : y ^ 2 + (n : ℤ) * z ^ 2 = (q : ℤ) * (K : ℤ))
    (hxy : x ≡ y [ZMOD (n : ℤ)])
    (hybz : y ≡ b * z [ZMOD (q : ℤ)])
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (q : ℤ)])
    (hpK : p ∈ K.primeFactors)
    (hp4 : p % 4 = 3) :
    Even (padicValNat p K) := by
  classical
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpK
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_dvdK : p ∣ K := Nat.dvd_of_mem_primeFactors hpK

  -- `p ≠ q` from mod-4 residues.
  have hp_ne_q : p ≠ q := by
    intro h
    subst h
    have : (p % 4) ≠ 3 := by simpa [hq1]
    exact this hp4

  -- Hence `p ∤ q` (since `q` is prime and its divisors are `1` or `q`).
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro hpq
    have hdiv : p = 1 ∨ p = q := (Nat.dvd_prime hq_prime).1 hpq
    cases hdiv with
    | inl hp1 => exact hp.ne_one hp1
    | inr hpq_eq => exact hp_ne_q hpq_eq

  -- Key: `p ∤ n` for primes `p ≡ 3 (mod 4)` dividing `K`.
  -- (This is the Q₁ analogue of the `p ∣ n` contradiction in the `2q` route; here we use `q ≡ -1 (mod n)`.)
  have hp_not_dvd_n : ¬ p ∣ n := by
    intro hp_dvd_n
    have hpK_int : (p : ℤ) ∣ (K : ℤ) := by exact_mod_cast hp_dvdK
    have hp_dvd_nmx : (p : ℤ) ∣ (n : ℤ) - x ^ 2 := by simpa [hK_eq] using hpK_int
    have hn_modp : ((n : ℤ) : ZMod p) = (x ^ 2 : ZMod p) := by
      have hsub0 : (((n : ℤ) - x ^ 2 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) - x ^ 2 : ℤ) p).2 hp_dvd_nmx
      have : ((n : ℤ) : ZMod p) - (x ^ 2 : ZMod p) = 0 := by
        simpa [Int.cast_sub] using hsub0
      exact sub_eq_zero.mp this

    have hx0_modp : (x : ZMod p) = 0 := by
      have hn0p : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).2 hp_dvd_n
      have hx2 : (x ^ 2 : ZMod p) = 0 := by simpa [hn0p] using hn_modp.symm
      have : (x : ZMod p) * (x : ZMod p) = 0 := by simpa [pow_two] using hx2
      exact (mul_eq_zero.mp this).elim id id

    -- `x ≡ y (mod n)` and `p ∣ n` ⇒ `x ≡ y (mod p)` ⇒ `y = 0` in `ZMod p`.
    have hxy_p : x ≡ y [ZMOD (p : ℤ)] := Int.ModEq.of_dvd (by exact_mod_cast hp_dvd_n) hxy
    have hy0_modp : (y : ZMod p) = 0 := by
      have : (y : ZMod p) = (x : ZMod p) := by
        have := congrArg (fun t : ℤ => (t : ZMod p)) (Int.ModEq.symm hxy_p)
        simpa using this
      simpa [hx0_modp] using this

    have hp_dvd_y : (p : ℤ) ∣ y :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd y p).1 (by simpa using hy0_modp)
    rcases hp_dvd_y with ⟨y1, hy1⟩
    -- Also `p ∣ x` in ℤ.
    have hp_dvd_x : (p : ℤ) ∣ x :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd x p).1 (by simpa using hx0_modp)
    rcases hp_dvd_x with ⟨x1, hx1⟩

    -- Squarefree: write `n = p * n1` with `p ∤ n1`.
    have hn_eq : n = p * (n / p) := (Nat.mul_div_cancel' hp_dvd_n).symm
    set n1 : ℕ := n / p
    have hn1_ne0_modp : (n1 : ZMod p) ≠ 0 := by
      intro hn1_0
      have hp_dvd_n1 : p ∣ n1 := (ZMod.natCast_eq_zero_iff n1 p).1 hn1_0
      have hp2_dvd_n : p * p ∣ n := by
        rcases hp_dvd_n1 with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        simpa [hn_eq, ht, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      have hsf := (Nat.squarefree_iff_prime_squarefree).1 hn_sq p hp
      exact hsf hp2_dvd_n

    have hn_nat : n = p * n1 := by simpa [n1] using (Nat.mul_div_cancel' hp_dvd_n).symm
    -- Define `K1 = K / p` in ℕ.
    set K1 : ℕ := K / p
    have hK_nat : K = p * K1 := by simpa [K1] using (Nat.mul_div_cancel' hp_dvdK).symm

    -- From `K = n - x^2` and `x = p*x1`, show `K1 ≡ n1 (mod p)`.
    have hK1_mod : (K1 : ℤ) ≡ (n1 : ℤ) [ZMOD (p : ℤ)] := by
      have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hnZ : (n : ℤ) = (p : ℤ) * (n1 : ℤ) := by exact_mod_cast hn_nat
      have hKZ : (K : ℤ) = (p : ℤ) * (K1 : ℤ) := by exact_mod_cast hK_nat
      have : (p : ℤ) * (K1 : ℤ) = (p : ℤ) * ((n1 : ℤ) - (p : ℤ) * (x1 ^ 2)) := by
        calc
          (p : ℤ) * (K1 : ℤ) = (K : ℤ) := by simpa [hKZ]
          _ = (n : ℤ) - x ^ 2 := hK_eq
          _ = (p : ℤ) * (n1 : ℤ) - ((p : ℤ) * x1) ^ 2 := by simpa [hnZ, hx1]
          _ = (p : ℤ) * ((n1 : ℤ) - (p : ℤ) * (x1 ^ 2)) := by
                simp [pow_two, mul_assoc, mul_left_comm, mul_comm]; ring
      have hk1 : (K1 : ℤ) = (n1 : ℤ) - (p : ℤ) * (x1 ^ 2) := (mul_left_cancel₀ hpz this)
      refine (Int.modEq_iff_dvd).2 ?_
      refine ⟨x1 ^ 2, ?_⟩
      have : (n1 : ℤ) - ((n1 : ℤ) - (p : ℤ) * (x1 ^ 2)) = (p : ℤ) * (x1 ^ 2) := by ring
      simpa [hk1] using this

    -- Divide the main equation by `p`.
    have h_div :
        (p : ℤ) * (y1 ^ 2) + (n1 : ℤ) * (z ^ 2) = (q : ℤ) * (K1 : ℤ) := by
      have hnZ : (n : ℤ) = (p : ℤ) * (n1 : ℤ) := by exact_mod_cast hn_nat
      have hKZ : (K : ℤ) = (p : ℤ) * (K1 : ℤ) := by exact_mod_cast hK_nat
      have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have h_eqK' :
          ((p : ℤ) * y1) ^ 2 + (p : ℤ) * (n1 : ℤ) * (z ^ 2) =
            (q : ℤ) * ((p : ℤ) * (K1 : ℤ)) := by
        simpa [hnZ, hKZ, hy1, mul_assoc, mul_left_comm, mul_comm] using h_eqK
      have hm :
          (p : ℤ) * ((p : ℤ) * (y1 ^ 2) + (n1 : ℤ) * (z ^ 2))
            = (p : ℤ) * ((q : ℤ) * (K1 : ℤ)) := by
        calc
          (p : ℤ) * ((p : ℤ) * (y1 ^ 2) + (n1 : ℤ) * (z ^ 2))
              = ((p : ℤ) * y1) ^ 2 + (p : ℤ) * (n1 : ℤ) * (z ^ 2) := by ring
          _ = (q : ℤ) * ((p : ℤ) * (K1 : ℤ)) := h_eqK'
          _ = (p : ℤ) * ((q : ℤ) * (K1 : ℤ)) := by ring
      exact (mul_left_cancel₀ hpz hm)

    -- Reduce modulo `p`, substitute `K1 ≡ n1`, and conclude `z^2 ≡ q (mod p)`.
    have hz2_eq : (z : ZMod p) ^ 2 = (q : ZMod p) := by
      have hmod1 : (n1 : ZMod p) * ((z : ZMod p) ^ 2) = (q : ZMod p) * (K1 : ZMod p) := by
        have := congrArg (fun t : ℤ => (t : ZMod p)) h_div
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
      have hK1_cast : (K1 : ZMod p) = (n1 : ZMod p) := by
        have := congrArg (fun t : ℤ => (t : ZMod p)) hK1_mod.eq
        simpa using this
      have hmod2 : (n1 : ZMod p) * ((z : ZMod p) ^ 2) = (n1 : ZMod p) * (q : ZMod p) := by
        simpa [hK1_cast, mul_assoc, mul_left_comm, mul_comm] using hmod1
      exact mul_left_cancel₀ hn1_ne0_modp hmod2

    -- From `q ≡ -1 (mod n)` and `p ∣ n`, get `q ≡ -1 (mod p)` hence `z^2 = -1`, contradict `p % 4 = 3`.
    have hq_mod_p : (q : ℤ) ≡ (-1 : ℤ) [ZMOD (p : ℤ)] :=
      Int.ModEq.of_dvd (by exact_mod_cast hp_dvd_n) hq_mod
    have hq0 : (q : ZMod p) = (-1 : ZMod p) := by
      have := congrArg (fun t : ℤ => (t : ZMod p)) hq_mod_p.eq
      simpa using this
    have hz_sq_neg1 : (z : ZMod p) ^ 2 = (-1 : ZMod p) := by simpa [hq0] using hz2_eq
    have : p % 4 ≠ 3 :=
      ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (p := p)
        (x := (z : ZMod p)) (y := (1 : ZMod p))
        (by simp) (by simpa [pow_two] using hz_sq_neg1)
    exact this (by simpa [hp4])

  -- Force `p ∣ y` and `p ∣ z` (Q₁ mod-`p` kernel).
  have hp_dvd_yz : (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z :=
    ankeny_p_dvd_yz_of_dvd_K_q1 (n := n) (q := q) (K := K) (p := p) (x := x) (y := y) (z := z)
      hp hp4 hp_dvdK hp_not_dvd_n hK_eq h_eqK
  have hp_dvd_y : (p : ℤ) ∣ y := hp_dvd_yz.1
  have hp_dvd_z : (p : ℤ) ∣ z := hp_dvd_yz.2

  -- Show `p^2 ∣ K` (the key cancellation step used by the eventual recursion).
  have hp2_dvd_K : p * p ∣ K := by
    rcases hp_dvd_y with ⟨y1, rfl⟩
    rcases hp_dvd_z with ⟨z1, rfl⟩
    -- `p^2 ∣ y^2 + n z^2 = q*K`.
    have hp2_dvd_qK : p ^ 2 ∣ q * K := by
      have hp2Z : ((p : ℤ) ^ 2) ∣ (q : ℤ) * (K : ℤ) := by
        refine ⟨(y1 ^ 2 + (n : ℤ) * z1 ^ 2), ?_⟩
        -- expand and match `h_eqK`
        have : ((p : ℤ) * y1) ^ 2 + (n : ℤ) * ((p : ℤ) * z1) ^ 2 =
            (p : ℤ) ^ 2 * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by
          ring
        calc
          (q : ℤ) * (K : ℤ)
              = ((p : ℤ) * y1) ^ 2 + (n : ℤ) * ((p : ℤ) * z1) ^ 2 := by
                    simpa [mul_assoc, mul_left_comm, mul_comm] using h_eqK.symm
          _ = (p : ℤ) ^ 2 * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := this
      -- cast back to `ℕ`
      have hp2Z' : (p ^ 2 : ℤ) ∣ (q * K : ℤ) := by simpa [Nat.cast_pow] using hp2Z
      exact (Int.ofNat_dvd_natCast).1 hp2Z'
    have hcop : Nat.Coprime (p ^ 2) q := by
      have : Nat.Coprime p q := (hp.coprime_iff_not_dvd).2 hp_not_dvd_q
      exact this.pow_left 2
    have hp2_dvd_K' : p ^ 2 ∣ K :=
      hcop.dvd_of_dvd_mul_left (by simpa [Nat.mul_assoc] using hp2_dvd_qK)
    simpa [pow_two] using hp2_dvd_K'

  -- Finish: show odd `padicValNat p K` is impossible (same shape as the `2q` route).
  have hK_ne0 : K ≠ 0 := by
    intro hK0
    subst hK0
    simpa using hpK

  have hp_dvd_nmx : (p : ℤ) ∣ (n : ℤ) - x ^ 2 := by
    have : (p : ℤ) ∣ (K : ℤ) := by exact_mod_cast hp_dvdK
    simpa [hK_eq] using this

  -- Local kernel (same as in the `2q` lemma): once we have `p ∣ (n - x^2)` and `p ∣ (y^2 + n z^2)`
  -- with `p % 4 = 3` and `p ∤ n`, we can force `p ∣ y` and `p ∣ z`.
  have dvd_yz_of_dvd_form :
      ∀ {y z : ℤ},
        (p : ℤ) ∣ (n : ℤ) - x ^ 2 →
        (p : ℤ) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) →
        (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z := by
    intro y z hp_nmx hp_form
    haveI : Fact p.Prime := ⟨hp⟩
    have hn_modp : (n : ZMod p) = (x : ZMod p) ^ 2 := by
      have hsub0 : (((n : ℤ) - x ^ 2 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) - x ^ 2 : ℤ) p).2 hp_nmx
      have : ((n : ℤ) : ZMod p) - (x ^ 2 : ZMod p) = 0 := by
        simpa [Int.cast_sub] using hsub0
      simpa [pow_two, mul_assoc] using (sub_eq_zero.mp this)

    have hx0 : (x : ZMod p) ≠ 0 := by
      intro hx
      have : (n : ZMod p) = 0 := by simpa [hn_modp, hx]
      exact hp_not_dvd_n ((ZMod.natCast_eq_zero_iff n p).1 this)

    have hform0 : ((y ^ 2 + (n : ℤ) * z ^ 2 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (y ^ 2 + (n : ℤ) * z ^ 2) p).2 hp_form

    have hy2_eq : (y : ZMod p) ^ 2 = -((x : ZMod p) * (z : ZMod p)) ^ 2 := by
      have h0 :
          (y : ZMod p) ^ 2 + (n : ZMod p) * (z : ZMod p) ^ 2 = 0 := by
        simpa [pow_two, Int.cast_add, Int.cast_mul, Int.cast_natCast, add_assoc, add_comm,
          add_left_comm, mul_assoc, mul_comm, mul_left_comm] using hform0
      have hy : (y : ZMod p) ^ 2 = -((n : ZMod p) * (z : ZMod p) ^ 2) :=
        eq_neg_of_add_eq_zero_left h0
      have hy' : (y : ZMod p) ^ 2 = -(((x : ZMod p) ^ 2) * (z : ZMod p) ^ 2) := by
        simpa [hn_modp] using hy
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy'

    have hxz0 : (x : ZMod p) * (z : ZMod p) = 0 := by
      by_contra hxz_ne
      have : p % 4 ≠ 3 :=
        ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (p := p)
          (x := (y : ZMod p)) (y := (x : ZMod p) * (z : ZMod p))
          hxz_ne (by
            simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy2_eq)
      exact this hp4

    have hz0 : (z : ZMod p) = 0 := (mul_eq_zero.mp hxz0).resolve_left hx0
    have hy0 : (y : ZMod p) = 0 := by
      have : (y : ZMod p) ^ 2 = 0 := by simpa [hxz0] using hy2_eq
      have : (y : ZMod p) * (y : ZMod p) = 0 := by simpa [pow_two] using this
      exact (mul_eq_zero.mp this).elim id id

    have hp_dvd_y : (p : ℤ) ∣ y :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd y p).1 (by simpa using hy0)
    have hp_dvd_z : (p : ℤ) ∣ z :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd z p).1 (by simpa using hz0)
    exact ⟨hp_dvd_y, hp_dvd_z⟩

  -- Power version: if `p^(2t+1)` divides the form, then `p^(t+1)` divides `y` and `z`.
  have pow_dvd_yz_of_pow_dvd_form :
      ∀ (t : ℕ) {y z : ℤ},
        (p : ℤ) ^ (2 * t + 1) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) →
        (p : ℤ) ^ (t + 1) ∣ y ∧ (p : ℤ) ^ (t + 1) ∣ z := by
    intro t
    induction t with
    | zero =>
        intro y z hdiv
        have hp_form : (p : ℤ) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by simpa using hdiv
        simpa using (dvd_yz_of_dvd_form (y := y) (z := z) hp_dvd_nmx hp_form)
    | succ t ih =>
        intro y z hdiv
        have hp_form : (p : ℤ) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by
          have hn0 : (2 * t + 3) ≠ 0 := by omega
          have hpdiv : (p : ℤ) ∣ (p : ℤ) ^ (2 * t + 3) := dvd_pow_self (p : ℤ) hn0
          exact hpdiv.trans hdiv
        rcases dvd_yz_of_dvd_form (y := y) (z := z) hp_dvd_nmx hp_form with ⟨hy, hz⟩
        rcases hy with ⟨y1, rfl⟩
        rcases hz with ⟨z1, rfl⟩
        have hfac :
            ((p : ℤ) * y1) ^ 2 + (n : ℤ) * ((p : ℤ) * z1) ^ 2
              = (p : ℤ) ^ 2 * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by
          ring
        have hp_ne0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hp2_ne0 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hp_ne0
        have hpow : (p : ℤ) ^ (2 * t + 3) = (p : ℤ) ^ 2 * (p : ℤ) ^ (2 * t + 1) := by
          calc
            (p : ℤ) ^ (2 * t + 3) = (p : ℤ) ^ (2 + (2 * t + 1)) := by
              congr 1
              omega
            _ = (p : ℤ) ^ 2 * (p : ℤ) ^ (2 * t + 1) := by
              simp [pow_add]
        have hdiv' :
            (p : ℤ) ^ (2 * t + 1) ∣ (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by
          have ht : 2 * (t + 1) + 1 = 2 * t + 3 := by omega
          have : (p : ℤ) ^ 2 * (p : ℤ) ^ (2 * t + 1) ∣ (p : ℤ) ^ 2 * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by
            simpa [ht, hpow, hfac] using hdiv
          exact (Int.mul_dvd_mul_iff_left hp2_ne0).1 this
        have hyz := ih (y := y1) (z := z1) hdiv'
        refine ⟨?_, ?_⟩
        · simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
            (Int.mul_dvd_mul_left (p : ℤ) hyz.1)
        · simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
            (Int.mul_dvd_mul_left (p : ℤ) hyz.2)

  -- If `padicValNat p K` were odd, force one more factor of `p` into `K`, contradiction.
  by_contra h_even
  have hk_odd : Odd (padicValNat p K) := Nat.not_even_iff_odd.1 h_even
  rcases hk_odd with ⟨t, hk⟩

  have hpowK : p ^ (2 * t + 1) ∣ K := by
    have : (2 * t + 1) ≤ padicValNat p K := by simpa [hk]
    exact (padicValNat_dvd_iff_le (p := p) (a := K) (n := 2 * t + 1) hK_ne0).2 this

  have hpow_form : (p : ℤ) ^ (2 * t + 1) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by
    have hnat : p ^ (2 * t + 1) ∣ q * K :=
      dvd_mul_of_dvd_right hpowK q
    have hZ : (p ^ (2 * t + 1) : ℤ) ∣ (q * K : ℤ) :=
      (Int.ofNat_dvd_natCast).2 hnat
    have hZ' : (p ^ (2 * t + 1) : ℤ) ∣ ((q : ℤ) * (K : ℤ)) := by
      simpa [Nat.cast_mul, mul_assoc] using hZ
    have : (p ^ (2 * t + 1) : ℤ) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by
      simpa [h_eqK, mul_assoc, mul_left_comm, mul_comm] using hZ'
    simpa [Nat.cast_pow] using this

  have hyz_pow : (p : ℤ) ^ (t + 1) ∣ y ∧ (p : ℤ) ^ (t + 1) ∣ z :=
    pow_dvd_yz_of_pow_dvd_form t (y := y) (z := z) hpow_form

  have hpow_form2 : (p : ℤ) ^ (2 * t + 2) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by
    rcases hyz_pow.1 with ⟨y1, rfl⟩
    rcases hyz_pow.2 with ⟨z1, rfl⟩
    refine ⟨y1 ^ 2 + (n : ℤ) * z1 ^ 2, ?_⟩
    have hp2 :
        ((p : ℤ) ^ (t + 1)) ^ 2 = (p : ℤ) ^ (2 * t + 2) := by
      have ht : (t + 1) * 2 = 2 * t + 2 := by omega
      rw [← pow_mul]
      simpa [ht]
    calc
      ((p : ℤ) ^ (t + 1) * y1) ^ 2 + (n : ℤ) * ((p : ℤ) ^ (t + 1) * z1) ^ 2
          = ((p : ℤ) ^ (t + 1)) ^ 2 * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by ring
      _ = (p : ℤ) ^ (2 * t + 2) * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by
          simpa [hp2, mul_assoc, mul_left_comm, mul_comm]

  have hpow_nat2 : p ^ (2 * t + 2) ∣ q * K := by
    have hpowZ : ((p : ℤ) ^ (2 * t + 2)) ∣ ((q : ℤ) * (K : ℤ)) := by
      simpa [h_eqK, mul_assoc, mul_left_comm, mul_comm] using hpow_form2
    have hpowZ' : (p ^ (2 * t + 2) : ℤ) ∣ ((q : ℤ) * (K : ℤ)) := by
      simpa [Nat.cast_pow] using hpowZ
    have : (p ^ (2 * t + 2) : ℤ) ∣ (q * K : ℤ) := by
      simpa [Nat.cast_mul, mul_assoc] using hpowZ'
    exact (Int.ofNat_dvd_natCast).1 this

  have hcop : Nat.Coprime (p ^ (2 * t + 2)) q := by
    have : Nat.Coprime p q := (hp.coprime_iff_not_dvd).2 hp_not_dvd_q
    exact this.pow_left (2 * t + 2)

  have hpowK2 : p ^ (2 * t + 2) ∣ K :=
    (hcop.dvd_of_dvd_mul_left (by simpa [Nat.mul_assoc] using hpow_nat2))

  have hmax : ¬ p ^ (padicValNat p K + 1) ∣ K :=
    pow_succ_padicValNat_not_dvd (p := p) (n := K) hK_ne0
  have hcontra : p ^ (padicValNat p K + 1) ∣ K := by
    have hexp : padicValNat p K + 1 = 2 * t + 2 := by
      calc
        padicValNat p K + 1 = (2 * t + 1) + 1 := by simpa [hk]
        _ = 2 * t + 2 := by omega
    simpa [hexp] using hpowK2
  exact hmax hcontra

/-- Reduction of `2qx² + y² + nz² = 2nq` to `n = x² + u² + v²`.

This is the “arithmetic back half” of the Ankeny-style proof: once we have one special quadratic-form
representation, we need to manufacture a *sum of two squares* witness.

Research note (Ankeny 1957, Proc. AMS 8(2), pp. 316–319):
the classical writeup proves (for squarefree `m ≡ 3 (mod 8)`) an identity of the form
\[
  m = R^2 + 2 v
\]
and then shows that every odd prime dividing `v` to an odd power is \( \equiv 1 \pmod 4 \),
so `2*v` is a sum of two squares; hence `m` is a sum of three squares.

Our current Lean development is arranged slightly differently (we work with `K := (n - x^2).natAbs`),
but the *intended invariant* is the same: use `Nat.eq_sq_add_sq_iff` (mathlib’s “sum of two squares”
criterion) to prove `K` is a sum of two squares by ruling out primes \(p \equiv 3 \pmod 4\) appearing
to odd exponent.
-/
