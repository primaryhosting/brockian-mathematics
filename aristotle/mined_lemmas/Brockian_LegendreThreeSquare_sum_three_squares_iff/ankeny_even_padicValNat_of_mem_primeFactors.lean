import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma ankeny_even_padicValNat_of_mem_primeFactors
    {n q K p : ℕ} {x y z b : ℤ}
    (hn_odd : Odd n)
    (hq1 : q % 4 = 1)
    (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹)
    (hq_prime : Nat.Prime q)
    (hn_sq : Squarefree n)
    (hK_eq : (K : ℤ) = (n : ℤ) - x ^ 2)
    (h_eqK : y ^ 2 + (n : ℤ) * z ^ 2 = 2 * (q : ℤ) * (K : ℤ))
    (hxy : x ≡ y [ZMOD (n : ℤ)])
    (hybz : y ≡ b * z [ZMOD (2 * q : ℤ)])
    (hpK : p ∈ K.primeFactors)
    (hp4 : p % 4 = 3) :
    Even (padicValNat p K) := by
  -- Proof outline (implemented below):
  --
  -- - Use `hpK` to get `p ∣ K` and basic exclusions (`p ≠ 2`, `p ≠ q` from `hp4`, `hq1`).
  -- - Show `¬ p ∣ n` (otherwise `z^2 ≡ -1 (mod p)` from `hq_mod`, contradicting `p % 4 = 3`).
  -- - If `padicValNat p K` were odd, then `p^(2t+1) ∣ K` forces `p^(t+1) ∣ y,z` from the form
  --   `y^2 + n z^2 = 2*q*K`, hence `p^(2t+2) ∣ 2*q*K`.
  -- - Since `p ∤ 2*q`, this bumps the valuation of `K`, contradicting minimality of `2t+1`.
  classical
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpK
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_dvdK : p ∣ K := Nat.dvd_of_mem_primeFactors hpK

  -- Easy exclusions: `p ≠ 2` and `p ≠ q`.
  have hp_ne2 : p ≠ 2 := by
    intro h
    -- `2 % 4 = 2`, not `3`
    subst h
    simp at hp4
  have hp_ne_q : p ≠ q := by
    intro h
    subst h
    -- `q % 4 = 1` contradicts `p % 4 = 3`
    have : (p % 4) ≠ 3 := by simpa [hq1]
    exact this hp4

  -- First, rule out the case `p ∣ n` for primes `p ≡ 3 (mod 4)`.
  -- This is the case split that appears in Ankeny/Aluffi: if `p ∣ n`, one derives that `-1` is a square mod `p`.
  have hp_not_dvd_n : ¬ p ∣ n := by
    intro hp_dvd_n
    -- Sketch (Ankeny/Aluffi):
    --
    -- If `p ∣ n` and `p ∣ K = n - x^2`, then `x ≡ 0 (mod p)` and hence `x^2 ≡ 0 (mod p^2)`,
    -- so `K ≡ n (mod p^2)`.
    --
    -- From `y^2 + n z^2 = 2 q K` we first get `p ∣ y`, so `y^2 ≡ 0 (mod p^2)`.
    -- Reducing the equation mod `p^2` then yields `n z^2 ≡ 2 q K (mod p^2)`.
    -- Dividing by `p` and using `K/p ≡ n/p (mod p)` gives `z^2 ≡ 2 q (mod p)`.
    --
    -- Finally, the congruence `hq_mod : q = -(2)⁻¹ (mod n)` implies `2q ≡ -1 (mod p)`,
    -- so `z^2 ≡ -1 (mod p)`, contradicting `p % 4 = 3`.
    have hpK_int : (p : ℤ) ∣ (K : ℤ) := by exact_mod_cast hp_dvdK
    have hp_dvd_nmx : (p : ℤ) ∣ (n : ℤ) - x ^ 2 := by simpa [hK_eq] using hpK_int
    have hn_modp : ((n : ℤ) : ZMod p) = (x ^ 2 : ZMod p) := by
      have hsub0 : (((n : ℤ) - x ^ 2 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) - x ^ 2 : ℤ) p).2 hp_dvd_nmx
      have : ((n : ℤ) : ZMod p) - (x ^ 2 : ZMod p) = 0 := by
        simpa [Int.cast_sub] using hsub0
      exact sub_eq_zero.mp this

    have hx0_modp : (x : ZMod p) = 0 := by
      -- if `p ∣ n` then `n = 0` in `ZMod p`; hence `x^2 = 0`, hence `x=0`.
      have hn0p : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).2 hp_dvd_n
      have hx2 : (x ^ 2 : ZMod p) = 0 := by simpa [hn0p] using hn_modp.symm
      have : (x : ZMod p) * (x : ZMod p) = 0 := by simpa [pow_two] using hx2
      exact (mul_eq_zero.mp this).elim id id

    -- Since `x ≡ y (mod n)` and `p ∣ n`, we get `x ≡ y (mod p)` and hence `y = 0` in `ZMod p`.
    have hxy_p : x ≡ y [ZMOD (p : ℤ)] :=
      Int.ModEq.of_dvd (by exact_mod_cast hp_dvd_n) hxy
    have hy0_modp : (y : ZMod p) = 0 := by
      have : (y : ZMod p) = (x : ZMod p) := by
        -- cast the ModEq into `ZMod p`
        have := congrArg (fun t : ℤ => (t : ZMod p)) (Int.ModEq.symm hxy_p)
        simpa using this
      simpa [hx0_modp] using this

    -- Step 1: `p ∣ y`, hence `p^2 ∣ y^2`.
    have hp_dvd_y : (p : ℤ) ∣ y :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd y p).1 (by simpa using hy0_modp)
    rcases hp_dvd_y with ⟨y1, rfl⟩

    -- Step 2: write `n = p * n1` with `p ∤ n1` (using squarefreeness).
    have hp_nat : Nat.Prime p := hp
    have hn_eq : n = p * (n / p) := by
      -- `p ∣ n`
      exact (Nat.mul_div_cancel' hp_dvd_n).symm
    set n1 : ℕ := n / p
    have hn1_ne0_modp : (n1 : ZMod p) ≠ 0 := by
      -- If `p ∣ n1`, then `p^2 ∣ n`, contradicting `Squarefree n`.
      intro hn1_0
      have hp_dvd_n1 : p ∣ n1 := (ZMod.natCast_eq_zero_iff n1 p).1 hn1_0
      have hp2_dvd_n : p * p ∣ n := by
        -- `n = p * n1` and `p ∣ n1`
        rcases hp_dvd_n1 with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        -- `n = p * (p * t)`
        -- (use `hn_eq : n = p * n1` and `ht : n1 = p * t`)
        simpa [hn_eq, ht, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      -- squarefree contradiction
      have hsf := (Nat.squarefree_iff_prime_squarefree).1 hn_sq p hp_nat
      exact hsf hp2_dvd_n

    -- Step 3: use `Odd n`, so `2` is a unit in `ZMod n` and
    -- `hq_mod` really does mean `2*q = -1` in `ZMod n`. Then cast down to `ZMod p`.
    have h2u_n : IsUnit (2 : ZMod n) := GeometryOfNumbers.NumberTheory.zmod_isUnit_two_of_odd n hn_odd
    have h2q_n : (2 : ZMod n) * (q : ZMod n) = (-1 : ZMod n) := by
      calc
        (2 : ZMod n) * (q : ZMod n) = (2 : ZMod n) * (-(2 : ZMod n)⁻¹) := by simpa [hq_mod]
        _ = -((2 : ZMod n) * (2 : ZMod n)⁻¹) := by ring
        _ = (-1 : ZMod n) := by
          have h : (2 : ZMod n) * (2 : ZMod n)⁻¹ = (1 : ZMod n) :=
            ZMod.mul_inv_of_unit (2 : ZMod n) h2u_n
          simpa [h]
    have h2q_eq_neg1 : (2 : ZMod p) * (q : ZMod p) = (-1 : ZMod p) := by
      -- Convert `2*q = -1` in `ZMod n` into an integer divisibility statement, then reduce mod `p`.
      have h2q_add1_n : (2 : ZMod n) * (q : ZMod n) + 1 = 0 := by
        simp [h2q_n]
      have hn_dvd : (n : ℤ) ∣ (2 * (q : ℤ) + 1) := by
        -- cast the `ZMod n` equality to `ℤ`-divisibility
        have hZ : ((2 * (q : ℤ) + 1 : ℤ) : ZMod n) = 0 := by
          -- `(2*q+1 : ZMod n) = (2:ZMod n)*(q:ZMod n)+1`
          simpa [Int.cast_add, Int.cast_mul, Int.cast_natCast, add_assoc, mul_assoc, two_mul] using h2q_add1_n
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * (q : ℤ) + 1) n).1 hZ
      have hp_dvd_n_int : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hp_dvd_n
      have hp_dvd : (p : ℤ) ∣ (2 * (q : ℤ) + 1) := hp_dvd_n_int.trans hn_dvd
      have hZp : ((2 * (q : ℤ) + 1 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * (q : ℤ) + 1) p).2 hp_dvd
      -- rearrange `(2*q+1)=0` into `2*q=-1`
      have : (2 : ZMod p) * (q : ZMod p) + 1 = 0 := by
        simpa [Int.cast_add, Int.cast_mul, Int.cast_natCast, add_assoc, mul_assoc, two_mul] using hZp
      exact eq_neg_of_add_eq_zero_left this

    -- Step 4: a clean “divide by `p` once” argument (no `p^2` arithmetic needed).
    --
    -- Write `x = p*x1` (since `x = 0` in `ZMod p`).
    have hp_dvd_x : (p : ℤ) ∣ x :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd x p).1 (by simpa using hx0_modp)
    rcases hp_dvd_x with ⟨x1, rfl⟩

    -- Define `K1 = K / p` in ℕ, with `n = p*n1` and `K = p*K1`.
    have hn_nat : n = p * n1 := by
      simpa [n1] using (Nat.mul_div_cancel' hp_dvd_n).symm
    set K1 : ℕ := K / p
    have hK_nat : K = p * K1 := by
      simpa [K1] using (Nat.mul_div_cancel' hp_dvdK).symm

    -- From `K = n - (p*x1)^2` and `n = p*n1`, show `K1 ≡ n1 (mod p)`.
    have hK1_mod : (K1 : ℤ) ≡ (n1 : ℤ) [ZMOD (p : ℤ)] := by
      have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hnZ : (n : ℤ) = (p : ℤ) * (n1 : ℤ) := by
        -- cast `hn_nat`
        exact_mod_cast hn_nat
      have hKZ : (K : ℤ) = (p : ℤ) * (K1 : ℤ) := by
        exact_mod_cast hK_nat
      -- Expand `x^2 = (p*x1)^2 = p^2*x1^2` and cancel the common factor `p`.
      have : (p : ℤ) * (K1 : ℤ) = (p : ℤ) * ((n1 : ℤ) - (p : ℤ) * (x1 ^ 2)) := by
        -- Start from `hK_eq : (K:ℤ) = n - x^2`.
        -- Here `x` has been rewritten as `p*x1`.
        calc
          (p : ℤ) * (K1 : ℤ) = (K : ℤ) := by simpa [hKZ]
          _ = (n : ℤ) - ((p : ℤ) * x1) ^ 2 := by simpa [hK_eq]
          _ = (p : ℤ) * (n1 : ℤ) - (p : ℤ) ^ 2 * (x1 ^ 2) := by
                -- expand `((p*x1)^2)` into `p^2 * x1^2`
                simp [hnZ, pow_two, mul_assoc, mul_left_comm, mul_comm]
          _ = (p : ℤ) * ((n1 : ℤ) - (p : ℤ) * (x1 ^ 2)) := by ring
      have hk1 : (K1 : ℤ) = (n1 : ℤ) - (p : ℤ) * (x1 ^ 2) :=
        (mul_left_cancel₀ hpz this)
      -- Hence `K1 - n1` is a multiple of `p`.
      refine (Int.modEq_iff_dvd).2 ?_
      refine ⟨x1 ^ 2, ?_⟩
      -- `n1 - (n1 - p*x1^2) = p*x1^2`
      have : (n1 : ℤ) - ((n1 : ℤ) - (p : ℤ) * (x1 ^ 2)) = (p : ℤ) * (x1 ^ 2) := by
        ring
      simpa [hk1] using this

    -- Divide the main equation by `p` (exactly, because each term has a factor `p`).
    have h_div :
        (p : ℤ) * (y1 ^ 2) + (n1 : ℤ) * (z ^ 2) = 2 * (q : ℤ) * (K1 : ℤ) := by
      have hnZ : (n : ℤ) = (p : ℤ) * (n1 : ℤ) := by exact_mod_cast hn_nat
      have hKZ : (K : ℤ) = (p : ℤ) * (K1 : ℤ) := by exact_mod_cast hK_nat
      have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      -- Start from `h_eqK`, rewrite `n`/`K`, factor out `p`, then cancel.
      have h_eqK' :
          ((p : ℤ) * y1) ^ 2 + (p : ℤ) * (n1 : ℤ) * (z ^ 2) =
            2 * (q : ℤ) * ((p : ℤ) * (K1 : ℤ)) := by
        -- rewrite `n` and `K` in `h_eqK`
        simpa [hnZ, hKZ, mul_assoc, mul_left_comm, mul_comm] using h_eqK
      have hR : (p : ℤ) * (2 * (q : ℤ) * (K1 : ℤ)) = 2 * (q : ℤ) * ((p : ℤ) * (K1 : ℤ)) := by
        ring
      have hm :
          (p : ℤ) * ((p : ℤ) * (y1 ^ 2) + (n1 : ℤ) * (z ^ 2))
            = (p : ℤ) * (2 * (q : ℤ) * (K1 : ℤ)) := by
        calc
          (p : ℤ) * ((p : ℤ) * (y1 ^ 2) + (n1 : ℤ) * (z ^ 2))
              = ((p : ℤ) * y1) ^ 2 + (p : ℤ) * (n1 : ℤ) * (z ^ 2) := by ring
          _ = 2 * (q : ℤ) * ((p : ℤ) * (K1 : ℤ)) := h_eqK'
          _ = (p : ℤ) * (2 * (q : ℤ) * (K1 : ℤ)) := by
                simpa using hR.symm
      exact (mul_left_cancel₀ hpz hm)

    -- Reduce `h_div` modulo `p` and substitute `K1 ≡ n1 (mod p)` to obtain `z^2 ≡ 2q (mod p)`.
    have hz2_eq : (z : ZMod p) ^ 2 = (2 : ZMod p) * (q : ZMod p) := by
      -- First, modulo `p`: drop the `p * y1^2` term.
      have hmod1 : (n1 : ZMod p) * ((z : ZMod p) ^ 2) = (2 : ZMod p) * (q : ZMod p) * (K1 : ZMod p) := by
        have := congrArg (fun t : ℤ => (t : ZMod p)) h_div
        -- `p * y1^2` vanishes in `ZMod p`.
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
      -- Replace `K1` by `n1` using the congruence.
      have hK1_cast : (K1 : ZMod p) = (n1 : ZMod p) := by
        -- cast `Int.ModEq` into `ZMod p`
        have := congrArg (fun t : ℤ => (t : ZMod p)) hK1_mod.eq
        -- `Int.cast` agrees with `Nat.cast` here.
        simpa using this
      have hmod2 : (n1 : ZMod p) * ((z : ZMod p) ^ 2) = (2 : ZMod p) * (q : ZMod p) * (n1 : ZMod p) := by
        simpa [hK1_cast, mul_assoc, mul_left_comm, mul_comm] using hmod1
      -- Cancel `n1` (it is nonzero mod p).
      have hn1_ne0 : (n1 : ZMod p) ≠ 0 := hn1_ne0_modp
      -- Reassociate so both sides are `n1 * (...)`, then cancel.
      have hmod2' : (n1 : ZMod p) * ((z : ZMod p) ^ 2) = (n1 : ZMod p) * ((2 : ZMod p) * (q : ZMod p)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmod2
      exact mul_left_cancel₀ hn1_ne0 hmod2'

    -- From `z^2 = 2q` and `2q = -1`, get `z^2 = -1`, contradict `p % 4 = 3`.
    have hz_sq_neg1 : (z : ZMod p) ^ 2 = (-1 : ZMod p) := by
      -- rewrite using `h2q_eq_neg1`
      -- (this is the only place we use `hz2_eq`)
      simpa [hz2_eq, h2q_eq_neg1]
    have hz_ne0 : (z : ZMod p) ≠ 0 := by
      intro hz0
      have : (0 : ZMod p) = (-1 : ZMod p) := by simpa [hz0] using hz_sq_neg1
      simpa using this
    have hp_ne : p % 4 ≠ 3 :=
      ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (p := p) (x := (1 : ZMod p)) (y := (z : ZMod p))
        hz_ne0 (by
          -- `1^2 = -(z^2)` since `z^2 = -1`
          simp [hz_sq_neg1])
    exact hp_ne hp4

  -- Now we are in the main case `p ∤ n`. We can apply the mod-`p` contradiction lemma already proven.
  have hp_dvd_yz : (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z :=
    ankeny_p_dvd_yz_of_dvd_K (n := n) (q := q) (K := K) (p := p) (x := x) (y := y) (z := z)
      hp hp4 hp_dvdK hp_not_dvd_n hK_eq h_eqK

  -- Finish: show odd `padicValNat p K` is impossible.
  have hK_ne0 : K ≠ 0 := by
    intro hK0
    subst hK0
    simpa using hpK

  have hp_dvd_nmx : (p : ℤ) ∣ (n : ℤ) - x ^ 2 := by
    have : (p : ℤ) ∣ (K : ℤ) := by exact_mod_cast hp_dvdK
    simpa [hK_eq] using this

  -- Local kernel: if `p ∣ (n - x^2)` and `p ∣ (y^2 + n z^2)` with `p % 4 = 3` and `p ∤ n`,
  -- then `p ∣ y` and `p ∣ z`.
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
        -- `p` divides the form, hence `p ∣ y` and `p ∣ z`.
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

  -- If `padicValNat p K` were odd, we can force one more factor of `p` into `K`, contradiction.
  by_contra h_even
  have hk_odd : Odd (padicValNat p K) := Nat.not_even_iff_odd.1 h_even
  rcases hk_odd with ⟨t, hk⟩

  have hpowK : p ^ (2 * t + 1) ∣ K := by
    -- Use the characterization: `p^k ∣ K ↔ k ≤ padicValNat p K` (for `K ≠ 0`).
    have : (2 * t + 1) ≤ padicValNat p K := by simpa [hk]
    exact (padicValNat_dvd_iff_le (p := p) (a := K) (n := 2 * t + 1) hK_ne0).2 this

  have hpow_form : (p : ℤ) ^ (2 * t + 1) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by
    -- Start in `ℕ`, then cast to `ℤ`, and finally rewrite using `h_eqK`.
    have hnat : p ^ (2 * t + 1) ∣ 2 * q * K :=
      dvd_mul_of_dvd_right hpowK (2 * q)
    have hZ : (p ^ (2 * t + 1) : ℤ) ∣ (2 * q * K : ℤ) :=
      (Int.ofNat_dvd_natCast).2 hnat
    have hZ' : (p ^ (2 * t + 1) : ℤ) ∣ (2 * (q : ℤ) * (K : ℤ)) := by
      simpa [Nat.cast_mul, mul_assoc] using hZ
    -- rewrite `2*q*K` into the form of the left-hand side using `h_eqK`
    have : (p ^ (2 * t + 1) : ℤ) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by
      simpa [h_eqK, mul_assoc, mul_left_comm, mul_comm] using hZ'
    -- convert `(p ^ k : ℤ)` to `((p : ℤ) ^ k)`
    simpa [Nat.cast_pow] using this

  have hyz_pow : (p : ℤ) ^ (t + 1) ∣ y ∧ (p : ℤ) ^ (t + 1) ∣ z :=
    pow_dvd_yz_of_pow_dvd_form t (y := y) (z := z) hpow_form

  have hpow_form2 : (p : ℤ) ^ (2 * t + 2) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by
    rcases hyz_pow.1 with ⟨y1, rfl⟩
    rcases hyz_pow.2 with ⟨z1, rfl⟩
    -- factor out `p^(2t+2)`
    refine ⟨y1 ^ 2 + (n : ℤ) * z1 ^ 2, ?_⟩
    have hp2 :
        ((p : ℤ) ^ (t + 1)) ^ 2 = (p : ℤ) ^ (2 * t + 2) := by
      have ht : (t + 1) * 2 = 2 * t + 2 := by omega
      -- rewrite `((p^(t+1))^2)` as `p^((t+1)*2)`
      rw [← pow_mul]
      simpa [ht]
    calc
      ((p : ℤ) ^ (t + 1) * y1) ^ 2 + (n : ℤ) * ((p : ℤ) ^ (t + 1) * z1) ^ 2
          = ((p : ℤ) ^ (t + 1)) ^ 2 * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by ring
      _ = (p : ℤ) ^ (2 * t + 2) * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by
          simpa [hp2, mul_assoc, mul_left_comm, mul_comm]

  have hpow_nat2 : p ^ (2 * t + 2) ∣ 2 * q * K := by
    -- cast back to `ℕ` via `Int.ofNat_dvd_natCast`
    have hpowZ : ((p : ℤ) ^ (2 * t + 2)) ∣ (2 * (q : ℤ) * (K : ℤ)) := by
      simpa [h_eqK, mul_assoc, mul_left_comm, mul_comm] using hpow_form2
    have hpowZ' : (p ^ (2 * t + 2) : ℤ) ∣ (2 * (q : ℤ) * (K : ℤ)) := by
      simpa [Nat.cast_pow] using hpowZ
    have : (p ^ (2 * t + 2) : ℤ) ∣ (2 * q * K : ℤ) := by
      -- Avoid expanding casts aggressively (it can trigger simp recursion); associativity is enough.
      simpa [mul_assoc] using hpowZ'
    exact (Int.ofNat_dvd_natCast).1 this

  -- Show `p ∤ 2*q` (we use primality of `q` here).
  have hp_not_dvd_two : ¬ p ∣ 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hval : padicValNat p 2 = 0 := padicValNat_primes (p := p) (q := 2) hp_ne2
    intro hp2
    have : padicValNat p 2 ≠ 0 :=
      (dvd_iff_padicValNat_ne_zero (p := p) (n := 2) (hn0 := by decide)).1 hp2
    exact this hval

  have hp_not_dvd_q : ¬ p ∣ q := by
    haveI : Fact (Nat.Prime q) := ⟨hq_prime⟩
    have hval : padicValNat p q = 0 := padicValNat_primes (p := p) (q := q) hp_ne_q
    intro hpq
    have : padicValNat p q ≠ 0 :=
      (dvd_iff_padicValNat_ne_zero (p := p) (n := q) (hn0 := hq_prime.ne_zero)).1 hpq
    exact this hval

  have hp_not_dvd_2q : ¬ p ∣ 2 * q := by
    intro h
    have := (hp.dvd_mul).1 h
    cases this with
    | inl hp2 => exact hp_not_dvd_two hp2
    | inr hpq => exact hp_not_dvd_q hpq

  have hcop : Nat.Coprime (p ^ (2 * t + 2)) (2 * q) := by
    -- `Coprime p (2*q)` and then lift to powers.
    have : Nat.Coprime p (2 * q) := (hp.coprime_iff_not_dvd).2 hp_not_dvd_2q
    exact this.pow_left (2 * t + 2)

  have hpowK2 : p ^ (2 * t + 2) ∣ K :=
    (hcop.dvd_of_dvd_mul_left (by simpa [Nat.mul_assoc] using hpow_nat2))

  have hmax : ¬ p ^ (padicValNat p K + 1) ∣ K :=
    pow_succ_padicValNat_not_dvd (p := p) (n := K) hK_ne0
  have hcontra : p ^ (padicValNat p K + 1) ∣ K := by
    -- since `padicValNat p K = 2t+1` by `hk`
    have hexp : padicValNat p K + 1 = 2 * t + 2 := by
      calc
        padicValNat p K + 1 = (2 * t + 1) + 1 := by simpa [hk]
        _ = 2 * t + 2 := by omega
    -- rewrite the exponent to avoid simp recursion issues
    simpa [hexp] using hpowK2
  exact hmax hcontra

/-!
### Q₁ version: even valuation kernel

This is the Q₁ analogue of `ankeny_even_padicValNat_of_mem_primeFactors`.

In the Q₁ route we have an identity
\[
  y^2 + n z^2 = q \cdot K
\]
instead of `2*q*K`, and a slightly different congruence interface (`mod q` rather than `mod 2q`).

The intended structure is the same:
- for primes `p % 4 = 3` dividing `K`, force `p ∣ y,z` using `ankeny_p_dvd_yz_of_dvd_K_q1`,
- then show `p^2 ∣ K` and descend.
-/
