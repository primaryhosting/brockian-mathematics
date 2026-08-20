import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma ankeny_Q_mod (n q : ℕ) (b : ℤ) (x y z : ℤ)
    (hn_odd : Odd n)
    (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹)
    (hxy : x ≡ y [ZMOD n])
    (hybz : y ≡ b * z [ZMOD (2 * q)])
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (2 * q)]) :
    ankeny_Q n q x y z ≡ 0 [ZMOD (2 * n * q)] := by
  -- This lemma is the “algebraic glue” used after the Minkowski step:
  --
  -- - mod `n`: use `x ≡ y` and `2q ≡ -1` (from `hq_mod`)
  -- - mod `2q`: use `y ≡ b z` and `b^2 ≡ -n` (from `hb`)
  -- - combine by CRT (since `gcd(n,2q)=1` in the Ankeny setup)
  --
  -- We start by proving the mod-`2q` part, since it is self-contained.
  have hQ_mod_2q : ankeny_Q n q x y z ≡ 0 [ZMOD (2 * q : ℤ)] := by
    have hy2 : y ^ 2 ≡ (b * z) ^ 2 [ZMOD (2 * q : ℤ)] := hybz.pow 2
    have hy2' : y ^ 2 ≡ b ^ 2 * z ^ 2 [ZMOD (2 * q : ℤ)] := by
      -- `(b*z)^2 = b^2 * z^2`
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy2
    have hb_mul : b ^ 2 * z ^ 2 ≡ (-(n : ℤ)) * z ^ 2 [ZMOD (2 * q : ℤ)] :=
      Int.ModEq.mul_right (z ^ 2) hb
    have hsum_cancel : (-(n : ℤ)) * z ^ 2 + (n : ℤ) * z ^ 2 = 0 := by ring
    have hy_nz : y ^ 2 + (n : ℤ) * z ^ 2 ≡ 0 [ZMOD (2 * q : ℤ)] := by
      have h1 : y ^ 2 + (n : ℤ) * z ^ 2 ≡ b ^ 2 * z ^ 2 + (n : ℤ) * z ^ 2 [ZMOD (2 * q : ℤ)] :=
        (hy2'.add (Int.ModEq.refl _))
      have h2 : b ^ 2 * z ^ 2 + (n : ℤ) * z ^ 2 ≡ (-(n : ℤ)) * z ^ 2 + (n : ℤ) * z ^ 2 [ZMOD (2 * q : ℤ)] :=
        (hb_mul.add (Int.ModEq.refl _))
      have h3 : (-(n : ℤ)) * z ^ 2 + (n : ℤ) * z ^ 2 ≡ 0 [ZMOD (2 * q : ℤ)] := by
        simpa [hsum_cancel] using (Int.ModEq.refl (0 : ℤ))
      exact h1.trans (h2.trans h3)
    -- The `2q*x^2` term is 0 modulo `2q`.
    have h2qxx : (2 * (q : ℤ)) * x ^ 2 ≡ 0 [ZMOD (2 * q : ℤ)] := by
      refine (Int.modEq_zero_iff_dvd).2 ?_
      exact dvd_mul_right (2 * (q : ℤ)) (x ^ 2)
    -- Assemble.
    have : (2 * (q : ℤ)) * x ^ 2 + (y ^ 2 + (n : ℤ) * z ^ 2) ≡ 0 [ZMOD (2 * q : ℤ)] := by
      simpa [add_assoc, add_comm, add_left_comm] using (h2qxx.add hy_nz)
    simpa [ankeny_Q, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this

  -- Step 2: the mod-`n` part. This is where `hq_mod` is used to derive `2q ≡ -1 (mod n)`.
  have h2unit : IsUnit (2 : ZMod n) := GeometryOfNumbers.NumberTheory.zmod_isUnit_two_of_odd n hn_odd
  have hqunit : IsUnit (q : ZMod n) := by
    have h2inv : IsUnit ((2 : ZMod n)⁻¹) := by
      -- `ZMod.isUnit_inv` is the correct lemma here (since `ZMod n` is not a division monoid).
      simpa using (ZMod.isUnit_inv (m := n) (n := (2 : ℤ)) (by simpa using h2unit))
    have : IsUnit (-( (2 : ZMod n)⁻¹)) := IsUnit.neg h2inv
    simpa [hq_mod] using this
  have hnq : Nat.Coprime q n :=
    (ZMod.isUnit_iff_coprime q n).1 (by simpa using hqunit)
  have hncoprime : Nat.Coprime n (2 * q) := by
    have hn2 : Nat.Coprime n 2 := (Nat.coprime_two_right.2 hn_odd)
    have hnq' : Nat.Coprime n q := (Nat.coprime_comm.1 hnq)
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (hn2.mul_right hnq')
  have hmn : (n : ℤ).natAbs.Coprime (2 * q : ℤ).natAbs := by
    simpa using hncoprime

  have h2q_add_one_dvd : (n : ℤ) ∣ (2 * (q : ℤ) + 1) := by
    -- In `ZMod n`, `2*q + 1 = 0`.
    have hZ : ((2 * (q : ℤ) + 1 : ℤ) : ZMod n) = 0 := by
      -- `q = -(2)⁻¹` ⇒ `2*q = -1` ⇒ `2*q + 1 = 0`
      have h2q : (2 : ZMod n) * (q : ZMod n) = (-1 : ZMod n) := by
        calc
          (2 : ZMod n) * (q : ZMod n)
              = (2 : ZMod n) * (-(2 : ZMod n)⁻¹) := by simpa [hq_mod]
          _ = -((2 : ZMod n) * (2 : ZMod n)⁻¹) := by ring
          _ = (-1 : ZMod n) := by
            have h : (2 : ZMod n) * (2 : ZMod n)⁻¹ = (1 : ZMod n) :=
              ZMod.mul_inv_of_unit (2 : ZMod n) h2unit
            simpa [h]
      -- Convert `2*q = -1` to `2*q + 1 = 0`.
      have : (2 : ZMod n) * (q : ZMod n) + 1 = 0 := by
        calc
          (2 : ZMod n) * (q : ZMod n) + 1 = (-1 : ZMod n) + 1 := by simpa [h2q]
          _ = 0 := by simp
      -- Rewrite into the exact `ℤ`-cast form used below.
      simpa [two_mul, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * (q : ℤ) + 1) n).1 hZ

  have hQ_mod_n : ankeny_Q n q x y z ≡ 0 [ZMOD (n : ℤ)] := by
    have hx2 : x ^ 2 ≡ y ^ 2 [ZMOD (n : ℤ)] := hxy.pow 2
    have hmul : (2 * (q : ℤ)) * (x ^ 2) ≡ (2 * (q : ℤ)) * (y ^ 2) [ZMOD (n : ℤ)] :=
      Int.ModEq.mul_left _ hx2
    have hQ' :
        ankeny_Q n q x y z ≡ (2 * (q : ℤ)) * (y ^ 2) + (y ^ 2) + (n : ℤ) * (z ^ 2) [ZMOD (n : ℤ)] := by
      have hadd :
          (2 * (q : ℤ)) * (x ^ 2) + (y ^ 2) + (n : ℤ) * (z ^ 2)
            ≡ (2 * (q : ℤ)) * (y ^ 2) + (y ^ 2) + (n : ℤ) * (z ^ 2) [ZMOD (n : ℤ)] :=
        (hmul.add (Int.ModEq.refl _)).add (Int.ModEq.refl _)
      simpa [ankeny_Q, pow_two, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hadd
    have h2q1 : (2 * (q : ℤ) + 1) ≡ 0 [ZMOD (n : ℤ)] :=
      (Int.modEq_zero_iff_dvd).2 h2q_add_one_dvd
    have hnz : (n : ℤ) * (z ^ 2) ≡ 0 [ZMOD (n : ℤ)] := by
      refine (Int.modEq_zero_iff_dvd).2 ?_
      exact dvd_mul_right (n : ℤ) (z ^ 2)
    have hlin : (2 * (q : ℤ)) * (y ^ 2) + (y ^ 2) = (2 * (q : ℤ) + 1) * (y ^ 2) := by ring
    have hfirst : (2 * (q : ℤ) + 1) * (y ^ 2) ≡ 0 [ZMOD (n : ℤ)] :=
      by
        simpa using (Int.ModEq.mul_right (y ^ 2) h2q1)
    have : (2 * (q : ℤ)) * (y ^ 2) + (y ^ 2) + (n : ℤ) * (z ^ 2) ≡ 0 [ZMOD (n : ℤ)] := by
      simpa [hlin] using (hfirst.add hnz)
    exact hQ'.trans this

  -- Step 3: combine the mod-`n` and mod-`2q` statements.
  have hcrt : ankeny_Q n q x y z ≡ 0 [ZMOD (n : ℤ) * (2 * q : ℤ)] :=
    (Int.modEq_and_modEq_iff_modEq_mul hmn).1 ⟨hQ_mod_n, hQ_mod_2q⟩
  -- Normalize the modulus `(n : ℤ) * (2*q : ℤ)` to `2*n*q`.
  have hmul_nat : (n : ℤ) * (2 * q : ℤ) = (2 * n * q : ℤ) := by ring
  simpa [hmul_nat] using hcrt

/-- Minkowski application: there exists a representation `2qx² + y² + nz² = 2nq`. -/
