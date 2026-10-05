import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
The moduli `1 + (i+1)q` used to code finite sequences, and the Chinese remainder theorem
for them.
-/
import RequestProject.H10.Arith

open Dioph Finset

namespace H10

/-- The `i`-th modulus of the Chinese remainder coding with parameter `q`. -/
def modAt (q i : ℕ) : ℕ := 1 + (i + 1) * q

/-- The product of the moduli `modAt q i` for `i ≤ n`. -/
def modProd (q n : ℕ) : ℕ := ∏ i ∈ Finset.range (n + 1), modAt q i

theorem modAt_pos (q i : ℕ) : 0 < modAt q i := by
  simp [modAt]

theorem modProd_pos (q n : ℕ) : 0 < modProd q n :=
  Finset.prod_pos fun i _ => modAt_pos q i

theorem modProd_eq_apProd (q n : ℕ) : modProd q n = apProd 1 q (n + 1) := by
  unfold modProd apProd modAt
  induction n with
  | zero => simp
  | succ n ih =>
      conv_rhs => rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1 + 1)]
      rw [Finset.prod_range_succ, ih]

theorem lt_modAt {q i y : ℕ} (h : y < q) : y < modAt q i := by
  have : q ≤ (i+1) * q := Nat.le_mul_of_pos_left _ (by omega)
  simp only [modAt]
  omega

theorem coprime_modAt_of_lt {q n a b : ℕ} (hq : (n + 1).factorial ∣ q)
    (hab : a < b) (hbn : b ≤ n) : Nat.Coprime (modAt q a) (modAt q b) := by
  set d := Nat.gcd (modAt q a) (modAt q b) with hd
  have hda : d ∣ modAt q a := Nat.gcd_dvd_left _ _
  have hdb : d ∣ modAt q b := Nat.gcd_dvd_right _ _
  have hsub : modAt q a - (a+1) * q = 1 := by simp [modAt]
  have hdiff : d ∣ (b - a) * q := by
    have h1 : modAt q b - modAt q a = (b - a) * q := by
      simp only [modAt]
      have h2 : (b + 1) * q - (a + 1) * q = (b - a) * q := by
        rw [← Nat.sub_mul]
        congr 1
        omega
      omega
    rw [← h1]
    exact Nat.dvd_sub hdb hda
  have hcop_dq : Nat.Coprime d q := by
    have h1 : Nat.gcd d q ∣ modAt q a := (Nat.gcd_dvd_left d q).trans hda
    have h2 : Nat.gcd d q ∣ (a+1) * q := Dvd.dvd.mul_left (Nat.gcd_dvd_right d q) _
    have h3 : Nat.gcd d q ∣ 1 := by rw [← hsub]; exact Nat.dvd_sub h1 h2
    exact Nat.eq_one_of_dvd_one h3
  have hdba : d ∣ b - a := hcop_dq.dvd_of_dvd_mul_right hdiff
  have hdq : d ∣ q := hdba.trans ((Nat.dvd_factorial (by omega) (by omega)).trans hq)
  have hd1 : d ∣ 1 := by
    rw [← hsub]
    exact Nat.dvd_sub hda (Dvd.dvd.mul_left hdq _)
  exact Nat.eq_one_of_dvd_one hd1

/-- Distinct moduli are coprime, provided `q` is divisible by `(n+1)!`. -/
theorem coprime_modAt {q n i j : ℕ} (hq : (n + 1).factorial ∣ q)
    (hi : i ≤ n) (hj : j ≤ n) (hne : i ≠ j) : Nat.Coprime (modAt q i) (modAt q j) := by
  rcases Nat.lt_or_ge i j with h | h
  · exact coprime_modAt_of_lt hq h hj
  · exact (coprime_modAt_of_lt hq (by omega : j < i) hi).symm

theorem modAt_dvd_modProd {q n i : ℕ} (hi : i ≤ n) : modAt q i ∣ modProd q n :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega))

/-- If each modulus divides `X`, so does their product. -/
theorem modProd_dvd_of_forall {q n X : ℕ} (hq : (n + 1).factorial ∣ q)
    (h : ∀ i ≤ n, modAt q i ∣ X) : modProd q n ∣ X := by
  have key : ∀ m : ℕ, m ≤ n + 1 → (∏ i ∈ Finset.range m, modAt q i) ∣ X := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        intro hm
        rw [Finset.prod_range_succ]
        refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (ih (by omega)) (h m (by omega))
        refine Nat.Coprime.prod_left (fun i hi => ?_)
        simp only [Finset.mem_range] at hi
        exact coprime_modAt hq (by omega) (by omega) (by omega)
  exact key (n+1) le_rfl

/-- Chinese remainder theorem for the moduli `modAt q i`, `i ≤ n`: any finite sequence of
residues is realised, by arbitrarily large numbers. -/
theorem crt_exists {q n : ℕ} (hq : (n + 1).factorial ∣ q) (a : ℕ → ℕ) (b : ℕ) :
    ∃ U, b ≤ U ∧ ∀ i ≤ n, U ≡ a i [MOD modAt q i] := by
  have main : ∀ m : ℕ, m ≤ n → ∃ U, ∀ i ≤ m, U ≡ a i [MOD modAt q i] := by
    intro m
    induction m with
    | zero =>
        intro _
        exact ⟨a 0, fun i hi => by
          have : i = 0 := by omega
          subst this
          rfl⟩
    | succ m ih =>
        intro hm
        obtain ⟨U, hU⟩ := ih (by omega)
        have hcop : Nat.Coprime (∏ i ∈ Finset.range (m+1), modAt q i) (modAt q (m+1)) := by
          refine Nat.Coprime.prod_left (fun i hi => ?_)
          simp only [Finset.mem_range] at hi
          exact coprime_modAt hq (by omega) (by omega) (by omega)
        obtain ⟨V, hV1, hV2⟩ := Nat.chineseRemainder hcop U (a (m+1))
        refine ⟨V, fun i hi => ?_⟩
        rcases Nat.lt_or_ge i (m+1) with h | h
        · refine Nat.ModEq.trans ?_ (hU i (by omega))
          exact Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega))) hV1
        · have : i = m + 1 := by omega
          subst this
          exact hV2
  obtain ⟨U, hU⟩ := main n le_rfl
  refine ⟨U + (b + 1) * modProd q n, ?_, ?_⟩
  · have h1 : 1 ≤ modProd q n := modProd_pos q n
    calc b ≤ (b+1) * 1 := by omega
      _ ≤ (b+1) * modProd q n := Nat.mul_le_mul_left _ h1
      _ ≤ U + (b+1) * modProd q n := by omega
  · intro i hi
    have hdvd : modAt q i ∣ (b+1) * modProd q n := Dvd.dvd.mul_left (modAt_dvd_modProd hi) _
    have hmod : U ≡ U + (b+1) * modProd q n [MOD modAt q i] :=
      (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2 (by simpa using hdvd)
    exact hmod.symm.trans (hU i hi)

end H10

/-
Binomial coefficients, factorials and products of arithmetic progressions are Diophantine.
-/
import RequestProject.H10.Poly

open Dioph Finset

namespace H10

variable {α : Type}

/-! ### Binomial coefficients -/

theorem geom_sum_pred (u k : ℕ) (hu : 1 ≤ u) : ∑ j ∈ range k, (u - 1) * u ^ j = u ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have h1 : 1 ≤ u ^ k := Nat.one_le_pow _ _ hu
      have h2 : u ^ k ≤ u ^ k * u := Nat.le_mul_of_pos_right _ hu
      have h3 : (u-1) * u^k = u^k * u - u^k := by
        have h4 : u^k * u - u^k = u^k * (u-1) := by rw [Nat.mul_sub]; simp
        rw [h4, Nat.mul_comm]
      omega

theorem sum_choose_pow (n u : ℕ) : (u+1)^n = ∑ j ∈ range (n+1), n.choose j * u ^ j := by
  rw [add_pow]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_comm]

/-- The binomial coefficient `choose n k` is the `k`-th digit of `(u+1)^n` in base `u`. -/
theorem choose_eq_digit (n k u : ℕ) (hu : 2^n < u) : n.choose k = ((u+1)^n / u^k) % u := by
  have hu1 : 1 ≤ u := le_of_lt (lt_of_le_of_lt (Nat.one_le_two_pow) hu)
  have hchoose : ∀ j, n.choose j ≤ u - 1 := by
    intro j
    have h1 : n.choose j ≤ 2^n := Nat.choose_le_two_pow n j
    omega
  have hlow : ∀ m : ℕ, ∑ j ∈ range m, n.choose j * u ^ j < u ^ m := by
    intro m
    calc ∑ j ∈ range m, n.choose j * u ^ j ≤ ∑ j ∈ range m, (u-1) * u ^ j :=
          Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (hchoose j)
      _ = u ^ m - 1 := geom_sum_pred u m hu1
      _ < u ^ m := by have : 1 ≤ u^m := Nat.one_le_pow _ _ hu1; omega
  rcases Nat.lt_or_ge n k with hk | hk
  · have h0 : (u+1)^n < u ^ k := by
      calc (u+1)^n = ∑ j ∈ range (n+1), n.choose j * u ^ j := sum_choose_pow n u
        _ < u ^ (n+1) := hlow (n+1)
        _ ≤ u ^ k := Nat.pow_le_pow_right hu1 hk
    rw [Nat.div_eq_of_lt h0, Nat.zero_mod, Nat.choose_eq_zero_of_lt hk]
  · have hsplit : (u+1)^n = (∑ j ∈ range k, n.choose j * u ^ j)
        + u ^ k * (n.choose k + u * ∑ j ∈ Ico (k+1) (n+1), n.choose j * u ^ (j - k - 1)) := by
      rw [sum_choose_pow n u, ← Finset.sum_range_add_sum_Ico _ (by omega : k ≤ n+1),
        Finset.sum_eq_sum_Ico_succ_bot (by omega : k < n+1)]
      have h5 : ∀ j ∈ Ico (k+1) (n+1),
          n.choose j * u ^ j = u^k * (u * (n.choose j * u ^ (j-k-1))) := by
        intro j hj
        simp only [Finset.mem_Ico] at hj
        have h6 : u ^ j = u^k * (u * u^(j-k-1)) := by
          rw [← pow_succ', ← pow_add]
          congr 1
          omega
        rw [h6]; ring
      rw [Finset.sum_congr rfl h5, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    have hpos : 0 < u ^ k := by positivity
    rw [hsplit, Nat.add_mul_div_left _ _ hpos,
      Nat.div_eq_of_lt (hlow k), Nat.zero_add, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by have := hchoose k; omega)]

/-- Binomial coefficients are Diophantine. -/
theorem diophFn_choose {f g : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g) :
    DiophFn fun v => (f v).choose (g v) := by
  have du : DiophFn fun v => 2 ^ f v + 1 :=
    diophFn_add (diophFn_pow (diophFn_const 2) df) (diophFn_const 1)
  have key : DiophFn fun v => (((2 ^ f v + 1) + 1) ^ f v / (2 ^ f v + 1) ^ g v) % (2 ^ f v + 1) :=
    diophFn_mod (diophFn_div (diophFn_pow (diophFn_add du (diophFn_const 1)) df)
      (diophFn_pow du dg)) du
  exact DiophFn.congr key fun v => (choose_eq_digit (f v) (g v) (2 ^ f v + 1) (by omega)).symm

/-! ### Factorials -/

/-- An explicit form of the estimate `r(r-1)⋯(r-n+1) ≥ r^n - n^2 r^(n-1)`. -/
theorem pow_succ_le_descFactorial (r n : ℕ) :
    r ^ (n+1) ≤ r * r.descFactorial n + n * n * r ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rcases Nat.lt_or_ge r (n+1) with h | h
      · have h1 : r ^ (n+1+1) ≤ ((n+1)*(n+1)) * r^(n+1) := by
          rw [pow_succ']
          exact Nat.mul_le_mul_right _ (by nlinarith)
        omega
      · rw [Nat.descFactorial_succ]
        set D : ℤ := (r.descFactorial n : ℤ) with hD
        set X : ℤ := (r:ℤ)^n with hX
        have hXnn : (0:ℤ) ≤ X := by positivity
        have hr : (0:ℤ) ≤ (r:ℤ) := Int.natCast_nonneg r
        have hn : (0:ℤ) ≤ (n:ℤ) := Int.natCast_nonneg n
        have hDnn : (0:ℤ) ≤ D := Int.natCast_nonneg _
        have hrn : (n:ℤ) ≤ (r:ℤ) := by
          exact_mod_cast le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self n) h)
        have ihz : (r:ℤ) * X ≤ (r:ℤ) * D + (n:ℤ) * n * X := by
          have h2 : ((r ^ (n+1) : ℕ) : ℤ) ≤ ((r * r.descFactorial n + n * n * r ^ n : ℕ) : ℤ) :=
            Int.ofNat_le.mpr ih
          push_cast at h2
          rw [pow_succ'] at h2
          linarith [h2]
        have e1 : ((r:ℤ) - n) * ((r:ℤ) * X - (n:ℤ)*n*X) ≤ ((r:ℤ) - n) * ((r:ℤ) * D) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        have key : (r:ℤ) * ((r:ℤ) * X)
            ≤ (r:ℤ) * (((r:ℤ) - n) * D) + ((n:ℤ)+1)*((n:ℤ)+1)*((r:ℤ)*X) := by
          nlinarith [e1, mul_nonneg (mul_nonneg hn (mul_nonneg hn hn)) hXnn,
            mul_nonneg (mul_nonneg hr hn) hXnn, mul_nonneg hr hXnn]
        have hcast : ((r - n : ℕ) : ℤ) = (r:ℤ) - n := by
          push_cast [Nat.cast_sub (by exact_mod_cast hrn)]; ring
        have final : ((r ^ (n+1+1) : ℕ) : ℤ) ≤
            ((r * ((r - n) * r.descFactorial n) + (n+1) * (n+1) * r ^ (n+1) : ℕ) : ℤ) := by
          push_cast [hcast]
          rw [pow_succ', pow_succ']
          rw [hD, hX] at key
          linarith [key]
        exact_mod_cast final

/-- Davis' formula for the factorial: `n! = r^n / choose r n` once `r` is large. -/
theorem factorial_eq_div (n r : ℕ) (hr : n * n * (n.factorial + 1) < r) :
    n.factorial = r ^ n / r.choose n := by
  set F := n.factorial with hF
  have hF0 : 0 < F := Nat.factorial_pos n
  have hr0 : 0 < r := by nlinarith [Nat.zero_le (n*n*(F+1))]
  have hnr : n ≤ r := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · omega
    · nlinarith
  have hD : r.descFactorial n = F * r.choose n := Nat.descFactorial_eq_factorial_mul_choose r n
  have hC0 : 0 < r.choose n := Nat.choose_pos hnr
  have hrn : 0 < r ^ n := by positivity
  have key : F * r ^ n < (F + 1) * r.descFactorial n := by
    have h1 := pow_succ_le_descFactorial r n
    have h2 : (F+1) * (n * n) * r ^ n < r * r ^ n :=
      (Nat.mul_lt_mul_right hrn).mpr (by calc (F+1)*(n*n) = n*n*(F+1) := by ring
                                            _ < r := hr)
    have h4 : r ^ (n+1) = r * r ^ n := by rw [pow_succ']
    have h3 : (F+1) * (r * r ^ n) ≤ (F+1) * (r * r.descFactorial n) + (F+1) * (n * n * r ^ n) := by
      rw [← h4]; nlinarith
    have h5 : r * (F * r ^ n) < r * ((F+1) * r.descFactorial n) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left h5
  refine (Nat.div_eq_of_lt_le ?_ ?_).symm
  · rw [← hD]; exact Nat.descFactorial_le_pow r n
  · have h6 : F * r ^ n < F * ((F+1) * r.choose n) := by
      calc F * r ^ n < (F+1) * r.descFactorial n := key
        _ = F * ((F+1) * r.choose n) := by rw [hD]; ring
    exact Nat.lt_of_mul_lt_mul_left h6

theorem factorial_bound (n : ℕ) : n * n * (n.factorial + 1) < (n+1)^(2*n+4) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : n.factorial ≤ (n+1)^n :=
      le_trans (Nat.factorial_le_pow n) (Nat.pow_le_pow_left (by omega) n)
    have h2 : (1:ℕ) ≤ (n+1)^n := Nat.one_le_pow _ _ (by omega)
    have h3 : n * n * (n.factorial + 1) ≤ ((n+1)*(n+1)) * (2*(n+1)^n) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    have h4 : ((n+1)*(n+1)) * (2*(n+1)^n) ≤ (n+1)^(n+3) := by
      have h5 : (n+1)^(n+3) = ((n+1)*(n+1)) * ((n+1)^n * (n+1)) := by ring
      rw [h5]
      exact Nat.mul_le_mul_left _ (by nlinarith)
    have h6 : (n+1)^(n+3) < (n+1)^(2*n+4) := Nat.pow_lt_pow_right (by omega) (by omega)
    omega

/-- Factorials are Diophantine. -/
theorem diophFn_factorial {f : (α → ℕ) → ℕ} (df : DiophFn f) :
    DiophFn fun v => (f v).factorial := by
  have dr : DiophFn fun v => (f v + 1) ^ (2 * f v + 4) :=
    diophFn_pow (diophFn_add df (diophFn_const 1))
      (diophFn_add (diophFn_mul (diophFn_const 2) df) (diophFn_const 4))
  have key : DiophFn fun v =>
      ((f v + 1) ^ (2 * f v + 4)) ^ f v / ((f v + 1) ^ (2 * f v + 4)).choose (f v) :=
    diophFn_div (diophFn_pow dr df) (diophFn_choose dr df)
  exact DiophFn.congr key fun v => (factorial_eq_div (f v) _ (factorial_bound (f v))).symm

/-! ### Products of arithmetic progressions -/

/-- The product `(a+b)(a+2b)⋯(a+mb)`. -/
def apProd (a b m : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 m, (a + i * b)

theorem apProd_le (a b m : ℕ) : apProd a b m ≤ (a + m * b) ^ m := by
  have h : apProd a b m ≤ ∏ _i ∈ Finset.Icc 1 m, (a + m * b) := by
    refine Finset.prod_le_prod' ?_
    intro i hi
    simp only [Finset.mem_Icc] at hi
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.2) _
  simpa [Nat.card_Icc] using h

theorem apProd_modEq (a b c m M : ℕ) (h : b * c ≡ a [MOD M]) :
    apProd a b m ≡ b ^ m * (m.factorial * (c + m).choose m) [MOD M] := by
  have hasc : ∏ i ∈ Finset.Icc 1 m, (c + i) = (c+1).ascFactorial m := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.ascFactorial_succ]; ring
  rw [← ZMod.natCast_eq_natCast_iff] at h ⊢
  push_cast [apProd] at h ⊢
  have hcongr : ∀ i ∈ Finset.Icc 1 m, ((a : ZMod M) + i * b) = b * (c + i) := by
    intro i _
    rw [← h]; ring
  rw [Finset.prod_congr rfl hcongr, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
  have hasc' : ∏ i ∈ Finset.Icc 1 m, ((c : ZMod M) + i)
      = (((c+1).ascFactorial m : ℕ) : ZMod M) := by
    rw [← hasc]; push_cast; ring
  rw [hasc', Nat.ascFactorial_eq_factorial_mul_choose]
  push_cast
  ring_nf

/-- Characterisation of the product of an arithmetic progression by congruences: this is what
makes it Diophantine. -/
theorem apProd_spec (a b m y : ℕ) :
    y = apProd a b m ↔
      (b = 0 ∧ y = a ^ m) ∨
      (1 ≤ b ∧ y < b * (a + m*b)^m + 1 ∧
        ∃ c, (b * c) % (b * (a + m*b)^m + 1) = a % (b * (a + m*b)^m + 1) ∧
          y % (b * (a + m*b)^m + 1)
            = (b^m * (m.factorial * (c + m).choose m)) % (b * (a + m*b)^m + 1)) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · constructor
    · rintro rfl
      exact Or.inl ⟨rfl, by simp [apProd, Nat.card_Icc]⟩
    · rintro (⟨-, rfl⟩ | ⟨h, -⟩)
      · simp [apProd, Nat.card_Icc]
      · omega
  · set K := (a + m*b)^m with hK
    set M := b * K + 1 with hM
    have hMK : K < M := by
      have : K ≤ b * K := Nat.le_mul_of_pos_left _ hb
      omega
    have hprod : apProd a b m < M := lt_of_le_of_lt (apProd_le a b m) hMK
    have hinv : ∃ c, b * c ≡ a [MOD M] := by
      refine ⟨(a * (M - K)) % M, ?_⟩
      have h1 : b * ((a * (M - K)) % M) ≡ b * (a * (M - K)) [MOD M] :=
        Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
      refine h1.trans ?_
      have hcomm : M * b = b * M := Nat.mul_comm _ _
      have hbK : b * K = M - 1 := by omega
      have h5 : M ≤ M * b := Nat.le_mul_of_pos_right _ hb
      have h6 : b * K ≤ b * M := Nat.mul_le_mul_left _ (le_of_lt hMK)
      have hbm : b * (M - K) = M * (b-1) + 1 := by
        have h3 : b * (M - K) = b * M - b * K := by rw [Nat.mul_sub]
        have h4 : M * (b - 1) = M * b - M := by rw [Nat.mul_sub]; simp
        omega
      have h2 : b * (a * (M - K)) = a + (a*(b-1))*M := by
        calc b * (a * (M - K)) = a * (b * (M - K)) := by ring
          _ = a * (M * (b-1) + 1) := by rw [hbm]
          _ = a + (a*(b-1))*M := by ring
      rw [h2]
      have h8 : a + (a*(b-1))*M ≡ a + 0 [MOD M] :=
        Nat.ModEq.add_left a ((Nat.modEq_zero_iff_dvd).2 ⟨a*(b-1), by ring⟩)
      simpa using h8
    obtain ⟨c0, hc0⟩ := hinv
    constructor
    · rintro rfl
      refine Or.inr ⟨hb, hprod, c0 % M, ?_, ?_⟩
      · exact (Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)).trans hc0
      · exact apProd_modEq a b (c0 % M) m M
          ((Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)).trans hc0)
    · rintro (⟨h, -⟩ | ⟨-, hy, c, hc1, hc2⟩)
      · omega
      · have h1 : apProd a b m ≡ b ^ m * (m.factorial * (c + m).choose m) [MOD M] :=
          apProd_modEq a b c m M hc1
        have h7 : y ≡ apProd a b m [MOD M] := Nat.ModEq.trans hc2 (Nat.ModEq.symm h1)
        exact Nat.ModEq.eq_of_lt_of_lt h7 hy hprod

/-- Products of arithmetic progressions are Diophantine. -/
theorem diophFn_apProd {f g h : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g)
    (dh : DiophFn h) : DiophFn fun v => apProd (f v) (g v) (h v) := by
  set F : (Option α → ℕ) → ℕ := fun w => f (w ∘ some) with hF
  set G : (Option α → ℕ) → ℕ := fun w => g (w ∘ some) with hG
  set H : (Option α → ℕ) → ℕ := fun w => h (w ∘ some) with hH
  set Y : (Option α → ℕ) → ℕ := fun w => w none with hY
  have dF : DiophFn F := diophFn_lift df
  have dG : DiophFn G := diophFn_lift dg
  have dH : DiophFn H := diophFn_lift dh
  have dY : DiophFn Y := diophFn_head
  set M : (Option α → ℕ) → ℕ := fun w => G w * (F w + H w * G w) ^ H w + 1 with hM
  have dM : DiophFn M :=
    diophFn_add (diophFn_mul dG (diophFn_pow (diophFn_add dF (diophFn_mul dH dG)) dH))
      (diophFn_const 1)
  -- the existential part
  have dex : Dioph {w : Option α → ℕ | ∃ c,
      (G w * c) % M w = F w % M w ∧
        Y w % M w = (G w ^ H w * ((H w).factorial * (c + H w).choose (H w))) % M w} := by
    refine dioph_ex ?_
    have dc : DiophFn (fun w' : Option (Option α) → ℕ => w' none) := diophFn_head
    have dF' : DiophFn (fun w' : Option (Option α) → ℕ => F (w' ∘ some)) := diophFn_lift dF
    have dG' : DiophFn (fun w' : Option (Option α) → ℕ => G (w' ∘ some)) := diophFn_lift dG
    have dH' : DiophFn (fun w' : Option (Option α) → ℕ => H (w' ∘ some)) := diophFn_lift dH
    have dY' : DiophFn (fun w' : Option (Option α) → ℕ => Y (w' ∘ some)) := diophFn_lift dY
    have dM' : DiophFn (fun w' : Option (Option α) → ℕ => M (w' ∘ some)) := diophFn_lift dM
    exact dioph_and (dioph_eq (diophFn_mod (diophFn_mul dG' dc) dM') (diophFn_mod dF' dM'))
      (dioph_eq (diophFn_mod dY' dM')
        (diophFn_mod (diophFn_mul (diophFn_pow dG' dH')
          (diophFn_mul (diophFn_factorial dH') (diophFn_choose (diophFn_add dc dH') dH'))) dM'))
  have dT : Dioph {w : Option α → ℕ | (G w = 0 ∧ Y w = F w ^ H w) ∨
      (1 ≤ G w ∧ Y w < M w ∧ ∃ c,
        (G w * c) % M w = F w % M w ∧
        Y w % M w = (G w ^ H w * ((H w).factorial * (c + H w).choose (H w))) % M w)} :=
    dioph_or (dioph_and (dioph_eq dG (diophFn_const 0)) (dioph_eq dY (diophFn_pow dF dH)))
      (dioph_and (dioph_le (diophFn_const 1) dG) (dioph_and (dioph_lt dY dM) dex))
  refine Dioph.ext dT fun w => ?_
  constructor
  · intro hw
    exact ((apProd_spec (F w) (G w) (H w) (Y w)).2 hw).symm
  · intro hw
    exact (apProd_spec (F w) (G w) (H w) (Y w)).1 hw.symm

end H10

/-
Auxiliary facts about the integer polynomials underlying Mathlib's `Dioph` predicate:

* a polynomial depends on only finitely many variables, and is bounded by
  `C * (B+1)^d` on arguments bounded by `B`;
* polynomials respect congruences;
* every Diophantine set can be described with only finitely many auxiliary variables.
-/
import RequestProject.H10.Basic

open Dioph

namespace H10

variable {γ δ α : Type}

/-- A polynomial depends on only finitely many of its variables, and is bounded by
`C * (B+1)^d` on arguments bounded by `B`. -/
theorem IsPoly.spec {f : (γ → ℕ) → ℤ} (hf : IsPoly f) :
    ∃ (s : Finset γ) (C d : ℕ),
      (∀ x y : γ → ℕ, (∀ i ∈ s, x i = y i) → f x = f y) ∧
      (∀ (x : γ → ℕ) (B : ℕ), (∀ i ∈ s, x i ≤ B) → |f x| ≤ (C : ℤ) * (B + 1) ^ d) := by
  classical
  induction hf with
  | proj i =>
      refine ⟨{i}, 1, 1, ?_, ?_⟩
      · intro x y h; exact congrArg _ (h i (Finset.mem_singleton_self i))
      · intro x B h
        have h2 := h i (Finset.mem_singleton_self i)
        show |((x i : ℤ))| ≤ _
        rw [abs_of_nonneg (Int.natCast_nonneg (x i))]
        have : (x i : ℤ) ≤ (B : ℤ) + 1 := by exact_mod_cast Nat.le_succ_of_le h2
        simpa using this
  | const n =>
      refine ⟨∅, n.natAbs, 0, fun x y _ => rfl, ?_⟩
      intro x B _
      show |n| ≤ _
      simp only [pow_zero, mul_one, Int.abs_eq_natAbs, le_refl]
  | @sub f g _ _ ihf ihg =>
      obtain ⟨s1, C1, d1, e1, b1⟩ := ihf
      obtain ⟨s2, C2, d2, e2, b2⟩ := ihg
      refine ⟨s1 ∪ s2, C1 + C2, max d1 d2, ?_, ?_⟩
      · intro x y h
        show f x - g x = f y - g y
        rw [e1 x y (fun i hi => h i (Finset.mem_union_left _ hi)),
          e2 x y (fun i hi => h i (Finset.mem_union_right _ hi))]
      · intro x B h
        have h1 := b1 x B (fun i hi => h i (Finset.mem_union_left _ hi))
        have h2 := b2 x B (fun i hi => h i (Finset.mem_union_right _ hi))
        show |f x - g x| ≤ _
        calc |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
          _ ≤ (C1:ℤ) * ((B:ℤ)+1)^d1 + (C2:ℤ) * ((B:ℤ)+1)^d2 := by gcongr
          _ ≤ (C1:ℤ) * ((B:ℤ)+1)^(max d1 d2) + (C2:ℤ) * ((B:ℤ)+1)^(max d1 d2) := by
              gcongr <;> omega
          _ = ((C1 + C2 : ℕ):ℤ) * ((B:ℤ)+1)^(max d1 d2) := by push_cast; ring
  | @mul f g _ _ ihf ihg =>
      obtain ⟨s1, C1, d1, e1, b1⟩ := ihf
      obtain ⟨s2, C2, d2, e2, b2⟩ := ihg
      refine ⟨s1 ∪ s2, C1 * C2, d1 + d2, ?_, ?_⟩
      · intro x y h
        show f x * g x = f y * g y
        rw [e1 x y (fun i hi => h i (Finset.mem_union_left _ hi)),
          e2 x y (fun i hi => h i (Finset.mem_union_right _ hi))]
      · intro x B h
        have h1 := b1 x B (fun i hi => h i (Finset.mem_union_left _ hi))
        have h2 := b2 x B (fun i hi => h i (Finset.mem_union_right _ hi))
        show |f x * g x| ≤ _
        rw [abs_mul]
        calc |f x| * |g x| ≤ ((C1:ℤ) * ((B:ℤ)+1)^d1) * ((C2:ℤ) * ((B:ℤ)+1)^d2) := by
              apply mul_le_mul h1 h2 (abs_nonneg _)
              positivity
          _ = ((C1*C2 : ℕ):ℤ) * ((B:ℤ)+1)^(d1+d2) := by push_cast; ring

/-- Polynomials respect congruences. -/
theorem IsPoly.modEq {f : (γ → ℕ) → ℤ} (hf : IsPoly f) {m : ℤ} {x y : γ → ℕ}
    (h : ∀ i, (x i : ℤ) ≡ (y i : ℤ) [ZMOD m]) : f x ≡ f y [ZMOD m] := by
  induction hf with
  | proj i => exact h i
  | const n => exact Int.ModEq.refl n
  | sub _ _ ihf ihg => exact ihf.sub ihg
  | mul _ _ ihf ihg => exact ihf.mul ihg

/-- Substituting variables (or the constant `0`) into a polynomial gives a polynomial. -/
theorem IsPoly.subst {f : (γ → ℕ) → ℤ} (hf : IsPoly f) (σ : γ → Option δ) :
    IsPoly (fun w : δ → ℕ => f (fun c => (σ c).elim 0 w)) := by
  induction hf with
  | proj i =>
      cases h : σ i with
      | none => simpa [h] using IsPoly.const (α := δ) 0
      | some d => simpa [h] using IsPoly.proj (α := δ) d
  | const n => exact IsPoly.const n
  | sub _ _ ihf ihg => exact ihf.sub ihg
  | mul _ _ ihf ihg => exact ihf.mul ihg

/-- Every Diophantine set can be defined using only finitely many auxiliary variables. -/
theorem dioph_normal {S : Set (α → ℕ)} (h : Dioph S) :
    ∃ (β : Type) (_ : Fintype β) (p : Poly (α ⊕ β)),
      ∀ v, v ∈ S ↔ ∃ t : β → ℕ, p (Sum.elim v t) = 0 := by
  classical
  obtain ⟨β, p, pe⟩ := h
  obtain ⟨s, C, d, hdep, -⟩ := IsPoly.spec p.isPoly
  set sb : Finset β := s.preimage Sum.inr (Sum.inr_injective.injOn) with hsb
  have hmem : ∀ b : β, b ∈ sb ↔ Sum.inr b ∈ s := by
    intro b; simp [hsb]
  refine ⟨{b : β // b ∈ sb}, inferInstance,
    ⟨fun w => p (fun c => ((Sum.elim (fun a => some (Sum.inl a))
      (fun b => if hb : b ∈ sb then some (Sum.inr ⟨b, hb⟩) else none)
        c : Option (α ⊕ _))).elim 0 w),
      IsPoly.subst p.isPoly _⟩, ?_⟩
  intro v
  refine Iff.trans (pe v) ?_
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun b => t b.1, ?_⟩
    refine Eq.trans ?_ ht
    refine hdep _ _ ?_
    rintro (a | b) hc
    · rfl
    · have : b ∈ sb := (hmem b).2 hc
      simp [this]
  · rintro ⟨t, ht⟩
    refine ⟨fun b => if hb : b ∈ sb then t ⟨b, hb⟩ else 0, ?_⟩
    refine Eq.trans ?_ ht
    refine hdep _ _ ?_
    rintro (a | b) hc
    · rfl
    · have : b ∈ sb := (hmem b).2 hc
      simp [this]

/-- A finite conjunction of Diophantine conditions is Diophantine. -/
theorem dioph_forall_finset {β : Type} {S : β → Set (α → ℕ)} (t : Finset β)
    (h : ∀ j, Dioph (S j)) : Dioph {v | ∀ j ∈ t, v ∈ S j} := by
  classical
  induction t using Finset.induction with
  | empty =>
      have huniv : Dioph (Set.univ : Set (α → ℕ)) :=
        Dioph.of_no_dummies _ 0 (fun v => ⟨fun _ => Poly.zero_apply v, fun _ => trivial⟩)
      exact Dioph.ext huniv (fun v => by simp)
  | insert a t ha ih =>
      refine Dioph.ext (Dioph.inter (h a) ih) fun v => ?_
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩ j (rfl | hj)
        · exact h1
        · exact h2 j hj
      · intro H
        exact ⟨H a (Or.inl rfl), fun j hj => H j (Or.inr hj)⟩

theorem dioph_forall_fintype {β : Type} [Fintype β] {S : β → Set (α → ℕ)}
    (h : ∀ j, Dioph (S j)) : Dioph {v | ∀ j, v ∈ S j} := by
  exact Dioph.ext (dioph_forall_finset Finset.univ h)
    fun v => ⟨fun H j => H j (Finset.mem_univ j), fun H j _ => H j⟩

end H10

/-
Convenience layer over Mathlib's `Dioph` API, phrased for an arbitrary index type `α`
rather than the `Vector3` de Bruijn encoding.
-/
import Mathlib

open Dioph Nat

namespace H10

variable {α : Type}

@[inherit_doc] local infixr:67 " ::ₒ " => Option.elim'

/-! ### Congruence -/

/-- Diophantine functions are closed under pointwise equality. -/
theorem DiophFn.congr {f g : (α → ℕ) → ℕ} (df : DiophFn f) (h : ∀ v, f v = g v) : DiophFn g :=
  Dioph.ext df fun v => by simp only [Set.mem_setOf_eq, h]

/-- Diophantine sets are closed under pointwise equivalence. -/
theorem Dioph.congr {S T : Set (α → ℕ)} (d : Dioph S) (h : ∀ v, v ∈ S ↔ v ∈ T) : Dioph T :=
  Dioph.ext d h

/-! ### Basic functions -/

/-- The freshly quantified variable is a Diophantine function. -/
theorem diophFn_head : DiophFn (fun w : Option α → ℕ => w none) := Dioph.proj_dioph none

/-- Lifting a Diophantine function along the `Option` weakening. -/
theorem diophFn_lift {f : (α → ℕ) → ℕ} (df : DiophFn f) :
    DiophFn (fun w : Option α → ℕ => f (w ∘ some)) := Dioph.reindex_diophFn some df

/-- Lifting a Diophantine set along the `Option` weakening. -/
theorem dioph_lift {S : Set (α → ℕ)} (d : Dioph S) :
    Dioph {w : Option α → ℕ | (w ∘ some) ∈ S} := Dioph.reindex_dioph _ some d

theorem diophFn_const (n : ℕ) : DiophFn (fun _ : α → ℕ => n) := Dioph.const_dioph n

theorem diophFn_proj (i : α) : DiophFn (fun v : α → ℕ => v i) := Dioph.proj_dioph i

/-! ### Existential quantification -/

/-- Existential quantification over one new variable. -/
theorem dioph_ex {P : ℕ → (α → ℕ) → Prop}
    (h : Dioph {w : Option α → ℕ | P (w none) (w ∘ some)}) :
    Dioph {v : α → ℕ | ∃ x, P x v} :=
  Dioph.ext (Dioph.ex1_dioph h) fun _ =>
    ⟨fun ⟨x, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, hx⟩⟩

/-- Existential quantification over a whole family of new variables. -/
theorem dioph_ex_vec {β : Type} {P : (β → ℕ) → (α → ℕ) → Prop}
    (h : Dioph {w : α ⊕ β → ℕ | P (w ∘ Sum.inr) (w ∘ Sum.inl)}) :
    Dioph {v : α → ℕ | ∃ x : β → ℕ, P x v} := by
  refine Dioph.ext (Dioph.ex_dioph h) fun v => ?_
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa [Function.comp_def] using hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa [Function.comp_def] using hx⟩

/-! ### Logical connectives -/

theorem dioph_and {S T : Set (α → ℕ)} (ds : Dioph S) (dt : Dioph T) :
    Dioph {v | v ∈ S ∧ v ∈ T} := Dioph.inter ds dt

theorem dioph_or {S T : Set (α → ℕ)} (ds : Dioph S) (dt : Dioph T) :
    Dioph {v | v ∈ S ∨ v ∈ T} := Dioph.union ds dt

/-! ### Arithmetic -/

section
variable {f g : (α → ℕ) → ℕ}

theorem diophFn_add (df : DiophFn f) (dg : DiophFn g) : DiophFn fun v => f v + g v :=
  Dioph.add_dioph df dg

theorem diophFn_mul (df : DiophFn f) (dg : DiophFn g) : DiophFn fun v => f v * g v :=
  Dioph.mul_dioph df dg

theorem diophFn_sub (df : DiophFn f) (dg : DiophFn g) : DiophFn fun v => f v - g v :=
  Dioph.sub_dioph df dg

theorem diophFn_div (df : DiophFn f) (dg : DiophFn g) : DiophFn fun v => f v / g v :=
  Dioph.div_dioph df dg

theorem diophFn_mod (df : DiophFn f) (dg : DiophFn g) : DiophFn fun v => f v % g v :=
  Dioph.mod_dioph df dg

theorem diophFn_pow (df : DiophFn f) (dg : DiophFn g) : DiophFn fun v => f v ^ g v :=
  Dioph.pow_dioph df dg

theorem dioph_eq (df : DiophFn f) (dg : DiophFn g) : Dioph {v | f v = g v} :=
  Dioph.eq_dioph df dg

theorem dioph_le (df : DiophFn f) (dg : DiophFn g) : Dioph {v | f v ≤ g v} :=
  Dioph.le_dioph df dg

theorem dioph_lt (df : DiophFn f) (dg : DiophFn g) : Dioph {v | f v < g v} :=
  Dioph.lt_dioph df dg

theorem dioph_ne (df : DiophFn f) (dg : DiophFn g) : Dioph {v | f v ≠ g v} :=
  Dioph.ne_dioph df dg

theorem dioph_dvd (df : DiophFn f) (dg : DiophFn g) : Dioph {v | f v ∣ g v} :=
  Dioph.dvd_dioph df dg

end

end H10

