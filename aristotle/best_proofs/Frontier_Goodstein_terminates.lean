import Mathlib

/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Ordinal

/-! ### Elementary facts about base-`b` digits -/

lemma pow_log_pos (b n : ℕ) : 0 < b ^ Nat.log b n := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · exact pow_pos hb _

lemma mod_pow_log_lt_self (b : ℕ) {n : ℕ} (hn : n ≠ 0) : n % b ^ Nat.log b n < n :=
  lt_of_lt_of_le (Nat.mod_lt _ (pow_log_pos b n)) (Nat.pow_log_le_self b hn)

lemma mod_lt_pow_log (b n : ℕ) : n % b ^ Nat.log b n < b ^ Nat.log b n :=
  Nat.mod_lt _ (pow_log_pos b n)

lemma leading_digit_pos (b : ℕ) {n : ℕ} (hn : n ≠ 0) : 0 < n / b ^ Nat.log b n :=
  Nat.div_pos (Nat.pow_log_le_self b hn) (pow_log_pos b n)

lemma leading_digit_lt {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : n / b ^ Nat.log b n < b := by
  rw [Nat.div_lt_iff_lt_mul (pow_log_pos b n)]
  have := Nat.lt_pow_succ_log_self (b := b) (by omega) n
  simpa [pow_succ, Nat.mul_comm] using this

lemma log_of_digits {c E d r : ℕ} (hd0 : 0 < d) (hdc : d < c) (hr : r < c ^ E) :
    Nat.log c (c ^ E * d + r) = E := by
  refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_
  · calc c ^ E = c ^ E * 1 := by ring
      _ ≤ c ^ E * d := Nat.mul_le_mul_left _ hd0
      _ ≤ _ := Nat.le_add_right _ _
  · calc c ^ E * d + r < c ^ E * d + c ^ E := by omega
      _ = c ^ E * (d + 1) := by ring
      _ ≤ c ^ E * c := Nat.mul_le_mul_left _ (by omega)
      _ = c ^ (E + 1) := by ring

lemma div_of_digits {c E d r : ℕ} (hr : r < c ^ E) : (c ^ E * d + r) / c ^ E = d := by
  have h : 0 < c ^ E := by omega
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ h, Nat.div_eq_of_lt hr, Nat.zero_add]

lemma mod_of_digits {c E d r : ℕ} (hr : r < c ^ E) : (c ^ E * d + r) % c ^ E = r := by
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-! ### Hereditary base-`b` representations -/

/-- `hbEval b n` is the ordinal obtained by writing `n` in hereditary base `b`
(i.e. writing `n` in base `b`, and recursively writing the exponents in base `b` as well)
and then replacing every occurrence of the base `b` by the ordinal `ω`. -/
noncomputable def hbEval (b : ℕ) : ℕ → Ordinal.{0}
  | n =>
    if hn : n = 0 then 0
    else
      Ordinal.omega0 ^ (hbEval b (Nat.log b n)) * ((n / b ^ Nat.log b n : ℕ) : Ordinal) +
        hbEval b (n % b ^ Nat.log b n)
  decreasing_by
  · exact Nat.log_lt_self b hn
  · exact mod_pow_log_lt_self b hn

/-- `baseChange b c n` rewrites `n` in hereditary base `b` and then replaces every
occurrence of the base `b` by `c`. -/
def baseChange (b c : ℕ) : ℕ → ℕ
  | n =>
    if hn : n = 0 then 0
    else
      c ^ (baseChange b c (Nat.log b n)) * (n / b ^ Nat.log b n) +
        baseChange b c (n % b ^ Nat.log b n)
  decreasing_by
  · exact Nat.log_lt_self b hn
  · exact mod_pow_log_lt_self b hn

@[simp] lemma hbEval_zero (b : ℕ) : hbEval b 0 = 0 := by rw [hbEval]; simp

lemma hbEval_eq (b : ℕ) {n : ℕ} (hn : n ≠ 0) :
    hbEval b n = Ordinal.omega0 ^ (hbEval b (Nat.log b n)) * ((n / b ^ Nat.log b n : ℕ) : Ordinal) +
      hbEval b (n % b ^ Nat.log b n) := by
  rw [hbEval]; simp [hn]

@[simp] lemma baseChange_zero (b c : ℕ) : baseChange b c 0 = 0 := by rw [baseChange]; simp

lemma baseChange_eq (b c : ℕ) {n : ℕ} (hn : n ≠ 0) :
    baseChange b c n = c ^ (baseChange b c (Nat.log b n)) * (n / b ^ Nat.log b n) +
      baseChange b c (n % b ^ Nat.log b n) := by
  rw [baseChange]; simp [hn]

/-! ### Monotonicity of the ordinal evaluation -/

lemma omega_mul_add_lt {a x : Ordinal.{0}} {d : ℕ} (hx : x < omega0 ^ a) :
    omega0 ^ a * (d : Ordinal) + x < omega0 ^ a * ((d : Ordinal) + 1) := by
  rw [mul_add, mul_one]
  exact (add_lt_add_iff_left _).2 hx

lemma omega_mul_le {a : Ordinal.{0}} {x y : Ordinal.{0}} (h : x ≤ y) :
    omega0 ^ a * x ≤ omega0 ^ a * y := mul_le_mul_right h _

lemma omega_mul_succ_le {a : Ordinal.{0}} {d : ℕ} :
    omega0 ^ a * ((d : Ordinal) + 1) ≤ omega0 ^ (a + 1) := by
  rw [opow_add, opow_one]
  refine mul_le_mul_right ?_ _
  have h : ((d + 1 : ℕ) : Ordinal) < omega0 := nat_lt_omega0 _
  push_cast at h
  exact h.le

theorem hbEval_key {b : ℕ} (hb : 2 ≤ b) : ∀ N : ℕ,
    (∀ n ≤ N, ∀ m < n, hbEval b m < hbEval b n) ∧
      (∀ k ≤ N, ∀ n < b ^ k, hbEval b n < Ordinal.omega0 ^ hbEval b k) := by
  intro N
  induction N with
  | zero =>
    constructor
    · intro n hn m hm
      exact absurd hm (by omega)
    · intro k hk n hn
      have hk0 : k = 0 := by omega
      subst hk0
      have hn0 : n = 0 := by simpa using hn
      subst hn0
      simp
  | succ N ih =>
    obtain ⟨M, P⟩ := ih
    have M' : ∀ n ≤ N + 1, ∀ m < n, hbEval b m < hbEval b n := by
      intro n hn m hm
      rcases Nat.lt_or_ge n (N + 1) with h | h
      · exact M n (by omega) m hm
      · have hnN : n = N + 1 := by omega
        have hn0 : n ≠ 0 := by omega
        have hen : Nat.log b n < n := Nat.log_lt_self b hn0
        have hrn : n % b ^ Nat.log b n < n := mod_pow_log_lt_self b hn0
        have hd0 : 0 < n / b ^ Nat.log b n := leading_digit_pos b hn0
        have hnn := hbEval_eq b hn0
        have hlow : omega0 ^ hbEval b (Nat.log b n) * ((n / b ^ Nat.log b n : ℕ) : Ordinal)
            ≤ hbEval b n := by rw [hnn]; exact le_self_add
        rcases eq_or_ne m 0 with rfl | hm0
        · rw [hbEval_zero]
          refine lt_of_lt_of_le ?_ hlow
          exact mul_pos (opow_pos _ omega0_pos) (by exact_mod_cast hd0)
        · have hmm := hbEval_eq b hm0
          have hlog : Nat.log b m ≤ Nat.log b n := Nat.log_mono_right hm.le
          rcases lt_or_eq_of_le hlog with hlt | heq
          · have h1 : hbEval b m < omega0 ^ hbEval b (Nat.log b m + 1) :=
              P (Nat.log b m + 1) (by omega) m (Nat.lt_pow_succ_log_self (by omega) m)
            have h2 : hbEval b (Nat.log b m + 1) ≤ hbEval b (Nat.log b n) := by
              rcases eq_or_lt_of_le (show Nat.log b m + 1 ≤ Nat.log b n by omega) with heq' | hlt'
              · rw [heq']
              · exact le_of_lt (M (Nat.log b n) (by omega) _ hlt')
            have h3 : omega0 ^ hbEval b (Nat.log b m + 1) ≤ omega0 ^ hbEval b (Nat.log b n) :=
              opow_le_opow_right omega0_pos h2
            have h4 : omega0 ^ hbEval b (Nat.log b n)
                ≤ omega0 ^ hbEval b (Nat.log b n) * ((n / b ^ Nat.log b n : ℕ) : Ordinal) := by
              nth_rewrite 1 [show omega0 ^ hbEval b (Nat.log b n)
                  = omega0 ^ hbEval b (Nat.log b n) * 1 by simp]
              exact omega_mul_le (by exact_mod_cast hd0)
            exact lt_of_lt_of_le h1 (h3.trans (h4.trans hlow))
          · have hdle : m / b ^ Nat.log b n ≤ n / b ^ Nat.log b n := Nat.div_le_div_right hm.le
            rcases lt_or_eq_of_le hdle with hdlt | hdeq
            · have hr' : hbEval b (m % b ^ Nat.log b m) < omega0 ^ hbEval b (Nat.log b m) :=
                P (Nat.log b m) (by omega) _ (mod_lt_pow_log b m)
              have step1 : hbEval b m
                  < omega0 ^ hbEval b (Nat.log b m) * (((m / b ^ Nat.log b m : ℕ) : Ordinal) + 1) := by
                rw [hmm]; exact omega_mul_add_lt hr'
              have step2 : omega0 ^ hbEval b (Nat.log b m)
                  * (((m / b ^ Nat.log b m : ℕ) : Ordinal) + 1)
                  ≤ omega0 ^ hbEval b (Nat.log b n) * ((n / b ^ Nat.log b n : ℕ) : Ordinal) := by
                rw [heq]
                refine omega_mul_le ?_
                have h6 : ((m / b ^ Nat.log b n : ℕ) : Ordinal) + 1
                    = (((m / b ^ Nat.log b n) + 1 : ℕ) : Ordinal) := by push_cast; rfl
                rw [h6]
                exact_mod_cast Nat.succ_le_of_lt hdlt
              exact lt_of_lt_of_le step1 (step2.trans hlow)
            · have hrr : m % b ^ Nat.log b m < n % b ^ Nat.log b n := by
                have e1 := Nat.div_add_mod m (b ^ Nat.log b m)
                have e2 := Nat.div_add_mod n (b ^ Nat.log b n)
                rw [heq] at e1 ⊢
                rw [← hdeq] at e2
                omega
              have h5 := M (n % b ^ Nat.log b n) (by omega) _ hrr
              rw [heq] at h5
              rw [hmm, hnn, heq, hdeq]
              exact (add_lt_add_iff_left _).2 h5
    refine ⟨M', ?_⟩
    intro k hk n hn
    rcases Nat.lt_or_ge k (N + 1) with h | h
    · exact P k (by omega) n hn
    · have hkN : k = N + 1 := by omega
      rcases eq_or_ne n 0 with rfl | hn0
      · simpa using opow_pos (hbEval b k) omega0_pos
      · have hlogk : Nat.log b n < k := Nat.log_lt_of_lt_pow hn0 hn
        have hr' : hbEval b (n % b ^ Nat.log b n) < omega0 ^ hbEval b (Nat.log b n) :=
          P (Nat.log b n) (by omega) _ (mod_lt_pow_log b n)
        have hEe : hbEval b (Nat.log b n) < hbEval b k := M' k (by omega) _ hlogk
        calc hbEval b n
            < omega0 ^ hbEval b (Nat.log b n) * (((n / b ^ Nat.log b n : ℕ) : Ordinal) + 1) := by
              rw [hbEval_eq b hn0]; exact omega_mul_add_lt hr'
          _ ≤ omega0 ^ (hbEval b (Nat.log b n) + 1) := omega_mul_succ_le
          _ ≤ omega0 ^ hbEval b k :=
              opow_le_opow_right omega0_pos (Order.add_one_le_iff.mpr hEe)

theorem hbEval_strictMono {b : ℕ} (hb : 2 ≤ b) : StrictMono (hbEval b) := by
  intro m n h
  exact (hbEval_key hb n).1 n le_rfl m h

theorem hbEval_lt_opow {b : ℕ} (hb : 2 ≤ b) {n k : ℕ} (h : n < b ^ k) :
    hbEval b n < Ordinal.omega0 ^ hbEval b k :=
  (hbEval_key hb k).2 k le_rfl n h

/-! ### Monotonicity of the base change -/

theorem baseChange_key {b c : ℕ} (hb : 2 ≤ b) (hbc : b ≤ c) : ∀ N : ℕ,
    (∀ n ≤ N, ∀ m < n, baseChange b c m < baseChange b c n) ∧
      (∀ k ≤ N, ∀ n < b ^ k, baseChange b c n < c ^ baseChange b c k) := by
  have hc : 2 ≤ c := le_trans hb hbc
  intro N
  induction N with
  | zero =>
    refine ⟨fun n hn m hm => absurd hm (by omega), ?_⟩
    intro k hk n hn
    have hk0 : k = 0 := by omega
    subst hk0
    have hn0 : n = 0 := by simpa using hn
    subst hn0
    simp
  | succ N ih =>
    obtain ⟨M, P⟩ := ih
    have M' : ∀ n ≤ N + 1, ∀ m < n, baseChange b c m < baseChange b c n := by
      intro n hn m hm
      rcases Nat.lt_or_ge n (N + 1) with h | h
      · exact M n (by omega) m hm
      · have hn0 : n ≠ 0 := by omega
        have hen : Nat.log b n < n := Nat.log_lt_self b hn0
        have hrn : n % b ^ Nat.log b n < n := mod_pow_log_lt_self b hn0
        have hd0 : 0 < n / b ^ Nat.log b n := leading_digit_pos b hn0
        have hnn := baseChange_eq b c hn0
        have hcp : 0 < c ^ baseChange b c (Nat.log b n) := pow_pos (by omega) _
        have hlow : c ^ baseChange b c (Nat.log b n) * (n / b ^ Nat.log b n)
            ≤ baseChange b c n := by omega
        rcases eq_or_ne m 0 with rfl | hm0
        · have hpos : 0 < c ^ baseChange b c (Nat.log b n) * (n / b ^ Nat.log b n) :=
            Nat.mul_pos hcp hd0
          simp only [baseChange_zero]
          omega
        · have hmm := baseChange_eq b c hm0
          have hlog : Nat.log b m ≤ Nat.log b n := Nat.log_mono_right hm.le
          rcases lt_or_eq_of_le hlog with hlt | heq
          · have h1 : baseChange b c m < c ^ baseChange b c (Nat.log b m + 1) :=
              P (Nat.log b m + 1) (by omega) m (Nat.lt_pow_succ_log_self (by omega) m)
            have h2 : baseChange b c (Nat.log b m + 1) ≤ baseChange b c (Nat.log b n) := by
              rcases eq_or_lt_of_le (show Nat.log b m + 1 ≤ Nat.log b n by omega) with heq' | hlt'
              · rw [heq']
              · exact le_of_lt (M (Nat.log b n) (by omega) _ hlt')
            have h3 : c ^ baseChange b c (Nat.log b m + 1) ≤ c ^ baseChange b c (Nat.log b n) :=
              Nat.pow_le_pow_right (by omega) h2
            have h4 : c ^ baseChange b c (Nat.log b n)
                ≤ c ^ baseChange b c (Nat.log b n) * (n / b ^ Nat.log b n) :=
              Nat.le_mul_of_pos_right _ hd0
            omega
          · have hdle : m / b ^ Nat.log b n ≤ n / b ^ Nat.log b n := Nat.div_le_div_right hm.le
            rcases lt_or_eq_of_le hdle with hdlt | hdeq
            · have hr' : baseChange b c (m % b ^ Nat.log b m) < c ^ baseChange b c (Nat.log b m) :=
                P (Nat.log b m) (by omega) _ (mod_lt_pow_log b m)
              rw [heq] at hmm hr'
              have key : baseChange b c m
                  < c ^ baseChange b c (Nat.log b n) * (n / b ^ Nat.log b n) := by
                calc baseChange b c m
                    = c ^ baseChange b c (Nat.log b n) * (m / b ^ Nat.log b n)
                      + baseChange b c (m % b ^ Nat.log b n) := hmm
                  _ < c ^ baseChange b c (Nat.log b n) * (m / b ^ Nat.log b n)
                      + c ^ baseChange b c (Nat.log b n) := by omega
                  _ = c ^ baseChange b c (Nat.log b n) * (m / b ^ Nat.log b n + 1) := by ring
                  _ ≤ c ^ baseChange b c (Nat.log b n) * (n / b ^ Nat.log b n) :=
                      Nat.mul_le_mul_left _ (by omega)
              omega
            · have hrr : m % b ^ Nat.log b m < n % b ^ Nat.log b n := by
                have e1 := Nat.div_add_mod m (b ^ Nat.log b m)
                have e2 := Nat.div_add_mod n (b ^ Nat.log b n)
                rw [heq] at e1 ⊢
                rw [← hdeq] at e2
                omega
              have h5 := M (n % b ^ Nat.log b n) (by omega) _ hrr
              rw [heq] at hmm h5
              rw [hdeq] at hmm
              omega
    refine ⟨M', ?_⟩
    intro k hk n hn
    rcases Nat.lt_or_ge k (N + 1) with h | h
    · exact P k (by omega) n hn
    · rcases eq_or_ne n 0 with rfl | hn0
      · simpa using pow_pos (show 0 < c by omega) (baseChange b c k)
      · have hlogk : Nat.log b n < k := Nat.log_lt_of_lt_pow hn0 hn
        have hr' : baseChange b c (n % b ^ Nat.log b n) < c ^ baseChange b c (Nat.log b n) :=
          P (Nat.log b n) (by omega) _ (mod_lt_pow_log b n)
        have hEe : baseChange b c (Nat.log b n) < baseChange b c k := M' k (by omega) _ hlogk
        have hdb : n / b ^ Nat.log b n < b := leading_digit_lt hb n
        calc baseChange b c n
            = c ^ baseChange b c (Nat.log b n) * (n / b ^ Nat.log b n)
              + baseChange b c (n % b ^ Nat.log b n) := baseChange_eq b c hn0
          _ < c ^ baseChange b c (Nat.log b n) * (n / b ^ Nat.log b n)
              + c ^ baseChange b c (Nat.log b n) := by omega
          _ = c ^ baseChange b c (Nat.log b n) * (n / b ^ Nat.log b n + 1) := by ring
          _ ≤ c ^ baseChange b c (Nat.log b n) * c := Nat.mul_le_mul_left _ (by omega)
          _ = c ^ (baseChange b c (Nat.log b n) + 1) := by ring
          _ ≤ c ^ baseChange b c k := Nat.pow_le_pow_right (by omega) (by omega)

theorem baseChange_strictMono {b c : ℕ} (hb : 2 ≤ b) (hbc : b ≤ c) :
    StrictMono (baseChange b c) := by
  intro m n h
  exact (baseChange_key hb hbc n).1 n le_rfl m h

theorem baseChange_lt_pow {b c : ℕ} (hb : 2 ≤ b) (hbc : b ≤ c) {n k : ℕ} (h : n < b ^ k) :
    baseChange b c n < c ^ baseChange b c k :=
  (baseChange_key hb hbc k).2 k le_rfl n h

lemma baseChange_pos {b c : ℕ} (hb : 2 ≤ b) (hbc : b ≤ c) {n : ℕ} (hn : n ≠ 0) :
    0 < baseChange b c n := by
  have := baseChange_strictMono hb hbc (Nat.pos_of_ne_zero hn)
  simpa using this

/-! ### The base change does not change the ordinal value -/

theorem hbEval_baseChange {b c : ℕ} (hb : 2 ≤ b) (hbc : b ≤ c) (n : ℕ) :
    hbEval c (baseChange b c n) = hbEval b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hd0 : 0 < n / b ^ Nat.log b n := leading_digit_pos b hn0
      have hdb : n / b ^ Nat.log b n < b := leading_digit_lt hb n
      have hr : n % b ^ Nat.log b n < b ^ Nat.log b n := mod_lt_pow_log b n
      have hen : Nat.log b n < n := Nat.log_lt_self b hn0
      have hrn : n % b ^ Nat.log b n < n := mod_pow_log_lt_self b hn0
      have hR := baseChange_eq b c hn0
      have hRr : baseChange b c (n % b ^ Nat.log b n) < c ^ baseChange b c (Nat.log b n) :=
        baseChange_lt_pow hb hbc hr
      have hlogc : Nat.log c (baseChange b c n) = baseChange b c (Nat.log b n) := by
        rw [hR]; exact log_of_digits hd0 (by omega) hRr
      have hdivc : baseChange b c n / c ^ baseChange b c (Nat.log b n) = n / b ^ Nat.log b n := by
        rw [hR]; exact div_of_digits hRr
      have hmodc : baseChange b c n % c ^ baseChange b c (Nat.log b n)
          = baseChange b c (n % b ^ Nat.log b n) := by
        rw [hR]; exact mod_of_digits hRr
      have hBn0 : baseChange b c n ≠ 0 := (baseChange_pos hb hbc hn0).ne'
      rw [hbEval_eq c hBn0, hbEval_eq b hn0, hlogc, hdivc, hmodc, ih _ hen, ih _ hrn]

/-! ### Goodstein sequences -/

/-- The Goodstein sequence starting at `n`: `goodstein n 0 = n`, and `goodstein n (k+1)` is
obtained from `goodstein n k` by rewriting it in hereditary base `k+2`, replacing the base
`k+2` by `k+3`, and subtracting one. -/
def goodstein (n : ℕ) : ℕ → ℕ
  | 0 => n
  | (k + 1) => baseChange (k + 2) (k + 3) (goodstein n k) - 1

/-- **Goodstein's theorem**: every Goodstein sequence eventually reaches `0`. -/
theorem Goodstein_terminates (n : ℕ) : ∃ k, goodstein n k = 0 := by
  by_contra hcon
  push_neg at hcon
  set f : ℕ → Ordinal.{0} := fun k => hbEval (k + 2) (goodstein n k) with hf
  have hstep : ∀ k, f (k + 1) < f k := by
    intro k
    have hbase : (2 : ℕ) ≤ k + 2 := by omega
    have hle : (k + 2 : ℕ) ≤ k + 3 := by omega
    have hgk : goodstein n k ≠ 0 := hcon k
    have hA : 0 < baseChange (k + 2) (k + 3) (goodstein n k) :=
      baseChange_pos hbase hle hgk
    have h1 : baseChange (k + 2) (k + 3) (goodstein n k) - 1 <
        baseChange (k + 2) (k + 3) (goodstein n k) := by omega
    have h2 : hbEval (k + 3) (baseChange (k + 2) (k + 3) (goodstein n k) - 1) <
        hbEval (k + 3) (baseChange (k + 2) (k + 3) (goodstein n k)) :=
      hbEval_strictMono (by omega) h1
    have h3 : hbEval (k + 3) (baseChange (k + 2) (k + 3) (goodstein n k)) =
        hbEval (k + 2) (goodstein n k) := hbEval_baseChange hbase hle _
    simp only [hf, goodstein]
    have : (k + 1 + 2) = k + 3 := by omega
    rw [this]
    exact h3 ▸ h2
  obtain ⟨x, ⟨k, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Ordinal.{0})).has_min (Set.range f) ⟨f 0, 0, rfl⟩
  exact hmin (f (k + 1)) ⟨k + 1, rfl⟩ (hstep k)

end Frontier

