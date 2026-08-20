/-
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

/-! ## Elementary facts about base-`b` digits -/

theorem pow_log_pos (b n : ℕ) : 0 < b ^ Nat.log b n := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp [Nat.log_zero_left]
  · exact pow_pos hb _

theorem mod_pow_log_lt {b n : ℕ} (hn : n ≠ 0) : n % b ^ Nat.log b n < n :=
  lt_of_lt_of_le (Nat.mod_lt _ (pow_log_pos b n)) (Nat.pow_log_le_self b hn)

theorem digit_pos {b n : ℕ} (hn : n ≠ 0) : 1 ≤ n / b ^ Nat.log b n :=
  (Nat.one_le_div_iff (pow_log_pos b n)).2 (Nat.pow_log_le_self b hn)

theorem digit_lt {b n : ℕ} (hb : 2 ≤ b) : n / b ^ Nat.log b n < b := by
  have h := Nat.lt_pow_succ_log_self (b := b) hb n
  rw [Nat.div_lt_iff_lt_mul (pow_log_pos b n)]
  simpa [pow_succ, Nat.mul_comm] using h

/-! ## A generic hereditary base-`b` evaluation -/

/-- `hval b pw mul n` is the value of the hereditary base-`b` representation of `n`,
where the "power" operation is interpreted by `pw` and multiplication by a digit by `mul`. -/
def hval {α : Type*} [Zero α] [Add α] (b : ℕ) (pw : α → α) (mul : α → ℕ → α) (n : ℕ) : α :=
  if _hn : n = 0 then 0
  else
    mul (pw (hval b pw mul (Nat.log b n))) (n / b ^ Nat.log b n)
      + hval b pw mul (n % b ^ Nat.log b n)
termination_by n
decreasing_by
  · exact Nat.log_lt_self b _hn
  · exact mod_pow_log_lt _hn

@[simp] theorem hval_zero {α : Type*} [Zero α] [Add α] (b : ℕ) (pw : α → α) (mul : α → ℕ → α) :
    hval b pw mul 0 = 0 := by
  rw [hval]; simp

theorem hval_eq {α : Type*} [Zero α] [Add α] (b : ℕ) (pw : α → α) (mul : α → ℕ → α)
    {n : ℕ} (hn : n ≠ 0) :
    hval b pw mul n =
      mul (pw (hval b pw mul (Nat.log b n))) (n / b ^ Nat.log b n)
        + hval b pw mul (n % b ^ Nat.log b n) := by
  rw [hval]; simp [hn]

/-- The properties of `pw`, `mul` and the order on `α` needed for the argument. -/
structure HypSet (α : Type*) [LinearOrder α] [Zero α] [One α] [Add α]
    (b : ℕ) (pw : α → α) (mul : α → ℕ → α) : Prop where
  zero_le : ∀ a : α, 0 ≤ a
  add_lt_left : ∀ a x y : α, x < y → a + x < a + y
  add_le_left : ∀ a x y : α, x ≤ y → a + x ≤ a + y
  add_zero' : ∀ a : α, a + 0 = a
  mul_one' : ∀ a : α, mul a 1 = a
  mul_mono : ∀ (a : α) (k l : ℕ), k ≤ l → mul a k ≤ mul a l
  mul_succ' : ∀ (a : α) (k : ℕ), mul a (k + 1) = mul a k + a
  pw_pos : ∀ a : α, 0 < pw a
  pw_mono : ∀ a c : α, a ≤ c → pw a ≤ pw c
  pw_step : ∀ (a : α) (k : ℕ), k ≤ b → mul (pw a) (k + 1) ≤ pw (a + 1)
  add_one_le : ∀ a c : α, a < c → a + 1 ≤ c

section Generic

variable {α : Type*} [LinearOrder α] [Zero α] [One α] [Add α]
  {b : ℕ} {pw : α → α} {mul : α → ℕ → α}

theorem hval_pos (h : HypSet α b pw mul) {n : ℕ} (hn : n ≠ 0) : 0 < hval b pw mul n := by
  rw [hval_eq b pw mul hn]
  set A := pw (hval b pw mul (Nat.log b n)) with hA
  calc (0 : α) < A := h.pw_pos _
    _ = mul A 1 := (h.mul_one' _).symm
    _ ≤ mul A (n / b ^ Nat.log b n) := h.mul_mono _ _ _ (digit_pos hn)
    _ ≤ mul A (n / b ^ Nat.log b n) + hval b pw mul (n % b ^ Nat.log b n) := by
        have := h.add_le_left (mul A (n / b ^ Nat.log b n)) 0
          (hval b pw mul (n % b ^ Nat.log b n)) (h.zero_le _)
        simpa [h.add_zero'] using this

/-- The two key facts, proved by simultaneous strong induction:
`hval` is strictly monotone, and it maps `[0, b^E)` below `pw (hval E)`. -/
theorem hval_key (h : HypSet α b pw mul) (hb : 2 ≤ b) (n : ℕ) :
    (∀ m, m < n → hval b pw mul m < hval b pw mul n) ∧
      (∀ m, m < b ^ n → hval b pw mul m < pw (hval b pw mul n)) := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    have part1 : ∀ m, m < n → hval b pw mul m < hval b pw mul n := by
      intro m hmn
      have hn : n ≠ 0 := by omega
      have hEn : Nat.log b n < n := Nat.log_lt_self b hn
      have hrb : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ (pow_log_pos b n)
      have hrn : n % b ^ Nat.log b n < n := mod_pow_log_lt hn
      have hc1 : 1 ≤ n / b ^ Nat.log b n := digit_pos hn
      have hvn : hval b pw mul n =
          mul (pw (hval b pw mul (Nat.log b n))) (n / b ^ Nat.log b n)
            + hval b pw mul (n % b ^ Nat.log b n) := hval_eq b pw mul hn
      set A := pw (hval b pw mul (Nat.log b n)) with hA
      have hQE : ∀ x, x < b ^ Nat.log b n → hval b pw mul x < A := (IH _ hEn).2
      have htail : ∀ x : α, x ≤ mul A (n / b ^ Nat.log b n) →
          x ≤ hval b pw mul n := by
        intro x hx
        refine hx.trans ?_
        rw [hvn]
        have := h.add_le_left (mul A (n / b ^ Nat.log b n)) 0
          (hval b pw mul (n % b ^ Nat.log b n)) (h.zero_le _)
        simpa [h.add_zero'] using this
      rcases eq_or_ne m 0 with rfl | hm0
      · simpa using hval_pos h hn
      · have hvm : hval b pw mul m =
            mul (pw (hval b pw mul (Nat.log b m))) (m / b ^ Nat.log b m)
              + hval b pw mul (m % b ^ Nat.log b m) := hval_eq b pw mul hm0
        have hEE' : Nat.log b m ≤ Nat.log b n := Nat.log_mono_right hmn.le
        rcases lt_or_eq_of_le hEE' with hlt | heq
        · have h1 : m < b ^ Nat.log b n :=
            lt_of_lt_of_le (Nat.lt_pow_succ_log_self hb m)
              (Nat.pow_le_pow_right (by omega) (by omega))
          refine lt_of_lt_of_le (hQE m h1) (htail A ?_)
          calc A = mul A 1 := (h.mul_one' A).symm
            _ ≤ mul A (n / b ^ Nat.log b n) := h.mul_mono _ _ _ hc1
        · rw [heq] at hvm
          have hdiv : m / b ^ Nat.log b n ≤ n / b ^ Nat.log b n :=
            Nat.div_le_div_right hmn.le
          have hr'b : m % b ^ Nat.log b n < b ^ Nat.log b n := by
            rw [← heq]; exact Nat.mod_lt _ (pow_log_pos b m)
          rcases lt_or_eq_of_le hdiv with hcc | hcc
          · rw [hvm]
            have step1 : mul A (m / b ^ Nat.log b n) + hval b pw mul (m % b ^ Nat.log b n)
                < mul A (m / b ^ Nat.log b n) + A :=
              h.add_lt_left _ _ _ (hQE _ hr'b)
            refine lt_of_lt_of_le step1 (htail _ ?_)
            calc mul A (m / b ^ Nat.log b n) + A
                = mul A (m / b ^ Nat.log b n + 1) := (h.mul_succ' _ _).symm
              _ ≤ mul A (n / b ^ Nat.log b n) := h.mul_mono _ _ _ hcc
          · -- same leading digit: compare the remainders
            have hmm : b ^ Nat.log b n * (m / b ^ Nat.log b n) + m % b ^ Nat.log b n = m :=
              Nat.div_add_mod m _
            have hnn : b ^ Nat.log b n * (n / b ^ Nat.log b n) + n % b ^ Nat.log b n = n :=
              Nat.div_add_mod n _
            have hrr : m % b ^ Nat.log b n < n % b ^ Nat.log b n := by
              rw [hcc] at hmm; omega
            rw [hvm, hvn, hcc]
            exact h.add_lt_left _ _ _ ((IH _ hrn).1 _ hrr)
    refine ⟨part1, ?_⟩
    intro m hm
    rcases eq_or_ne m 0 with rfl | hm0
    · simpa using h.pw_pos (hval b pw mul n)
    · have hE'n : Nat.log b m < n := Nat.log_lt_of_lt_pow hm0 hm
      have hr' : m % b ^ Nat.log b m < b ^ Nat.log b m := Nat.mod_lt _ (pow_log_pos b m)
      have hc'b : m / b ^ Nat.log b m < b := digit_lt hb
      have hQE' := (IH _ hE'n).2
      have hlt : hval b pw mul (Nat.log b m) < hval b pw mul n := part1 _ hE'n
      calc hval b pw mul m
          = mul (pw (hval b pw mul (Nat.log b m))) (m / b ^ Nat.log b m)
              + hval b pw mul (m % b ^ Nat.log b m) := hval_eq b pw mul hm0
        _ < mul (pw (hval b pw mul (Nat.log b m))) (m / b ^ Nat.log b m)
              + pw (hval b pw mul (Nat.log b m)) := h.add_lt_left _ _ _ (hQE' _ hr')
        _ = mul (pw (hval b pw mul (Nat.log b m))) (m / b ^ Nat.log b m + 1) :=
              (h.mul_succ' _ _).symm
        _ ≤ pw (hval b pw mul (Nat.log b m) + 1) := h.pw_step _ _ (by omega)
        _ ≤ pw (hval b pw mul n) := h.pw_mono _ _ (h.add_one_le _ _ hlt)

theorem hval_strictMono (h : HypSet α b pw mul) (hb : 2 ≤ b) :
    StrictMono (hval b pw mul) := fun m n hmn => (hval_key h hb n).1 m hmn

theorem hval_lt_pw (h : HypSet α b pw mul) (hb : 2 ≤ b) {E m : ℕ} (hm : m < b ^ E) :
    hval b pw mul m < pw (hval b pw mul E) := (hval_key h hb E).2 m hm

end Generic

/-! ## The two instances: ordinals and natural numbers -/

/-- The ordinal obtained from the hereditary base-`b` representation of `n` by replacing
each occurrence of `b` by `ω`. -/
noncomputable def hord (b : ℕ) (n : ℕ) : Ordinal.{0} :=
  hval b (fun a => (Ordinal.omega0.{0}) ^ a) (fun a k => a * (k : Ordinal.{0})) n

/-- The natural number obtained from the hereditary base-`b` representation of `n` by
replacing each occurrence of `b` by `b + 1`. -/
def bump (b : ℕ) (n : ℕ) : ℕ :=
  hval b (fun a => (b + 1) ^ a) (fun a k => a * k) n

theorem hypSet_ord (b : ℕ) :
    HypSet Ordinal b (fun a => (Ordinal.omega0) ^ a) (fun a k => a * (k : Ordinal)) where
  zero_le a := bot_le

  add_lt_left a x y h := add_lt_add_right h a
  add_le_left a x y h := (add_le_add_iff_left a).mpr h
  add_zero' a := add_zero a
  mul_one' a := by simp
  mul_mono a k l h := mul_le_mul_right (Nat.cast_le.2 h) a
  mul_succ' a k := by push_cast; rw [mul_add_one]
  pw_pos a := Ordinal.opow_pos a Ordinal.omega0_pos
  pw_mono a c h := Ordinal.opow_le_opow_right Ordinal.omega0_pos h
  pw_step a k _ := by
    show (Ordinal.omega0 ^ a) * ((k + 1 : ℕ) : Ordinal) ≤ Ordinal.omega0 ^ (a + 1)
    rw [opow_add, opow_one]
    exact mul_le_mul_right (le_of_lt (Ordinal.nat_lt_omega0 _)) _
  add_one_le a c h := Order.add_one_le_of_lt h

theorem hypSet_nat (b : ℕ) : HypSet ℕ b (fun a => (b + 1) ^ a) (fun a k => a * k) where
  zero_le a := Nat.zero_le a
  add_lt_left a x y h := by omega
  add_le_left a x y h := by omega
  add_zero' a := by omega
  mul_one' a := by simp
  mul_mono a k l h := Nat.mul_le_mul_left a h
  mul_succ' a k := by ring
  pw_pos a := pow_pos (Nat.succ_pos b) a
  pw_mono a c h := Nat.pow_le_pow_right (Nat.succ_pos b) h
  pw_step a k hk := by
    show ((b + 1) ^ a) * (k + 1) ≤ (b + 1) ^ (a + 1)
    rw [pow_succ]
    exact Nat.mul_le_mul_left _ (by omega)
  add_one_le a c h := h

@[simp] theorem hord_zero (b : ℕ) : hord b 0 = 0 := hval_zero _ _ _

@[simp] theorem bump_zero (b : ℕ) : bump b 0 = 0 := hval_zero _ _ _

theorem hord_eq (b : ℕ) {n : ℕ} (hn : n ≠ 0) :
    hord b n = Ordinal.omega0 ^ (hord b (Nat.log b n)) * ((n / b ^ Nat.log b n : ℕ) : Ordinal)
      + hord b (n % b ^ Nat.log b n) := hval_eq _ _ _ hn

theorem bump_eq (b : ℕ) {n : ℕ} (hn : n ≠ 0) :
    bump b n = (b + 1) ^ (bump b (Nat.log b n)) * (n / b ^ Nat.log b n)
      + bump b (n % b ^ Nat.log b n) := hval_eq _ _ _ hn

theorem bump_lt_pow {b : ℕ} (hb : 2 ≤ b) {E m : ℕ} (hm : m < b ^ E) :
    bump b m < (b + 1) ^ (bump b E) := hval_lt_pw (hypSet_nat b) hb hm

theorem hord_strictMono {b : ℕ} (hb : 2 ≤ b) : StrictMono (hord b) :=
  hval_strictMono (hypSet_ord b) hb

theorem bump_strictMono {b : ℕ} (hb : 2 ≤ b) : StrictMono (bump b) :=
  hval_strictMono (hypSet_nat b) hb

/-- Base change: the hereditary base-`(b+1)` value of `bump b n` is the hereditary base-`b`
value of `n`. -/
theorem hord_bump {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : hord (b + 1) (bump b n) = hord b n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hEn : Nat.log b n < n := Nat.log_lt_self b hn
      have hrn : n % b ^ Nat.log b n < n := mod_pow_log_lt hn
      have hrb : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ (pow_log_pos b n)
      have hc1 : 1 ≤ n / b ^ Nat.log b n := digit_pos hn
      have hcb : n / b ^ Nat.log b n < b := digit_lt hb
      set E := Nat.log b n with hEdef
      set c := n / b ^ E with hcdef
      set r := n % b ^ E with hrdef
      set P := bump b E with hPdef
      have hsmall : bump b r < (b + 1) ^ P := bump_lt_pow hb hrb
      have hM : bump b n = (b + 1) ^ P * c + bump b r := bump_eq b hn
      -- identify the leading exponent, digit and remainder of `bump b n` in base `b+1`
      have hpos : 0 < (b + 1) ^ P := pow_pos (Nat.succ_pos b) P
      have hle : (b + 1) ^ P ≤ bump b n := by
        rw [hM]; nlinarith [Nat.one_le_iff_ne_zero.mp hc1]
      have hlt : bump b n < (b + 1) ^ (P + 1) := by
        rw [hM, pow_succ]
        have : (b + 1) ^ P * c + bump b r < (b + 1) ^ P * c + (b + 1) ^ P := by omega
        calc (b + 1) ^ P * c + bump b r < (b + 1) ^ P * c + (b + 1) ^ P := this
          _ = (b + 1) ^ P * (c + 1) := by ring
          _ ≤ (b + 1) ^ P * (b + 1) := Nat.mul_le_mul_left _ (by omega)
      have hlog : Nat.log (b + 1) (bump b n) = P := Nat.log_eq_of_pow_le_of_lt_pow hle hlt
      have hdiv : bump b n / (b + 1) ^ P = c := by
        rw [hM, Nat.mul_add_div hpos, Nat.div_eq_of_lt hsmall, Nat.add_zero]
      have hmod : bump b n % (b + 1) ^ P = bump b r := by
        rw [hM, Nat.mul_add_mod, Nat.mod_eq_of_lt hsmall]
      have hMne : bump b n ≠ 0 := by
        have := hpos.trans_le hle; omega
      rw [hord_eq (b + 1) hMne, hlog, hdiv, hmod, IH E hEn, IH r hrn, hord_eq b hn]

/-! ## The Goodstein sequence -/

/-- `goodstein n k` is the `k`-th term of the Goodstein sequence starting at `n`;
the term `goodstein n k` is thought of as written in hereditary base `k + 2`. -/
def goodstein (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => bump (k + 2) (goodstein n k) - 1

/-! ### Sanity checks: the first terms of the Goodstein sequence starting at `4`

The classical Goodstein sequence starting at `4` is `4, 26, 41, 60, 83, ...`. -/

theorem bump_one (b : ℕ) : bump b 1 = 1 := by
  rw [bump_eq b (by norm_num), Nat.log_one_right b]
  simp

theorem bump_two_four : bump 2 4 = 27 := by
  have l4 : Nat.log 2 4 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have l2 : Nat.log 2 2 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have b2 : bump 2 2 = 3 := by
    rw [bump_eq 2 (by norm_num), l2, bump_one 2]
    norm_num
  rw [bump_eq 2 (by norm_num), l4, b2]
  norm_num

theorem goodstein_four_one : goodstein 4 1 = 26 := by
  show bump 2 4 - 1 = 26
  rw [bump_two_four]

theorem goodstein_four_two : goodstein 4 2 = 41 := by
  show bump 3 (goodstein 4 1) - 1 = 41
  rw [goodstein_four_one]
  have l26 : Nat.log 3 26 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have l8 : Nat.log 3 8 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have l2 : Nat.log 3 2 = 0 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have b2 : bump 3 2 = 2 := by
    rw [bump_eq 3 (by norm_num), l2]; norm_num
  have b8 : bump 3 8 = 10 := by
    rw [bump_eq 3 (by norm_num), l8, bump_one 3]; norm_num [b2]
  rw [bump_eq 3 (by norm_num), l26, b2]
  norm_num [b8]

/-- **Goodstein's theorem**: every Goodstein sequence eventually reaches `0`. -/
theorem Goodstein_terminates (n : ℕ) : ∃ k, goodstein n k = 0 := by
  by_contra hcon
  push_neg at hcon
  have hdec : ∀ k : ℕ, hord (k + 1 + 2) (goodstein n (k + 1)) < hord (k + 2) (goodstein n k) := by
    intro k
    have hb : 2 ≤ k + 2 := by omega
    have hne : goodstein n k ≠ 0 := hcon k
    have hMne : bump (k + 2) (goodstein n k) ≠ 0 := by
      intro h0
      exact hne ((bump_strictMono hb).injective (by simpa using h0))
    have h1 : goodstein n (k + 1) = bump (k + 2) (goodstein n k) - 1 := rfl
    have h2 : bump (k + 2) (goodstein n k) - 1 < bump (k + 2) (goodstein n k) := by omega
    calc hord (k + 1 + 2) (goodstein n (k + 1))
        < hord (k + 2 + 1) (bump (k + 2) (goodstein n k)) := by
          rw [h1]; exact hord_strictMono (by omega) h2
      _ = hord (k + 2) (goodstein n k) := hord_bump hb _
  exact (RelEmbedding.natGT (fun k => hord (k + 2) (goodstein n k)) hdec).not_wellFounded
    wellFounded_lt

end Frontier

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

