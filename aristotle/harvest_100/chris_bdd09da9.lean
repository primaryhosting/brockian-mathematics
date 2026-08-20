import Mathlib

/-!
# Further Diophantine functions: binomial coefficients and factorials

Mathlib's `Mathlib/NumberTheory/Dioph.lean` develops the basic theory of Diophantine sets and
functions and culminates in Matiyasevich's theorem that exponentiation is Diophantine
(`Dioph.pow_dioph`).  Two further classical steps on the way to the MRDP theorem are formalized
here, both unconditionally:

* `CS.choose_dioph`: the binomial coefficient `(n, k) ↦ n.choose k` is a Diophantine function.
  This follows from `Dioph.pow_dioph` because `n.choose k` is the `k`-th digit of `(u + 1) ^ n`
  in base `u := 2 ^ n + 1`, and division and remainder are Diophantine.
* `CS.factorial_dioph`: the factorial `r ↦ r !` is a Diophantine function.  This follows from
  `CS.choose_dioph` because `r ! = u ^ r / u.choose r` as soon as `u` is large enough compared
  to `r`, and `u := (2 * r) ^ (r + 2) + 2 * r + 1` is large enough.
-/

set_option autoImplicit false

namespace CS

open Finset Nat

/-! ## Digits in base `u` -/

/-- A number with all digits `< u` and at most `k` digits is `< u ^ k`. -/
theorem sum_digits_lt (u : ℕ) (a : ℕ → ℕ) (ha : ∀ i, a i < u) (k : ℕ) :
    (∑ i ∈ range k, a i * u ^ i) < u ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have h1 := ha k
      have h2 : (a k + 1) * u ^ k ≤ u * u ^ k := Nat.mul_le_mul_right _ (by omega)
      nlinarith [ih]

theorem tail_step (u : ℕ) (a : ℕ → ℕ) (m k : ℕ) (hk : k < m) :
    (∑ i ∈ range (m - k), a (k + i) * u ^ i)
      = a k + u * ∑ i ∈ range (m - k - 1), a (k + 1 + i) * u ^ i := by
  have hm : m - k = (m - k - 1) + 1 := by omega
  rw [hm, Finset.sum_range_succ']
  simp [Finset.mul_sum, pow_succ, mul_comm, mul_assoc, add_comm, add_left_comm]

theorem tail_div (u : ℕ) (hu : 1 < u) (a : ℕ → ℕ) (ha : ∀ i, a i < u) (m : ℕ) :
    ∀ k ≤ m, (∑ i ∈ range m, a i * u ^ i) / u ^ k = ∑ i ∈ range (m - k), a (k + i) * u ^ i := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hstep := tail_step u a m k (by omega)
      rw [pow_succ, ← Nat.div_div_eq_div_mul, h1, hstep,
        Nat.add_mul_div_left _ _ (by omega : 0 < u), Nat.div_eq_of_lt (ha k)]
      have hmk : m - (k + 1) = m - k - 1 := by omega
      rw [hmk]
      omega

/-- Extraction of the `k`-th digit in base `u`. -/
theorem digit_extract (u : ℕ) (hu : 1 < u) (a : ℕ → ℕ) (ha : ∀ i, a i < u) (m k : ℕ)
    (hk : k < m) : (∑ i ∈ range m, a i * u ^ i) / u ^ k % u = a k := by
  rw [tail_div u hu a ha m k (le_of_lt hk), tail_step u a m k hk,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ha k)]

/-! ## Binomial coefficients are Diophantine -/

/-- `n.choose k` is the `k`-th digit of `(u + 1) ^ n` in base `u = 2 ^ n + 1`. -/
theorem choose_eq_digit (n k : ℕ) :
    n.choose k = (2 ^ n + 2) ^ n / (2 ^ n + 1) ^ k % (2 ^ n + 1) := by
  set u := 2 ^ n + 1 with hudef
  have hu : 1 < u := by
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have ha : ∀ i, n.choose i < u := fun i => lt_of_le_of_lt (Nat.choose_le_two_pow n i) (by omega)
  have hexp : (2 ^ n + 2) ^ n = ∑ i ∈ range (n + 1), n.choose i * u ^ i := by
    have h : (2 : ℕ) ^ n + 2 = u + 1 := by omega
    rw [h, add_pow]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  rcases lt_or_ge k (n + 1) with hk | hk
  · rw [hexp, digit_extract u hu _ ha (n + 1) k hk]
  · have h0 : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hlt : (2 ^ n + 2) ^ n < u ^ (n + 1) := by
      rw [hexp]; exact sum_digits_lt u _ ha (n + 1)
    have hle : u ^ (n + 1) ≤ u ^ k := Nat.pow_le_pow_right (by omega) hk
    rw [h0, Nat.div_eq_of_lt (lt_of_lt_of_le hlt hle)]
    simp

open Dioph in
/-- **Binomial coefficients are Diophantine.** -/
theorem choose_dioph {α : Type} {f g : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g) :
    DiophFn fun v => (f v).choose (g v) := by
  have d2 : DiophFn fun _ : α → ℕ => (2 : ℕ) := const_dioph 2
  have d1 : DiophFn fun _ : α → ℕ => (1 : ℕ) := const_dioph 1
  have dp : DiophFn fun v => 2 ^ f v := pow_dioph d2 df
  have dA : DiophFn fun v => (2 ^ f v + 2) ^ f v := pow_dioph (add_dioph dp d2) df
  have dB : DiophFn fun v => (2 ^ f v + 1) ^ g v := pow_dioph (add_dioph dp d1) dg
  have dC : DiophFn fun v => 2 ^ f v + 1 := add_dioph dp d1
  have hd := mod_dioph (div_dioph dA dB) dC
  have heq : (fun v => (f v).choose (g v))
      = fun v => (2 ^ f v + 2) ^ f v / (2 ^ f v + 1) ^ g v % (2 ^ f v + 1) :=
    funext fun v => choose_eq_digit _ _
  rw [heq]
  exact hd

/-! ## Factorials are Diophantine -/

theorem pow_add_le_aux (b c : ℕ) :
    ∀ k : ℕ, (b + c) ^ (k + 1) ≤ b ^ (k + 1) + (k + 1) * c * (b + c) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc (b + c) ^ (k + 2) = (b + c) * (b + c) ^ (k + 1) := by ring
        _ ≤ (b + c) * (b ^ (k + 1) + (k + 1) * c * (b + c) ^ k) := Nat.mul_le_mul_left _ ih
        _ = b ^ (k + 2) + c * b ^ (k + 1) + (k + 1) * c * ((b + c) * (b + c) ^ k) := by ring
        _ ≤ b ^ (k + 2) + c * (b + c) ^ (k + 1) + (k + 1) * c * (b + c) ^ (k + 1) := by
            gcongr
            · exact Nat.le_add_right _ _
            · exact le_of_eq (by ring)
        _ = b ^ (k + 2) + (k + 2) * c * (b + c) ^ (k + 1) := by ring

/-- If `u` is large compared with `r`, then `r ! = u ^ r / u.choose r`. -/
theorem factorial_eq_pow_div_choose (r u : ℕ) (hr : 1 ≤ r) (h1 : 2 ^ r * r ! * r ^ 2 < u)
    (h2 : 2 * r ≤ u) : r ! = u ^ r / u.choose r := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  set r := k + 1 with hrdef
  set w := u - r with hw
  have hur : r ≤ u := by omega
  have huw : u = w + r := by omega
  have hww : u ≤ 2 * w := by omega
  have hupos : 0 < u := by omega
  have hC : 0 < u.choose r := Nat.choose_pos hur
  have hD : u.descFactorial r = r ! * u.choose r := Nat.descFactorial_eq_factorial_mul_choose u r
  have hDle : r ! * u.choose r ≤ u ^ r := hD ▸ Nat.descFactorial_le_pow u r
  have hwD : w ^ r ≤ r ! * u.choose r := by
    rw [← hD]
    calc w ^ r ≤ (u + 1 - r) ^ r := Nat.pow_le_pow_left (by omega) _
      _ ≤ u.descFactorial r := Nat.pow_sub_le_descFactorial u r
  have hkey : r ! * r ^ 2 * u ^ k < w ^ r := by
    have e1 : 2 ^ r * (r ! * r ^ 2) * u ^ k < u * u ^ k := by
      have h3 : 2 ^ r * r ! * r ^ 2 * u ^ k < u * u ^ k :=
        Nat.mul_lt_mul_of_pos_right h1 (pow_pos hupos k)
      calc 2 ^ r * (r ! * r ^ 2) * u ^ k = 2 ^ r * r ! * r ^ 2 * u ^ k := by ring
        _ < u * u ^ k := h3
    have e2 : u * u ^ k ≤ 2 ^ r * w ^ r := by
      calc u * u ^ k = u ^ r := by rw [hrdef]; ring
        _ ≤ (2 * w) ^ r := Nat.pow_le_pow_left hww r
        _ = 2 ^ r * w ^ r := by rw [Nat.mul_pow]
    have h4 : 2 ^ r * (r ! * r ^ 2 * u ^ k) < 2 ^ r * w ^ r := by
      calc 2 ^ r * (r ! * r ^ 2 * u ^ k) = 2 ^ r * (r ! * r ^ 2) * u ^ k := by ring
        _ < u * u ^ k := e1
        _ ≤ 2 ^ r * w ^ r := e2
    exact lt_of_mul_lt_mul_left h4 (Nat.zero_le _)
  have hpow : u ^ r ≤ w ^ r + r * r * u ^ k := by
    calc u ^ r = (w + r) ^ (k + 1) := by rw [huw]
      _ ≤ w ^ (k + 1) + (k + 1) * r * (w + r) ^ k := pow_add_le_aux w r k
      _ = w ^ r + r * r * u ^ k := by rw [← huw, hrdef]
  have hstrict : r ! * u ^ r < (r ! + 1) * (r ! * u.choose r) := by
    calc r ! * u ^ r ≤ r ! * (w ^ r + r * r * u ^ k) := Nat.mul_le_mul_left _ hpow
      _ = r ! * w ^ r + r ! * (r * r) * u ^ k := by ring
      _ < r ! * w ^ r + w ^ r := by
          have h5 : r ! * (r * r) * u ^ k = r ! * r ^ 2 * u ^ k := by ring
          omega
      _ ≤ r ! * (r ! * u.choose r) + r ! * u.choose r := by
          have h3 : r ! * w ^ r ≤ r ! * (r ! * u.choose r) := Nat.mul_le_mul_left _ hwD
          omega
      _ = (r ! + 1) * (r ! * u.choose r) := by ring
  have hlt : u ^ r < (r ! + 1) * u.choose r := by
    have h6 : r ! * u ^ r < r ! * ((r ! + 1) * u.choose r) := by
      calc r ! * u ^ r < (r ! + 1) * (r ! * u.choose r) := hstrict
        _ = r ! * ((r ! + 1) * u.choose r) := by ring
    exact lt_of_mul_lt_mul_left h6 (Nat.zero_le _)
  have hge : r ! ≤ u ^ r / u.choose r := (Nat.le_div_iff_mul_le hC).2 hDle
  have hle : u ^ r / u.choose r < r ! + 1 := (Nat.div_lt_iff_lt_mul hC).2 hlt
  omega

/-- An explicit formula for the factorial in terms of a binomial coefficient. -/
theorem factorial_formula (r : ℕ) :
    r ! = ((2 * r) ^ (r + 2) + 2 * r + 1) ^ r / (((2 * r) ^ (r + 2) + 2 * r + 1).choose r) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · refine factorial_eq_pow_div_choose r _ hr ?_ (by omega)
    have hfac : r ! ≤ r ^ r := Nat.factorial_le_pow r
    have h1 : 2 ^ r * r ! * r ^ 2 ≤ (2 * r) ^ r * r ^ 2 := by
      have h : 2 ^ r * r ! ≤ 2 ^ r * r ^ r := Nat.mul_le_mul_left _ hfac
      calc 2 ^ r * r ! * r ^ 2 ≤ 2 ^ r * r ^ r * r ^ 2 := Nat.mul_le_mul_right _ h
        _ = (2 * r) ^ r * r ^ 2 := by rw [Nat.mul_pow]
    have h2 : (2 * r) ^ r * r ^ 2 ≤ (2 * r) ^ (r + 2) := by
      calc (2 * r) ^ r * r ^ 2 ≤ (2 * r) ^ r * (2 * r) ^ 2 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
        _ = (2 * r) ^ (r + 2) := by rw [← pow_add]
    omega

open Dioph in
/-- **The factorial is a Diophantine function.** -/
theorem factorial_dioph {α : Type} {f : (α → ℕ) → ℕ} (df : DiophFn f) :
    DiophFn fun v => (f v)! := by
  have d1 : DiophFn fun _ : α → ℕ => (1 : ℕ) := const_dioph 1
  have d2 : DiophFn fun _ : α → ℕ => (2 : ℕ) := const_dioph 2
  have dtwice : DiophFn fun v => 2 * f v := mul_dioph d2 df
  have dexp : DiophFn fun v => f v + 2 := add_dioph df d2
  have du : DiophFn fun v => (2 * f v) ^ (f v + 2) + 2 * f v + 1 :=
    add_dioph (add_dioph (pow_dioph dtwice dexp) dtwice) d1
  have hd := div_dioph (pow_dioph du df) (choose_dioph du df)
  have heq : (fun v => (f v)!)
      = fun v => ((2 * f v) ^ (f v + 2) + 2 * f v + 1) ^ f v /
          (((2 * f v) ^ (f v + 2) + 2 * f v + 1).choose (f v)) :=
    funext fun v => factorial_formula _
  rw [heq]
  exact hd

/-! ## The finite products `∏ (1 + k * t)` are Diophantine -/

theorem prod_modEq (y t M r : ℕ) (h : t * r = (t - 1) * M + 1) :
    (t ^ y * ∏ i ∈ range y, (r + 1 + i)) ≡ ∏ i ∈ range y, (1 + (i + 1) * t) [MOD M] := by
  induction y with
  | zero => simp; rfl
  | succ y ih =>
      have step : t * (r + 1 + y) ≡ 1 + (y + 1) * t [MOD M] := by
        have heq : t * (r + 1 + y) = 1 + (y + 1) * t + M * (t - 1) := by
          have h2 : t * (r + 1 + y) = t * r + t + t * y := by ring
          rw [h2, h]; ring
        show _ % M = _ % M
        rw [heq, Nat.add_mul_mod_self_left]
      rw [Finset.prod_range_succ, Finset.prod_range_succ, pow_succ]
      calc t ^ y * t * ((∏ i ∈ range y, (r + 1 + i)) * (r + 1 + y))
          = (t ^ y * ∏ i ∈ range y, (r + 1 + i)) * (t * (r + 1 + y)) := by ring
        _ ≡ (∏ i ∈ range y, (1 + (i + 1) * t)) * (1 + (y + 1) * t) [MOD M] := ih.mul step

theorem prod_le_pow (y t : ℕ) : ∏ i ∈ range y, (1 + (i + 1) * t) ≤ (1 + y * t) ^ y := by
  calc ∏ i ∈ range y, (1 + (i + 1) * t) ≤ ∏ _i ∈ range y, (1 + y * t) := by
        refine Finset.prod_le_prod' ?_
        intro i hi
        have : i + 1 ≤ y := by simpa using hi
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ this) 1
    _ = (1 + y * t) ^ y := by simp

/-- An explicit formula for `∏_{k=1}^{y} (1 + k * t)`, obtained by inverting `t` modulo a
large modulus coprime to `t`. -/
theorem prod_formula (y t : ℕ) :
    ∏ i ∈ range y, (1 + (i + 1) * t)
      = t ^ y * (y ! * (((t - 1) * (1 + y * t) ^ y + 1 + y).choose y))
          % (t * (1 + y * t) ^ y + 1) + (1 - t) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [Nat.mod_one]
  · set K := (1 + y * t) ^ y with hK
    set M := t * K + 1 with hM
    set r := (t - 1) * K + 1 with hr
    have htr : t * r = (t - 1) * M + 1 := by
      rw [hr, hM]
      cases t with
      | zero => omega
      | succ s => ring_nf; simp; omega
    have hprod : ∏ i ∈ range y, (r + 1 + i) = y ! * (r + y).choose y := by
      rw [← Nat.ascFactorial_eq_factorial_mul_choose, Nat.ascFactorial_eq_prod_range]
    have hcong := prod_modEq y t M r htr
    rw [hprod] at hcong
    have hlt : ∏ i ∈ range y, (1 + (i + 1) * t) < M := by
      have h1 := prod_le_pow y t
      have h2 : K ≤ t * K := Nat.le_mul_of_pos_left _ ht
      omega
    have h0 : (1 : ℕ) - t = 0 := by omega
    rw [h0, Nat.add_zero]
    have h3 := hcong.symm
    unfold Nat.ModEq at h3
    rw [Nat.mod_eq_of_lt hlt] at h3
    rw [← h3]

open Dioph in
/-- **The products `(y, t) ↦ ∏_{k=1}^{y} (1 + k * t)` form a Diophantine function.**
These products supply the pairwise coprime moduli used in the Chinese-remainder coding of
finite sequences in the proof of the MRDP theorem. -/
theorem prod_one_add_mul_dioph {α : Type} {f g : (α → ℕ) → ℕ} (df : DiophFn f)
    (dg : DiophFn g) : DiophFn fun v => ∏ i ∈ range (f v), (1 + (i + 1) * g v) := by
  have d1 : DiophFn fun _ : α → ℕ => (1 : ℕ) := const_dioph 1
  have dK : DiophFn fun v => (1 + f v * g v) ^ f v :=
    pow_dioph (add_dioph d1 (mul_dioph df dg)) df
  have dM : DiophFn fun v => g v * (1 + f v * g v) ^ f v + 1 := add_dioph (mul_dioph dg dK) d1
  have dr : DiophFn fun v => (g v - 1) * (1 + f v * g v) ^ f v + 1 :=
    add_dioph (mul_dioph (sub_dioph dg d1) dK) d1
  have dch : DiophFn fun v => ((g v - 1) * (1 + f v * g v) ^ f v + 1 + f v).choose (f v) :=
    choose_dioph (add_dioph dr df) df
  have dnum : DiophFn fun v => g v ^ f v *
      ((f v)! * ((g v - 1) * (1 + f v * g v) ^ f v + 1 + f v).choose (f v)) :=
    mul_dioph (pow_dioph dg df) (mul_dioph (factorial_dioph df) dch)
  have hd := add_dioph (mod_dioph dnum dM) (sub_dioph d1 dg)
  have heq : (fun v => ∏ i ∈ range (f v), (1 + (i + 1) * g v))
      = fun v => g v ^ f v * ((f v)! *
          ((g v - 1) * (1 + f v * g v) ^ f v + 1 + f v).choose (f v))
            % (g v * (1 + f v * g v) ^ f v + 1) + (1 - g v) :=
    funext fun v => prod_formula _ _
  rw [heq]
  exact hd

end CS

/-
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command of a file, so the header above is written
-- as a plain comment and repeated as a module docstring below.)

import Mathlib
import RequestProject.DiophAux

/-!
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

* `CS.haltSet`, `CS.haltSet_re`, `CS.haltSet_not_computable`: the halting problem, transported
  from `Nat.Partrec.Code` to a subset of `ℕ`.
* `CS.MRDP`: the statement of the Matiyasevich–Robinson–Davis–Putnam theorem ("every recursively
  enumerable set of naturals is Diophantine").  Mathlib contains the deepest number-theoretic
  ingredient of its proof (`Dioph.pow_dioph`, Matiyasevich's theorem that exponentiation is
  Diophantine) but not the theorem itself; see the `TODO` in `Mathlib/NumberTheory/Dioph.lean`
  ("Finish the solution of Hilbert's tenth problem").  It is therefore taken here as an explicit
  hypothesis of `CS.hilbert10_undecidable` rather than being reproved.
* `CS.hilbert10_undecidable`: **Hilbert's tenth problem is undecidable**.  Assuming `MRDP`, there
  is a single integer polynomial `p` in one distinguished parameter and finitely many further
  unknowns such that no algorithm decides, given the parameter `a`, whether `p (a, t) = 0` is
  solvable in natural numbers `t`.
* `CS.dioph_rePred` and `CS.dioph_iff_rePred`: the converse (easy) half of MRDP, proved
  unconditionally: every Diophantine subset of `ℕ` is recursively enumerable.  Consequently
  Diophantine sets are exactly the recursively enumerable sets if and only if `MRDP` holds.

The file `RequestProject/DiophAux.lean` contains further unconditional steps towards MRDP that go
beyond Mathlib: binomial coefficients (`CS.choose_dioph`), factorials (`CS.factorial_dioph`) and
the products `∏_{k=1}^{y} (1 + k * t)` (`CS.prod_one_add_mul_dioph`) are Diophantine functions.
-/

set_option autoImplicit false

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ## The halting set, transported to `ℕ` -/

/-- The halting set: `n ∈ haltSet` iff the `n`-th partial recursive program halts on input `0`. -/
def haltSet : Set ℕ := fun n => (eval (Denumerable.ofNat Code n) 0).Dom

theorem haltSet_re : REPred haltSet :=
  (ComputablePred.halting_problem_re 0).comp (Computable.ofNat Code)

theorem haltSet_not_computable : ¬ ComputablePred haltSet := by
  intro h
  refine ComputablePred.halting_problem 0 ?_
  obtain ⟨inst, hc⟩ := h
  have h2 : ComputablePred fun c : Code => haltSet (Encodable.encode c) :=
    ⟨fun c => inst _, hc.comp (Computable.encode (α := Code))⟩
  refine h2.of_eq fun c => ?_
  simp [haltSet, Denumerable.ofNat_encode]

/-! ## Statement of the MRDP theorem -/

/-- The Matiyasevich–Robinson–Davis–Putnam theorem: every recursively enumerable set of natural
numbers is Diophantine, i.e. is the set of parameters for which some integer polynomial equation
has a solution in the natural numbers. -/
def MRDP : Prop :=
  ∀ S : Set ℕ, REPred S → Dioph {v : Fin 1 → ℕ | S (v 0)}

/-! ## Hilbert's tenth problem is undecidable -/

/-- **Hilbert's tenth problem is undecidable.**

Given the MRDP theorem, there is a single integer polynomial `p` in one distinguished parameter
`a` and finitely many further unknowns `t` such that no algorithm decides, given `a`, whether the
Diophantine equation `p (a, t) = 0` has a solution `t` in the natural numbers.  In particular
there is no algorithm deciding solvability of arbitrary Diophantine equations. -/
theorem hilbert10_undecidable (mrdp : MRDP) :
    ∃ (β : Type) (p : Poly (Fin 1 ⊕ β)),
      ¬ ComputablePred fun a : ℕ => ∃ t : β → ℕ, p (Sum.elim (fun _ => a) t) = 0 := by
  obtain ⟨β, p, hp⟩ := mrdp haltSet haltSet_re
  refine ⟨β, p, fun h => haltSet_not_computable ?_⟩
  refine h.of_eq fun a => ?_
  have := hp (fun _ => a)
  simpa using this.symm

/-! ## The easy half of MRDP: Diophantine sets are recursively enumerable

This direction is proved unconditionally.  Together with `MRDP` it says that the Diophantine
subsets of `ℕ` are exactly the recursively enumerable ones, so the undecidable set produced by
`hilbert10_undecidable` is as complicated as the halting problem, but no worse. -/

/-- An integer polynomial function depends on only finitely many of its variables. -/
theorem isPoly_support {γ : Type} {f : (γ → ℕ) → ℤ} (hf : IsPoly f) :
    ∃ l : List γ, ∀ v w : γ → ℕ, (∀ i ∈ l, v i = w i) → f v = f w := by
  induction hf with
  | proj i => exact ⟨[i], fun v w hvw => by simp [hvw i (List.mem_singleton_self i)]⟩
  | const n => exact ⟨[], fun v w _ => rfl⟩
  | sub _ _ ih₁ ih₂ =>
      obtain ⟨l₁, h₁⟩ := ih₁; obtain ⟨l₂, h₂⟩ := ih₂
      refine ⟨l₁ ++ l₂, fun v w hvw => ?_⟩
      dsimp only
      rw [h₁ v w fun i hi => hvw i (List.mem_append_left _ hi),
          h₂ v w fun i hi => hvw i (List.mem_append_right _ hi)]
  | mul _ _ ih₁ ih₂ =>
      obtain ⟨l₁, h₁⟩ := ih₁; obtain ⟨l₂, h₂⟩ := ih₂
      refine ⟨l₁ ++ l₂, fun v w hvw => ?_⟩
      dsimp only
      rw [h₁ v w fun i hi => hvw i (List.mem_append_left _ hi),
          h₂ v w fun i hi => hvw i (List.mem_append_right _ hi)]

/-- If every variable of an integer polynomial is substituted by a computable function of a
parameter `x`, the resulting integer-valued function is a difference of two computable
natural-number-valued functions. -/
theorem isPoly_computable {γ A : Type} [Primcodable A] (φ : A → γ → ℕ)
    (hφ : ∀ i, Computable fun x => φ x i) {f : (γ → ℕ) → ℤ} (hf : IsPoly f) :
    ∃ g h : A → ℕ, Computable g ∧ Computable h ∧ ∀ x, f (φ x) = (g x : ℤ) - (h x : ℤ) := by
  induction hf with
  | proj i => exact ⟨fun x => φ x i, fun _ => 0, hφ i, Computable.const 0, fun x => by simp⟩
  | const n =>
      exact ⟨fun _ => n.toNat, fun _ => (-n).toNat, Computable.const _, Computable.const _,
        fun x => by dsimp only; omega⟩
  | sub _ _ ih₁ ih₂ =>
      obtain ⟨g₁, h₁, hg₁, hh₁, e₁⟩ := ih₁
      obtain ⟨g₂, h₂, hg₂, hh₂, e₂⟩ := ih₂
      refine ⟨fun x => g₁ x + h₂ x, fun x => h₁ x + g₂ x,
        (Primrec₂.to_comp Primrec.nat_add).comp hg₁ hh₂,
        (Primrec₂.to_comp Primrec.nat_add).comp hh₁ hg₂, fun x => ?_⟩
      dsimp only
      rw [e₁, e₂]; push_cast; ring
  | mul _ _ ih₁ ih₂ =>
      obtain ⟨g₁, h₁, hg₁, hh₁, e₁⟩ := ih₁
      obtain ⟨g₂, h₂, hg₂, hh₂, e₂⟩ := ih₂
      refine ⟨fun x => g₁ x * g₂ x + h₁ x * h₂ x, fun x => g₁ x * h₂ x + h₁ x * g₂ x,
        (Primrec₂.to_comp Primrec.nat_add).comp
          ((Primrec₂.to_comp Primrec.nat_mul).comp hg₁ hg₂)
          ((Primrec₂.to_comp Primrec.nat_mul).comp hh₁ hh₂),
        (Primrec₂.to_comp Primrec.nat_add).comp
          ((Primrec₂.to_comp Primrec.nat_mul).comp hg₁ hh₂)
          ((Primrec₂.to_comp Primrec.nat_mul).comp hh₁ hg₂), fun x => ?_⟩
      dsimp only
      rw [e₁, e₂]; push_cast; ring

/-- A predicate of the form `∃ L : List ℕ, g (a, L) = h (a, L)` with `g`, `h` computable is
recursively enumerable. -/
theorem rePred_of_exists_list {S : Set ℕ} (g h : ℕ × List ℕ → ℕ) (hg : Computable g)
    (hh : Computable h) (key : ∀ a : ℕ, S a ↔ ∃ L : List ℕ, g (a, L) = h (a, L)) : REPred S := by
  have hcomp : Computable fun q : ℕ × ℕ => decide
      (g (q.1, Denumerable.ofNat (List ℕ) q.2) = h (q.1, Denumerable.ofNat (List ℕ) q.2)) :=
    (Primrec₂.to_comp (Primrec.eq (α := ℕ)).decide).comp
      (hg.comp (Computable.fst.pair ((Computable.ofNat (List ℕ)).comp Computable.snd)))
      (hh.comp (Computable.fst.pair ((Computable.ofNat (List ℕ)).comp Computable.snd)))
  have hq : Partrec₂ (fun a n => (Part.some (decide
      (g (a, Denumerable.ofNat (List ℕ) n) = h (a, Denumerable.ofNat (List ℕ) n))) : Part Bool)) :=
    Computable₂.partrec₂ hcomp
  refine ((Partrec.rfind hq).dom_re).of_eq fun a => ?_
  rw [Nat.rfind_dom, key]
  constructor
  · rintro ⟨n, hn, -⟩
    exact ⟨Denumerable.ofNat (List ℕ) n, by simpa using hn⟩
  · rintro ⟨L, hL⟩
    exact ⟨Encodable.encode L, by simp [hL], fun {m} _ => trivial⟩

/-- **Every Diophantine subset of `ℕ` is recursively enumerable** (the easy half of MRDP). -/
theorem dioph_rePred {S : Set ℕ} (hS : Dioph {v : Fin 1 → ℕ | S (v 0)}) : REPred S := by
  classical
  obtain ⟨β, p, hp⟩ := hS
  obtain ⟨l, hl⟩ := isPoly_support p.isPoly
  set lb : List β := l.filterMap Sum.getRight? with hlbdef
  set assign : ℕ × List ℕ → (Fin 1 ⊕ β → ℕ) := fun x =>
    Sum.elim (fun _ => x.1)
      (fun b => if hb : ∃ i : Fin lb.length, lb.get i = b then x.2.getD (hb.choose : ℕ) 0 else 0)
    with hassign
  have hcoord : ∀ c : Fin 1 ⊕ β, Computable fun x => assign x c := by
    intro c
    cases c with
    | inl i => exact Computable.fst
    | inr b =>
        by_cases hb : ∃ i : Fin lb.length, lb.get i = b
        · simp only [hassign, Sum.elim_inr, dif_pos hb]
          exact (Primrec₂.to_comp (Primrec.list_getD 0)).comp Computable.snd (Computable.const _)
        · simp only [hassign, Sum.elim_inr, dif_neg hb]
          exact Computable.const 0
  obtain ⟨g, h, hg, hh, e⟩ := isPoly_computable assign hcoord p.isPoly
  refine rePred_of_exists_list g h hg hh fun a => ?_
  have key : S a ↔ ∃ L : List ℕ, p (assign (a, L)) = 0 := by
    have h1 : S a ↔ ∃ t : β → ℕ, p (Sum.elim (fun _ => a) t) = 0 := by
      have := hp (fun _ => a); simpa using this
    rw [h1]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨lb.map t, ?_⟩
      rw [← ht]
      refine hl _ _ fun c hc => ?_
      cases c with
      | inl i => simp [hassign]
      | inr b =>
          have hbmem : b ∈ lb := by
            rw [hlbdef, List.mem_filterMap]
            exact ⟨Sum.inr b, hc, rfl⟩
          have hb : ∃ i : Fin lb.length, lb.get i = b := List.mem_iff_get.1 hbmem
          simp only [hassign, Sum.elim_inr, dif_pos hb]
          have hlen : (hb.choose : ℕ) < (lb.map t).length := by simp
          rw [List.getD_eq_getElem _ _ hlen, List.getElem_map]
          congr 1
          simpa [List.get_eq_getElem] using hb.choose_spec
    · rintro ⟨L, hL⟩
      exact ⟨fun b => assign (a, L) (Sum.inr b), by
        rw [show Sum.elim (fun _ : Fin 1 => a) (fun b => assign (a, L) (Sum.inr b))
            = assign (a, L) from funext fun c => by cases c <;> simp [hassign]]
        exact hL⟩
  rw [key]
  exact exists_congr fun L => by rw [e (a, L)]; omega

/-- Assuming MRDP, the Diophantine subsets of `ℕ` are exactly the recursively enumerable ones. -/
theorem dioph_iff_rePred (mrdp : MRDP) (S : Set ℕ) :
    Dioph {v : Fin 1 → ℕ | S (v 0)} ↔ REPred S :=
  ⟨dioph_rePred, mrdp S⟩

end CS

