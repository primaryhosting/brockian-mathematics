/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Statement: Every Goodstein sequence reaches 0 (uses ε₀ well-foundedness; independent of PA).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- written as a plain block comment; it is repeated as a module docstring below.)


/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Ordinal

/-! ## Hereditary base representations

For a base `b ≥ 2`, every positive natural number `n` can be written as
`n = b ^ e * c + r` with `e = Nat.log b n`, `1 ≤ c < b` and `r < b ^ e`, and iterating this
inside the exponent yields the *hereditary base-`b` representation* of `n`.

Two operations are defined by this recursion:

* `ordOf b n` : the ordinal obtained by replacing the base `b` by `ω` in the hereditary
  base-`b` representation of `n` (a "Goodstein ordinal", an ordinal `< ε₀`);
* `shiftBase b n` : the natural number obtained by replacing the base `b` by `b + 1`
  in the hereditary base-`b` representation of `n`.
-/

private lemma pow_log_pos (b n : ℕ) : 0 < b ^ Nat.log b n := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    simp
  · exact pow_pos hb _

private lemma mod_pow_log_lt (b n : ℕ) (h : n ≠ 0) : n % b ^ Nat.log b n < n :=
  lt_of_lt_of_le (Nat.mod_lt _ (pow_log_pos b n)) (Nat.pow_log_le_self b h)

/-- The ordinal attached to `n` by replacing the base `b` by `ω` in the hereditary base-`b`
representation of `n`. -/
noncomputable def ordOf (b n : ℕ) : Ordinal.{0} :=
  if h : n = 0 then 0
  else
    ω ^ ordOf b (Nat.log b n) * ((n / b ^ Nat.log b n : ℕ) : Ordinal)
      + ordOf b (n % b ^ Nat.log b n)
  termination_by n
  decreasing_by
  · exact Nat.log_lt_self b h
  · exact mod_pow_log_lt b n h

/-- The natural number obtained by replacing the base `b` by `b + 1` in the hereditary base-`b`
representation of `n`. -/
def shiftBase (b n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    (b + 1) ^ shiftBase b (Nat.log b n) * (n / b ^ Nat.log b n)
      + shiftBase b (n % b ^ Nat.log b n)
  termination_by n
  decreasing_by
  · exact Nat.log_lt_self b h
  · exact mod_pow_log_lt b n h

/-- The Goodstein sequence starting at `n`: `goodstein n 0 = n` (read in base `2`), and each
step rewrites the current value in hereditary base `k + 2`, bumps the base to `k + 3`, and
subtracts one. -/
def goodstein (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => shiftBase (k + 2) (goodstein n k) - 1

/-! ## Basic unfolding lemmas -/

@[simp] lemma ordOf_zero (b : ℕ) : ordOf b 0 = 0 := by rw [ordOf]; simp

lemma ordOf_eq_of_ne_zero {b n : ℕ} (h : n ≠ 0) :
    ordOf b n =
      ω ^ ordOf b (Nat.log b n) * ((n / b ^ Nat.log b n : ℕ) : Ordinal)
      + ordOf b (n % b ^ Nat.log b n) := by
  rw [ordOf]; simp [h]

@[simp] lemma shiftBase_zero (b : ℕ) : shiftBase b 0 = 0 := by rw [shiftBase]; simp

lemma shiftBase_eq_of_ne_zero {b n : ℕ} (h : n ≠ 0) :
    shiftBase b n =
      (b + 1) ^ shiftBase b (Nat.log b n) * (n / b ^ Nat.log b n)
        + shiftBase b (n % b ^ Nat.log b n) := by
  rw [shiftBase]; simp [h]

/-! ## Arithmetic of the base-`b` decomposition -/

lemma div_pow_log_pos {b n : ℕ} (h : n ≠ 0) : 0 < n / b ^ Nat.log b n :=
  Nat.div_pos (Nat.pow_log_le_self b h) (pow_log_pos b n)

lemma div_pow_log_lt {b n : ℕ} (hb : 2 ≤ b) : n / b ^ Nat.log b n < b := by
  have hlt : n < b ^ (Nat.log b n + 1) := Nat.lt_pow_succ_log_self hb n
  have := Nat.div_lt_of_lt_mul (by simpa [pow_succ] using hlt)
  simpa using this

/-! ## Ordinal estimates -/

/-- A "carry" estimate: if `X < ω ^ A` and `A < B` then `ω ^ A * c + X < ω ^ B`. -/
lemma opow_mul_add_lt_opow {A B X : Ordinal} {c : ℕ} (hAB : A < B) (hX : X < ω ^ A) :
    ω ^ A * (c : Ordinal) + X < ω ^ B := by
  calc ω ^ A * (c : Ordinal) + X < ω ^ A * (c : Ordinal) + ω ^ A := add_lt_add_right hX _
    _ = ω ^ A * ((c : Ordinal) + 1) := by rw [mul_add, mul_one]
    _ ≤ ω ^ A * ω := by
        refine mul_le_mul_right ?_ _
        rw [show ((c : Ordinal) + 1) = ((c + 1 : ℕ) : Ordinal) by push_cast; rfl]
        exact le_of_lt (Ordinal.nat_lt_omega0 _)
    _ = ω ^ (A + 1) := by rw [Ordinal.add_one_eq_succ, Ordinal.opow_succ]
    _ ≤ ω ^ B := by
        refine Ordinal.opow_le_opow_right Ordinal.omega0_pos ?_
        rwa [Ordinal.add_one_eq_succ, Order.succ_le_iff]

/-- A "digit" estimate: if `X < ω ^ A` and `c < d` then `ω ^ A * c + X < ω ^ A * d`. -/
lemma opow_mul_add_lt_opow_mul {A X : Ordinal} {c d : ℕ} (hcd : c < d) (hX : X < ω ^ A) :
    ω ^ A * (c : Ordinal) + X < ω ^ A * (d : Ordinal) := by
  calc ω ^ A * (c : Ordinal) + X < ω ^ A * (c : Ordinal) + ω ^ A := add_lt_add_right hX _
    _ = ω ^ A * ((c : Ordinal) + 1) := by rw [mul_add, mul_one]
    _ ≤ ω ^ A * (d : Ordinal) := by
        refine mul_le_mul_right ?_ _
        rw [show ((c : Ordinal) + 1) = ((c + 1 : ℕ) : Ordinal) by push_cast; rfl]
        exact_mod_cast hcd

/-- Main induction: `ordOf b` is strictly monotone, and `n < b ^ e` implies
`ordOf b n < ω ^ ordOf b e`. -/
lemma ordOf_key {b : ℕ} (hb : 2 ≤ b) (N : ℕ) :
    (∀ m, m < N → ordOf b m < ordOf b N) ∧ (∀ x, x < b ^ N → ordOf b x < ω ^ ordOf b N) := by
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  have part1 : ∀ m, m < N → ordOf b m < ordOf b N := by
    intro m hm
    have hN : N ≠ 0 := by omega
    have hNeq : ordOf b N =
        ω ^ ordOf b (Nat.log b N) * ((N / b ^ Nat.log b N : ℕ) : Ordinal)
          + ordOf b (N % b ^ Nat.log b N) := ordOf_eq_of_ne_zero hN
    have heN : Nat.log b N < N := Nat.log_lt_self b hN
    have hrlt : N % b ^ Nat.log b N < b ^ Nat.log b N := Nat.mod_lt _ (pow_log_pos b N)
    have hcpos : 0 < N / b ^ Nat.log b N := div_pow_log_pos hN
    have hpos : (0 : Ordinal) <
        ω ^ ordOf b (Nat.log b N) * ((N / b ^ Nat.log b N : ℕ) : Ordinal) := by
      refine mul_pos (Ordinal.opow_pos _ Ordinal.omega0_pos) ?_
      exact_mod_cast hcpos
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · rw [ordOf_zero, hNeq]
      exact lt_of_lt_of_le hpos (le_self_add)
    · have hm0 : m ≠ 0 := by omega
      have hmeq : ordOf b m =
          ω ^ ordOf b (Nat.log b m) * ((m / b ^ Nat.log b m : ℕ) : Ordinal)
            + ordOf b (m % b ^ Nat.log b m) := ordOf_eq_of_ne_zero hm0
      have hr'lt : m % b ^ Nat.log b m < b ^ Nat.log b m := Nat.mod_lt _ (pow_log_pos b m)
      have hee : Nat.log b m ≤ Nat.log b N := Nat.log_mono_right (le_of_lt hm)
      rcases lt_or_eq_of_le hee with hlt | heq
      · have h1 : ordOf b (Nat.log b m) < ordOf b (Nat.log b N) := (IH _ heN).1 _ hlt
        have h2 : ordOf b (m % b ^ Nat.log b m) < ω ^ ordOf b (Nat.log b m) :=
          (IH _ (lt_trans hlt heN)).2 _ hr'lt
        have h3 : ordOf b m < ω ^ ordOf b (Nat.log b N) := by
          rw [hmeq]; exact opow_mul_add_lt_opow h1 h2
        refine lt_of_lt_of_le h3 ?_
        rw [hNeq]
        refine le_trans ?_ (le_self_add)
        calc ω ^ ordOf b (Nat.log b N) = ω ^ ordOf b (Nat.log b N) * 1 := by rw [mul_one]
          _ ≤ ω ^ ordOf b (Nat.log b N) * ((N / b ^ Nat.log b N : ℕ) : Ordinal) := by
              refine mul_le_mul_right ?_ _
              exact_mod_cast hcpos
      · rw [heq] at hmeq hr'lt
        have h2 : ordOf b (m % b ^ Nat.log b N) < ω ^ ordOf b (Nat.log b N) :=
          (IH _ heN).2 _ hr'lt
        have hcle : m / b ^ Nat.log b N ≤ N / b ^ Nat.log b N :=
          Nat.div_le_div_right (le_of_lt hm)
        rcases lt_or_eq_of_le hcle with hclt | hceq
        · rw [hNeq, hmeq]
          exact lt_of_lt_of_le (opow_mul_add_lt_opow_mul hclt h2) le_self_add
        · have hmd : b ^ Nat.log b N * (m / b ^ Nat.log b N) + m % b ^ Nat.log b N = m :=
            Nat.div_add_mod m (b ^ Nat.log b N)
          have hNd : b ^ Nat.log b N * (N / b ^ Nat.log b N) + N % b ^ Nat.log b N = N :=
            Nat.div_add_mod N (b ^ Nat.log b N)
          have hrr : m % b ^ Nat.log b N < N % b ^ Nat.log b N := by
            rw [hceq] at hmd
            omega
          have h3 : ordOf b (m % b ^ Nat.log b N) < ordOf b (N % b ^ Nat.log b N) :=
            (IH _ (lt_of_lt_of_le hrlt (Nat.pow_log_le_self b hN))).1 _ hrr
          rw [hmeq, hNeq, hceq]
          exact add_lt_add_right h3 _
  refine ⟨part1, ?_⟩
  intro x hx
  rcases Nat.eq_zero_or_pos x with rfl | hxpos
  · simpa using Ordinal.opow_pos (ordOf b N) Ordinal.omega0_pos
  · have hx0 : x ≠ 0 := by omega
    have hbe : b ^ Nat.log b x ≤ x := Nat.pow_log_le_self b hx0
    have heN : Nat.log b x < N := by
      by_contra hcon
      push_neg at hcon
      have : b ^ N ≤ b ^ Nat.log b x := Nat.pow_le_pow_right (by omega) hcon
      omega
    have h1 : ordOf b (Nat.log b x) < ordOf b N := part1 _ heN
    have h2 : ordOf b (x % b ^ Nat.log b x) < ω ^ ordOf b (Nat.log b x) :=
      (IH _ heN).2 _ (Nat.mod_lt _ (pow_log_pos b x))
    rw [ordOf_eq_of_ne_zero hx0]
    exact opow_mul_add_lt_opow h1 h2

lemma ordOf_strictMono {b : ℕ} (hb : 2 ≤ b) : StrictMono (ordOf b) :=
  fun _ _ h => (ordOf_key hb _).1 _ h

lemma ordOf_lt_opow {b : ℕ} (hb : 2 ≤ b) {x e : ℕ} (h : x < b ^ e) :
    ordOf b x < ω ^ ordOf b e :=
  (ordOf_key hb e).2 x h

lemma ordOf_pow {b : ℕ} (hb : 2 ≤ b) (k : ℕ) : ordOf b (b ^ k) = ω ^ ordOf b k := by
  have hbpos : 0 < b := by omega
  have hne : b ^ k ≠ 0 := Nat.ne_of_gt (pow_pos hbpos k)
  rw [ordOf_eq_of_ne_zero hne, Nat.log_pow hb (b := b) k, Nat.div_self (pow_pos hbpos k),
    Nat.mod_self, ordOf_zero, Nat.cast_one, mul_one, add_zero]

/-! ## The shift preserves the associated ordinal -/

lemma shiftBase_ne_zero {b n : ℕ} (h : n ≠ 0) : shiftBase b n ≠ 0 := by
  rw [shiftBase_eq_of_ne_zero h]
  have h1 : 0 < (b + 1) ^ shiftBase b (Nat.log b n) := pow_pos (Nat.succ_pos b) _
  have h2 : 0 < n / b ^ Nat.log b n := div_pow_log_pos h
  have := Nat.mul_pos h1 h2
  omega

lemma ordOf_shiftBase {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    ordOf (b + 1) (shiftBase b n) = ordOf b n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have hn : n ≠ 0 := by omega
    have hb1 : 2 ≤ b + 1 := by omega
    set e := Nat.log b n with he
    set c := n / b ^ e with hc
    set r := n % b ^ e with hr
    have heN : e < n := Nat.log_lt_self b hn
    have hrlt : r < b ^ e := Nat.mod_lt _ (pow_log_pos b n)
    have hrn : r < n := mod_pow_log_lt b n hn
    have hcpos : 0 < c := div_pow_log_pos hn
    have hcb : c < b := div_pow_log_lt hb
    set E := shiftBase b e with hE
    set R := shiftBase b r with hR
    have hSE : ordOf (b + 1) E = ordOf b e := IH e heN
    have hSR : ordOf (b + 1) R = ordOf b r := IH r hrn
    have hRlt : R < (b + 1) ^ E := by
      have h1 : ordOf (b + 1) R < ordOf (b + 1) ((b + 1) ^ E) := by
        rw [hSR, ordOf_pow hb1 E, hSE]
        exact ordOf_lt_opow hb hrlt
      exact (ordOf_strictMono hb1).lt_iff_lt.mp h1
    have hS : shiftBase b n = (b + 1) ^ E * c + R := shiftBase_eq_of_ne_zero hn
    have hSne : shiftBase b n ≠ 0 := shiftBase_ne_zero hn
    have hlog : Nat.log (b + 1) (shiftBase b n) = E := by
      refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_
      · rw [hS]
        have : (b + 1) ^ E ≤ (b + 1) ^ E * c := Nat.le_mul_of_pos_right _ hcpos
        omega
      · rw [hS, pow_succ]
        have h2 : (b + 1) ^ E * c + (b + 1) ^ E = (b + 1) ^ E * (c + 1) := by ring
        have h3 : (b + 1) ^ E * (c + 1) ≤ (b + 1) ^ E * (b + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
    have hdiv : shiftBase b n / (b + 1) ^ E = c := by
      rw [hS, Nat.mul_add_div (pow_pos (Nat.succ_pos b) _), Nat.div_eq_of_lt hRlt, Nat.add_zero]
    have hmod : shiftBase b n % (b + 1) ^ E = R := by
      rw [hS, Nat.mul_add_mod, Nat.mod_eq_of_lt hRlt]
    rw [ordOf_eq_of_ne_zero hSne, hlog, hdiv, hmod, hSE, hSR, ordOf_eq_of_ne_zero hn]

/-! ## The Goodstein ordinals lie below `ε₀`

The ordinals `ordOf b n` used as the termination measure are exactly the ordinals `< ε₀`
occurring in the usual proof of Goodstein's theorem; this is the point where the
(unprovable in `PA`) well-foundedness of `ε₀` is used. -/

lemma opow_lt_epsilon0 {a : Ordinal} (h : a < ε₀) : ω ^ a < ε₀ := by
  calc ω ^ a < ω ^ (ε₀ : Ordinal) := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr h
    _ = ε₀ := Ordinal.omega0_opow_epsilon 0

lemma add_lt_epsilon0 {a c : Ordinal} (ha : a < ε₀) (hc : c < ε₀) : a + c < ε₀ := by
  have h := Ordinal.principal_add_omega0_opow (ε₀ : Ordinal)
  rw [Ordinal.omega0_opow_epsilon] at h
  exact h ha hc

lemma mul_lt_epsilon0 {a c : Ordinal} (ha : a < ε₀) (hc : c < ε₀) : a * c < ε₀ := by
  have h := Ordinal.principal_mul_omega0_opow_opow (ε₀ : Ordinal)
  rw [Ordinal.omega0_opow_epsilon, Ordinal.omega0_opow_epsilon] at h
  exact h ha hc

/-- Every ordinal attached to a natural number by the hereditary base-`b` representation is
smaller than `ε₀`. -/
lemma ordOf_lt_epsilon0 (b n : ℕ) : ordOf b n < ε₀ := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [Ordinal.epsilon_pos 0]
  · have hn : n ≠ 0 := by omega
    rw [ordOf_eq_of_ne_zero hn]
    exact add_lt_epsilon0
      (mul_lt_epsilon0 (opow_lt_epsilon0 (IH _ (Nat.log_lt_self b hn)))
        (Ordinal.natCast_lt_epsilon _ 0))
      (IH _ (mod_pow_log_lt b n hn))

/-! ## Goodstein's theorem -/

lemma goodstein_descent (n k : ℕ) (h : goodstein n k ≠ 0) :
    ordOf (k + 3) (goodstein n (k + 1)) < ordOf (k + 2) (goodstein n k) := by
  have hb : 2 ≤ k + 2 := by omega
  have hSne : shiftBase (k + 2) (goodstein n k) ≠ 0 := shiftBase_ne_zero h
  have hlt : goodstein n (k + 1) < shiftBase (k + 2) (goodstein n k) := by
    rw [goodstein]
    omega
  have hmono := ordOf_strictMono (show 2 ≤ k + 2 + 1 by omega) hlt
  rw [ordOf_shiftBase hb] at hmono
  simpa using hmono

/-- **Goodstein's theorem**: every Goodstein sequence eventually reaches `0`. -/
theorem Goodstein_terminates (n : ℕ) : ∃ k, goodstein n k = 0 := by
  by_contra hcon
  push_neg at hcon
  have hdesc : ∀ k, ordOf (k + 1 + 2) (goodstein n (k + 1)) < ordOf (k + 2) (goodstein n k) :=
    fun k => by simpa using goodstein_descent n k (hcon k)
  exact not_strictAnti_of_wellFoundedLT (fun k => ordOf (k + 2) (goodstein n k))
    (strictAnti_nat_of_succ_lt hdesc)

end Frontier


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

