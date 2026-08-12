/-
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` before any module docstring command, so the header above is
-- kept verbatim as a plain block comment.)

import Mathlib

namespace Frontier

open Ordinal

/-- Syntax trees for hereditary base-`b` representations:
`oadd e c r` denotes `b ^ (value of e) * c + (value of r)`. -/
inductive HB where
  | zero : HB
  | oadd : HB → ℕ → HB → HB
deriving DecidableEq

namespace HB

/-- Size of a tree, used as a termination measure. -/
def size : HB → ℕ
  | .zero => 0
  | .oadd e _ r => e.size + r.size + 1

/-- Numerical value of a tree in base `b`. -/
def evalN (b : ℕ) : HB → ℕ
  | .zero => 0
  | .oadd e c r => b ^ (evalN b e) * c + evalN b r

/-- Ordinal value of a tree when the base is replaced by the ordinal `x`. -/
noncomputable def evalO (x : Ordinal) : HB → Ordinal
  | .zero => 0
  | .oadd e c r => x ^ (evalO x e) * (c : Ordinal) + evalO x r

/-- Well-formedness of a hereditary base-`b` representation: digits are nonzero and `< b`,
exponents are again well formed, and the tail is smaller than `b ^ (leading exponent)`
(which encodes that exponents are strictly decreasing). -/
inductive WF (b : ℕ) : HB → Prop
  | zero : WF b .zero
  | oadd {e c r} : WF b e → WF b r → 0 < c → c < b →
      evalN b r < b ^ evalN b e → WF b (.oadd e c r)

/-- The canonical hereditary base-`b` representation of a natural number. -/
def rep (b : ℕ) : ℕ → HB
  | 0 => .zero
  | (n + 1) =>
      .oadd (rep b (Nat.log b (n + 1))) ((n + 1) / b ^ Nat.log b (n + 1))
        (rep b ((n + 1) % b ^ Nat.log b (n + 1)))
  decreasing_by
  · exact Nat.log_lt_self b (Nat.succ_ne_zero n)
  · have hpos : 0 < b ^ Nat.log b (n + 1) := by
      rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb; rw [Nat.log_zero_left]; norm_num
      · positivity
    exact lt_of_lt_of_le (Nat.mod_lt _ hpos) (Nat.pow_log_le_self b (Nat.succ_ne_zero n))

/-! ### Numerical lemmas -/

lemma size_eq_zero : ∀ {t : HB}, t.size = 0 → t = .zero
  | .zero, _ => rfl
  | .oadd _ _ _, h => by simp [size] at h

lemma evalN_pos {b : ℕ} (hb : 1 ≤ b) : ∀ {t : HB}, WF b t → t ≠ .zero → 0 < evalN b t := by
  rintro (_ | ⟨e, c, r⟩) h hne
  · exact absurd rfl hne
  · cases h with
    | oadd he hr hc hcb hlt =>
      have h1 : 0 < b ^ evalN b e * c := Nat.mul_pos (pow_pos hb _) hc
      simp only [evalN]
      omega

lemma evalN_lt_pow_succ {b : ℕ} {e : HB} {c : ℕ} {r : HB} (h : WF b (.oadd e c r)) :
    evalN b (.oadd e c r) < b ^ (evalN b e + 1) := by
  cases h with
  | oadd he hr hc hcb hlt =>
    have h1 : b ^ evalN b e * c + b ^ evalN b e ≤ b ^ evalN b e * b := by
      have h2 : b ^ evalN b e * (c + 1) ≤ b ^ evalN b e * b := Nat.mul_le_mul_left _ (by omega)
      simpa [Nat.mul_add] using h2
    simp only [evalN, pow_succ]
    omega

lemma evalN_lt_of_exp_lt {b : ℕ} (hb : 1 ≤ b) {e : HB} {c : ℕ} {r f : HB} {d : ℕ} {s : HB}
    (ht : WF b (.oadd e c r)) (hu : WF b (.oadd f d s)) (h : evalN b e < evalN b f) :
    evalN b (.oadd e c r) < evalN b (.oadd f d s) := by
  have h1 := evalN_lt_pow_succ ht
  have h2 : b ^ (evalN b e + 1) ≤ b ^ evalN b f := Nat.pow_le_pow_right hb (by omega)
  cases hu with
  | oadd hf hs hd hdb hlts =>
    have h3 : b ^ evalN b f ≤ b ^ evalN b f * d := Nat.le_mul_of_pos_right _ hd
    simp only [evalN] at h1 ⊢
    omega

lemma nat_digit_lt {P c r d s : ℕ} (hs : s < P) (h : P * c + r < P * d + s) :
    c < d ∨ (c = d ∧ r < s) := by
  rcases lt_trichotomy c d with h1 | h1 | h1
  · exact Or.inl h1
  · subst h1; exact Or.inr ⟨rfl, by omega⟩
  · exfalso
    have h2 : P * (d + 1) ≤ P * c := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega

lemma nat_digit_eq {P c r d s : ℕ} (hr : r < P) (hs : s < P) (h : P * c + r = P * d + s) :
    c = d ∧ r = s := by
  rcases lt_trichotomy c d with h1 | h1 | h1
  · exfalso
    have h2 : P * (c + 1) ≤ P * d := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega
  · subst h1; exact ⟨rfl, by omega⟩
  · exfalso
    have h2 : P * (d + 1) ≤ P * c := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega

/-! ### Ordinal lemmas -/

lemma ord_term_lt {x α β : Ordinal} {c : ℕ} (hc : (c : Ordinal) < x)
    (hβ : β < x ^ α) : x ^ α * (c : Ordinal) + β < x ^ (α + 1) := by
  have h1 : x ^ α * (c : Ordinal) + β < x ^ α * (c : Ordinal) + x ^ α :=
    add_lt_add_right hβ _
  have h2 : x ^ α * (c : Ordinal) + x ^ α = x ^ α * ((c : Ordinal) + 1) := by
    rw [mul_add, mul_one]
  have h3 : x ^ α * ((c : Ordinal) + 1) ≤ x ^ α * x :=
    mul_le_mul_right (Order.add_one_le_iff.mpr hc) _
  have h4 : x ^ α * x = x ^ (α + 1) := by rw [Ordinal.opow_add, Ordinal.opow_one]
  exact lt_of_lt_of_le (h1.trans_eq h2) (h3.trans_eq h4)

lemma evalO_pos {b : ℕ} {x : Ordinal} (hx : 0 < x) {t : HB} (ht : WF b t) (h : t ≠ .zero) :
    0 < evalO x t := by
  cases ht with
  | zero => exact absurd rfl h
  | oadd he hr hc hcb hlt =>
    rename_i e c r
    have h1 : 0 < x ^ evalO x e * (c : Ordinal) :=
      mul_pos (opow_pos _ hx) (by exact_mod_cast hc)
    exact lt_of_lt_of_le h1 le_self_add

lemma ord_lt_of_digit_lt {x A er es : Ordinal} {c d : ℕ} (hcd : c < d) (her : er < x ^ A) :
    x ^ A * (c : Ordinal) + er < x ^ A * (d : Ordinal) + es := by
  have h1 : x ^ A * (c : Ordinal) + er < x ^ A * (c : Ordinal) + x ^ A :=
    add_lt_add_right her _
  have h2 : x ^ A * (c : Ordinal) + x ^ A = x ^ A * ((c : Ordinal) + 1) := by
    rw [mul_add, mul_one]
  have h3 : x ^ A * ((c : Ordinal) + 1) ≤ x ^ A * (d : Ordinal) := by
    refine mul_le_mul_right ?_ _
    exact_mod_cast Nat.succ_le_of_lt hcd
  exact lt_of_lt_of_le (h1.trans_eq h2) (h3.trans le_self_add)

/-- The master comparison lemma: for well-formed base-`b` trees, the numerical order in base `b`
is reflected by the ordinal order after replacing the base by any ordinal `x ≥ b`. -/
lemma key {b : ℕ} (hb : 2 ≤ b) {x : Ordinal} (hx : (b : Ordinal) ≤ x) (N : ℕ) :
    (∀ t u : HB, t.size + u.size ≤ N → WF b t → WF b u →
        (evalN b t < evalN b u → evalO x t < evalO x u) ∧
        (evalN b t = evalN b u → evalO x t = evalO x u))
      ∧ (∀ t E : HB, t.size + E.size ≤ N → WF b t → WF b E → evalN b t < b ^ evalN b E →
        evalO x t < x ^ evalO x E) := by
  have hx0 : (0 : Ordinal) < x :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : 0 < b)) hx
  induction N with
  | zero =>
    constructor
    · intro t u hN _ _
      have h1 : t = .zero := size_eq_zero (by omega)
      have h2 : u = .zero := size_eq_zero (by omega)
      subst h1; subst h2
      exact ⟨by simp [evalN], fun _ => rfl⟩
    · intro t E hN _ _ _
      have h1 : t = .zero := size_eq_zero (by omega)
      subst h1
      simpa [evalO] using opow_pos (evalO x E) hx0
  | succ N ih =>
    constructor
    · rintro (_ | ⟨e, c, r⟩) (_ | ⟨f, d, s⟩) hN ht hu
      · exact ⟨by simp [evalN], fun _ => rfl⟩
      · refine ⟨fun _ => ?_, fun h => ?_⟩
        · simpa [evalO] using evalO_pos hx0 hu (by simp)
        · exact absurd h.symm (evalN_pos (by omega) hu (by simp)).ne'
      · refine ⟨fun h => ?_, fun h => ?_⟩
        · exact absurd h (Nat.not_lt_zero _)
        · exact absurd h (evalN_pos (by omega) ht (by simp)).ne'
      · cases ht with
        | oadd he hr hc hcb hlt =>
        cases hu with
        | oadd hf hs hd hdb hlts =>
        simp only [size] at hN
        have m_ef : e.size + f.size ≤ N := by omega
        have m_rs : r.size + s.size ≤ N := by omega
        have m_rf : r.size + f.size ≤ N := by omega
        have m_tf : (HB.oadd e c r).size + f.size ≤ N := by simp only [size]; omega
        have ht : WF b (HB.oadd e c r) := WF.oadd he hr hc hcb hlt
        have hu : WF b (HB.oadd f d s) := WF.oadd hf hs hd hdb hlts
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rcases lt_trichotomy (evalN b e) (evalN b f) with hef | hef | hef
          · have hb2 : evalN b (HB.oadd e c r) < b ^ evalN b f :=
              lt_of_lt_of_le (evalN_lt_pow_succ ht) (Nat.pow_le_pow_right (by omega) (by omega))
            have h1 : evalO x (HB.oadd e c r) < x ^ evalO x f := ih.2 _ _ m_tf ht hf hb2
            refine lt_of_lt_of_le h1 ?_
            calc x ^ evalO x f = x ^ evalO x f * 1 := (mul_one _).symm
              _ ≤ x ^ evalO x f * (d : Ordinal) := by
                  refine mul_le_mul_right ?_ _
                  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
              _ ≤ evalO x (HB.oadd f d s) := by
                  simp only [evalO]
                  exact le_self_add
          · have hEF : evalO x e = evalO x f := (ih.1 e f m_ef he hf).2 hef
            simp only [evalN] at h
            rw [hef] at h hlt
            rcases nat_digit_lt hlts h with hcd | ⟨hcd, hrs⟩
            · have h2 : evalO x r < x ^ evalO x f := ih.2 r f m_rf hr hf hlt
              simp only [evalO]
              rw [hEF]
              exact ord_lt_of_digit_lt hcd h2
            · subst hcd
              simp only [evalO]
              rw [hEF]
              exact add_lt_add_right ((ih.1 r s m_rs hr hs).1 hrs) _
          · exact absurd h (asymm (evalN_lt_of_exp_lt (by omega) hu ht hef))
        · have hef : evalN b e = evalN b f := by
            rcases lt_trichotomy (evalN b e) (evalN b f) with h1 | h1 | h1
            · exact absurd h (ne_of_lt (evalN_lt_of_exp_lt (by omega) ht hu h1))
            · exact h1
            · exact absurd h.symm (ne_of_lt (evalN_lt_of_exp_lt (by omega) hu ht h1))
          have hEF : evalO x e = evalO x f := (ih.1 e f m_ef he hf).2 hef
          simp only [evalN] at h
          rw [hef] at h hlt
          obtain ⟨hcd, hrs⟩ := nat_digit_eq hlt hlts h
          have hRS : evalO x r = evalO x s := (ih.1 r s m_rs hr hs).2 hrs
          simp only [evalO]
          rw [hEF, hcd, hRS]
    · rintro (_ | ⟨e, c, r⟩) E hN ht hE h
      · simpa [evalO] using opow_pos (evalO x E) hx0
      · cases ht with
        | oadd he hr hc hcb hlt =>
        simp only [size] at hN
        have m_eE : e.size + E.size ≤ N := by omega
        have m_re : r.size + e.size ≤ N := by omega
        have hle : b ^ evalN b e ≤ evalN b (HB.oadd e c r) := by
          have h1 : b ^ evalN b e * 1 ≤ b ^ evalN b e * c := Nat.mul_le_mul_left _ hc
          simp only [evalN]
          omega
        have hexp : evalN b e < evalN b E :=
          (Nat.pow_lt_pow_iff_right (by omega : 1 < b)).mp (lt_of_le_of_lt hle h)
        have h1 : evalO x e < evalO x E := (ih.1 e E m_eE he hE).1 hexp
        have h2 : evalO x r < x ^ evalO x e := ih.2 r e m_re hr he hlt
        have h3 : evalO x (HB.oadd e c r) < x ^ (evalO x e + 1) := by
          simp only [evalO]
          exact ord_term_lt (lt_of_lt_of_le (by exact_mod_cast hcb) hx) h2
        exact lt_of_lt_of_le h3 (opow_le_opow_right hx0 (Order.add_one_le_iff.mpr h1))

lemma evalO_lt_of_evalN_lt {b : ℕ} (hb : 2 ≤ b) {x : Ordinal} (hx : (b : Ordinal) ≤ x) {t u : HB}
    (ht : WF b t) (hu : WF b u) (h : evalN b t < evalN b u) : evalO x t < evalO x u :=
  ((key hb hx (t.size + u.size)).1 t u le_rfl ht hu).1 h

lemma evalO_lt_pow {b : ℕ} (hb : 2 ≤ b) {x : Ordinal} (hx : (b : Ordinal) ≤ x) {t E : HB}
    (ht : WF b t) (hE : WF b E) (h : evalN b t < b ^ evalN b E) : evalO x t < x ^ evalO x E :=
  (key hb hx (t.size + E.size)).2 t E le_rfl ht hE h

/-- Evaluating at a natural ordinal base agrees with the numerical evaluation. -/
lemma evalO_natCast (b : ℕ) : ∀ t : HB, evalO (b : Ordinal) t = (evalN b t : Ordinal) := by
  intro t
  induction t with
  | zero => simp [evalO, evalN]
  | oadd e c r ihe ihr =>
    rw [evalO, evalN, ihe, ihr, Nat.cast_add, Ordinal.natCast_mul, Ordinal.opow_natCast,
      Ordinal.natCast_pow]

/-- A well-formed base-`b` representation is also a well-formed base-`b'` representation
for any larger base `b'`.  (This is the "base bump" step of Goodstein's process.) -/
lemma WF_mono {b b' : ℕ} (hb : 2 ≤ b) (hbb : b ≤ b') : ∀ {t : HB}, WF b t → WF b' t := by
  intro t ht
  induction ht with
  | zero => exact WF.zero
  | oadd he hr hc hcb hlt ihe ihr =>
    refine WF.oadd ihe ihr hc (lt_of_lt_of_le hcb hbb) ?_
    have hx : (b : Ordinal.{0}) ≤ (b' : Ordinal.{0}) := by exact_mod_cast hbb
    have h := evalO_lt_pow hb hx hr he hlt
    rw [evalO_natCast, evalO_natCast, Ordinal.opow_natCast, ← Ordinal.natCast_pow] at h
    exact_mod_cast h

/-! ### The canonical representation -/

lemma evalN_rep {b : ℕ} (hb : 2 ≤ b) : ∀ n : ℕ, evalN b (rep b n) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [rep, evalN]
    | (m + 1) =>
      have hlog : Nat.log b (m + 1) < m + 1 := Nat.log_lt_self b (Nat.succ_ne_zero m)
      have hpos : 0 < b ^ Nat.log b (m + 1) := pow_pos (by omega) _
      have hmod : (m + 1) % b ^ Nat.log b (m + 1) < m + 1 :=
        lt_of_lt_of_le (Nat.mod_lt _ hpos) (Nat.pow_log_le_self b (Nat.succ_ne_zero m))
      rw [rep, evalN, ih _ hlog, ih _ hmod]
      exact Nat.div_add_mod (m + 1) _

lemma WF_rep {b : ℕ} (hb : 2 ≤ b) : ∀ n : ℕ, WF b (rep b n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [rep]; exact WF.zero
    | (m + 1) =>
      have hlog : Nat.log b (m + 1) < m + 1 := Nat.log_lt_self b (Nat.succ_ne_zero m)
      have hpos : 0 < b ^ Nat.log b (m + 1) := pow_pos (by omega) _
      have hple : b ^ Nat.log b (m + 1) ≤ m + 1 := Nat.pow_log_le_self b (Nat.succ_ne_zero m)
      have hmod : (m + 1) % b ^ Nat.log b (m + 1) < m + 1 :=
        lt_of_lt_of_le (Nat.mod_lt _ hpos) hple
      rw [rep]
      refine WF.oadd (ih _ hlog) (ih _ hmod) (Nat.div_pos hple hpos) ?_ ?_
      · refine Nat.div_lt_of_lt_mul ?_
        have h1 := Nat.lt_pow_succ_log_self (by omega : 1 < b) (m + 1)
        calc m + 1 < b ^ (Nat.log b (m + 1) + 1) := h1
          _ = b ^ Nat.log b (m + 1) * b := by rw [pow_succ]
          _ = b ^ Nat.log b (m + 1) * b := rfl
      · rw [evalN_rep hb, evalN_rep hb]
        exact Nat.mod_lt _ hpos

end HB

open HB

/-- The Goodstein sequence started at `n`: the `k`-th term lives in base `k + 2`. -/
def goodstein (n : ℕ) : ℕ → ℕ
  | 0 => n
  | (k + 1) =>
      let m := goodstein n k
      if m = 0 then 0 else evalN (k + 3) (rep (k + 2) m) - 1

/-- The ordinal assigned to the natural number `m` written in hereditary base `b`. -/
noncomputable def ord (b m : ℕ) : Ordinal.{0} := evalO Ordinal.omega0.{0} (rep b m)

/-- One Goodstein step strictly decreases the associated ordinal. -/
lemma ord_step_lt {b : ℕ} (hb : 2 ≤ b) {m : ℕ} (hm : m ≠ 0) :
    ord (b + 1) (evalN (b + 1) (rep b m) - 1) < ord b m := by
  have hb1 : 2 ≤ b + 1 := by omega
  have ht : WF b (rep b m) := WF_rep hb m
  have ht' : WF (b + 1) (rep b m) := WF_mono hb (by omega) ht
  have hval : evalN b (rep b m) = m := evalN_rep hb m
  have hne : rep b m ≠ .zero := by
    intro h
    rw [h] at hval
    exact hm (by simpa [evalN] using hval.symm)
  have hM : 0 < evalN (b + 1) (rep b m) := evalN_pos (by omega) ht' hne
  have h1 : evalN (b + 1) (rep (b + 1) (evalN (b + 1) (rep b m) - 1))
      = evalN (b + 1) (rep b m) - 1 := evalN_rep hb1 _
  have h2 : evalN (b + 1) (rep (b + 1) (evalN (b + 1) (rep b m) - 1))
      < evalN (b + 1) (rep b m) := by omega
  have hx : ((b + 1 : ℕ) : Ordinal.{0}) ≤ Ordinal.omega0.{0} := le_of_lt (Ordinal.nat_lt_omega0 _)
  simpa [ord] using evalO_lt_of_evalN_lt hb1 hx (WF_rep hb1 _) ht' h2

-- Sanity check (evaluation only, not part of the proof):
-- `#eval (List.range 6).map (goodstein 3)` produces `[3, 3, 3, 2, 1, 0]`, and
-- `#eval (List.range 6).map (goodstein 4)` produces `[4, 26, 41, 60, 83, 109]`,
-- the classical Goodstein sequences for 3 and 4.

/-- **Goodstein's theorem**: every Goodstein sequence reaches `0`. -/
theorem Goodstein_terminates (n : ℕ) : ∃ k, goodstein n k = 0 := by
  by_contra hcon
  push_neg at hcon
  have hstep : ∀ k, ord (k + 1 + 2) (goodstein n (k + 1)) < ord (k + 2) (goodstein n k) := by
    intro k
    have hm : goodstein n k ≠ 0 := hcon k
    have h := ord_step_lt (b := k + 2) (by omega) hm
    have heq : goodstein n (k + 1) = evalN (k + 3) (rep (k + 2) (goodstein n k)) - 1 := by
      rw [goodstein]
      simp [hm]
    rw [heq]
    simpa using h
  obtain ⟨k, hk⟩ :=
    WellFounded.not_rel_apply_succ (r := (· < · : Ordinal.{0} → Ordinal.{0} → Prop))
      (fun k => ord (k + 2) (goodstein n k))
  exact hk (hstep k)

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

