/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is a plain
-- block comment; its text is otherwise verbatim.)

import Mathlib

/-!
We work with Mathlib's model of computation `Nat.Partrec.Code` together with its canonical
step-indexed evaluator `Nat.Partrec.Code.evaln`.  The running time of a program `c` on input `x`
is the least step bound `k` for which `evaln k c x` returns a value.

We exhibit an explicit total computable function `gfun` (a doubly exponentially growing function)
with *no fastest program*: for every program `c` computing `gfun` there is another program `d`
computing `gfun` which is strictly faster on all but finitely many inputs.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ### Elementary arithmetic helpers -/


theorem evaln_output_bound :
    ∀ (k : ℕ) (c : Code) (n m : ℕ), evaln k c n = some m → m + 2 ≤ (k + 2) ^ 2 ^ cdepth c := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  match k with
  | 0 => intro c n m h; simp [evaln] at h
  | (k + 1) =>
    intro c
    induction c with
    | zero =>
      intro n m h
      simp [evaln, Option.bind_eq_some_iff] at h
      show m + 2 ≤ (k + 3) ^ (2 ^ 1)
      have h' : (k + 3) ^ (2 ^ 1) = (k + 3) * (k + 3) := by norm_num [pow_succ]
      rw [h']; nlinarith [h.2]
    | succ =>
      intro n m h
      simp [evaln, Option.bind_eq_some_iff] at h
      show m + 2 ≤ (k + 3) ^ (2 ^ 1)
      have h' : (k + 3) ^ (2 ^ 1) = (k + 3) * (k + 3) := by norm_num [pow_succ]
      rw [h']; nlinarith [h.1, h.2]
    | left =>
      intro n m h
      simp [evaln, Option.bind_eq_some_iff] at h
      have h1 : m ≤ n := by rw [← h.2]; exact Nat.unpair_left_le n
      show m + 2 ≤ (k + 3) ^ (2 ^ 1)
      have h' : (k + 3) ^ (2 ^ 1) = (k + 3) * (k + 3) := by norm_num [pow_succ]
      rw [h']; nlinarith [h.1]
    | right =>
      intro n m h
      simp [evaln, Option.bind_eq_some_iff] at h
      have h1 : m ≤ n := by rw [← h.2]; exact Nat.unpair_right_le n
      show m + 2 ≤ (k + 3) ^ (2 ^ 1)
      have h' : (k + 3) ^ (2 ^ 1) = (k + 3) * (k + 3) := by norm_num [pow_succ]
      rw [h']; nlinarith [h.1]
    | pair cf cg ihf ihg =>
      intro n m h
      simp [evaln, Option.bind_eq_some_iff, Seq.seq] at h
      obtain ⟨hn, a, ha, b, hb, hab⟩ := h
      have h1 : a + 2 ≤ (k + 3) ^ 2 ^ cdepth cf := ihf n a ha
      have h2 : b + 2 ≤ (k + 3) ^ 2 ^ cdepth cg := ihg n b hb
      show m + 2 ≤ (k + 3) ^ 2 ^ (1 + max (cdepth cf) (cdepth cg))
      rw [pow_pow_succ]
      set C := (k + 3) ^ 2 ^ (max (cdepth cf) (cdepth cg)) with hC
      have hf : (k + 3) ^ 2 ^ cdepth cf ≤ C := pow_pow_mono k (le_max_left _ _)
      have hg : (k + 3) ^ 2 ^ cdepth cg ≤ C := pow_pow_mono k (le_max_right _ _)
      have hC2 : 2 ≤ C := le_trans (by omega) (base_le_pow_pow k _)
      have hmax : max a b + 2 ≤ C := by
        rcases le_total a b with hab' | hab' <;> simp [hab'] <;> omega
      have hlt : Nat.pair a b < (max a b + 1) ^ 2 := pair_lt_sq a b
      have hsq : (max a b + 1) ^ 2 ≤ (C - 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hCC : (C - 1) ^ 2 + 2 ≤ C * C := by
        have h' : (C - 1) ^ 2 = (C - 1) * (C - 1) := by ring
        have h'' : C - 1 + 1 = C := by omega
        nlinarith [hC2, h'']
      omega
    | comp cf cg ihf ihg =>
      intro n m h
      simp [evaln, Option.bind_eq_some_iff] at h
      obtain ⟨hn, a, ha, hb⟩ := h
      have h1 : m + 2 ≤ (k + 3) ^ 2 ^ cdepth cf := ihf a m hb
      show m + 2 ≤ (k + 3) ^ 2 ^ (1 + max (cdepth cf) (cdepth cg))
      exact h1.trans (pow_pow_mono k (by omega))
    | prec cf cg ihf ihg =>
      intro n m h
      simp [evaln, Option.bind_eq_some_iff] at h
      obtain ⟨hn, h2⟩ := h
      show m + 2 ≤ (k + 3) ^ 2 ^ (1 + max (cdepth cf) (cdepth cg))
      cases hy : (Nat.unpair n).2 with
      | zero =>
        rw [hy] at h2
        simp at h2
        have h1 : m + 2 ≤ (k + 3) ^ 2 ^ cdepth cf := ihf _ _ h2
        exact h1.trans (pow_pow_mono k (by omega))
      | succ y =>
        rw [hy] at h2
        simp [Option.bind_eq_some_iff] at h2
        obtain ⟨i, -, h3⟩ := h2
        have h1 : m + 2 ≤ (k + 3) ^ 2 ^ cdepth cg := ihg _ _ h3
        exact h1.trans (pow_pow_mono k (by omega))
    | rfind' cf ihf =>
      intro n m h
      simp [evaln, Option.bind_eq_some_iff] at h
      obtain ⟨hn, a, ha, h2⟩ := h
      show m + 2 ≤ (k + 3) ^ 2 ^ (1 + cdepth cf)
      by_cases ha0 : a = 0
      · simp [ha0] at h2
        have hmn : m ≤ n := by rw [← h2]; exact Nat.unpair_right_le n
        have h3 : k + 3 ≤ (k + 3) ^ 2 ^ (cdepth cf) := base_le_pow_pow k _
        rw [pow_pow_succ]
        nlinarith
      · simp [ha0] at h2
        have hrec := ihk k (by omega) (Code.rfind' cf) _ _ h2
        simp only [cdepth] at hrec ⊢
        exact hrec.trans (Nat.pow_le_pow_left (by omega) _)

/-! ### Running time -/

/-- The running time of the program `c` on input `x`: the least step bound sufficing to
produce an output (`0` if `c` diverges on `x`). -/
