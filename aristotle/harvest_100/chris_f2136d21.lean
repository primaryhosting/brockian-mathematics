/-
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false

/-!
# Ladner's theorem

This file formalises Ladner's theorem: if `P ≠ NP`, then there is an `NP`-intermediate
language, i.e. a language that lies in `NP`, is not in `P`, and is not `NP`-complete.

Since Mathlib contains no development of time-bounded computation, the classes `P`, `NP` and the
polynomial time computable functions are packaged into an abstract structure `CS.Setting`, whose
fields are the standard, model independent facts used in Ladner's proof:

* `P` is contained in `NP`;
* `P` and the polynomial time functions come with enumerations `Mdec`, `Redf` (recursive
  presentability of `P`);
* `P` is closed under finite variations, contains the empty language, and is closed downwards
  under polynomial time many-one reductions;
* `NP` is closed under intersection with a language in `P`;
* `holeEff`: for `A` in `NP`, the hole pattern of the delayed diagonalisation, i.e. the set of
  lengths `n` at which the stage function `CS.stage` is even, is decidable in polynomial time.

Only the last field depends on the machine model: it is the statement that Ladner's clocked
delayed diagonalisation can be carried out in polynomial time.  Everything else -- the
construction of the stage function, the case analysis on whether it is bounded, and the
verification of the three requirements on the resulting language -- is proved here.

The construction is Ladner's blowing-holes argument.  Given `A` in `NP` but not in `P` we build
a nondecreasing stage function `stage A Mdec Redf : ℕ → ℕ`, increasing it by one exactly when the
current requirement is met by some short string, and set
`ladnerLang s A x = A x && (stage (x.length) is even)`.  If the stage function were bounded it
would be eventually equal to some `k`: for even `k = 2 * i` the `i`-th polynomial time decider
would decide `ladnerLang s A`, which is then a finite variant of `A`, so `A` would be in `P`;
for odd `k = 2 * i + 1` the language `ladnerLang s A` would be finite (hence in `P`) while the
`i`-th polynomial time function reduces `A` to it, so again `A` would be in `P`.  Hence the
stage function is unbounded, and every even (resp. odd) stage is eventually left, which
diagonalises against every polynomial time decider (resp. against every polynomial time
reduction of `A` to `ladnerLang s A`).
-/

namespace CS

/-- Binary strings. -/
abbrev Str := List Bool

/-- A language is a decision predicate on binary strings. -/
abbrev Lang := Str → Bool

/-- `holed A t` is the language `A` with "holes" punched into it: a string `x` of length `n`
is kept only when the stage value `t n` is even. -/
def holed (A : Lang) (t : ℕ → ℕ) : Lang :=
  fun x => A x && decide (t x.length % 2 = 0)

/-- The diagonalisation requirement examined at step `n`, given the table `t` of stage values
computed so far.

If the current stage `t n` is even, say `t n = 2 * i`, we look (among the strings of length at
most `log₂ (n+1)`) for a point where the `i`-th polynomial time decider fails to decide
`holed A t`.  If the current stage is odd, say `t n = 2 * i + 1`, we look for a point where the
`i`-th polynomial time function fails to be a reduction of `A` to `holed A t`. -/
def wit (A : Lang) (Mdec : ℕ → Lang) (Redf : ℕ → Str → Str) (t : ℕ → ℕ) (n : ℕ) : Prop :=
  if t n % 2 = 0 then
    ∃ x : Str, x.length ≤ Nat.log 2 (n + 1) ∧ Mdec (t n / 2) x ≠ holed A t x
  else
    ∃ x : Str, x.length ≤ Nat.log 2 (n + 1) ∧ (Redf (t n / 2) x).length ≤ Nat.log 2 (n + 1) ∧
      A x ≠ holed A t (Redf (t n / 2) x)

open Classical in
/-- One step of the stage construction: the stage is increased by one exactly when the current
requirement has a witness. -/
noncomputable def stageStep (A : Lang) (Mdec : ℕ → Lang) (Redf : ℕ → Str → Str)
    (t : ℕ → ℕ) (n : ℕ) : ℕ :=
  if wit A Mdec Redf t n then t n + 1 else t n

/-- `tbl A Mdec Redf n` is the table of stage values; it is correct on arguments `≤ n`. -/
noncomputable def tbl (A : Lang) (Mdec : ℕ → Lang) (Redf : ℕ → Str → Str) : ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | n + 1 => fun m =>
      if m ≤ n then tbl A Mdec Redf n m else stageStep A Mdec Redf (tbl A Mdec Redf n) n

/-- The stage function of Ladner's delayed diagonalisation. -/
noncomputable def stage (A : Lang) (Mdec : ℕ → Lang) (Redf : ℕ → Str → Str) (n : ℕ) : ℕ :=
  tbl A Mdec Redf n n

section StageBasics

variable {A : Lang} {Mdec : ℕ → Lang} {Redf : ℕ → Str → Str}

lemma log_two_succ_le (n : ℕ) : Nat.log 2 (n + 1) ≤ n :=
  Nat.lt_succ_iff.mp (Nat.log_lt_self 2 (Nat.succ_ne_zero n))

/-- `wit` only inspects the table on arguments `≤ n`. -/
lemma wit_congr {t t' : ℕ → ℕ} {n : ℕ} (h : ∀ m ≤ n, t m = t' m) :
    wit A Mdec Redf t n ↔ wit A Mdec Redf t' n := by
  have hn : t n = t' n := h n le_rfl
  have hh : ∀ x : Str, x.length ≤ Nat.log 2 (n + 1) → holed A t x = holed A t' x := by
    intro x hx
    simp only [holed, h x.length (le_trans hx (log_two_succ_le n))]
  unfold wit
  rw [hn]
  by_cases hpar : t' n % 2 = 0
  · rw [if_pos hpar, if_pos hpar]
    constructor <;> rintro ⟨x, hx, hne⟩ <;> refine ⟨x, hx, ?_⟩
    · rw [← hh x hx]; exact hne
    · rw [hh x hx]; exact hne
  · rw [if_neg hpar, if_neg hpar]
    constructor <;> rintro ⟨x, hx, hr, hne⟩ <;> refine ⟨x, hx, hr, ?_⟩
    · rw [← hh _ hr]; exact hne
    · rw [hh _ hr]; exact hne

lemma tbl_agree : ∀ {m n : ℕ}, m ≤ n → tbl A Mdec Redf n m = stage A Mdec Redf m := by
  intro m n
  induction n with
  | zero => intro h; rw [Nat.le_zero.mp h]; rfl
  | succ n ih =>
      intro h
      rcases eq_or_lt_of_le h with h' | h'
      · rw [← h']; rfl
      · have hmn : m ≤ n := Nat.lt_succ_iff.mp h'
        simp only [tbl, if_pos hmn, ih hmn]

/-- For any bound there are arbitrarily late steps whose search window is large enough. -/
lemma exists_log_ge (N a b : ℕ) :
    ∃ n, N ≤ n ∧ a ≤ Nat.log 2 (n + 1) ∧ b ≤ Nat.log 2 (n + 1) := by
  obtain ⟨u, hu⟩ : ∃ u, u = 2 ^ a := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = 2 ^ b := ⟨_, rfl⟩
  refine ⟨N + u + v, by omega, ?_, ?_⟩ <;>
    rw [Nat.le_log_iff_pow_le (by norm_num) (Nat.succ_ne_zero _)] <;> omega

lemma stage_zero : stage A Mdec Redf 0 = 0 := rfl

lemma stage_succ_eq (n : ℕ) :
    stage A Mdec Redf (n + 1) = stageStep A Mdec Redf (stage A Mdec Redf) n := by
  have h1 : stage A Mdec Redf (n + 1) = stageStep A Mdec Redf (tbl A Mdec Redf n) n := by
    show tbl A Mdec Redf (n + 1) (n + 1) = _
    simp only [tbl, if_neg (by omega : ¬ (n + 1 ≤ n))]
  have hw : wit A Mdec Redf (tbl A Mdec Redf n) n ↔ wit A Mdec Redf (stage A Mdec Redf) n :=
    wit_congr (fun m hm => tbl_agree hm)
  rw [h1]
  simp only [stageStep]
  rw [tbl_agree (le_refl n)]
  by_cases hc : wit A Mdec Redf (stage A Mdec Redf) n
  · rw [if_pos (hw.mpr hc), if_pos hc]
  · rw [if_neg (fun h => hc (hw.mp h)), if_neg hc]

lemma stage_succ_of_wit {n : ℕ} (hw : wit A Mdec Redf (stage A Mdec Redf) n) :
    stage A Mdec Redf (n + 1) = stage A Mdec Redf n + 1 := by
  rw [stage_succ_eq]
  simp only [stageStep]
  rw [if_pos hw]

lemma stage_succ_of_not_wit {n : ℕ} (hw : ¬ wit A Mdec Redf (stage A Mdec Redf) n) :
    stage A Mdec Redf (n + 1) = stage A Mdec Redf n := by
  rw [stage_succ_eq]
  simp only [stageStep]
  rw [if_neg hw]

lemma stage_succ_le (n : ℕ) : stage A Mdec Redf (n + 1) ≤ stage A Mdec Redf n + 1 := by
  by_cases hw : wit A Mdec Redf (stage A Mdec Redf) n
  · rw [stage_succ_of_wit hw]
  · rw [stage_succ_of_not_wit hw]; omega

lemma stage_mono : Monotone (stage A Mdec Redf) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  by_cases hw : wit A Mdec Redf (stage A Mdec Redf) n
  · rw [stage_succ_of_wit hw]; omega
  · rw [stage_succ_of_not_wit hw]

/-- If the stage does not increase at `n`, then the requirement at `n` has no witness. -/
lemma not_wit_of_stage_eq {n : ℕ} (h : stage A Mdec Redf (n + 1) = stage A Mdec Redf n) :
    ¬ wit A Mdec Redf (stage A Mdec Redf) n := by
  intro hw
  rw [stage_succ_of_wit hw] at h
  omega

/-- If the stage is unbounded, then every value `k` is reached and left. -/
lemma exists_stage_step (hub : ∀ N, ∃ n, N < stage A Mdec Redf n) (k : ℕ) :
    ∃ n, stage A Mdec Redf n = k ∧ wit A Mdec Redf (stage A Mdec Redf) n := by
  classical
  have hex : ∃ n, k < stage A Mdec Redf n := hub k
  set m := Nat.find hex with hm
  have hmspec : k < stage A Mdec Redf m := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, stage_zero] at hmspec
    omega
  obtain ⟨p, hp⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  have hple : ¬ (k < stage A Mdec Redf p) := Nat.find_min hex (by omega)
  have hstep : stage A Mdec Redf (p + 1) ≤ stage A Mdec Redf p + 1 := stage_succ_le p
  rw [hp] at hmspec
  have hpk : stage A Mdec Redf p = k := by omega
  refine ⟨p, hpk, ?_⟩
  by_contra hw
  rw [stage_succ_of_not_wit hw] at hmspec
  omega

end StageBasics

/-- An abstract axiomatisation of the ingredients of complexity theory that Ladner's theorem
needs.  All the fields are standard, model independent facts about `P`, `NP` and polynomial time
many-one reductions, except for `holeEff`, which packages the (machine model dependent)
statement that the clocked delayed diagonalisation used in Ladner's proof runs in polynomial
time. -/
structure Setting where
  /-- The class of languages decidable in polynomial time. -/
  P : Set Lang
  /-- The class of languages accepted in nondeterministic polynomial time. -/
  NP : Set Lang
  /-- The polynomial time computable functions on strings. -/
  PolyFun : Set (Str → Str)
  /-- `P ⊆ NP`. -/
  P_subset_NP : P ⊆ NP
  /-- An enumeration of polynomial time deciders. -/
  Mdec : ℕ → Lang
  /-- Every enumerated decider decides a language in `P`. -/
  Mdec_mem : ∀ i, Mdec i ∈ P
  /-- Every language in `P` occurs in the enumeration. -/
  Mdec_surj : ∀ L ∈ P, ∃ i, L = Mdec i
  /-- An enumeration of the polynomial time computable functions. -/
  Redf : ℕ → Str → Str
  /-- Every enumerated function is polynomial time computable. -/
  Redf_mem : ∀ i, Redf i ∈ PolyFun
  /-- Every polynomial time computable function occurs in the enumeration. -/
  Redf_surj : ∀ r ∈ PolyFun, ∃ i, r = Redf i
  /-- `P` is closed under finite variations. -/
  P_variant : ∀ L ∈ P, ∀ (M : Lang) (N : ℕ), (∀ x : Str, N ≤ x.length → M x = L x) → M ∈ P
  /-- The empty language is in `P`. -/
  P_empty : (fun _ => false : Lang) ∈ P
  /-- `P` is closed downwards under polynomial time many-one reductions. -/
  P_red : ∀ (A B : Lang), (∃ r ∈ PolyFun, ∀ x, A x = B (r x)) → B ∈ P → A ∈ P
  /-- `NP` is closed under intersection with a language in `P`. -/
  NP_inter_P : ∀ A ∈ NP, ∀ h ∈ P, (fun x => A x && h x : Lang) ∈ NP
  /-- Effectivity of the delayed diagonalisation: for a language in `NP`, the set of lengths at
  which Ladner's stage function is even is polynomial time decidable. -/
  holeEff : ∀ A ∈ NP,
    (fun x : Str => decide (stage A Mdec Redf x.length % 2 = 0) : Lang) ∈ P

namespace Setting

variable (s : Setting)

/-- Polynomial time many-one (Karp) reducibility. -/
def Reduces (A B : Lang) : Prop := ∃ r ∈ s.PolyFun, ∀ x, A x = B (r x)

/-- `L` is `NP`-complete. -/
def NPComplete (L : Lang) : Prop := L ∈ s.NP ∧ ∀ K ∈ s.NP, s.Reduces K L

/-- `L` is `NP`-intermediate: in `NP`, not in `P`, and not `NP`-complete. -/
def NPIntermediate (L : Lang) : Prop := L ∈ s.NP ∧ L ∉ s.P ∧ ¬ s.NPComplete L

end Setting

section Ladner

variable (s : Setting) {A : Lang}

/-- The language produced by Ladner's construction. -/
noncomputable def ladnerLang (s : Setting) (A : Lang) : Lang :=
  holed A (stage A s.Mdec s.Redf)

variable (hA : A ∈ s.NP) (hAP : A ∉ s.P)

include hA in
lemma ladnerLang_mem_NP : ladnerLang s A ∈ s.NP :=
  s.NP_inter_P A hA _ (s.holeEff A hA)

include hAP in
/-- The stage function of the construction is unbounded: otherwise it would be eventually
constant, and the corresponding requirement would show that `A` is in `P`. -/
lemma stage_unbounded : ∀ N, ∃ n, N < stage A s.Mdec s.Redf n := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨B, hB⟩ := hcon
  set st := stage A s.Mdec s.Redf with hstdef
  have hbdd : BddAbove (Set.range st) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  have hne : (Set.range st).Nonempty := ⟨st 0, ⟨0, rfl⟩⟩
  obtain ⟨N, hN⟩ : ∃ N, st N = sSup (Set.range st) := Nat.sSup_mem hne hbdd
  set k := sSup (Set.range st) with hk
  have hle : ∀ n, st n ≤ k := fun n => le_csSup hbdd ⟨n, rfl⟩
  have heq : ∀ n, N ≤ n → st n = k := fun n hn =>
    le_antisymm (hle n) (hN ▸ stage_mono hn)
  have hnw : ∀ n, N ≤ n → ¬ wit A s.Mdec s.Redf st n := by
    intro n hn
    refine not_wit_of_stage_eq ?_
    rw [← hstdef, heq (n + 1) (by omega), heq n hn]
  by_cases hpar : k % 2 = 0
  · have hdec : ∀ x : Str, s.Mdec (k / 2) x = holed A st x := by
      intro x
      obtain ⟨n, hn, hx, -⟩ := exists_log_ge N x.length 0
      have hw := hnw n hn
      unfold wit at hw
      rw [heq n hn, if_pos hpar] at hw
      push_neg at hw
      exact hw x hx
    have hLP : ladnerLang s A ∈ s.P := by
      have hfun : s.Mdec (k / 2) = ladnerLang s A := funext hdec
      rw [← hfun]
      exact s.Mdec_mem _
    refine hAP (s.P_variant _ hLP A N ?_)
    intro x hx
    show A x = (A x && decide (st x.length % 2 = 0))
    rw [heq x.length hx]
    simp [hpar]
  · have hred : ∀ x : Str, A x = holed A st (s.Redf (k / 2) x) := by
      intro x
      obtain ⟨n, hn, hx, hy⟩ := exists_log_ge N x.length (s.Redf (k / 2) x).length
      have hw := hnw n hn
      unfold wit at hw
      rw [heq n hn, if_neg hpar] at hw
      push_neg at hw
      exact hw x hx hy
    have hLP : ladnerLang s A ∈ s.P := by
      refine s.P_variant _ s.P_empty _ N ?_
      intro x hx
      show (A x && decide (st x.length % 2 = 0)) = false
      rw [heq x.length hx]
      simp [hpar]
    exact hAP (s.P_red A (ladnerLang s A) ⟨s.Redf (k / 2), s.Redf_mem _, hred⟩ hLP)

include hAP in
lemma ladnerLang_not_mem_P : ladnerLang s A ∉ s.P := by
  intro hLP
  obtain ⟨i, hi⟩ := s.Mdec_surj _ hLP
  obtain ⟨n, hn, hw⟩ := exists_stage_step (stage_unbounded s hAP) (2 * i)
  unfold wit at hw
  rw [hn, if_pos (by omega : 2 * i % 2 = 0)] at hw
  obtain ⟨x, -, hne⟩ := hw
  refine hne ?_
  rw [show 2 * i / 2 = i by omega, ← hi]
  rfl

include hAP in
lemma not_reduces_ladnerLang : ¬ s.Reduces A (ladnerLang s A) := by
  rintro ⟨r, hrmem, hr⟩
  obtain ⟨i, hi⟩ := s.Redf_surj r hrmem
  obtain ⟨n, hn, hw⟩ := exists_stage_step (stage_unbounded s hAP) (2 * i + 1)
  unfold wit at hw
  rw [hn, if_neg (by omega : ¬ ((2 * i + 1) % 2 = 0))] at hw
  obtain ⟨x, -, -, hne⟩ := hw
  refine hne ?_
  rw [show (2 * i + 1) / 2 = i by omega, ← hi]
  exact hr x

end Ladner

/-- **Ladner's theorem**: if `P ≠ NP`, then there is an `NP`-intermediate language, i.e. a
language which lies in `NP`, is not in `P`, and is not `NP`-complete. -/
theorem ladner (s : Setting) (h : s.P ≠ s.NP) : ∃ L : Lang, s.NPIntermediate L := by
  have hex : ∃ A : Lang, A ∈ s.NP ∧ A ∉ s.P := by
    by_contra hcon
    push_neg at hcon
    exact h (Set.Subset.antisymm s.P_subset_NP (fun A hA => hcon A hA))
  obtain ⟨A, hA, hAP⟩ := hex
  refine ⟨ladnerLang s A, ladnerLang_mem_NP s hA, ladnerLang_not_mem_P s hAP, ?_⟩
  rintro ⟨-, hcomp⟩
  exact not_reduces_ladnerLang s hAP (hcomp A hA)

end CS

