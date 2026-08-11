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

import RequestProject.BGS.PartA
import RequestProject.BGS.PartB

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Statement: There are oracles A,B with P^A=NP^A and P^B≠NP^B (relativization barrier).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header block above is placed after the `import` lines because Lean 4 requires
`import` commands to come first in a file.)

The model of relativized computation is developed in `RequestProject.BGS.Model`:

* an *oracle* is a set of binary strings, `Oracle := Str → Bool`;
* an *oracle machine* `OM` is a pair of computable functions `ask`, `out`: `ask z l`
  returns the next query on input `z` (a pair of an input and a certificate) given the
  list `l` of oracle answers received so far, and `out z l` returns the verdict;
* `Bounded M k` says that all queries of `M` have length at most `(|x|+2)^k`, where `x`
  is the proper input, and a machine is run for `(|x|+2)^k` steps;
* `Po A L` (`L ∈ P^A`) and `NPo A L` (`L ∈ NP^A`) are the usual definitions, and
  `PClass A`, `NPClass A` are the corresponding classes of languages.

`RequestProject.BGS.PartA` builds an oracle `A` (by recursion on the length of strings)
which encodes acceptance of the `NP^A` computations, so that `P^A = NP^A`.

`RequestProject.BGS.PartB` builds an oracle `B` by diagonalization, so that the unary
language `LB = {1^n : B contains a string of length n}` lies in `NP^B` but not in `P^B`.
-/

namespace CS

/-- **Baker–Gill–Solovay theorem** (the relativization barrier): there is an oracle `A`
with `P^A = NP^A` and an oracle `B` with `P^B ≠ NP^B`. -/
theorem baker_gill_solovay :
    (∃ A : Oracle, PClass A = NPClass A) ∧ (∃ B : Oracle, PClass B ≠ NPClass B) :=
  ⟨⟨oracleA, PClass_oracleA_eq⟩, ⟨oracleB, PClass_oracleB_ne⟩⟩

end CS

/-
# An oracle `A` with `P^A = NP^A`

The oracle `A` is built by recursion on the length of strings: a string of the form
`pad i k x` (a padded encoding of the machine index `i`, the polynomial degree `k` and
the input `x`) belongs to `A` exactly when the `i`-th machine, run as an `NP` machine
with bound `k`, accepts `x`.  The padding guarantees that `|pad i k x|` exceeds the time
bound `(|x|+2)^k`, so the queries made during that computation concern strictly shorter
strings and the recursion is well founded.

Consequently a deterministic machine can decide any language of `NP^A` with a single
query to `A`.
-/
import RequestProject.BGS.Aux

namespace CS

/-! ## The padded encoding -/

/-- The padded encoding of a machine index `i`, a degree `k` and an input `x`. -/
def pad (i k : ℕ) (x : Str) : Str :=
  List.replicate (tb k x + 1) true ++ false :: (List.replicate (Nat.pair i k) true ++ false :: x)

theorem split_eq : ∀ {m m' : ℕ} {r r' : Str},
    List.replicate m true ++ false :: r = List.replicate m' true ++ false :: r' →
      m = m' ∧ r = r' := by
  intro m
  induction m with
  | zero =>
      intro m' r r' h
      cases m' with
      | zero => simpa using h
      | succ j => simp [List.replicate_succ] at h
  | succ i ih =>
      intro m' r r' h
      cases m' with
      | zero => simp [List.replicate_succ] at h
      | succ j =>
          simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨hm, hr⟩ := ih h
          exact ⟨by omega, hr⟩

theorem pad_inj {i k i' k' : ℕ} {x x' : Str} (h : pad i k x = pad i' k' x') :
    i = i' ∧ k = k' ∧ x = x' := by
  unfold pad at h
  obtain ⟨-, h2⟩ := split_eq h
  obtain ⟨hp, hx⟩ := split_eq h2
  have hu := congrArg Nat.unpair hp
  rw [Nat.unpair_pair, Nat.unpair_pair] at hu
  exact ⟨(Prod.mk.injEq _ _ _ _ ▸ hu).1, (Prod.mk.injEq _ _ _ _ ▸ hu).2, hx⟩

theorem pad_length (i k : ℕ) (x : Str) :
    (pad i k x).length = tb k x + Nat.pair i k + x.length + 3 := by
  simp [pad]
  omega

theorem tb_lt_pad_length (i k : ℕ) (x : Str) : tb k x < (pad i k x).length := by
  rw [pad_length]; omega

/-! ## The oracle -/

open scoped Classical in
/-- `Alen n` is the oracle `A` restricted to strings of length `< n` (and `false`
elsewhere). -/
noncomputable def Alen : ℕ → Oracle
  | 0 => fun _ => false
  | (n + 1) => fun q =>
      if q.length = n then
        decide (∃ (i k : ℕ) (x : Str), pad i k x = q ∧ ∃ y : Str, y.length ≤ tb k x ∧
          runB (mach i) (Alen n) (x, y) (tb k x) = true)
      else if q.length < n then Alen n q else false

/-- The oracle `A` of the first half of the Baker–Gill–Solovay theorem. -/
noncomputable def oracleA : Oracle := fun q => Alen (q.length + 1) q

theorem Alen_of_lt {n : ℕ} {q : Str} (h : q.length < n) : Alen (n + 1) q = Alen n q := by
  rw [Alen]
  simp only
  rw [if_neg (by omega : ¬ q.length = n), if_pos h]

theorem Alen_eq_oracleA : ∀ (n : ℕ) (q : Str), q.length < n → Alen n q = oracleA q := by
  intro n
  induction n with
  | zero => intro q h; omega
  | succ n ih =>
      intro q h
      rcases Nat.lt_or_ge q.length n with hlt | hge
      · rw [Alen_of_lt hlt]; exact ih q hlt
      · have : q.length = n := by omega
        rw [oracleA, this]

theorem oracleA_spec (i k : ℕ) (x : Str) (hb : Bounded (mach i) k) :
    oracleA (pad i k x) = true ↔
      ∃ y : Str, y.length ≤ tb k x ∧ runB (mach i) oracleA (x, y) (tb k x) = true := by
  classical
  set q := pad i k x with hq
  set n := q.length with hn
  have hlt : tb k x < n := hn ▸ tb_lt_pad_length i k x
  have hagree : ∀ q' : Str, q'.length < n → oracleA q' = Alen n q' := by
    intro q' h'
    exact (Alen_eq_oracleA n q' h').symm
  have hrun : ∀ y : Str, runB (mach i) oracleA (x, y) (tb k x)
      = runB (mach i) (Alen n) (x, y) (tb k x) :=
    fun y => runB_congr_len (mach i) k hb (Alen n) oracleA (x, y) n hlt hagree _
  have hdef : oracleA q =
      decide (∃ (i' k' : ℕ) (x' : Str), pad i' k' x' = q ∧ ∃ y : Str, y.length ≤ tb k' x' ∧
        runB (mach i') (Alen n) (x', y) (tb k' x') = true) := by
    have h0 : oracleA q = Alen (n + 1) q := rfl
    rw [h0, Alen]
    simp only
    rw [if_pos rfl]
  rw [hdef, decide_eq_true_iff]
  constructor
  · rintro ⟨i', k', x', hpad, y, hy, hacc⟩
    obtain ⟨rfl, rfl, rfl⟩ := pad_inj (hq ▸ hpad.symm : pad i k x = pad i' k' x')
    exact ⟨y, hy, by rw [hrun]; exact hacc⟩
  · rintro ⟨y, hy, hacc⟩
    exact ⟨i, k, x, hq.symm, y, hy, by rw [← hrun]; exact hacc⟩

/-! ## The deterministic machine that queries `A` -/

theorem primrec_pad (i k : ℕ) : Primrec (fun x : Str => pad i k x) := by
  have hlen : Primrec (fun x : Str => tb k x + 1) := by
    have h1 : Primrec (fun x : Str => x.length + 2) :=
      Primrec.succ.comp (Primrec.succ.comp Primrec.list_length)
    have h2 : Primrec (fun x : Str => (x.length + 2) ^ k) := (primrec_pow_const k).comp h1
    exact Primrec.succ.comp h2
  have hA : Primrec (fun x : Str => List.replicate (tb k x + 1) true) :=
    primrec_replicate_true.comp hlen
  have hB : Primrec (fun x : Str => false :: (List.replicate (Nat.pair i k) true ++ false :: x)) :=
    Primrec.list_cons.comp (Primrec.const false)
      (Primrec.list_append.comp (Primrec.const _)
        (Primrec.list_cons.comp (Primrec.const false) Primrec.id))
  exact Primrec.list_append.comp hA hB

/-- The deterministic machine that, on input `x`, queries `A` at `pad i k x` and returns
the answer. -/
noncomputable def padMachine (i k : ℕ) : OM where
  ask := fun z _ => pad i k z.1
  out := fun _ l => l.headI
  ask_computable := by
    have h2 : Computable (fun p : (Str × Str) × List Bool => pad i k p.1.1) :=
      (primrec_pad i k).to_comp.comp (Computable.fst.comp Computable.fst)
    exact h2
  out_computable := by
    have h2 : Computable (fun p : (Str × Str) × List Bool => p.2.headI) :=
      Primrec.list_headI.to_comp.comp Computable.snd
    exact h2

theorem pad_len_bound (i k : ℕ) : ∃ k', ∀ x : Str, (pad i k x).length ≤ tb k' x := by
  obtain ⟨k', hk'⟩ := tbn_dom k (Nat.pair i k)
  refine ⟨k', fun x => ?_⟩
  rw [pad_length]
  exact hk' x.length

theorem runB_padMachine (i k : ℕ) (O : Oracle) (x y : Str) (T : ℕ) (hT : 1 ≤ T) :
    runB (padMachine i k) O (x, y) T = O (pad i k x) := by
  unfold runB
  exact ans_headI (padMachine i k) O (x, y) T hT

/-! ## `NP^A ⊆ P^A` -/

theorem NPo_oracleA_imp_Po (L : Language) (h : NPo oracleA L) : Po oracleA L := by
  obtain ⟨M, k, hb, hL⟩ := h
  obtain ⟨i, rfl⟩ := mach_surjective M
  obtain ⟨k', hk'⟩ := pad_len_bound i k
  refine ⟨padMachine i k, k', fun z l => hk' z.1, fun x => ?_⟩
  have h1 : runB (padMachine i k) oracleA (x, []) (tb k' x) = oracleA (pad i k x) :=
    runB_padMachine i k oracleA x [] (tb k' x) (tb_pos k' x)
  rw [h1, oracleA_spec i k x hb]
  exact hL x

/-- **First half of Baker–Gill–Solovay**: there is an oracle `A` with `P^A = NP^A`. -/
theorem PClass_oracleA_eq : PClass oracleA = NPClass oracleA := by
  ext L
  constructor
  · intro h; exact Po_imp_NPo oracleA L h
  · intro h; exact NPo_oracleA_imp_Po L h

end CS

/-
# Auxiliary lemmas

Elementary arithmetic and computability facts used in the construction of the two
oracles.
-/
import RequestProject.BGS.Model

namespace CS

open Filter

/-- The all-ones string of length `n`. -/
def ones (n : ℕ) : Str := List.replicate n true

@[simp] theorem ones_length (n : ℕ) : (ones n).length = n := by simp [ones]

/-! ## Computability helpers -/

theorem primrec_pow_const (k : ℕ) : Primrec (fun n : ℕ => n ^ k) := by
  induction k with
  | zero => simpa using (Primrec.const 1)
  | succ k ih => simpa [pow_succ] using Primrec.nat_mul.comp ih Primrec.id

theorem primrec_replicate_true : Primrec (fun n : ℕ => List.replicate n true) := by
  have h : Primrec (fun n : ℕ => (List.range n).map (fun _ => true)) :=
    Primrec.list_map Primrec.list_range (Primrec.const true).to₂
  refine h.of_eq (fun n => ?_)
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, List.replicate_succ']

/-! ## Arithmetic -/

theorem tbn_pos (k n : ℕ) : 0 < tbn k n := Nat.one_le_pow _ _ (by omega)

theorem tb_pos (k : ℕ) (x : Str) : 0 < tb k x := tbn_pos _ _

theorem tbn_mono (k : ℕ) {m n : ℕ} (h : m ≤ n) : tbn k m ≤ tbn k n :=
  Nat.pow_le_pow_left (by omega) _

/-- A polynomial `(n+2)^k` plus a linear term is dominated by a bigger polynomial. -/
theorem tbn_dom (k c : ℕ) : ∃ k', ∀ n : ℕ, tbn k n + c + n + 3 ≤ tbn k' n := by
  refine ⟨k + 1 + (c + 5), fun n => ?_⟩
  simp only [tbn]
  set a := (n + 2) ^ k with ha
  set D := (n + 2) * (c + 5) with hD
  have h1 : (c + 5) < 2 ^ (c + 5) := Nat.lt_two_pow_self
  have h2 : (2 : ℕ) ^ (c + 5) ≤ (n + 2) ^ (c + 5) := Nat.pow_le_pow_left (by omega) _
  have hB : D + 1 ≤ (n + 2) * (n + 2) ^ (c + 5) := by
    have h : (n + 2) * (c + 5) < (n + 2) * (n + 2) ^ (c + 5) := by
      have h' : c + 5 < (n + 2) ^ (c + 5) := lt_of_lt_of_le h1 h2
      gcongr
    omega
  have h3 : (n + 2) ^ (k + 1 + (c + 5)) = a * ((n + 2) * (n + 2) ^ (c + 5)) := by
    rw [ha, ← pow_succ', ← pow_add]; ring_nf
  have h4 : 1 ≤ a := Nat.one_le_pow _ _ (by omega)
  have h7 : c + n + 4 ≤ D := by rw [hD]; nlinarith
  rw [h3]
  calc a + c + n + 3 ≤ a + D := by omega
    _ ≤ a * D + a := by nlinarith
    _ = a * (D + 1) := by ring
    _ ≤ a * ((n + 2) * (n + 2) ^ (c + 5)) := Nat.mul_le_mul_left _ hB

/-- Polynomials are eventually dominated by `2^n`; there are arbitrarily large `n`
with `(n+2)^k < 2^n`. -/
theorem exists_big (k m : ℕ) : ∃ n, m < n ∧ tbn k n < 2 ^ n := by
  have h := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k (one_lt_two)
  have hc : (0 : ℝ) < ((2 : ℝ) * 3 ^ k)⁻¹ := by positivity
  have h2 := h.def hc
  rw [Filter.eventually_atTop] at h2
  obtain ⟨N, hN⟩ := h2
  refine ⟨max (max N m.succ) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le (Nat.lt_succ_self m) (le_trans (le_max_right N m.succ) (le_max_left _ _))
  · simp only [tbn]
    set n := max (max N m.succ) 1 with hn
    have hn1 : 1 ≤ n := le_max_right _ _
    have hnN : N ≤ n := le_trans (le_max_left N m.succ) (le_max_left _ _)
    have key := hN n hnN
    simp only [norm_pow, Real.norm_natCast, Real.norm_ofNat] at key
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have h3 : ((n : ℝ) + 2) ^ k ≤ 3 ^ k * (n : ℝ) ^ k := by
      rw [← mul_pow]
      gcongr
      linarith
    have h4 : (3 : ℝ) ^ k * (n : ℝ) ^ k ≤ 3 ^ k * (((2 : ℝ) * 3 ^ k)⁻¹ * 2 ^ n) := by
      have h0 : (0 : ℝ) < 3 ^ k := by positivity
      exact mul_le_mul_of_nonneg_left key (le_of_lt h0)
    have h5 : (3 : ℝ) ^ k * (((2 : ℝ) * 3 ^ k)⁻¹ * 2 ^ n) = 2 ^ n / 2 := by field_simp
    have h6 : ((n : ℝ) + 2) ^ k < 2 ^ n := by
      have hpos : (0 : ℝ) < 2 ^ n := by positivity
      calc ((n : ℝ) + 2) ^ k ≤ 3 ^ k * (n : ℝ) ^ k := h3
        _ ≤ 2 ^ n / 2 := by rw [← h5]; exact h4
        _ < 2 ^ n := by linarith
    have hcast : (((n + 2) ^ k : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by push_cast; exact h6
    exact_mod_cast hcast

end CS

/-
# A relativized model of computation

This file sets up the model of oracle computation used in the formalization of the
Baker–Gill–Solovay theorem.

An *oracle machine* is a pair of computable functions: `ask` produces the next query
from the input and the list of oracle answers received so far, and `out` produces the
final verdict from the input and the list of answers.  A machine is run for a number of
steps given by a polynomial bound in the length of the input, and its queries are
required to be of length at most that same bound.

The resources that are polynomially bounded are therefore the number of oracle queries
and the length of each query, while the transitions between queries are required to be
computable.  Since there are only countably many machines, the diagonalization argument
for the second oracle goes through, and the class `P^A` contains, for instance, every
computable language (via a machine that ignores its oracle).
-/
import Mathlib

namespace CS

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle is a set of strings, presented as its characteristic function. -/
abbrev Oracle := Str → Bool

/-- A language is a set of strings. -/
abbrev Language := Set Str

/-- An oracle machine: `ask z l` is the next query on input `z` after receiving the
answers `l`, and `out z l` is the verdict. The input `z` is a pair (proper input,
certificate); machines used for deterministic computation simply ignore the second
component. Both functions are required to be computable, so that there are only
countably many machines. -/
structure OM where
  ask : Str × Str → List Bool → Str
  out : Str × Str → List Bool → Bool
  ask_computable : Computable₂ ask
  out_computable : Computable₂ out

/-- The list of the first `n` oracle answers in the run of `M` with oracle `O` on `z`. -/
def ans (M : OM) (O : Oracle) (z : Str × Str) : ℕ → List Bool
  | 0 => []
  | n + 1 => ans M O z n ++ [O (M.ask z (ans M O z n))]

/-- The verdict of `M` with oracle `O` on input `z` after `T` queries. -/
def runB (M : OM) (O : Oracle) (z : Str × Str) (T : ℕ) : Bool := M.out z (ans M O z T)

/-- The polynomial time bound `(n+2)^k`, as a function of the length of the input. -/
def tbn (k n : ℕ) : ℕ := (n + 2) ^ k

/-- The polynomial time bound `(|x|+2)^k`. -/
def tb (k : ℕ) (x : Str) : ℕ := tbn k x.length

/-- All queries of `M` are of length at most the time bound. -/
def Bounded (M : OM) (k : ℕ) : Prop := ∀ z l, (M.ask z l).length ≤ tb k z.1

/-- `L ∈ P^A`. -/
def Po (A : Oracle) (L : Language) : Prop :=
  ∃ (M : OM) (k : ℕ), Bounded M k ∧ ∀ x, (x ∈ L ↔ runB M A (x, []) (tb k x) = true)

/-- `L ∈ NP^A`. -/
def NPo (A : Oracle) (L : Language) : Prop :=
  ∃ (M : OM) (k : ℕ), Bounded M k ∧
    ∀ x, (x ∈ L ↔ ∃ y : Str, y.length ≤ tb k x ∧ runB M A (x, y) (tb k x) = true)

/-- The class `P^A`. -/
def PClass (A : Oracle) : Set Language := {L | Po A L}

/-- The class `NP^A`. -/
def NPClass (A : Oracle) : Set Language := {L | NPo A L}

/-! ## Basic properties of runs -/

theorem ans_zero (M : OM) (O : Oracle) (z : Str × Str) : ans M O z 0 = [] := rfl

theorem ans_succ (M : OM) (O : Oracle) (z : Str × Str) (n : ℕ) :
    ans M O z (n + 1) = ans M O z n ++ [O (M.ask z (ans M O z n))] := rfl

theorem ans_length (M : OM) (O : Oracle) (z : Str × Str) (n : ℕ) :
    (ans M O z n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ans_succ, ih]

/-- If two oracles give the same answer to each query actually made in the run under
`O₁`, then the runs coincide. -/
theorem ans_congr (M : OM) (O₁ O₂ : Oracle) (z : Str × Str) (T : ℕ)
    (h : ∀ m < T, O₂ (M.ask z (ans M O₁ z m)) = O₁ (M.ask z (ans M O₁ z m))) :
    ans M O₂ z T = ans M O₁ z T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      have ih' := ih (fun m hm => h m (Nat.lt_succ_of_lt hm))
      rw [ans_succ, ans_succ, ih', h T (Nat.lt_succ_self T)]

theorem runB_congr (M : OM) (O₁ O₂ : Oracle) (z : Str × Str) (T : ℕ)
    (h : ∀ m < T, O₂ (M.ask z (ans M O₁ z m)) = O₁ (M.ask z (ans M O₁ z m))) :
    runB M O₂ z T = runB M O₁ z T := by
  unfold runB; rw [ans_congr M O₁ O₂ z T h]

/-- Locality with respect to length: if two oracles agree on all strings of length `< n`
and the machine's queries are shorter than `n`, the runs coincide. -/
theorem runB_congr_len (M : OM) (k : ℕ) (hM : Bounded M k) (O₁ O₂ : Oracle) (z : Str × Str)
    (n : ℕ) (hn : tb k z.1 < n) (h : ∀ q : Str, q.length < n → O₂ q = O₁ q) (T : ℕ) :
    runB M O₂ z T = runB M O₁ z T := by
  refine runB_congr M O₁ O₂ z T (fun m _ => ?_)
  exact h _ (lt_of_le_of_lt (hM z (ans M O₁ z m)) hn)

/-- The first answer received in a run of at least one step. -/
theorem ans_headI (M : OM) (O : Oracle) (z : Str × Str) :
    ∀ T, 1 ≤ T → (ans M O z T).headI = O (M.ask z []) := by
  intro T
  induction T with
  | zero => intro h; exact absurd h (by omega)
  | succ T ih =>
      intro _
      rcases Nat.eq_zero_or_pos T with hT | hT
      · subst hT; rfl
      · have hlen : (ans M O z T).length = T := ans_length M O z T
        obtain ⟨a, t, ht⟩ : ∃ a t, ans M O z T = a :: t := by
          cases hc : ans M O z T with
          | nil => rw [hc] at hlen; simp at hlen; omega
          | cons a t => exact ⟨a, t, rfl⟩
        have hih := ih hT
        rw [ht] at hih
        rw [ans_succ, ht]
        simpa using hih

/-- The machine `M` made to ignore the certificate part of its input. -/
def ignoreCert (M : OM) : OM where
  ask := fun z l => M.ask (z.1, []) l
  out := fun z l => M.out (z.1, []) l
  ask_computable :=
    Computable₂.comp M.ask_computable
      (Computable.pair (Computable.fst.comp Computable.fst) (Computable.const []))
      Computable.snd
  out_computable :=
    Computable₂.comp M.out_computable
      (Computable.pair (Computable.fst.comp Computable.fst) (Computable.const []))
      Computable.snd

theorem ans_ignoreCert (M : OM) (O : Oracle) (x y : Str) (n : ℕ) :
    ans (ignoreCert M) O (x, y) n = ans M O (x, []) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ans_succ, ans_succ, ih]; rfl

theorem runB_ignoreCert (M : OM) (O : Oracle) (x y : Str) (T : ℕ) :
    runB (ignoreCert M) O (x, y) T = runB M O (x, []) T := by
  unfold runB; rw [ans_ignoreCert]; rfl

theorem Bounded_ignoreCert {M : OM} {k : ℕ} (h : Bounded M k) : Bounded (ignoreCert M) k := by
  intro z l; exact h (z.1, []) l

/-- `P^A ⊆ NP^A`. -/
theorem Po_imp_NPo (A : Oracle) (L : Language) (h : Po A L) : NPo A L := by
  obtain ⟨M, k, hb, hL⟩ := h
  refine ⟨ignoreCert M, k, Bounded_ignoreCert hb, fun x => ?_⟩
  constructor
  · intro hx
    exact ⟨[], by simp, by rw [runB_ignoreCert]; exact (hL x).1 hx⟩
  · rintro ⟨y, _, hy⟩
    rw [runB_ignoreCert] at hy
    exact (hL x).2 hy

/-! ## There are only countably many machines -/

/-- The `ℕ`-level partial function attached to a computable function. -/
noncomputable def natFun {α σ} [Primcodable α] [Primcodable σ] (f : α → σ) : ℕ →. ℕ :=
  fun n => (Part.ofOption (Encodable.decode (α := α) n)).bind
    fun a => Part.some (Encodable.encode (f a))

theorem natFun_partrec {α σ} [Primcodable α] [Primcodable σ] (f : α → σ) (hf : Computable f) :
    Nat.Partrec (natFun f) := by
  have h : Nat.Partrec fun n => (Part.ofOption (Encodable.decode (α := α) n)).bind
      fun a => Part.map Encodable.encode ((f a : Part σ)) := hf
  refine h.of_eq ?_
  intro n
  simp [natFun]

theorem natFun_inj {α σ} [Primcodable α] [Primcodable σ] {f g : α → σ}
    (h : natFun f = natFun g) : f = g := by
  funext a
  have := congrFun h (Encodable.encode a)
  simpa [natFun, Encodable.encodek] using this

instance countable_computable {α σ} [Primcodable α] [Primcodable σ] :
    Countable {f : α → σ // Computable f} := by
  classical
  refine Function.Injective.countable
    (f := fun f : {f : α → σ // Computable f} =>
      (Nat.Partrec.Code.exists_code.mp (natFun_partrec f.1 f.2)).choose) ?_
  intro f g hfg
  have e1 := (Nat.Partrec.Code.exists_code.mp (natFun_partrec f.1 f.2)).choose_spec
  have e2 := (Nat.Partrec.Code.exists_code.mp (natFun_partrec g.1 g.2)).choose_spec
  simp only at hfg
  rw [hfg] at e1
  exact Subtype.ext (natFun_inj (e1.symm.trans e2))

instance : Countable OM := by
  refine Function.Injective.countable
    (f := fun M : OM =>
      ((⟨fun p => M.ask p.1 p.2, M.ask_computable⟩ :
          {f : (Str × Str) × List Bool → Str // Computable f}),
       (⟨fun p => M.out p.1 p.2, M.out_computable⟩ :
          {f : (Str × Str) × List Bool → Bool // Computable f}))) ?_
  rintro ⟨a₁, o₁, ha₁, ho₁⟩ ⟨a₂, o₂, ha₂, ho₂⟩ h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have ha : a₁ = a₂ := by funext z l; exact congrFun h1 (z, l)
  have ho : o₁ = o₂ := by funext z l; exact congrFun h2 (z, l)
  subst ha; subst ho; rfl

/-- A trivial machine, used to witness nonemptiness of `OM`. -/
def trivialOM : OM where
  ask := fun _ _ => []
  out := fun _ _ => false
  ask_computable := Computable.const []
  out_computable := Computable.const false

instance : Nonempty OM := ⟨trivialOM⟩

/-- An enumeration of all oracle machines. -/
noncomputable def mach : ℕ → OM := (exists_surjective_nat OM).choose

theorem mach_surjective : Function.Surjective mach := (exists_surjective_nat OM).choose_spec

end CS

/-
# An oracle `B` with `P^B ≠ NP^B`

The oracle `B` is built by diagonalization against all pairs (machine, polynomial
degree).  At stage `j` a fresh length `Nst j` is chosen, so large that the time bound of
the `j`-th machine on inputs of that length is smaller than `2 ^ (Nst j)` and larger
lengths are never touched again.  The `j`-th machine is run on `1 ^ (Nst j)` with the
oracle built so far; if it accepts, no string of length `Nst j` is added to `B`; if it
rejects, a string of length `Nst j` that it did not query is added.

The unary language `LB = {1^n : B contains a string of length n}` is then in `NP^B` but
not in `P^B`.
-/
import RequestProject.BGS.Aux

namespace CS

/-! ## Enumeration of pairs (machine, degree) -/

/-- The machine of the `j`-th pair. -/
noncomputable def Mi (j : ℕ) : OM := mach j.unpair.1

/-- The degree of the `j`-th pair. -/
def ki (j : ℕ) : ℕ := j.unpair.2

theorem Mi_pair (i k : ℕ) : Mi (Nat.pair i k) = mach i := by simp [Mi]

theorem ki_pair (i k : ℕ) : ki (Nat.pair i k) = k := by simp [ki]

/-! ## The diagonalization lengths -/

/-- The length used at stage `j`. -/
noncomputable def Nst : ℕ → ℕ
  | 0 => (exists_big (ki 0) 0).choose
  | (j + 1) => (exists_big (ki (j + 1)) (max (Nst j) (tbn (ki j) (Nst j)))).choose

/-- The time bound of the `j`-th machine on inputs of length `Nst j`. -/
noncomputable def Tst (j : ℕ) : ℕ := tbn (ki j) (Nst j)

theorem Tst_lt_two_pow (j : ℕ) : Tst j < 2 ^ (Nst j) := by
  cases j with
  | zero => exact (exists_big (ki 0) 0).choose_spec.2
  | succ j =>
      exact (exists_big (ki (j + 1)) (max (Nst j) (tbn (ki j) (Nst j)))).choose_spec.2

theorem Nst_lt_succ (j : ℕ) : Nst j < Nst (j + 1) := by
  have h := (exists_big (ki (j + 1)) (max (Nst j) (tbn (ki j) (Nst j)))).choose_spec.1
  have : max (Nst j) (tbn (ki j) (Nst j)) < Nst (j + 1) := h
  omega

theorem Tst_lt_Nst_succ (j : ℕ) : Tst j < Nst (j + 1) := by
  have h := (exists_big (ki (j + 1)) (max (Nst j) (tbn (ki j) (Nst j)))).choose_spec.1
  have : max (Nst j) (tbn (ki j) (Nst j)) < Nst (j + 1) := h
  have h2 : Tst j = tbn (ki j) (Nst j) := rfl
  omega

theorem Nst_strictMono : StrictMono Nst := strictMono_nat_of_lt_succ Nst_lt_succ

theorem Nst_mono {j j' : ℕ} (h : j ≤ j') : Nst j ≤ Nst j' := Nst_strictMono.monotone h

theorem Nst_inj {j j' : ℕ} (h : Nst j = Nst j') : j = j' := Nst_strictMono.injective h

/-! ## Counting: there is always an unqueried string -/

/-- The `n`-bit binary representation of `j`. -/
def bstr (n j : ℕ) : Str := (List.range n).map (fun i => j.testBit i)

@[simp] theorem bstr_length (n j : ℕ) : (bstr n j).length = n := by simp [bstr]

theorem bstr_getElem? {n j i : ℕ} (h : i < n) : (bstr n j)[i]? = some (j.testBit i) := by
  simp [bstr, h]

theorem bstr_inj {n j j' : ℕ} (hj : j < 2 ^ n) (hj' : j' < 2 ^ n) (h : bstr n j = bstr n j') :
    j = j' := by
  refine Nat.eq_of_testBit_eq (fun i => ?_)
  rcases Nat.lt_or_ge i n with hi | hi
  · have := congrArg (fun l : Str => l[i]?) h
    simp only [bstr_getElem? (j := j) hi, bstr_getElem? (j := j') hi] at this
    exact Option.some.inj this
  · have h1 : j < 2 ^ i := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by omega) hi)
    have h2 : j' < 2 ^ i := lt_of_lt_of_le hj' (Nat.pow_le_pow_right (by omega) hi)
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

theorem exists_unqueried (M : OM) (O : Oracle) (z : Str × Str) (T n : ℕ) (h : T < 2 ^ n) :
    ∃ w : Str, w.length = n ∧ ∀ m < T, M.ask z (ans M O z m) ≠ w := by
  classical
  by_contra hc
  push_neg at hc
  set S : Finset Str := (Finset.range T).image (fun m => M.ask z (ans M O z m)) with hS
  have hcard : S.card ≤ T := le_trans Finset.card_image_le (by simp)
  set V : Finset Str := (Finset.range (2 ^ n)).image (bstr n) with hV
  have hVcard : V.card = 2 ^ n := by
    rw [hV, Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    exact bstr_inj ha hb hab
  have hsub : V ⊆ S := by
    intro w hw
    rw [hV, Finset.mem_image] at hw
    obtain ⟨a, -, rfl⟩ := hw
    obtain ⟨m, hm, hmw⟩ := hc (bstr n a) (bstr_length n a)
    rw [hS, Finset.mem_image]
    exact ⟨m, Finset.mem_range.mpr hm, hmw⟩
  have := Finset.card_le_card hsub
  omega

open scoped Classical in
/-- A string of length `n` that `M` does not query during the first `T` steps of its run
on `z` with oracle `O`. -/
noncomputable def unqueried (M : OM) (O : Oracle) (z : Str × Str) (T n : ℕ) : Str :=
  if h : ∃ w : Str, w.length = n ∧ ∀ m < T, M.ask z (ans M O z m) ≠ w then h.choose else ones n

theorem unqueried_spec (M : OM) (O : Oracle) (z : Str × Str) (T n : ℕ) (h : T < 2 ^ n) :
    (unqueried M O z T n).length = n ∧
      ∀ m < T, M.ask z (ans M O z m) ≠ unqueried M O z T n := by
  classical
  have hex := exists_unqueried M O z T n h
  rw [unqueried, dif_pos hex]
  exact hex.choose_spec

/-! ## The stages -/

open scoped Classical in
/-- The oracle after `j` stages. -/
noncomputable def Bst : ℕ → Oracle
  | 0 => fun _ => false
  | (j + 1) => fun q =>
      if runB (Mi j) (Bst j) (ones (Nst j), []) (Tst j) = true then Bst j q
      else Bst j q || decide (q = unqueried (Mi j) (Bst j) (ones (Nst j), []) (Tst j) (Nst j))

/-- The verdict of the `j`-th machine at stage `j`. -/
noncomputable def stageRun (j : ℕ) : Bool := runB (Mi j) (Bst j) (ones (Nst j), []) (Tst j)

/-- The string added to the oracle at stage `j` (when the `j`-th machine rejects). -/
noncomputable def wit (j : ℕ) : Str :=
  unqueried (Mi j) (Bst j) (ones (Nst j), []) (Tst j) (Nst j)

theorem Bst_succ (j : ℕ) (q : Str) :
    Bst (j + 1) q =
      if stageRun j = true then Bst j q else (Bst j q || decide (q = wit j)) := rfl

theorem wit_length (j : ℕ) : (wit j).length = Nst j :=
  (unqueried_spec _ _ _ _ _ (Tst_lt_two_pow j)).1

theorem wit_unqueried (j : ℕ) :
    ∀ m < Tst j, (Mi j).ask (ones (Nst j), []) (ans (Mi j) (Bst j) (ones (Nst j), []) m)
      ≠ wit j :=
  (unqueried_spec _ _ _ _ _ (Tst_lt_two_pow j)).2

theorem Bst_zero (q : Str) : Bst 0 q = false := rfl

theorem Bst_mono_succ {j : ℕ} {q : Str} (h : Bst j q = true) : Bst (j + 1) q = true := by
  rw [Bst_succ]
  split
  · exact h
  · rw [h]; rfl

theorem Bst_mono {j j' : ℕ} {q : Str} (hjj : j ≤ j') (h : Bst j q = true) : Bst j' q = true := by
  induction j' with
  | zero =>
      have hj0 : j = 0 := by omega
      exact hj0 ▸ h
  | succ j' ih =>
      rcases Nat.lt_or_ge j (j' + 1) with hlt | hge
      · exact Bst_mono_succ (ih (by omega))
      · have : j = j' + 1 := by omega
        exact this ▸ h

theorem Bst_wit_true {j : ℕ} (h : stageRun j = false) : Bst (j + 1) (wit j) = true := by
  rw [Bst_succ, if_neg (by rw [h]; simp)]
  simp

theorem Bst_true_exists : ∀ (j : ℕ) (q : Str), Bst j q = true →
    ∃ j' < j, q = wit j' ∧ stageRun j' = false := by
  intro j
  induction j with
  | zero => intro q h; rw [Bst_zero] at h; exact absurd h (by simp)
  | succ j ih =>
      intro q h
      rw [Bst_succ] at h
      by_cases hs : stageRun j = true
      · rw [if_pos hs] at h
        obtain ⟨j', hj', hq, hr⟩ := ih q h
        exact ⟨j', by omega, hq, hr⟩
      · rw [if_neg hs] at h
        by_cases hb : Bst j q = true
        · obtain ⟨j', hj', hq, hr⟩ := ih q hb
          exact ⟨j', by omega, hq, hr⟩
        · simp only [Bool.or_eq_true, decide_eq_true_eq] at h
          rcases h with h | h
          · exact absurd h hb
          · exact ⟨j, by omega, h, by simpa using hs⟩

/-! ## The oracle `B` -/

open scoped Classical in
/-- The oracle `B` of the second half of the Baker–Gill–Solovay theorem. -/
noncomputable def oracleB : Oracle := fun q => decide (∃ j, Bst j q = true)

theorem oracleB_true_iff (q : Str) : oracleB q = true ↔ ∃ j, Bst j q = true := by
  classical
  rw [oracleB, decide_eq_true_iff]

theorem oracleB_of_Bst {j : ℕ} {q : Str} (h : Bst j q = true) : oracleB q = true :=
  (oracleB_true_iff q).2 ⟨j, h⟩

theorem oracleB_true_iff' (q : Str) :
    oracleB q = true ↔ ∃ j, q = wit j ∧ stageRun j = false := by
  rw [oracleB_true_iff]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨j', -, hq, hr⟩ := Bst_true_exists j q hj
    exact ⟨j', hq, hr⟩
  · rintro ⟨j, rfl, hr⟩
    exact ⟨j + 1, Bst_wit_true hr⟩

/-- The run of the `j`-th machine at stage `j` is not affected by the later stages. -/
theorem stage_run_eq (j : ℕ) (hb : Bounded (Mi j) (ki j)) :
    runB (Mi j) oracleB (ones (Nst j), []) (Tst j)
      = runB (Mi j) (Bst j) (ones (Nst j), []) (Tst j) := by
  refine runB_congr (Mi j) (Bst j) oracleB _ _ (fun m hm => ?_)
  set qm := (Mi j).ask (ones (Nst j), []) (ans (Mi j) (Bst j) (ones (Nst j), []) m) with hqm
  have hlen : qm.length ≤ Tst j := by
    have := hb (ones (Nst j), []) (ans (Mi j) (Bst j) (ones (Nst j), []) m)
    simpa [Tst, tb] using this
  by_cases hB : Bst j qm = true
  · rw [hB, oracleB_of_Bst hB]
  · have hBf : Bst j qm = false := by simpa using hB
    rw [hBf]
    cases hO : oracleB qm with
    | false => rfl
    | true =>
        exfalso
        obtain ⟨j', hq, hr⟩ := (oracleB_true_iff' qm).1 hO
        rcases lt_trichotomy j' j with hlt | heq | hgt
        · exact hB (Bst_mono (by omega) (hq ▸ Bst_wit_true hr))
        · apply wit_unqueried j m hm
          rw [← hqm, hq, heq]
        · have h1 : qm.length = Nst j' := by rw [hq]; exact wit_length j'
          have h2 : Nst (j + 1) ≤ Nst j' := Nst_mono (by omega)
          have h3 := Tst_lt_Nst_succ j
          omega

/-! ## The diagonal language -/

/-- The unary language `{1^n : B contains a string of length n}`. -/
def LB : Language := {x | x = ones x.length ∧ ∃ w : Str, w.length = x.length ∧ oracleB w = true}

theorem primrec_ones : Primrec ones := primrec_replicate_true

/-- The `NP` verifier for `LB`: it queries the certificate. -/
def verifier : OM where
  ask := fun z _ => if z.2.length ≤ z.1.length then z.2 else []
  out := fun z l => if z.1 = ones z.2.length then l.headI else false
  ask_computable := by
    have hc : PrimrecPred (fun p : (Str × Str) × List Bool => p.1.2.length ≤ p.1.1.length) :=
      PrimrecRel.comp Primrec.nat_le
        (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
    have h : Primrec (fun p : (Str × Str) × List Bool =>
        if p.1.2.length ≤ p.1.1.length then p.1.2 else ([] : Str)) :=
      Primrec.ite hc (Primrec.snd.comp Primrec.fst) (Primrec.const [])
    have h2 : Computable (fun p : (Str × Str) × List Bool =>
        if p.1.2.length ≤ p.1.1.length then p.1.2 else ([] : Str)) := h.to_comp
    exact h2
  out_computable := by
    have hc : PrimrecPred (fun p : (Str × Str) × List Bool => p.1.1 = ones p.1.2.length) :=
      PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.fst)
        (primrec_ones.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)))
    have h : Primrec (fun p : (Str × Str) × List Bool =>
        if p.1.1 = ones p.1.2.length then p.2.headI else false) :=
      Primrec.ite hc (Primrec.list_headI.comp Primrec.snd) (Primrec.const false)
    have h3 : Computable (fun p : (Str × Str) × List Bool =>
        if p.1.1 = ones p.1.2.length then p.2.headI else false) := h.to_comp
    exact h3

theorem runB_verifier (O : Oracle) (x y : Str) (T : ℕ) (hT : 1 ≤ T) :
    runB verifier O (x, y) T =
      (if x = ones y.length then O (if y.length ≤ x.length then y else []) else false) := by
  have h := ans_headI verifier O (x, y) T hT
  have hout : ∀ l : List Bool,
      verifier.out (x, y) l = (if x = ones y.length then l.headI else false) := fun _ => rfl
  show verifier.out (x, y) (ans verifier O (x, y) T) = _
  rw [hout, h]
  rfl

theorem LB_in_NPo : NPo oracleB LB := by
  refine ⟨verifier, 1, ?_, fun x => ?_⟩
  · intro z l
    have : tb 1 z.1 = z.1.length + 2 := by simp [tb, tbn]
    rw [this]
    by_cases h : z.2.length ≤ z.1.length
    · simp only [verifier, h, if_pos]
      omega
    · simp only [verifier, h, if_false]
      simp
  · have hT : 1 ≤ tb 1 x := tb_pos 1 x
    constructor
    · rintro ⟨hx, w, hw, hwB⟩
      refine ⟨w, ?_, ?_⟩
      · rw [hw]; simp [tb, tbn]
      · rw [runB_verifier oracleB x w _ hT, if_pos (by omega : w.length ≤ x.length), hwB]
        rw [if_pos (by rw [hw]; exact hx)]
    · rintro ⟨y, -, hy⟩
      rw [runB_verifier oracleB x y _ hT] at hy
      by_cases hx : x = ones y.length
      · rw [if_pos hx] at hy
        have hlen : y.length = x.length := by rw [hx]; simp
        rw [if_pos (by omega : y.length ≤ x.length)] at hy
        exact ⟨by rw [hx]; simp, y, hlen, hy⟩
      · rw [if_neg hx] at hy
        exact absurd hy (by simp)

theorem LB_not_in_Po : ¬ Po oracleB LB := by
  rintro ⟨M, k, hb, hL⟩
  obtain ⟨i, rfl⟩ := mach_surjective M
  set j := Nat.pair i k with hj
  have hMi : Mi j = mach i := Mi_pair i k
  have hki : ki j = k := ki_pair i k
  have hbj : Bounded (Mi j) (ki j) := by rw [hMi, hki]; exact hb
  set n := Nst j with hn
  have htb : tb k (ones n) = Tst j := by
    simp [tb, Tst, hki, tbn, hn]
  have hrun : runB (mach i) oracleB (ones n, []) (tb k (ones n)) = stageRun j := by
    rw [htb, ← hMi]
    exact stage_run_eq j hbj
  have hiff := hL (ones n)
  rw [hrun] at hiff
  by_cases hs : stageRun j = true
  · have hmem : ones n ∈ LB := hiff.2 hs
    obtain ⟨-, w, hw, hwB⟩ := hmem
    obtain ⟨j', hq, hr⟩ := (oracleB_true_iff' w).1 hwB
    have hlen : Nst j' = n := by rw [← wit_length j', ← hq, hw]; simp
    have : j' = j := Nst_inj (by rw [hlen, hn])
    subst this
    rw [hr] at hs
    exact absurd hs (by simp)
  · have hsf : stageRun j = false := by simpa using hs
    have hmem : ones n ∈ LB := by
      refine ⟨by simp, wit j, ?_, ?_⟩
      · rw [wit_length j]; simp [hn]
      · exact oracleB_of_Bst (Bst_wit_true hsf)
    have := hiff.1 hmem
    rw [hsf] at this
    exact absurd this (by simp)

/-- **Second half of Baker–Gill–Solovay**: there is an oracle `B` with `P^B ≠ NP^B`. -/
theorem PClass_oracleB_ne : PClass oracleB ≠ NPClass oracleB := by
  intro h
  have : LB ∈ PClass oracleB := by rw [h]; exact LB_in_NPo
  exact LB_not_in_Po this

end CS

