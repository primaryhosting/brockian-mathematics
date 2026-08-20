/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## What is proved here

Ladner's theorem: if `P ≠ NP`, then there is an `NP`-intermediate language, i.e.
a language that lies in `NP`, is not in `P`, and is not `NP`-complete.

Since Lean's mathematical library contains no model of resource-bounded
computation, the theorem is formulated over an abstract `CS.Framework`: a
bundle of the standard structural facts about the classes `P`, `NP`, about the
class `FP` of polynomial-time computable functions, and about the effective
enumerations of polynomial-time deciders and transducers.  Every field of
`CS.Framework` is a well-known true statement of complexity theory.

The proof is the usual delayed diagonalisation ("blowing holes in a hard
language"): starting from `L₀ ∈ NP \ P`, the language `holed = L₀ ∩ {x | the
stage at |x| is even}` is built, where the stage function is advanced by one
whenever a counterexample to the current requirement (either "the i-th
polynomial-time decider decides `holed`" or "the i-th polynomial-time function
reduces `L₀` to `holed`") turns up.  All of the mathematical content, namely
that the stage function must be unbounded and that consequently `holed` is
`NP`-intermediate, is proved here.

The single further assumption, `CS.Effectivity`, is the formal counterpart of
the standard informal step "the stage function can be computed in polynomial
time if it is advanced only as fast as a polynomial-time budget allows": it
asserts that the diagonalisation can be run along a slow schedule for which the
resulting set of hole lengths is polynomial-time decidable.  It says nothing
about the diagonalisation behaviour of the stage function, which is what is
proved below.

This file is deliberately independent of `Mathlib` (it uses only the Lean 4 core
prelude), so that the module docstring above can literally be the first thing in
the file.  A companion file `RequestProject/Main.lean` uses `Mathlib` to exhibit
a concrete `CS.Framework`, showing that the axioms bundled in `CS.Framework` are
consistent.
-/

namespace CS

/-- Binary strings. -/
abbrev Str := List Bool

/-- Languages, i.e. sets of binary strings. -/
abbrev Lang := Str → Prop

/--
An abstract complexity-theoretic framework.

The fields record the standard (true) structural facts about the classes `P`,
`NP` and about the class `FP` of polynomial-time computable functions, together
with effective enumerations `dec` of the `P`-languages and `fn` of the
polynomial-time functions.
-/
structure Framework where
  /-- The class of polynomial-time decidable languages. -/
  P : Lang → Prop
  /-- The class of languages decidable in nondeterministic polynomial time. -/
  NP : Lang → Prop
  /-- The class of polynomial-time computable string functions. -/
  FP : (Str → Str) → Prop
  /-- An enumeration of (clocked) polynomial-time deciders. -/
  dec : Nat → Str → Bool
  /-- An enumeration of (clocked) polynomial-time transducers. -/
  fn : Nat → Str → Str
  /-- Every enumerated decider decides a language in `P`. -/
  dec_mem : ∀ i, P (fun x => dec i x = true)
  /-- Every language in `P` is decided by some enumerated decider. -/
  dec_complete : ∀ L, P L → ∃ i, ∀ x, (dec i x = true ↔ L x)
  /-- Every enumerated transducer is a polynomial-time function. -/
  fn_mem : ∀ i, FP (fn i)
  /-- Every polynomial-time function occurs in the enumeration. -/
  fn_complete : ∀ g, FP g → ∃ i, ∀ x, fn i x = g x
  /-- `P ⊆ NP`. -/
  P_subset_NP : ∀ L, P L → NP L
  /-- The empty language is in `P`. -/
  P_empty : P (fun _ => False)
  /-- `NP` is closed under intersection with `P`-languages. -/
  NP_inter_P : ∀ L H, NP L → P H → NP (fun x => L x ∧ H x)
  /-- `P` is closed under changing membership on strings of bounded length. -/
  P_of_agree : ∀ (L M : Lang) (N : Nat), P L → (∀ x : Str, N ≤ x.length → (M x ↔ L x)) → P M
  /-- `P` is closed downwards under polynomial-time many-one reductions. -/
  P_of_reduction :
    ∀ (L M : Lang) (g : Str → Str), FP g → (∀ x, L x ↔ M (g x)) → P M → P L

/-- Polynomial-time many-one reducibility. -/
def Reduces (F : Framework) (L M : Lang) : Prop :=
  ∃ g, F.FP g ∧ ∀ x, L x ↔ M (g x)

/-- `A` is `NP`-hard: every `NP` language reduces to it. -/
def NPHard (F : Framework) (A : Lang) : Prop :=
  ∀ L, F.NP L → Reduces F L A

/-- `A` is `NP`-complete. -/
def NPComplete (F : Framework) (A : Lang) : Prop :=
  F.NP A ∧ NPHard F A

/-- `A` is `NP`-intermediate: in `NP`, not in `P`, and not `NP`-complete. -/
def NPIntermediate (F : Framework) (A : Lang) : Prop :=
  F.NP A ∧ ¬ F.P A ∧ ¬ NPComplete F A

/-!
## The delayed diagonalisation ("blowing holes in a hard language")
-/

/-- Membership in the "holed" language, relative to a stage function `st`:
`x` belongs iff `x ∈ L₀` and the stage at `s (|x|)` is even. -/
def MemA (L₀ : Lang) (s : Nat → Nat) (st : Nat → Nat) (x : Str) : Prop :=
  L₀ x ∧ st (s x.length) % 2 = 0

/-- At an even stage `k = 2i` we look for an input on which the `i`-th
polynomial-time decider errs on the holed language; at an odd stage `k = 2i+1`
we look for an input witnessing that the `i`-th polynomial-time function is not
a reduction of `L₀` to the holed language. -/
def Fails (F : Framework) (L₀ : Lang) (s : Nat → Nat) (st : Nat → Nat) (k : Nat) (x : Str) :
    Prop :=
  if k % 2 = 0 then ¬ ((F.dec (k / 2) x = true) ↔ MemA L₀ s st x)
  else ¬ (L₀ x ↔ MemA L₀ s st (F.fn (k / 2) x))

open Classical in
/-- The stage function of the delayed diagonalisation: the stage increases by one
as soon as a counterexample of small enough length to the current requirement has
shown up. -/
noncomputable def stage (F : Framework) (L₀ : Lang) (s : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let st : Nat → Nat := fun m => if _h : m ≤ n then stage F L₀ s m else 0
    let k := st n
    if ∃ x : Str, x.length ≤ n ∧ (F.fn (k / 2) x).length ≤ n ∧ Fails F L₀ s st k x then
      k + 1
    else k

/-- The diagonal language: `L₀` with holes punched in it. -/
def holed (F : Framework) (L₀ : Lang) (s : Nat → Nat) : Lang :=
  fun x => L₀ x ∧ stage F L₀ s (s x.length) % 2 = 0

/-- A slow, nondecreasing, unbounded schedule bounded by the identity. -/
def SlowSchedule (s : Nat → Nat) : Prop :=
  (∀ m n, m ≤ n → s m ≤ s n) ∧ (∀ m, s m ≤ m) ∧ (∀ N, ∃ m, N ≤ s m)

/--
The one effectivity assumption: for every `NP` language `L₀` the delayed
diagonalisation can be run on a slow enough schedule so that the resulting set
of "hole lengths" is polynomial-time decidable.  This is the formal counterpart
of the standard (informal) observation that the stage function of Ladner's
construction can be computed in polynomial time if it is only advanced as fast
as a polynomial-time budget allows.
-/
def Effectivity (F : Framework) : Prop :=
  ∀ L₀ : Lang, F.NP L₀ → ∃ s : Nat → Nat, SlowSchedule s ∧
    F.P (fun x : Str => stage F L₀ s (s x.length) % 2 = 0)

section Diagonalisation

variable {F : Framework} {L₀ : Lang} {s : Nat → Nat}

theorem Fails_congr (F : Framework) (L₀ : Lang) (s : Nat → Nat) (st₁ st₂ : Nat → Nat)
    (k : Nat) (x : Str) (h₁ : st₁ (s x.length) = st₂ (s x.length))
    (h₂ : st₁ (s (F.fn (k / 2) x).length) = st₂ (s (F.fn (k / 2) x).length)) :
    Fails F L₀ s st₁ k x ↔ Fails F L₀ s st₂ k x := by
  unfold Fails MemA
  by_cases hk : k % 2 = 0 <;> simp [hk, h₁, h₂]

theorem stage_zero (F : Framework) (L₀ : Lang) (s : Nat → Nat) : stage F L₀ s 0 = 0 := by
  rw [stage]

open Classical in
theorem stage_succ (hs : ∀ m, s m ≤ m) (n : Nat) :
    stage F L₀ s (n + 1) =
      (if ∃ x : Str, x.length ≤ n ∧ (F.fn (stage F L₀ s n / 2) x).length ≤ n ∧
          Fails F L₀ s (stage F L₀ s) (stage F L₀ s n) x then
        stage F L₀ s n + 1
      else stage F L₀ s n) := by
  rw [stage]
  have hnn : (if _h : n ≤ n then stage F L₀ s n else 0) = stage F L₀ s n :=
    dif_pos (Nat.le_refl n)
  have hiff : (∃ x : Str, x.length ≤ n ∧ (F.fn (stage F L₀ s n / 2) x).length ≤ n ∧
      Fails F L₀ s (fun m => if _h : m ≤ n then stage F L₀ s m else 0) (stage F L₀ s n) x)
      ↔ (∃ x : Str, x.length ≤ n ∧ (F.fn (stage F L₀ s n / 2) x).length ≤ n ∧
        Fails F L₀ s (stage F L₀ s) (stage F L₀ s n) x) := by
    constructor
    · rintro ⟨x, h1, h2, h3⟩
      exact ⟨x, h1, h2, (Fails_congr F L₀ s _ _ _ x (dif_pos (Nat.le_trans (hs x.length) h1))
        (dif_pos (Nat.le_trans (hs _) h2))).mp h3⟩
    · rintro ⟨x, h1, h2, h3⟩
      exact ⟨x, h1, h2, (Fails_congr F L₀ s _ _ _ x (dif_pos (Nat.le_trans (hs x.length) h1))
        (dif_pos (Nat.le_trans (hs _) h2))).mpr h3⟩
  simp only [hnn, hiff]

theorem stage_le_succ (hs : ∀ m, s m ≤ m) (n : Nat) :
    stage F L₀ s n ≤ stage F L₀ s (n + 1) ∧
      stage F L₀ s (n + 1) ≤ stage F L₀ s n + 1 := by
  rw [stage_succ hs n]
  by_cases h : ∃ x : Str, x.length ≤ n ∧ (F.fn (stage F L₀ s n / 2) x).length ≤ n ∧
      Fails F L₀ s (stage F L₀ s) (stage F L₀ s n) x <;> simp [h]

theorem stage_mono (hs : ∀ m, s m ≤ m) {m n : Nat} (h : m ≤ n) :
    stage F L₀ s m ≤ stage F L₀ s n := by
  induction n with
  | zero => have : m = 0 := Nat.le_zero.mp h; subst this; exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp h')) (stage_le_succ hs n).1
    · have : m = n + 1 := Nat.le_antisymm h h'
      subst this; exact Nat.le_refl _

/-- If the stage function is eventually constant, no requirement is ever violated. -/
theorem no_fail_of_eventually_const (hs : ∀ m, s m ≤ m) {N k : Nat}
    (hconst : ∀ n, N ≤ n → stage F L₀ s n = k) (x : Str) :
    ¬ Fails F L₀ s (stage F L₀ s) k x := by
  intro hfail
  have hx : x.length ≤ max N (max x.length (F.fn (k / 2) x).length) :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hy : (F.fn (k / 2) x).length ≤ max N (max x.length (F.fn (k / 2) x).length) :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hNn : N ≤ max N (max x.length (F.fn (k / 2) x).length) := Nat.le_max_left _ _
  have hkn : stage F L₀ s (max N (max x.length (F.fn (k / 2) x).length)) = k := hconst _ hNn
  have h1 : stage F L₀ s (max N (max x.length (F.fn (k / 2) x).length) + 1) = k :=
    hconst _ (Nat.le_trans hNn (Nat.le_succ _))
  rw [stage_succ hs, hkn] at h1
  have hex : ∃ x' : Str, x'.length ≤ max N (max x.length (F.fn (k / 2) x).length) ∧
      (F.fn (k / 2) x').length ≤ max N (max x.length (F.fn (k / 2) x).length) ∧
      Fails F L₀ s (stage F L₀ s) k x' := ⟨x, hx, hy, hfail⟩
  rw [if_pos hex] at h1
  omega

/-- The stage function is unbounded, hence it takes every value. -/
theorem stage_passes (hs : ∀ m, s m ≤ m) (hunb : ∀ j, ∃ n, j ≤ stage F L₀ s n) (k : Nat) :
    ∃ n, stage F L₀ s n = k ∧ stage F L₀ s (n + 1) = k + 1 := by
  obtain ⟨m, hm⟩ := hunb (k + 1)
  induction m with
  | zero => rw [stage_zero] at hm; omega
  | succ m ih =>
    by_cases h : k + 1 ≤ stage F L₀ s m
    · exact ih h
    · have h1 := stage_le_succ (F := F) (L₀ := L₀) hs m
      exact ⟨m, by omega, by omega⟩

end Diagonalisation

section Main

variable {F : Framework} {L₀ : Lang} {s : Nat → Nat}

/-- If the stage function stabilises at an even value, `L₀` would be in `P`. -/
theorem not_eventually_const_even (hsl : SlowSchedule s) (hL₀ : ¬ F.P L₀) {N k : Nat}
    (hk : k % 2 = 0) (hconst : ∀ n, N ≤ n → stage F L₀ s n = k) : False := by
  obtain ⟨hmono, hid, hunb⟩ := hsl
  have hnf := no_fail_of_eventually_const hid hconst
  have hdec : ∀ x, (F.dec (k / 2) x = true ↔ holed F L₀ s x) := by
    intro x
    have h := hnf x
    unfold Fails at h
    rw [if_pos hk] at h
    exact Classical.byContradiction h
  have hAP : F.P (holed F L₀ s) :=
    F.P_of_agree (fun x => F.dec (k / 2) x = true) (holed F L₀ s) 0 (F.dec_mem _)
      (fun x _ => (hdec x).symm)
  obtain ⟨M₀, hM₀⟩ := hunb N
  refine hL₀ (F.P_of_agree (holed F L₀ s) L₀ M₀ hAP ?_)
  intro x hx
  have h1 : N ≤ s x.length := Nat.le_trans hM₀ (hmono _ _ hx)
  have h2 : stage F L₀ s (s x.length) = k := hconst _ h1
  constructor
  · intro hL; exact ⟨hL, by rw [h2]; exact hk⟩
  · intro hA; exact hA.1

/-- If the stage function stabilises at an odd value, `L₀` would be in `P`. -/
theorem not_eventually_const_odd (hsl : SlowSchedule s) (hL₀ : ¬ F.P L₀) {N k : Nat}
    (hk : k % 2 = 1) (hconst : ∀ n, N ≤ n → stage F L₀ s n = k) : False := by
  obtain ⟨hmono, hid, hunb⟩ := hsl
  have hnf := no_fail_of_eventually_const hid hconst
  have hred : ∀ x, (L₀ x ↔ holed F L₀ s (F.fn (k / 2) x)) := by
    intro x
    have h := hnf x
    unfold Fails at h
    rw [if_neg (by omega : ¬ (k % 2 = 0))] at h
    exact Classical.byContradiction h
  obtain ⟨M₀, hM₀⟩ := hunb N
  have hAP : F.P (holed F L₀ s) := by
    refine F.P_of_agree (fun _ => False) (holed F L₀ s) M₀ F.P_empty ?_
    intro x hx
    have h1 : N ≤ s x.length := Nat.le_trans hM₀ (hmono _ _ hx)
    have h2 : stage F L₀ s (s x.length) = k := hconst _ h1
    constructor
    · intro hA
      have := hA.2
      rw [h2] at this
      omega
    · intro hf; exact hf.elim
  exact hL₀ (F.P_of_reduction L₀ (holed F L₀ s) (F.fn (k / 2)) (F.fn_mem _) hred hAP)

/-- Either the stage function is unbounded, or it is eventually constant. -/
theorem stage_unbounded_or_const (hs : ∀ m, s m ≤ m) :
    (∀ j, ∃ n, j ≤ stage F L₀ s n) ∨ ∃ N k, ∀ n, N ≤ n → stage F L₀ s n = k := by
  by_cases hc : ∃ N, ∀ n, N ≤ n → stage F L₀ s n = stage F L₀ s N
  · obtain ⟨N, hN⟩ := hc
    exact Or.inr ⟨N, stage F L₀ s N, hN⟩
  · refine Or.inl ?_
    have step : ∀ N, ∃ n, N ≤ n ∧ stage F L₀ s N < stage F L₀ s n := by
      intro N
      have hne : ¬ ∀ n, N ≤ n → stage F L₀ s n = stage F L₀ s N := fun h => hc ⟨N, h⟩
      apply Classical.byContradiction
      intro hno
      refine hne ?_
      intro n hn
      have h1 : ¬ (N ≤ n ∧ stage F L₀ s N < stage F L₀ s n) := fun hcc => hno ⟨n, hcc⟩
      have h2 := stage_mono (F := F) (L₀ := L₀) hs hn
      omega
    intro j
    induction j with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ j ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hm1, hm2⟩ := step n
      exact ⟨m, by omega⟩

/-- The stage function is unbounded. -/
theorem stage_unbounded (hsl : SlowSchedule s) (hL₀ : ¬ F.P L₀) (j : Nat) :
    ∃ n, j ≤ stage F L₀ s n := by
  rcases stage_unbounded_or_const (F := F) (L₀ := L₀) hsl.2.1 with h | ⟨N, k, hconst⟩
  · exact h j
  · by_cases hk : k % 2 = 0
    · exact (not_eventually_const_even hsl hL₀ hk hconst).elim
    · exact (not_eventually_const_odd hsl hL₀ (by omega) hconst).elim

/-- The holed language is not in `P`. -/
theorem holed_not_in_P (hsl : SlowSchedule s) (hL₀ : ¬ F.P L₀) :
    ¬ F.P (holed F L₀ s) := by
  intro hP
  obtain ⟨i, hi⟩ := F.dec_complete _ hP
  obtain ⟨n, hn1, hn2⟩ := stage_passes hsl.2.1 (stage_unbounded hsl hL₀) (2 * i)
  rw [stage_succ hsl.2.1, hn1] at hn2
  by_cases hex : ∃ x : Str, x.length ≤ n ∧ (F.fn (2 * i / 2) x).length ≤ n ∧
      Fails F L₀ s (stage F L₀ s) (2 * i) x
  · obtain ⟨x, -, -, hfail⟩ := hex
    unfold Fails at hfail
    rw [if_pos (by omega : 2 * i % 2 = 0)] at hfail
    rw [(by omega : 2 * i / 2 = i)] at hfail
    exact hfail (hi x)
  · rw [if_neg hex] at hn2
    omega

/-- `L₀` does not reduce to the holed language. -/
theorem not_reduces_holed (hsl : SlowSchedule s) (hL₀ : ¬ F.P L₀) :
    ¬ Reduces F L₀ (holed F L₀ s) := by
  intro hr
  obtain ⟨g, hg, hgred⟩ := hr
  obtain ⟨i, hi⟩ := F.fn_complete g hg
  obtain ⟨n, hn1, hn2⟩ := stage_passes hsl.2.1 (stage_unbounded hsl hL₀) (2 * i + 1)
  rw [stage_succ hsl.2.1, hn1] at hn2
  by_cases hex : ∃ x : Str, x.length ≤ n ∧ (F.fn ((2 * i + 1) / 2) x).length ≤ n ∧
      Fails F L₀ s (stage F L₀ s) (2 * i + 1) x
  · obtain ⟨x, -, -, hfail⟩ := hex
    unfold Fails at hfail
    rw [if_neg (by omega : ¬ ((2 * i + 1) % 2 = 0))] at hfail
    rw [(by omega : (2 * i + 1) / 2 = i)] at hfail
    have hx := hgred x
    rw [← hi x] at hx
    exact hfail hx
  · rw [if_neg hex] at hn2
    omega

/-- **Ladner's theorem.**  If `P ≠ NP` then there is an `NP`-intermediate language:
one that lies in `NP`, is not in `P`, and is not `NP`-complete. -/
theorem ladner (F : Framework) (heff : Effectivity F) (hPNP : F.P ≠ F.NP) :
    ∃ A : Lang, NPIntermediate F A := by
  have hex : ∃ L, F.NP L ∧ ¬ F.P L := by
    apply Classical.byContradiction
    intro hno
    refine hPNP ?_
    funext L
    refine propext ⟨F.P_subset_NP L, ?_⟩
    intro hNP
    apply Classical.byContradiction
    intro hnP
    exact hno ⟨L, hNP, hnP⟩
  obtain ⟨L₀, hNP, hP⟩ := hex
  obtain ⟨s, hsl, hholes⟩ := heff L₀ hNP
  refine ⟨holed F L₀ s, ?_, holed_not_in_P hsl hP, ?_⟩
  · exact F.NP_inter_P L₀ (fun x => stage F L₀ s (s x.length) % 2 = 0) hNP hholes
  · intro hc
    exact not_reduces_holed hsl hP (hc.2 L₀ hNP)

end Main

end CS

import Mathlib
import RequestProject.Ladner

/-!
# A consistency check for the axiomatic framework of `RequestProject.Ladner`

`CS.ladner` is proved for an arbitrary `CS.Framework`, i.e. from an explicitly
listed collection of standard structural facts about the complexity classes
`P`, `NP` and about polynomial-time reductions.  To make sure that this list of
assumptions is not contradictory (which would make the theorem vacuous), we
exhibit here a concrete `CS.Framework`: languages consisting of strings of
bounded length, with the identity as the only "polynomial-time function".

Of course this toy framework satisfies `P = NP`, so Ladner's theorem is
vacuously true for it; the point of the construction is only that the axioms of
`CS.Framework` are mutually consistent.
-/

namespace CS

open Encodable

/-- Languages all of whose members have bounded length. -/
def Bounded (L : Lang) : Prop := ∃ N, ∀ x : Str, N ≤ x.length → ¬ L x

/-- The `i`-th finite language, under the standard encoding of lists of strings. -/
def decEnum (i : Nat) (x : Str) : Bool :=
  decide (x ∈ ((decode (α := List Str) i).getD []))

theorem bounded_of_list (l : List Str) : Bounded (fun x => x ∈ l) := by
  refine ⟨(l.map List.length).sum + 1, ?_⟩
  intro x hx hmem
  have h1 : x.length ≤ (l.map List.length).sum :=
    List.single_le_sum (by intro y _; exact Nat.zero_le y) _ (List.mem_map_of_mem hmem)
  omega

theorem bounded_decEnum (i : Nat) : Bounded (fun x => decEnum i x = true) := by
  obtain ⟨N, hN⟩ := bounded_of_list ((decode (α := List Str) i).getD [])
  exact ⟨N, fun x hx hmem => hN x hx (by simpa [decEnum] using hmem)⟩

theorem exists_index_of_bounded {L : Lang} (h : Bounded L) :
    ∃ i, ∀ x, (decEnum i x = true ↔ L x) := by
  obtain ⟨N, hN⟩ := h
  have hfin : {x : Str | L x}.Finite := by
    refine (List.finite_length_lt Bool N).subset ?_
    intro x hx
    by_contra hcon
    exact hN x (by simpa using Nat.le_of_not_lt (by simpa using hcon)) hx
  refine ⟨encode hfin.toFinset.toList, ?_⟩
  intro x
  simp [decEnum, Encodable.encodek]

/-- A concrete framework: `P = NP` is the class of languages of bounded length,
and the identity is the only polynomial-time function. -/
def boundedFramework : Framework where
  P := Bounded
  NP := Bounded
  FP := fun g => g = id
  dec := decEnum
  fn := fun _ => id
  dec_mem i := bounded_decEnum i
  dec_complete _ h := exists_index_of_bounded h
  fn_mem _ := rfl
  fn_complete g hg := ⟨0, fun x => by rw [hg]⟩
  P_subset_NP _ h := h
  P_empty := ⟨0, fun _ _ h => h⟩
  NP_inter_P L H hL _ := by
    obtain ⟨N, hN⟩ := hL
    exact ⟨N, fun x hx hmem => hN x hx hmem.1⟩
  P_of_agree L M N hL hagree := by
    obtain ⟨N', hN'⟩ := hL
    refine ⟨max N N', fun x hx hM => hN' x (le_trans (le_max_right N N') hx) ?_⟩
    exact (hagree x (le_trans (le_max_left N N') hx)).mp hM
  P_of_reduction L M g hg hred hM := by
    subst hg
    obtain ⟨N, hN⟩ := hM
    exact ⟨N, fun x hx hL => hN x hx ((hred x).mp hL)⟩

/-- The axioms of `CS.Framework` are consistent. -/
theorem framework_consistent : Nonempty Framework := ⟨boundedFramework⟩

end CS

