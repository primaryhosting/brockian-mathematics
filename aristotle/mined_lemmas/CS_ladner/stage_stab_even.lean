/-
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The required header above is a plain block comment rather than a module
-- docstring `/-! ... -/` because Lean 4 does not allow any command, including a
-- module docstring, to precede the `import` lines.)

import Mathlib

/-!
## Overview

This file formalises **Ladner's theorem**: if `P ≠ NP` then there is an
*NP-intermediate* language, i.e. a language that lies in `NP`, is not in `P`,
and is not `NP`-complete.

Mathlib contains no development of time-bounded complexity classes, so the
complexity-theoretic setting is packaged as an explicit `CS.Framework`
structure whose fields are exactly the standard facts about `P`, `NP` and
polynomial-time many-one reductions that Ladner's argument uses:

* `P` is exactly the collection of languages decided by one of the machines of a
  fixed enumeration `dec` of polynomial-time deciders;
* polynomial-time many-one reductions are exactly the functions of a fixed
  enumeration `red`;
* `P ⊆ NP`, `∅ ∈ P`, `P` is closed under finite variants and downwards under
  many-one reductions;
* `SAT` is `NP`-complete;
* the enumerations come with *clocked* simulations `decT`, `haltsDec`, `redT`
  which are sound, monotone in the clock, and eventually converge (this is the
  usual efficient universal simulation, and it is what makes the delayed
  diagonalisation below effective);
* `holes_mem_NP`: the language obtained from `SAT` by punching holes according
  to the (explicitly defined) Ladner stage function lies in `NP`.  This single
  field records the effectiveness content of Ladner's construction, namely that
  the stage function is polynomial-time computable.

Strings are encoded as natural numbers, and the length of the string coded by
`x` is `Nat.size x` (the number of binary digits of `x`).  All searches in the
construction range over inputs of length at most `Nat.log 2 n` at stage `n`, and
all simulations are clocked by `n`, exactly as in the classical proof.

Everything apart from the framework's fields — the construction of the stage
function, its unboundedness, and the three defining properties of the
intermediate language — is proved.
-/

namespace CS

attribute [local instance] Classical.propDecidable

/-- A language: a set of natural numbers (binary strings encoded as numbers). -/
abbrev Lang := Set ℕ

/-- The machine data of a complexity-theoretic setting: enumerations of the
polynomial-time deciders and of the polynomial-time functions, clocked versions
of both, and a distinguished language `SAT`. -/
structure Machines where
  /-- `dec i x` : value computed by the `i`-th polynomial-time decider on `x`. -/
  dec : ℕ → ℕ → Bool
  /-- `red i x` : value of the `i`-th polynomial-time function on `x`. -/
  red : ℕ → ℕ → ℕ
  /-- `decT i x t` : the `i`-th decider simulated on `x` for `t` steps. -/
  decT : ℕ → ℕ → ℕ → Bool
  /-- `haltsDec i x t` : whether that simulation has finished within `t` steps. -/
  haltsDec : ℕ → ℕ → ℕ → Bool
  /-- `redT i x t` : the `i`-th function simulated on `x` for `t` steps. -/
  redT : ℕ → ℕ → ℕ → Option ℕ
  /-- A distinguished `NP`-complete language. -/
  SAT : Lang

namespace Machines

/-- The "bump condition" driving Ladner's delayed diagonalisation.

At stage `n`, with current counter `k`, and with the already-computed values of
the stage function on `[0, n]` given by `g`:

* if `k = 2 i` is even we look for a short input `x` on which the `i`-th
  polynomial-time decider provably disagrees with the language
  `{x | x ∈ SAT ∧ Even (g (Nat.size x))}`;
* if `k = 2 i + 1` is odd we look for a short input `x` witnessing that the
  `i`-th polynomial-time function is not a many-one reduction of `SAT` to that
  language.

All searches are bounded: only inputs of length at most `Nat.log 2 n` are
considered, and simulations are run for at most `n` steps. -/

lemma stage_stab_even (N k : ℕ) (hk : Even k) (hN : ∀ n, N ≤ n → F.M.stage n = k)
    (hnb : ∀ n, N ≤ n → ¬ F.M.bumpAt n) : F.M.SAT ∈ F.P := by
  set i := k / 2 with hi
  have hLP : F.ladnerLang ∈ F.P := by
    rw [F.mem_P]
    refine ⟨i, fun x => ?_⟩
    obtain ⟨t, ht⟩ := F.haltsDec_ex i x
    set n := max (max N (2 ^ Nat.size x)) t with hn
    have hnN : N ≤ n := le_trans (le_max_left _ _) (le_max_left _ _)
    have hnx : 2 ^ Nat.size x ≤ n := le_trans (le_max_right _ _) (le_max_left _ _)
    have hnt : t ≤ n := le_max_right _ _
    have hxlog : Nat.size x ≤ Nat.log 2 n := by
      have h1 := Nat.log_mono_right (b := 2) hnx
      rwa [Nat.log_pow (by norm_num) (Nat.size x)] at h1
    have hhalt : F.M.haltsDec i x n = true := F.haltsDec_mono i x t n hnt ht
    have hb := hnb n hnN
    rw [Machines.bumpAt, hN n hnN, Machines.bump, if_pos hk] at hb
    push_neg at hb
    have hkey := hb x hxlog hhalt
    rw [F.decT_sound i x n hhalt] at hkey
    exact hkey
  refine F.P_finite_variant F.ladnerLang F.M.SAT (2 ^ N) hLP ?_
  intro x hx
  have hsz : N ≤ Nat.size x := size_ge_of_ge N x hx
  simp only [Framework.ladnerLang, Set.mem_setOf_eq, hN _ hsz]
  exact ⟨fun hh => hh.1, fun hh => ⟨hh, hk⟩⟩

/-- If the stage function is eventually constant with an **odd** value then the
constructed language is finite while `SAT` reduces to it, so `SAT ∈ P`. -/
