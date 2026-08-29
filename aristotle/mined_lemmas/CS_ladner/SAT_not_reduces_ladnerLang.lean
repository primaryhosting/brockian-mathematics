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

lemma SAT_not_reduces_ladnerLang (h : F.P ≠ F.NP) :
    ¬ F.Reduces F.M.SAT F.ladnerLang := by
  rintro ⟨i, hi⟩
  obtain ⟨n, hn, hb⟩ := F.stage_attains h (2 * i + 1)
  have hodd : ¬ Even (2 * i + 1) := by simp [parity_simps]
  rw [Machines.bumpAt, hn, Machines.bump, if_neg hodd] at hb
  have hdiv : (2 * i + 1) / 2 = i := by omega
  rw [hdiv] at hb
  obtain ⟨x, _, y, _, hconv, hne⟩ := hb
  have hyv : y = F.M.red i x := F.redT_sound i x n y hconv
  subst hyv
  exact hne (hi x)

