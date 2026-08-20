/-
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file formalises the Impagliazzo–Wigderson derandomisation theorem

> strong circuit lower bounds imply `P = BPP`

inside an explicit, self-contained framework.

* Boolean circuits (`CS.Circuit`), their size and semantics, are defined concretely.
* Acceptance probabilities of Boolean functions of `m` random bits are defined
  concretely as rationals (`CS.accProb`).
* A *model of computation* (`CS.Model`) is an interface packaging a type of
  deterministic machines, a type of randomised machines and the standard
  structural facts about them that are used in the derandomisation argument
  (a Cook–Levin style conversion of a poly-time randomised machine into
  poly-size circuits in its random bits, and closure of `P` under enumeration of
  a polynomially bounded set of generator seeds followed by a majority vote).
* The hardness-to-randomness construction (Nisan–Wigderson generator together
  with Impagliazzo–Wigderson hardness amplification) is stated precisely as
  `CS.Model.HardnessGivesPRG`, and appears as an explicit hypothesis of the main
  theorem.

The main theorem `CS.impagliazzo_wigderson` proves, from these ingredients, the
equality of the classes `BPP` and `P`.  The genuinely proved mathematical
content is the derandomisation glue: a pseudorandom generator that fools the
poly-size circuit computing the acceptance predicate of a `BPP` machine makes
the deterministic majority vote over all seeds *correct*
(`CS.prg_majority_correct`), and the two inclusions `P ⊆ BPP`, `BPP ⊆ P` follow.

The framework is shown to be non-vacuous: `CS.trivialModel` is an explicit
`Model` satisfying every field, and it also satisfies the
hardness-to-randomness hypothesis (`CS.trivialModel_hardnessGivesPRG`).
-/

namespace CS

open Finset

/-! ## Languages -/

/-- A language, presented as a Boolean predicate on bit strings of each length. -/
abbrev Language := (n : ℕ) → (Fin n → Bool) → Bool

/-- `IsPoly p` says that `p : ℕ → ℕ` is bounded by a polynomial. -/

def IsPoly (p : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n, p n ≤ c * n ^ k + c

/-! ## Boolean circuits -/

/-- Boolean circuits (formulas over `∧`, `∨`, `¬`) in `m` input variables. -/
inductive Circuit (m : ℕ) where
  | const (b : Bool) : Circuit m
  | var (i : Fin m) : Circuit m
  | not (c : Circuit m) : Circuit m
  | and (c d : Circuit m) : Circuit m
  | or (c d : Circuit m) : Circuit m
  deriving Inhabited

/-- The Boolean function computed by a circuit. -/
