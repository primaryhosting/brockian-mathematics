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

theorem prg_majority_correct {m s : ℕ} (f : (Fin m → Bool) → Bool)
    (G : (Fin s → Bool) → (Fin m → Bool))
    (hfool : |accProb (fun y => f (G y)) - accProb f| ≤ 1/12) :
    (2/3 ≤ accProb f → 2 ^ s < 2 * (univ.filter fun y => f (G y) = true).card) ∧
      (accProb f ≤ 1/3 → 2 * (univ.filter fun y => f (G y) = true).card < 2 ^ s) := by
  have hpos : (0:ℚ) < 2 ^ s := by positivity
  set k : ℕ := (univ.filter fun y => f (G y) = true).card with hk
  have hval : accProb (fun y => f (G y)) = (k : ℚ) / 2 ^ s := rfl
  have h1 := abs_le.mp hfool
  obtain ⟨hlo, hhi⟩ := h1
  rw [hval] at hlo hhi
  constructor
  · intro hacc
    have hhalf : (1:ℚ)/2 < (k:ℚ) / 2 ^ s := by linarith
    rw [lt_div_iff₀ hpos] at hhalf
    have : (2:ℚ) ^ s < 2 * (k : ℚ) := by linarith
    exact_mod_cast this
  · intro hacc
    have hhalf : (k:ℚ) / 2 ^ s < 1/2 := by linarith
    rw [div_lt_iff₀ hpos] at hhalf
    have : 2 * (k : ℚ) < (2:ℚ) ^ s := by linarith
    exact_mod_cast this

/-! ## A model of computation -/

/-- An interface for a uniform model of computation, packaging deterministic and
randomised machines together with the structural facts used in the
derandomisation argument. -/
structure Model where
  /-- Deterministic machines. -/
  Det : Type
  /-- The language decided by a deterministic machine. -/
  run : Det → Language
  /-- Deterministic polynomial time. -/
  IsPolyTime : Det → Prop
  /-- Deterministic exponential time (the class `E`, used to state the hardness
  assumption). -/
  IsExpTime : Det → Prop
  /-- Randomised machines. -/
  Rand : Type
  /-- The number of random bits used on inputs of a given length. -/
  bits : Rand → ℕ → ℕ
  /-- The output of a randomised machine on a given input and random string. -/
  rrun : (M : Rand) → (n : ℕ) → (Fin n → Bool) → (Fin (bits M n) → Bool) → Bool
  /-- Randomised polynomial time. -/
  IsPolyTimeR : Rand → Prop
  /-- Uniform (polynomial-time computable) seed-stretching generators. -/
  PolyGen : (s m : ℕ → ℕ) → (∀ n, (Fin (s n) → Bool) → (Fin (m n) → Bool)) → Prop
  /-- A deterministic machine viewed as a randomised one. -/
  detAsRand : Det → Rand
  rrun_detAsRand : ∀ A n x r, rrun (detAsRand A) n x r = run A n x
  polyTime_detAsRand : ∀ A, IsPolyTime A → IsPolyTimeR (detAsRand A)
  /-- Cook–Levin: for a poly-time randomised machine, the acceptance predicate as a
  function of the random bits is computed by circuits of polynomial size. -/
  circuit_of_rand : ∀ M, IsPolyTimeR M → ∃ p, IsPoly p ∧ ∀ n x,
    ∃ C : Circuit (bits M n), C.size ≤ p n ∧ ∀ r, C.eval r = rrun M n x r
  /-- Deterministically enumerating a polynomially bounded seed space of a uniform
  generator and taking the majority vote stays inside `P`. -/
  derandomize : ∀ (M : Rand), IsPolyTimeR M → ∀ (s : ℕ → ℕ)
    (G : ∀ n, (Fin (s n) → Bool) → (Fin (bits M n) → Bool)),
    (∃ c : ℕ, ∀ n, 2 ^ s n ≤ c * n ^ c + c) → PolyGen s (bits M) G →
    ∃ A : Det, IsPolyTime A ∧ ∀ n x,
      run A n x =
        decide (2 ^ s n < 2 * (univ.filter fun y => rrun M n x (G n y) = true).card)

namespace Model

variable (Mo : Model)

/-- The class `P` of the model. -/
