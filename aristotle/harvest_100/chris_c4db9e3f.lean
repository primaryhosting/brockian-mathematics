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
def Circuit.eval {m : ℕ} : Circuit m → (Fin m → Bool) → Bool
  | .const b, _ => b
  | .var i, x => x i
  | .not c, x => !(c.eval x)
  | .and c d, x => (c.eval x) && (d.eval x)
  | .or c d, x => (c.eval x) || (d.eval x)

/-- The size (number of gates) of a circuit. -/
def Circuit.size {m : ℕ} : Circuit m → ℕ
  | .const _ => 1
  | .var _ => 1
  | .not c => c.size + 1
  | .and c d => c.size + d.size + 1
  | .or c d => c.size + d.size + 1

/-! ## Acceptance probabilities -/

/-- The probability that `f` accepts a uniformly random string of `m` bits. -/
def accProb {m : ℕ} (f : (Fin m → Bool) → Bool) : ℚ :=
  (((univ.filter fun r => f r = true).card : ℚ)) / 2 ^ m

lemma card_bits (m : ℕ) : Fintype.card (Fin m → Bool) = 2 ^ m := by
  simp

lemma accProb_of_const {m : ℕ} {f : (Fin m → Bool) → Bool} {b : Bool} (h : ∀ r, f r = b) :
    accProb f = if b = true then 1 else 0 := by
  have hpos : (0:ℚ) < 2 ^ m := by positivity
  cases b with
  | true =>
      have : (univ.filter fun r => f r = true) = (univ : Finset (Fin m → Bool)) := by
        apply Finset.filter_true_of_mem
        intro r _
        simp [h r]
      simp [accProb, this, card_bits m, hpos.ne']
  | false =>
      have : (univ.filter fun r => f r = true) = (∅ : Finset (Fin m → Bool)) := by
        apply Finset.filter_false_of_mem
        intro r _
        simp [h r]
      simp [accProb, this]

/-- **Derandomisation core.**  If a generator `G` fools the acceptance predicate `f`
to within `1/12`, then the deterministic majority vote over all seeds decides
correctly whenever `f` has a two-sided `2/3` versus `1/3` gap. -/
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
def Pclass : Set Language :=
  {L | ∃ A : Mo.Det, Mo.IsPolyTime A ∧ ∀ n x, Mo.run A n x = L n x}

/-- The class `BPP` of the model: bounded two-sided error `1/3`. -/
def BPPclass : Set Language :=
  {L | ∃ M : Mo.Rand, Mo.IsPolyTimeR M ∧ ∀ n x,
      (L n x = true → 2/3 ≤ accProb (Mo.rrun M n x)) ∧
      (L n x = false → accProb (Mo.rrun M n x) ≤ 1/3)}

/-- **Strong circuit lower bound**: some language in `E` requires circuits of size
`2 ^ Ω(n)`. -/
def StrongCircuitLowerBound : Prop :=
  ∃ (A : Mo.Det) (d : ℕ), 0 < d ∧ Mo.IsExpTime A ∧
    ∀ n (C : Circuit n), (∀ x, C.eval x = Mo.run A n x) → 2 ^ (n / d) ≤ C.size

/-- **Hardness to randomness** (Nisan–Wigderson generator plus Impagliazzo–Wigderson
hardness amplification): a strong circuit lower bound yields, for each poly-time
randomised machine and each polynomial circuit-size bound, a uniform pseudorandom
generator with polynomially many seeds fooling all such circuits to within
`1/12`. -/
def HardnessGivesPRG : Prop :=
  Mo.StrongCircuitLowerBound → ∀ (M : Mo.Rand), Mo.IsPolyTimeR M → ∀ p : ℕ → ℕ, IsPoly p →
    ∃ (s : ℕ → ℕ) (G : ∀ n, (Fin (s n) → Bool) → (Fin (Mo.bits M n) → Bool)),
      (∃ c : ℕ, ∀ n, 2 ^ s n ≤ c * n ^ c + c) ∧ Mo.PolyGen s (Mo.bits M) G ∧
      ∀ n (C : Circuit (Mo.bits M n)), C.size ≤ p n →
        |accProb (fun y => C.eval (G n y)) - accProb C.eval| ≤ 1/12

end Model

/-- Every language in `P` is in `BPP`. -/
theorem P_subset_BPP (Mo : Model) : Mo.Pclass ⊆ Mo.BPPclass := by
  rintro L ⟨A, hA, hrun⟩
  refine ⟨Mo.detAsRand A, Mo.polyTime_detAsRand A hA, ?_⟩
  intro n x
  constructor
  · intro hL
    have hconst : ∀ r, Mo.rrun (Mo.detAsRand A) n x r = true := by
      intro r; rw [Mo.rrun_detAsRand, hrun, hL]
    rw [accProb_of_const hconst]
    norm_num
  · intro hL
    have hconst : ∀ r, Mo.rrun (Mo.detAsRand A) n x r = false := by
      intro r; rw [Mo.rrun_detAsRand, hrun, hL]
    rw [accProb_of_const hconst]
    norm_num

/-- Under the hardness-to-randomness construction and a strong circuit lower bound,
every language in `BPP` is in `P`. -/
theorem BPP_subset_P (Mo : Model) (hNW : Mo.HardnessGivesPRG)
    (hard : Mo.StrongCircuitLowerBound) : Mo.BPPclass ⊆ Mo.Pclass := by
  rintro L ⟨M, hM, hL⟩
  obtain ⟨p, hp, hcirc⟩ := Mo.circuit_of_rand M hM
  obtain ⟨s, G, hseed, hgen, hfool⟩ := hNW hard M hM p hp
  obtain ⟨A, hA, hrunA⟩ := Mo.derandomize M hM s G hseed hgen
  refine ⟨A, hA, ?_⟩
  intro n x
  obtain ⟨C, hCsize, hCeval⟩ := hcirc n x
  have hCfun : C.eval = Mo.rrun M n x := funext hCeval
  have hf := hfool n C hCsize
  rw [hCfun] at hf
  obtain ⟨hacc, hrej⟩ := prg_majority_correct (Mo.rrun M n x) (G n) hf
  rw [hrunA n x]
  cases hLnx : L n x with
  | true =>
      have := hacc ((hL n x).1 hLnx)
      simp [this]
  | false =>
      have := hrej ((hL n x).2 hLnx)
      have hnot : ¬ (2 ^ s n < 2 * (univ.filter fun y => Mo.rrun M n x (G n y) = true).card) := by
        omega
      simp [hnot]

/-- **Impagliazzo–Wigderson.**  In any model of computation satisfying the standard
structural facts, if the hardness-to-randomness construction is available and
some language in `E` requires circuits of size `2 ^ Ω(n)`, then `P = BPP`. -/
theorem impagliazzo_wigderson (Mo : Model) (hNW : Mo.HardnessGivesPRG)
    (hard : Mo.StrongCircuitLowerBound) : Mo.BPPclass = Mo.Pclass :=
  Set.Subset.antisymm (BPP_subset_P Mo hNW hard) (P_subset_BPP Mo)

/-! ## Non-vacuity

An explicit model satisfying all the fields of `Model`, and also satisfying the
hardness-to-randomness hypothesis, so that the main theorem is not vacuous. -/

/-- A model whose machines are arbitrary language deciders, with no resource
restrictions and no genuine randomness. -/
def trivialModel : Model where
  Det := Language
  run := id
  IsPolyTime := fun _ => True
  IsExpTime := fun _ => True
  Rand := (n : ℕ) → (Fin n → Bool) → (Fin 0 → Bool) → Bool
  bits := fun _ _ => 0
  rrun := fun M => M
  IsPolyTimeR := fun _ => True
  PolyGen := fun _ _ _ => True
  detAsRand := fun A n x _ => A n x
  rrun_detAsRand := fun _ _ _ _ => rfl
  polyTime_detAsRand := fun _ _ => trivial
  circuit_of_rand := by
    intro M _
    refine ⟨fun _ => 1, ⟨1, 0, fun n => by simp⟩, ?_⟩
    intro n x
    refine ⟨Circuit.const (M n x (fun i => i.elim0)), le_refl _, ?_⟩
    intro r
    have : r = fun i : Fin 0 => i.elim0 := funext (fun i => i.elim0)
    simp [Circuit.eval, this]
  derandomize := by
    intro M _ s G _ _
    exact ⟨fun n x =>
      decide (2 ^ s n < 2 * (univ.filter fun y => M n x (G n y) = true).card),
      trivial, fun _ _ => rfl⟩

theorem trivialModel_hardnessGivesPRG : trivialModel.HardnessGivesPRG := by
  intro _ M _ p _
  refine ⟨fun _ => 0, fun _ _ => (fun i : Fin 0 => i.elim0), ⟨1, fun n => by simp⟩, trivial, ?_⟩
  intro n C _
  have hconst : ∀ r : Fin 0 → Bool, C.eval r = C.eval (fun i : Fin 0 => i.elim0) := by
    intro r
    have : r = fun i : Fin 0 => i.elim0 := funext (fun i => i.elim0)
    rw [this]
  rw [accProb_of_const (b := C.eval (fun i : Fin 0 => i.elim0)) hconst,
    accProb_of_const (f := fun y : Fin 0 → Bool => C.eval (fun i : Fin 0 => i.elim0))
      (b := C.eval (fun i : Fin 0 => i.elim0)) (fun _ => rfl)]
  norm_num

end CS

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

