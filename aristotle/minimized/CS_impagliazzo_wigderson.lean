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

open scoped BigOperators
open Finset

namespace CS

/-! ## Boolean strings, probabilities and majority votes -/

/-- Boolean strings of length `n`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- The probability that the test `T` accepts a uniformly random string of length `k`. -/

def prob {k : ℕ} (T : Bits k → Bool) : ℚ :=
  ((univ.filter fun r => T r = true).card : ℚ) / 2 ^ k

def maj {k : ℕ} (T : Bits k → Bool) : Bool := decide (1 / 2 < prob T)

/-- **Core derandomization step.**  If a generator `G` fools the test `T` to within `1/6`,
then the majority vote of `T ∘ G` over all seeds agrees with the bounded-error answer of `T`. -/

theorem maj_comp_eq_true {k l : ℕ} (T : Bits k → Bool) (G : Bits l → Bits k)
    (h : |prob T - prob (fun s => T (G s))| < 1 / 6) (hT : 2 / 3 ≤ prob T) :
    maj (fun s => T (G s)) = true := by
  rw [abs_sub_lt_iff] at h
  have h1 := h.1
  simp only [maj, decide_eq_true_eq]
  linarith

theorem maj_comp_eq_false {k l : ℕ} (T : Bits k → Bool) (G : Bits l → Bits k)
    (h : |prob T - prob (fun s => T (G s))| < 1 / 6) (hT : prob T ≤ 1 / 3) :
    maj (fun s => T (G s)) = false := by
  rw [abs_sub_lt_iff] at h
  have h2 := h.2
  simp only [maj, decide_eq_false_iff_not, not_lt]
  linarith

/-! ## Languages, randomized algorithms and pseudorandom generators -/

/-- A language: for every input length, a predicate on binary strings of that length. -/
abbrev Lang := (n : ℕ) → Bits n → Bool

/-- A family of randomized algorithms: on inputs of length `n` the algorithm tosses
`len n` coins. -/
structure RandAlg where
  /-- number of random bits used on inputs of length `n` -/
  len : ℕ → ℕ
  /-- the output of the algorithm on a given input and a given random string -/
  run : (n : ℕ) → Bits n → Bits (len n) → Bool

/-- `A` decides `L` with two-sided bounded error `1/3` (the `BPP` acceptance condition). -/

def RandAlg.Decides (A : RandAlg) (L : Lang) : Prop :=
  ∀ (n : ℕ) (x : Bits n),
    (L n x = true → 2 / 3 ≤ prob (A.run n x)) ∧
    (L n x = false → prob (A.run n x) ≤ 1 / 3)

/-- A pseudorandom generator with logarithmic seed length that fools all the tests
arising from the randomized algorithm `A` (one test for each input). -/
structure PRG (A : RandAlg) where
  /-- seed length used on inputs of length `n` -/
  seedLen : ℕ → ℕ
  /-- the generator stretches a seed to a full random string -/
  gen : (n : ℕ) → Bits (seedLen n) → Bits (A.len n)
  /-- the seed length is logarithmic in the input length -/
  seedLen_log : ∃ c : ℕ, ∀ n, seedLen n ≤ c * Nat.log 2 (n + 1) + c
  /-- the generator fools every test of the algorithm to within `1/6` -/
  fools : ∀ (n : ℕ) (x : Bits n),
    |prob (A.run n x) - prob (fun s => A.run n x (gen n s))| < 1 / 6

/-- The deterministic language obtained by running `A` on all pseudorandom strings
produced by `G` and taking the majority vote. -/

def derandomize (A : RandAlg) (G : PRG A) : Lang :=
  fun n x => maj (fun s => A.run n x (G.gen n s))

/-- If `G` fools `A` and `A` decides `L`, then the seed-majority algorithm computes `L`
exactly. -/

theorem derandomize_eq (A : RandAlg) (G : PRG A) (L : Lang) (hA : A.Decides L) :
    derandomize A G = L := by
  funext n x
  rcases hd : L n x with _ | _
  · exact maj_comp_eq_false _ _ (G.fools n x) ((hA n x).2 hd)
  · exact maj_comp_eq_true _ _ (G.fools n x) ((hA n x).1 hd)

/-! ## Boolean circuits -/

/-- Boolean circuits (in tree form) over `n` input variables, with `¬, ∧, ∨` gates. -/
inductive BoolCircuit (n : ℕ) where
  | var : Fin n → BoolCircuit n
  | const : Bool → BoolCircuit n
  | not : BoolCircuit n → BoolCircuit n
  | and : BoolCircuit n → BoolCircuit n → BoolCircuit n
  | or : BoolCircuit n → BoolCircuit n → BoolCircuit n

/-- The Boolean function computed by a circuit. -/

def BoolCircuit.eval {n : ℕ} : BoolCircuit n → Bits n → Bool
  | .var i, x => x i
  | .const b, _ => b
  | .not c, x => !(c.eval x)
  | .and c d, x => (c.eval x) && (d.eval x)
  | .or c d, x => (c.eval x) || (d.eval x)

/-- The number of gates of a circuit. -/

def BoolCircuit.size {n : ℕ} : BoolCircuit n → ℕ
  | .var _ => 1
  | .const _ => 1
  | .not c => c.size + 1
  | .and c d => c.size + d.size + 1
  | .or c d => c.size + d.size + 1

/-! ## An abstract model of efficient computation -/

/-- An abstract uniform model of computation, recording which languages are decidable in
deterministic polynomial time (`Poly`), which randomized algorithms run in polynomial
time (`EffRand`), which languages are decidable in deterministic exponential time
(`ExpTime`) and which pseudorandom generators are polynomial-time computable (`EffPRG`),
together with the two closure properties that we use:

* a deterministic polynomial-time decider can be regarded as a (zero-error) randomized
  polynomial-time algorithm;
* an efficient randomized algorithm combined with an efficient logarithmic-seed generator
  can be simulated deterministically in polynomial time, by cycling through all
  (polynomially many) seeds and taking a majority vote. -/
structure Model where
  /-- the class `P` -/
  Poly : Lang → Prop
  /-- the polynomial-time randomized algorithms -/
  EffRand : RandAlg → Prop
  /-- the class `E`/`EXP` of languages decidable in deterministic exponential time -/
  ExpTime : Lang → Prop
  /-- the polynomial-time computable pseudorandom generators -/
  EffPRG : {A : RandAlg} → PRG A → Prop
  /-- `P ⊆ BPP` -/
  det_mem_rand : ∀ L, Poly L → ∃ A, EffRand A ∧ A.Decides L
  /-- exhaustive search over the polynomially many seeds is a polynomial-time algorithm -/
  derandomize_poly : ∀ (A : RandAlg) (G : PRG A), EffRand A → EffPRG G →
    Poly (derandomize A G)

/-- The class `P` of the model. -/

def Model.P (M : Model) : Set Lang := {L | M.Poly L}

/-- The class `BPP` of the model. -/

def Model.BPP (M : Model) : Set Lang := {L | ∃ A, M.EffRand A ∧ A.Decides L}

/-- **Strong circuit lower bound.**  There is a language decidable in deterministic
exponential time whose characteristic functions require circuits of size `2 ^ (ε * n)`
for some `ε > 0` and all large `n`. -/

def StrongCircuitLowerBound (M : Model) : Prop :=
  ∃ L : Lang, M.ExpTime L ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ c : BoolCircuit n,
    (∀ x, c.eval x = L n x) → (2 : ℝ) ^ (ε * n) ≤ (c.size : ℝ)

/-- **Hardness versus randomness.**  The Nisan–Wigderson / Impagliazzo–Wigderson
construction: a strong circuit lower bound yields, for every efficient randomized
algorithm, an efficient pseudorandom generator with logarithmic seed length fooling it. -/

def HardnessToRandomness (M : Model) : Prop :=
  StrongCircuitLowerBound M → ∀ A : RandAlg, M.EffRand A → ∃ G : PRG A, M.EffPRG G

/-! ## The Impagliazzo–Wigderson theorem -/

/-- **Impagliazzo–Wigderson.**  In a model of computation equipped with the
hardness-versus-randomness construction, a strong circuit lower bound (a language in
exponential time requiring circuits of size `2 ^ (ε n)`) implies `P = BPP`.

The derandomization argument itself is proved here: from the pseudorandom generator
supplied by `HardnessToRandomness` one gets, for every bounded-error randomized
polynomial-time algorithm, a deterministic algorithm which enumerates all seeds and takes
a majority vote, and this deterministic algorithm decides *exactly* the same language
(`derandomize_eq`, via the `1/6`-fooling estimate `maj_comp_eq_true`/`maj_comp_eq_false`).
The two efficiency facts used — that a deterministic algorithm is a special randomized one
and that the seed enumeration runs in polynomial time — are the closure properties
recorded in `Model`. -/

theorem impagliazzo_wigderson (M : Model) (hIW : HardnessToRandomness M)
    (hLB : StrongCircuitLowerBound M) : M.P = M.BPP := by
  apply Set.eq_of_subset_of_subset
  · intro L hL
    exact M.det_mem_rand L hL
  · rintro L ⟨A, hA, hdec⟩
    obtain ⟨G, hG⟩ := hIW hLB A hA
    have h := M.derandomize_poly A G hA hG
    rw [derandomize_eq A G L hdec] at h
    exact h

/-! ## Non-vacuity: the axioms of `Model` and `HardnessToRandomness` are satisfiable -/

/-- A degenerate model in which every language is "polynomial time" and the randomized
algorithms considered are those using at most logarithmically many coins.  It witnesses
that the hypotheses of `impagliazzo_wigderson` (apart from the conjectural circuit lower
bound) are consistent. -/
