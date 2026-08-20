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
## Scope of the formalization

We work with explicitly defined Boolean circuits (`CS.Circuit`, with `size` and `eval`), with
exact acceptance counts and rational acceptance probabilities (`CS.accept`, `CS.prob`), and with
an abstract uniform model of computation (`CS.UniformModel`) recording the classes `P`, `BPP`,
polynomial-time generators and `E`, together with the standard structural facts about them
(a deterministic algorithm is a randomized one; conversion of an algorithm on a fixed input into
a polynomial-size circuit in its random bits; polynomial-time enumeration of the polynomially
many seeds of a logarithmic-seed generator).  `CS.nonempty_uniformModel` shows these
requirements are consistent.

The deep construction of Nisan–Wigderson and Impagliazzo–Wigderson -- turning an exponentially
hard language in `E` into a polynomial-time generator with logarithmic seed length that fools all
polynomial-size circuits -- is taken as the hypothesis `CS.IWGeneratorConstruction`.  What is
proved here is the rest of the theorem: the hard language supplied by the circuit lower bound is
fed to that construction and the resulting generator is used to derandomize an arbitrary `BPP`
algorithm by a strict majority vote over all seeds (`CS.derandomize`, proved in full), yielding
`P = BPP`.
-/

namespace CS

open Finset

/-- Bit strings of length `n`. -/
abbrev Bits (n : ℕ) : Type := Fin n → Bool

/-- A language, given by its characteristic function on each input length. -/
abbrev Lang : Type := (n : ℕ) → Bits n → Bool

/-! ### Boolean circuits -/

/-- Boolean circuits over `n` input variables, with `¬`, `∧`, `∨` gates. -/
inductive Circuit (n : ℕ) : Type
  | var : Fin n → Circuit n
  | tru : Circuit n
  | fls : Circuit n
  | neg : Circuit n → Circuit n
  | conj : Circuit n → Circuit n → Circuit n
  | disj : Circuit n → Circuit n → Circuit n
  deriving Inhabited

/-- The Boolean function computed by a circuit. -/

lemma card_bits (m : ℕ) : Fintype.card (Bits m) = 2 ^ m := by simp

