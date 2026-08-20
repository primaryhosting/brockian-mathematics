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

theorem nonempty_uniformModel : Nonempty UniformModel :=
  ⟨{ Poly := fun _ => True
     PolyRand := fun r A => ∃ k : ℕ, ∀ (n : ℕ) (x : Bits n), ∃ C : Circuit (r n),
       C.size ≤ (n + 2) ^ k ∧ ∀ ρ, C.eval ρ = A n x ρ
     PolyGen := fun _ _ _ => True
     InE := fun _ => True
     polyRand_of_poly := fun L _ => ⟨1, fun n x => by
       cases h : L n x
       · exact ⟨Circuit.fls, by simp [Circuit.size], fun ρ => by simp [Circuit.eval, h]⟩
       · exact ⟨Circuit.tru, by simp [Circuit.size], fun ρ => by simp [Circuit.eval, h]⟩⟩
     poly_congr := fun _ _ _ _ => trivial
     circuit_of_polyRand := fun _ _ h => h
     poly_majority := fun _ _ _ _ _ _ _ => trivial }⟩

/-! ### Hardness assumption -/

/-- `f` requires circuits of size `2 ^ (ε n)` on every input length, for some `ε > 0`:
the "strong circuit lower bound" hypothesis. -/
