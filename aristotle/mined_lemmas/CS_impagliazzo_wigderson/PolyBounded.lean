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

def PolyBounded (r : ℕ → ℕ) : Prop := ∃ k : ℕ, ∀ n, r n ≤ (n + 2) ^ k

/-- An abstract uniform model of computation.  It records which languages are decidable in
deterministic polynomial time (`Poly`), which randomized algorithms run in polynomial time
(`PolyRand`), which generators are polynomial-time computable (`PolyGen`) and which languages
are computable in deterministic exponential time (`InE`), together with the standard structural
facts about these notions that are used below:

* a deterministic polynomial-time algorithm is a randomized one that ignores its randomness;
* polynomial-time decidability only depends on the decided language;
* fixing an input, a polynomial-time randomized algorithm is computed, as a function of its
  random bits, by a polynomial-size circuit (the "algorithm to circuit" / Cook–Levin conversion);
* if the seed length is logarithmic, then the majority vote of a polynomial-time randomized
  algorithm over all outputs of a polynomial-time generator is computable in deterministic
  polynomial time (enumeration over the polynomially many seeds). -/
structure UniformModel where
  Poly : Lang → Prop
  PolyRand : (r : ℕ → ℕ) → ((n : ℕ) → Bits n → Bits (r n) → Bool) → Prop
  PolyGen : (s r : ℕ → ℕ) → ((n : ℕ) → Bits (s n) → Bits (r n)) → Prop
  InE : Lang → Prop
  polyRand_of_poly : ∀ L : Lang, Poly L → PolyRand (fun _ => 0) (fun n x _ => L n x)
  poly_congr : ∀ L L' : Lang, Poly L → (∀ n x, L n x = L' n x) → Poly L'
  circuit_of_polyRand : ∀ (r : ℕ → ℕ) (A : (n : ℕ) → Bits n → Bits (r n) → Bool), PolyRand r A →
    ∃ k : ℕ, ∀ (n : ℕ) (x : Bits n), ∃ C : Circuit (r n),
      C.size ≤ (n + 2) ^ k ∧ ∀ ρ, C.eval ρ = A n x ρ
  poly_majority : ∀ (r s : ℕ → ℕ) (A : (n : ℕ) → Bits n → Bits (r n) → Bool)
    (G : (n : ℕ) → Bits (s n) → Bits (r n)), PolyRand r A → PolyGen s r G → LogSeed s →
    Poly (fun n x => decide (2 ^ s n < 2 * accept (s n) (fun σ => A n x (G n σ))))

/-- The class `P` of the model. -/
