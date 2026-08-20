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
def Circuit.eval {n : ℕ} : Circuit n → Bits n → Bool
  | .var i, x => x i
  | .tru, _ => true
  | .fls, _ => false
  | .neg c, x => !(c.eval x)
  | .conj a b, x => (a.eval x) && (b.eval x)
  | .disj a b, x => (a.eval x) || (b.eval x)

/-- The number of gates of a circuit. -/
def Circuit.size {n : ℕ} : Circuit n → ℕ
  | .var _ => 1
  | .tru => 1
  | .fls => 1
  | .neg c => c.size + 1
  | .conj a b => a.size + b.size + 1
  | .disj a b => a.size + b.size + 1

/-- `f` is computed by some circuit with at most `s` gates. -/
def HasCircuitOfSize {n : ℕ} (f : Bits n → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit n, C.size ≤ s ∧ ∀ x, C.eval x = f x

/-! ### Acceptance probabilities -/

/-- The number of strings of length `m` accepted by `f`. -/
def accept (m : ℕ) (f : Bits m → Bool) : ℕ :=
  (Finset.univ.filter fun ρ : Bits m => f ρ = true).card

/-- The probability that `f` accepts a uniformly random string of length `m`. -/
def prob (m : ℕ) (f : Bits m → Bool) : ℚ := (accept m f : ℚ) / 2 ^ m

lemma card_bits (m : ℕ) : Fintype.card (Bits m) = 2 ^ m := by simp

lemma accept_le (m : ℕ) (f : Bits m → Bool) : accept m f ≤ 2 ^ m := by
  have := Finset.card_filter_le (Finset.univ : Finset (Bits m)) (fun ρ => f ρ = true)
  simpa [accept, card_bits] using this

lemma accept_true (m : ℕ) : accept m (fun _ => true) = 2 ^ m := by
  simp [accept]

lemma accept_false (m : ℕ) : accept m (fun _ => false) = 0 := by
  simp [accept]

lemma prob_nonneg (m : ℕ) (f : Bits m → Bool) : 0 ≤ prob m f := by
  unfold prob
  positivity

lemma prob_le_one (m : ℕ) (f : Bits m → Bool) : prob m f ≤ 1 := by
  unfold prob
  rw [div_le_one (by positivity)]
  exact_mod_cast accept_le m f

/-- If `f` accepts strictly more than half of the strings, the strict majority test succeeds. -/
lemma lt_two_mul_accept {m : ℕ} {f : Bits m → Bool} (h : (1 : ℚ) / 2 < prob m f) :
    2 ^ m < 2 * accept m f := by
  have hpos : (0 : ℚ) < 2 ^ m := by positivity
  rw [prob, lt_div_iff₀ hpos] at h
  have : ((2 : ℚ) ^ m : ℚ) < 2 * (accept m f : ℚ) := by linarith
  exact_mod_cast this

/-- If `f` accepts strictly fewer than half of the strings, the strict majority test fails. -/
lemma two_mul_accept_lt {m : ℕ} {f : Bits m → Bool} (h : prob m f < (1 : ℚ) / 2) :
    2 * accept m f < 2 ^ m := by
  have hpos : (0 : ℚ) < 2 ^ m := by positivity
  rw [prob, div_lt_iff₀ hpos] at h
  have : 2 * (accept m f : ℚ) < ((2 : ℚ) ^ m : ℚ) := by linarith
  exact_mod_cast this

/-! ### Randomized algorithms, generators and complexity classes -/

/-- `A`, using `r n` random bits on inputs of length `n`, decides `L` with two-sided error `1/3`. -/
def Decides (L : Lang) (r : ℕ → ℕ) (A : (n : ℕ) → Bits n → Bits (r n) → Bool) : Prop :=
  ∀ (n : ℕ) (x : Bits n),
    (L n x = true → 2 / 3 ≤ prob (r n) (A n x)) ∧
    (L n x = false → prob (r n) (A n x) ≤ 1 / 3)

/-- `G`, stretching `s n` seed bits to `r n` output bits, fools every circuit of size at most
`bound n` up to error `1/10`. -/
def Fools (s r : ℕ → ℕ) (G : (n : ℕ) → Bits (s n) → Bits (r n)) (bound : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (C : Circuit (r n)), C.size ≤ bound n →
    |prob (s n) (fun σ => C.eval (G n σ)) - prob (r n) C.eval| ≤ 1 / 10

/-- `s` is logarithmic, so that there are only polynomially many seeds. -/
def LogSeed (s : ℕ → ℕ) : Prop := ∃ c : ℕ, ∀ n, s n ≤ c * Nat.log 2 (n + 2) + c

/-- `r` is polynomially bounded. -/
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
def UniformModel.P (M : UniformModel) : Set Lang := {L | M.Poly L}

/-- The class `BPP` of the model. -/
def UniformModel.BPP (M : UniformModel) : Set Lang :=
  {L | ∃ (r : ℕ → ℕ) (A : (n : ℕ) → Bits n → Bits (r n) → Bool),
        PolyBounded r ∧ M.PolyRand r A ∧ Decides L r A}

/-- The requirements packaged into `UniformModel` are consistent: there is at least one such
model, so the main theorem below is not vacuous. -/
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
def ExponentiallyHard (f : Lang) : Prop :=
  ∃ ε : ℚ, 0 < ε ∧ ∀ n : ℕ, ¬ HasCircuitOfSize (f n) (2 ^ ⌊ε * n⌋₊)

/-- Some language in deterministic exponential time requires exponential size circuits. -/
def StrongCircuitLowerBound (M : UniformModel) : Prop :=
  ∃ f : Lang, M.InE f ∧ ExponentiallyHard f

/-- The Nisan–Wigderson / Impagliazzo–Wigderson generator: from any exponentially hard
language in `E` one can build, for every polynomially bounded output length and every
polynomial circuit-size bound, a polynomial-time computable generator with logarithmic seed
length fooling all circuits of that size. -/
def IWGeneratorConstruction (M : UniformModel) : Prop :=
  ∀ f : Lang, M.InE f → ExponentiallyHard f →
    ∀ (r : ℕ → ℕ) (k : ℕ), PolyBounded r →
      ∃ (s : ℕ → ℕ) (G : (n : ℕ) → Bits (s n) → Bits (r n)),
        LogSeed s ∧ M.PolyGen s r G ∧ Fools s r G (fun n => (n + 2) ^ k)

/-! ### The derandomization argument -/

/-- **Derandomization by seed enumeration.**  If `A` decides `L` with error `1/3`, if on every
fixed input `A` is computed by a circuit of size at most `bound n` in its random bits, and if
`G` fools all circuits of size `bound n` up to error `1/10`, then the strict majority vote of
`A` over all seeds of `G` decides `L` exactly. -/
theorem derandomize {L : Lang} {r s : ℕ → ℕ}
    {A : (n : ℕ) → Bits n → Bits (r n) → Bool} {G : (n : ℕ) → Bits (s n) → Bits (r n)}
    {bound : ℕ → ℕ} (hDec : Decides L r A) (hFool : Fools s r G bound)
    (hC : ∀ (n : ℕ) (x : Bits n), ∃ C : Circuit (r n),
      C.size ≤ bound n ∧ ∀ ρ, C.eval ρ = A n x ρ) :
    ∀ (n : ℕ) (x : Bits n),
      decide (2 ^ s n < 2 * accept (s n) (fun σ => A n x (G n σ))) = L n x := by
  intro n x
  obtain ⟨C, hCsize, hCeval⟩ := hC n x
  have hCfun : C.eval = A n x := funext hCeval
  have hfool := hFool n C hCsize
  rw [hCfun] at hfool
  have hfool' : |prob (s n) (fun σ => A n x (G n σ)) - prob (r n) (A n x)| ≤ 1 / 10 := hfool
  obtain ⟨hlo, hhi⟩ := abs_le.mp hfool'
  obtain ⟨htrue, hfalse⟩ := hDec n x
  cases hLx : L n x with
  | true =>
      have h1 : (2 : ℚ) / 3 ≤ prob (r n) (A n x) := htrue hLx
      have h2 : (1 : ℚ) / 2 < prob (s n) (fun σ => A n x (G n σ)) := by linarith
      have := lt_two_mul_accept h2
      simp [this]
  | false =>
      have h1 : prob (r n) (A n x) ≤ (1 : ℚ) / 3 := hfalse hLx
      have h2 : prob (s n) (fun σ => A n x (G n σ)) < (1 : ℚ) / 2 := by linarith
      have := two_mul_accept_lt h2
      simp [Nat.not_lt.mpr this.le]

/-- `P ⊆ BPP`: a deterministic algorithm is a randomized algorithm that ignores its coins. -/
theorem p_subset_bpp (M : UniformModel) : M.P ⊆ M.BPP := by
  intro L hL
  refine ⟨fun _ => 0, fun n x _ => L n x, ⟨0, fun n => by simp⟩,
    M.polyRand_of_poly L hL, ?_⟩
  intro n x
  constructor
  · intro h
    show (2 : ℚ) / 3 ≤ prob 0 (fun _ : Bits 0 => L n x)
    rw [show (fun _ : Bits 0 => L n x) = (fun _ : Bits 0 => true) by simp [h]]
    rw [prob, accept_true]
    norm_num
  · intro h
    show prob 0 (fun _ : Bits 0 => L n x) ≤ (1 : ℚ) / 3
    rw [show (fun _ : Bits 0 => L n x) = (fun _ : Bits 0 => false) by simp [h]]
    rw [prob, accept_false]
    norm_num

/-- **Impagliazzo–Wigderson.**  In a uniform model of computation equipped with the
Nisan–Wigderson/Impagliazzo–Wigderson generator construction, a strong circuit lower bound
(a language in `E` requiring circuits of size `2^(εn)`) implies `P = BPP`. -/
theorem impagliazzo_wigderson (M : UniformModel) (hIW : IWGeneratorConstruction M)
    (hHard : StrongCircuitLowerBound M) : M.P = M.BPP := by
  obtain ⟨f, hfE, hfHard⟩ := hHard
  refine Set.Subset.antisymm (p_subset_bpp M) ?_
  rintro L ⟨r, A, hr, hA, hDec⟩
  obtain ⟨k, hk⟩ := M.circuit_of_polyRand r A hA
  obtain ⟨s, G, hLog, hG, hFool⟩ := hIW f hfE hfHard r k hr
  have hEq := derandomize hDec hFool (fun n x => hk n x)
  exact M.poly_congr _ L (M.poly_majority r s A G hA hG hLog) hEq

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

