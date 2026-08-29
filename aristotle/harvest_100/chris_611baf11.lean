/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses only the Lean 4 core library),
so that the file can literally begin with the header comment above.

Encoding conventions:
* an input of length `n` is a natural number `x` (thought of as the bit string
  `x.testBit 0, …, x.testBit (n-1)`);
* a random string of length `r` is a natural number `ρ < 2 ^ r`;
* probabilities are handled by counting: `count r f` is the number of strings of length `r`
  on which `f` returns `true`, and a probability statement `p ≥ 2/3` is written as
  `2 * 2 ^ r ≤ 3 * count r f`.
-/

namespace CS

/-! ## Counting -/

/-- The number of strings `ρ < 2 ^ r` on which `f` returns `true`. -/
def count (r : Nat) (f : Nat → Bool) : Nat := (List.range (2 ^ r)).countP f

theorem count_add_count_not (r : Nat) (f : Nat → Bool) :
    count r f + count r (fun ρ => !f ρ) = 2 ^ r := by
  have h := List.length_eq_countP_add_countP (l := List.range (2 ^ r)) f
  have hf : (fun a => decide ¬ (f a = true)) = (fun a => !f a) := by
    funext a; cases f a <;> simp
  rw [hf, List.length_range] at h
  exact h.symm

theorem count_le (r : Nat) (f : Nat → Bool) : count r f ≤ 2 ^ r := by
  have h := count_add_count_not r f
  omega

theorem count_const_true (r : Nat) : count r (fun _ => true) = 2 ^ r := by
  have h : count r (fun _ => true) = (List.range (2 ^ r)).length := by
    rw [count, List.countP_eq_length]
    intro a _
    rfl
  rw [h, List.length_range]

/-! ## Boolean circuits -/

/-- Boolean circuits (with constants, input bits, and `¬`, `∧`, `∨` gates). -/
inductive Circuit where
  | const : Bool → Circuit
  | var : Nat → Circuit
  | not : Circuit → Circuit
  | and : Circuit → Circuit → Circuit
  | or : Circuit → Circuit → Circuit

/-- The Boolean function computed by a circuit, on an input encoded as a natural number. -/
def Circuit.eval : Circuit → Nat → Bool
  | .const b, _ => b
  | .var i, x => x.testBit i
  | .not c, x => !c.eval x
  | .and c d, x => c.eval x && d.eval x
  | .or c d, x => c.eval x || d.eval x

/-- The number of gates of a circuit. -/
def Circuit.size : Circuit → Nat
  | .const _ => 1
  | .var _ => 1
  | .not c => c.size + 1
  | .and c d => c.size + d.size + 1
  | .or c d => c.size + d.size + 1

/-! ## Languages, machine model, and complexity classes -/

/-- A language: `L n x` is the value of the language on the input `x` of length `n`. -/
abbrev Lang := Nat → Nat → Bool

/-- A randomized algorithm: `A n x ρ` is its output on the input `x` of length `n`
using the random string `ρ`. -/
abbrev RAlg := Nat → Nat → Nat → Bool

/-- `L` requires circuits of size `2 ^ Ω(n)`: for some `d > 0` and all large `n`, every
circuit computing the length-`n` slice of `L` has at least `2 ^ (n / d)` gates. -/
def HardLang (L : Lang) : Prop :=
  ∃ d N : Nat, 0 < d ∧
    ∀ n, N ≤ n → ∀ c : Circuit, (∀ x, x < 2 ^ n → c.eval x = L n x) → 2 ^ (n / d) ≤ c.size

/-- `r` is polynomially bounded. -/
def PolyBound (r : Nat → Nat) : Prop := ∃ k, ∀ n, r n ≤ n ^ k + k

/-- An abstract model of time-bounded computation.  `Poly L` says that `L` is decidable in
deterministic polynomial time, `RPoly r A` that the randomized algorithm `A`, which uses
`r n` random bits on inputs of length `n`, runs in polynomial time, and `ExpTime L` that `L`
is decidable in deterministic exponential time (the class `E`).  The only structural
assumption imposed on the model is that a deterministic polynomial-time algorithm is also a
polynomial-time randomized algorithm, namely one that ignores its random bits. -/
structure Model where
  Poly : Lang → Prop
  RPoly : (Nat → Nat) → RAlg → Prop
  ExpTime : Lang → Prop
  ignore_rand : ∀ {L : Lang} {r : Nat → Nat}, Poly L → RPoly r (fun n x _ => L n x)

/-- The class `P` of the model. -/
def Model.PClass (M : Model) : Lang → Prop := fun L => M.Poly L

/-- The class `BPP` of the model: languages decided with error probability at most `1/3`
by a polynomial-time randomized algorithm using polynomially many random bits.  The
correctness condition `2 * 2 ^ (r n) ≤ 3 * count (r n) (fun ρ => A n x ρ == L n x)` says
that the algorithm is correct on at least a `2/3` fraction of the random strings. -/
def Model.BPPClass (M : Model) : Lang → Prop := fun L =>
  ∃ r : Nat → Nat, PolyBound r ∧ ∃ A : RAlg, M.RPoly r A ∧
    ∀ n x, 2 * 2 ^ (r n) ≤ 3 * count (r n) (fun ρ => A n x ρ == L n x)

/-- A pseudorandom generator for the model, against polynomial-time randomized algorithms
that use `r n` random bits.

* `gen n` maps a seed of length `seedLen n` to a pseudorandom string of length `r n`;
* `fools_le` and `fools_ge` say that no polynomial-time algorithm distinguishes the output
  of the generator from a uniform random string with advantage bigger than `1/12`
  (the two inequalities are the two directions of `|p - q| ≤ 1/12`, cleared of
  denominators: `p = a / 2 ^ (r n)` and `q = b / 2 ^ (seedLen n)`);
* `derandomizes` says that the deterministic algorithm which enumerates *all* seeds and
  outputs the majority answer runs in polynomial time.  This is where the logarithmic seed
  length `seedLen n = O(log n)` produced by the Nisan–Wigderson construction is used. -/
structure PRG (M : Model) (r : Nat → Nat) where
  seedLen : Nat → Nat
  gen : Nat → Nat → Nat
  fools_le : ∀ {A : RAlg}, M.RPoly r A → ∀ n x,
      12 * (count (r n) (fun ρ => A n x ρ) * 2 ^ seedLen n)
        ≤ 12 * (count (seedLen n) (fun y => A n x (gen n y)) * 2 ^ r n)
            + 2 ^ r n * 2 ^ seedLen n
  fools_ge : ∀ {A : RAlg}, M.RPoly r A → ∀ n x,
      12 * (count (seedLen n) (fun y => A n x (gen n y)) * 2 ^ r n)
        ≤ 12 * (count (r n) (fun ρ => A n x ρ) * 2 ^ seedLen n)
            + 2 ^ r n * 2 ^ seedLen n
  derandomizes : ∀ {A : RAlg}, M.RPoly r A →
      M.Poly (fun n x =>
        decide (2 ^ seedLen n < 2 * count (seedLen n) (fun y => A n x (gen n y))))

/-- Strong circuit lower bounds: some language in `E` requires circuits of size `2 ^ Ω(n)`. -/
def Model.StrongCircuitLowerBounds (M : Model) : Prop :=
  ∃ L : Lang, M.ExpTime L ∧ HardLang L

/-- The Nisan–Wigderson / Impagliazzo–Wigderson hardness-versus-randomness tradeoff:
strong circuit lower bounds yield, for every polynomial bound on the number of random bits,
a pseudorandom generator with logarithmic seed length. -/
def Model.HardnessToPRG (M : Model) : Prop :=
  M.StrongCircuitLowerBounds → ∀ r : Nat → Nat, PolyBound r → Nonempty (PRG M r)

/-! ## The two arithmetic estimates behind majority voting -/

/-- If the acceptance probability is at least `2/3` and the generator fools the algorithm
with advantage at most `1/12`, then more than half of the seeds are accepting. -/
theorem majority_of_accept {R S a b : Nat} (hR : 0 < R) (hS : 0 < S)
    (hacc : 2 * R ≤ 3 * a) (hfool : 12 * (a * S) ≤ 12 * (b * R) + R * S) : S < 2 * b := by
  -- multiply the acceptance bound by `S`
  have h1 : 2 * R * S ≤ 3 * a * S := Nat.mul_le_mul_right S hacc
  have h1' : 2 * (R * S) ≤ 3 * (a * S) := by
    simp only [Nat.mul_assoc] at h1
    exact h1
  -- hence `7 * (R * S) ≤ 12 * (b * R)`
  have h2 : 7 * (R * S) ≤ 12 * (b * R) := by omega
  have h3 : R * (7 * S) ≤ R * (12 * b) := by
    calc R * (7 * S) = 7 * (R * S) := by
          simp [Nat.mul_comm, Nat.mul_assoc]
      _ ≤ 12 * (b * R) := h2
      _ = R * (12 * b) := by
          simp [Nat.mul_comm, Nat.mul_assoc]
  have h4 : 7 * S ≤ 12 * b := Nat.le_of_mul_le_mul_left h3 hR
  omega

/-- If the rejection probability is at least `2/3` and the generator fools the algorithm
with advantage at most `1/12`, then at most half of the seeds are accepting. -/
theorem minority_of_reject {R S a b : Nat} (hR : 0 < R)
    (hrej : 3 * a ≤ R) (hfool : 12 * (b * R) ≤ 12 * (a * S) + R * S) : 2 * b ≤ S := by
  have h1 : 3 * a * S ≤ R * S := Nat.mul_le_mul_right S hrej
  have h1' : 3 * (a * S) ≤ R * S := by
    simp only [Nat.mul_assoc] at h1
    exact h1
  have h2 : 12 * (b * R) ≤ 5 * (R * S) := by omega
  have h3 : R * (12 * b) ≤ R * (5 * S) := by
    calc R * (12 * b) = 12 * (b * R) := by
          simp [Nat.mul_comm, Nat.mul_assoc]
      _ ≤ 5 * (R * S) := h2
      _ = R * (5 * S) := by
          simp [Nat.mul_comm, Nat.mul_assoc]
  have h4 : 12 * b ≤ 5 * S := Nat.le_of_mul_le_mul_left h3 hR
  omega

/-! ## Derandomization -/

/-- **Key step.**  If a polynomial-time randomized algorithm `A` decides `L` with error at
most `1/3`, and a pseudorandom generator for the model exists, then `L` is in `P`: the
majority vote of `A` over all seeds of the generator computes `L`, and it runs in
polynomial time. -/
theorem derandomize_of_prg (M : Model) (r : Nat → Nat) (A : RAlg) (hA : M.RPoly r A)
    (L : Lang) (herr : ∀ n x, 2 * 2 ^ (r n) ≤ 3 * count (r n) (fun ρ => A n x ρ == L n x))
    (g : PRG M r) : M.Poly L := by
  have hB := g.derandomizes hA
  have key : ∀ n x,
      decide (2 ^ g.seedLen n < 2 * count (g.seedLen n) (fun y => A n x (g.gen n y)))
        = L n x := by
    intro n x
    have hR : 0 < 2 ^ (r n) := Nat.two_pow_pos _
    have hS : 0 < 2 ^ g.seedLen n := Nat.two_pow_pos _
    have hle := g.fools_le hA n x
    have hge := g.fools_ge hA n x
    have hcorr := herr n x
    cases hL : L n x with
    | false =>
        have hrewrite : (fun ρ => A n x ρ == L n x) = (fun ρ => !A n x ρ) := by
          funext ρ; simp [hL]
        rw [hrewrite] at hcorr
        have hsum := count_add_count_not (r n) (fun ρ => A n x ρ)
        have hrej : 3 * count (r n) (fun ρ => A n x ρ) ≤ 2 ^ (r n) := by omega
        have := minority_of_reject (R := 2 ^ (r n)) (S := 2 ^ g.seedLen n) hR hrej hge
        simp [Nat.not_lt.mpr this]
    | true =>
        have hrewrite : (fun ρ => A n x ρ == L n x) = (fun ρ => A n x ρ) := by
          funext ρ; simp [hL]
        rw [hrewrite] at hcorr
        have := majority_of_accept (R := 2 ^ (r n)) (S := 2 ^ g.seedLen n) hR hS hcorr hle
        simp [this]
  have hEq : (fun n x =>
      decide (2 ^ g.seedLen n < 2 * count (g.seedLen n) (fun y => A n x (g.gen n y)))) = L := by
    funext n x; exact key n x
  rwa [hEq] at hB

/-- `P ⊆ BPP` in any model. -/
theorem pclass_subset_bppClass (M : Model) (L : Lang) (hL : M.PClass L) : M.BPPClass L := by
  refine ⟨fun _ => 0, ⟨0, fun n => by simp⟩, fun n x _ => L n x, M.ignore_rand hL, ?_⟩
  intro n x
  have h : (fun _ : Nat => (L n x == L n x)) = (fun _ : Nat => true) := by
    funext ρ; simp
  rw [h, count_const_true]
  omega

/-- **Impagliazzo–Wigderson.**  In any model of computation for which the
hardness-versus-randomness tradeoff holds (strong circuit lower bounds yield a pseudorandom
generator with logarithmic seed length, fooling polynomial-time tests, whose seeds can be
enumerated in polynomial time), strong circuit lower bounds — the existence of a language in
`E` requiring circuits of size `2 ^ Ω(n)` — imply `P = BPP`. -/
theorem impagliazzo_wigderson (M : Model) (hNW : M.HardnessToPRG)
    (hLB : M.StrongCircuitLowerBounds) : M.PClass = M.BPPClass := by
  funext L
  apply propext
  constructor
  · exact pclass_subset_bppClass M L
  · rintro ⟨r, hr, A, hA, herr⟩
    obtain ⟨g⟩ := hNW hLB r hr
    exact derandomize_of_prg M r A hA L herr g


/-! ## Sanity checks on the formalization

The results below show that the notion of pseudorandom generator used above is neither
unsatisfiable nor trivially satisfiable.
-/

/-- The model in which every language is decidable in polynomial time.  It is used only to
witness that the pseudorandom generator axioms are satisfiable. -/
def trivialModel : Model where
  Poly := fun _ => True
  RPoly := fun _ _ => True
  ExpTime := fun _ => True
  ignore_rand := fun _ => trivial

/-- The hardness-versus-randomness hypothesis of the main theorem is satisfiable: there is a
model of computation for which it holds.  (In `trivialModel` the identity generator works.) -/
theorem exists_model_hardnessToPRG : ∃ M : Model, M.HardnessToPRG := by
  refine ⟨trivialModel, fun _ r _ => ⟨?_⟩⟩
  exact
    { seedLen := r
      gen := fun _ y => y
      fools_le := fun _ _ _ => Nat.le_add_right _ _
      fools_ge := fun _ _ _ => Nat.le_add_right _ _
      derandomizes := fun _ => trivial }

theorem countP_or_le (l : List Nat) (p q : Nat → Bool) :
    l.countP (fun a => p a || q a) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.countP_cons]
      cases p a <;> cases q a <;> simp <;> omega

theorem countP_eq_le_one (R v : Nat) : (List.range R).countP (fun ρ => v == ρ) ≤ 1 := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [List.range_succ, List.countP_append]
      by_cases h : v = R
      · simp [h]
        omega
      · simp [h]
        omega

/-- At most `l.length` strings lie in the image of `f` on `l`. -/
theorem countP_image_le (R : Nat) (l : List Nat) (f : Nat → Nat) :
    (List.range R).countP (fun ρ => l.any (fun y => f y == ρ)) ≤ l.length := by
  induction l with
  | nil => simp
  | cons y t ih =>
      have h1 : (List.range R).countP (fun ρ => (f y == ρ) || t.any (fun y => f y == ρ))
          ≤ (List.range R).countP (fun ρ => f y == ρ)
            + (List.range R).countP (fun ρ => t.any (fun y => f y == ρ)) :=
        countP_or_le _ _ _
      have h2 := countP_eq_le_one R (f y)
      simp only [List.any_cons, List.length_cons]
      omega

/-- A test that accepts all outputs of the generator but at most a `2 ^ s` fraction of all
strings violates the fooling condition, provided the seed is at least two bits shorter than
the output. -/
theorem distinguisher_gap {r s : Nat} {A : Nat → Bool} {gen : Nat → Nat} (h : s + 2 ≤ r)
    (hb : count s (fun y => A (gen y)) = 2 ^ s) (ha : count r A ≤ 2 ^ s) :
    ¬ 12 * (count s (fun y => A (gen y)) * 2 ^ r)
        ≤ 12 * (count r A * 2 ^ s) + 2 ^ r * 2 ^ s := by
  have hRS : 4 * 2 ^ s ≤ 2 ^ r := by
    have h1 : (2 : Nat) ^ (s + 2) ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) h
    have h2 : (2 : Nat) ^ (s + 2) = 4 * 2 ^ s := by
      rw [Nat.pow_add]
      omega
    omega
  have hSpos : 0 < 2 ^ s := Nat.two_pow_pos _
  have hQ : 4 * (2 ^ s * 2 ^ s) ≤ 2 ^ s * 2 ^ r := by
    calc 4 * (2 ^ s * 2 ^ s) = 2 ^ s * (4 * 2 ^ s) := by
          simp [Nat.mul_comm, Nat.mul_assoc]
      _ ≤ 2 ^ s * 2 ^ r := Nat.mul_le_mul_left _ hRS
  have haS : count r A * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ ha
  have hbR : count s (fun y => A (gen y)) * 2 ^ r = 2 ^ s * 2 ^ r := by rw [hb]
  have hRSprod : 2 ^ r * 2 ^ s = 2 ^ s * 2 ^ r := Nat.mul_comm _ _
  have hPpos : 0 < 2 ^ s * 2 ^ s := Nat.mul_pos hSpos hSpos
  omega

/-- The fooling condition is a genuine restriction: no generator whose seed length is at
least two bits shorter than its output length can fool *all* tests.  The test that accepts
exactly the strings in the image of the generator distinguishes it from uniform.  Hence
restricting the fooling condition to polynomial-time tests, as in `PRG`, is essential. -/
theorem no_universal_prg (r s : Nat) (gen : Nat → Nat) (h : s + 2 ≤ r) :
    ∃ A : Nat → Bool,
      ¬ 12 * (count s (fun y => A (gen y)) * 2 ^ r)
          ≤ 12 * (count r A * 2 ^ s) + 2 ^ r * 2 ^ s := by
  refine ⟨fun ρ => (List.range (2 ^ s)).any (fun y => gen y == ρ), ?_⟩
  refine distinguisher_gap (A := fun ρ => (List.range (2 ^ s)).any (fun y => gen y == ρ))
    (gen := gen) h ?_ ?_
  · have hlen : count s (fun y => (List.range (2 ^ s)).any (fun z => gen z == gen y))
        = (List.range (2 ^ s)).length := by
      rw [count, List.countP_eq_length]
      intro y hy
      simp only [List.any_eq_true]
      exact ⟨y, hy, by simp⟩
    rw [hlen, List.length_range]
  · have := countP_image_le (2 ^ r) (List.range (2 ^ s)) gen
    rw [List.length_range] at this
    exact this

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

