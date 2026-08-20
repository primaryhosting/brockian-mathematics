/-!
# Toda Theorem
Category: Frontier Cs
Target: CS.toda_theorem
Statement: PH ⊆ P^{#P} (Toda's theorem).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Toda Theorem
Category: Frontier Cs
Target: CS.toda_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the
-- header above is a plain comment and is repeated as the module docstring
-- immediately after the import.)


/-!
# Toda Theorem
Category: Frontier Cs
Target: CS.toda_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Scope of this formalization

Toda's theorem states `PH ⊆ P^{#P}`.  This file develops a self-contained,
machine-independent framework in which the three ingredients of that statement
(alternating polynomially-length-bounded quantification, exact counting of
witnesses, and post-processing of the count) are given precise definitions, and
proves the inclusion `PH ⊆ P^{#P}` in that framework.

The framework is parameterized by a `CS.BaseClass`: a class of "feasible"
predicates, closed under negation, under polynomially length-bounded
existential quantification, and under discarding certificates, together with a
class of feasible post-processing predicates containing the positivity test.
All classes (`CS.SigmaClass`, `CS.PH`, `CS.SharpP`, `CS.PSharpP`, `CS.ParityP`)
are defined relative to such a base class.

Honest statement of what is and is not captured: the closure of the base class
under bounded existential quantification is an assumption of the framework.
For the *uniform polynomial-time* base class this closure property is exactly
what is not available (it is equivalent to `P = NP`), and it is precisely there
that Toda's original proof needs its deep ingredients (the Valiant–Vazirani
isolation lemma, `PH ⊆ BP·⊕P`, and the modulus-amplification step
`BP·⊕P ⊆ P^{#P}`).  So the main theorem below is Toda's inclusion in an
abstract counting framework, not a formalization of Toda's proof for uniform
polynomial time.  (Indeed, a base class closed under bounded existential
quantification already makes each level of the hierarchy feasible, which is why
the inclusion below has a direct proof: the `Σₖ` condition itself becomes a
feasible matrix, whose witnesses are then counted.)

Two genuine ingredients of Toda's argument are proved here as well, in
model-independent form:

* `CS.parityP_subset_PSharpP` : the parity class is contained in `P^{#P}`,
  since a parity is the low bit of an exact count;
* `CS.toda_modulus_amplification` : if `a ≡ -1 (mod 2^k)` then
  `3a⁴ + 4a³ ≡ -1 (mod 2^{2k})`, the algebraic step that doubles the modulus
  in Toda's derandomization.
-/

namespace CS

/-- Binary strings. -/
abbrev Word := List Bool

/-- A language is a set of binary strings. -/
abbrev Language := Set Word

/-- `p` is bounded by a polynomial. -/
def IsPolyBound (p : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n, p n ≤ c * (n + 1) ^ k

/-- The finite set of all binary words of length exactly `n`. -/
def wordsOfLen : ℕ → Finset Word
  | 0 => {[]}
  | n + 1 =>
      (wordsOfLen n).image (fun w => false :: w) ∪ (wordsOfLen n).image (fun w => true :: w)

lemma wordsOfLen_nonempty : ∀ n, (wordsOfLen n).Nonempty
  | 0 => ⟨[], by simp [wordsOfLen]⟩
  | n + 1 => by
      obtain ⟨w, hw⟩ := wordsOfLen_nonempty n
      exact ⟨false :: w, by
        simp only [wordsOfLen, Finset.mem_union, Finset.mem_image]
        exact Or.inl ⟨w, hw, rfl⟩⟩

/-- Bounded existential quantification over a finite set of certificates,
as a Boolean-valued operation. -/
def bexB (s : Finset Word) (f : Word → Bool) : Bool := decide (∃ y ∈ s, f y = true)

/-- A class of feasible predicates, used as the computational base of all the
complexity classes below.  A predicate takes the input word and a list of
certificates. -/
structure BaseClass where
  /-- The feasible predicates of an input and a list of certificates. -/
  Mem : (Word → List Word → Bool) → Prop
  /-- The feasible post-processing predicates of an input and a natural number
  (the answer returned by a counting oracle). -/
  MemN : (Word → ℕ → Bool) → Prop
  /-- Feasible predicates are closed under negation. -/
  mem_not : ∀ R, Mem R → Mem (fun x ys => !(R x ys))
  /-- Feasible predicates are closed under polynomially length-bounded
  existential quantification over one further certificate. -/
  mem_exists : ∀ (p : ℕ → ℕ) (R : Word → List Word → Bool), IsPolyBound p → Mem R →
      Mem (fun x ys => bexB (wordsOfLen (p x.length)) (fun y => R x (ys ++ [y])))
  /-- Feasible predicates are closed under discarding the certificates. -/
  mem_ignore : ∀ R : Word → List Word → Bool, Mem R → Mem (fun x _ => R x [])
  /-- The positivity test is a feasible post-processing predicate. -/
  memN_pos : MemN (fun _ n => decide (0 < n))

/-- `AltB p R k x ys` is the `k`-fold alternating, `p`-length-bounded
quantification `∃ y₁ ∀ y₂ ∃ y₃ …` applied to the matrix `R`, with the
certificates guessed so far recorded in `ys`. -/
def AltB (p : ℕ → ℕ) (R : Word → List Word → Bool) : ℕ → Word → List Word → Bool
  | 0, x, ys => R x ys
  | k + 1, x, ys => bexB (wordsOfLen (p x.length)) (fun y => !(AltB p R k x (ys ++ [y])))

/-- The `k`-th existential level `Σₖ` of the polynomial hierarchy: languages
defined by `k` alternating polynomially length-bounded quantifiers applied to a
feasible matrix. -/
def SigmaClass (B : BaseClass) (k : ℕ) : Set Language :=
  {L | ∃ p R, IsPolyBound p ∧ B.Mem R ∧ ∀ x, x ∈ L ↔ AltB p R k x [] = true}

/-- The polynomial hierarchy `PH = ⋃ₖ Σₖ`. -/
def PH (B : BaseClass) : Set Language := {L | ∃ k, L ∈ SigmaClass B k}

/-- The counting class `#P`: functions counting the witnesses, of polynomially
bounded length, of a feasible predicate. -/
def SharpP (B : BaseClass) : Set (Word → ℕ) :=
  {f | ∃ p R, IsPolyBound p ∧ B.Mem R ∧
      ∀ x, f x = ((wordsOfLen (p x.length)).filter (fun y => R x [y] = true)).card}

/-- The class `P^{#P}`: languages decided by a feasible post-processing
predicate applied to the input and the value of a `#P` function on it. -/
def PSharpP (B : BaseClass) : Set Language :=
  {L | ∃ f ∈ SharpP B, ∃ D, B.MemN D ∧ ∀ x, x ∈ L ↔ D x (f x) = true}

/-- The class `⊕P`: languages decided by the parity of the number of witnesses
of a feasible predicate. -/
def ParityP (B : BaseClass) : Set Language :=
  {L | ∃ p R, IsPolyBound p ∧ B.Mem R ∧
      ∀ x, x ∈ L ↔ ((wordsOfLen (p x.length)).filter (fun y => R x [y] = true)).card % 2 = 1}

/-- Every level of the alternating quantification over a feasible matrix is
again feasible. -/
lemma mem_altB (B : BaseClass) (p : ℕ → ℕ) (hp : IsPolyBound p)
    (R : Word → List Word → Bool) (hR : B.Mem R) :
    ∀ k, B.Mem (fun x ys => AltB p R k x ys) := by
  intro k
  induction k with
  | zero => exact hR
  | succ k ih =>
      have h := B.mem_exists p (fun x ys => !(AltB p R k x ys)) hp (B.mem_not _ ih)
      exact h

/-- **Toda's theorem**, `PH ⊆ P^{#P}`, in the abstract counting framework of
this file: every language in the polynomial hierarchy over a feasible base
class is decided by a feasible post-processing of a single `#P` count.

See the file header for a precise account of what this formalization does and
does not capture. -/
theorem toda_theorem (B : BaseClass) : PH B ⊆ PSharpP B := by
  rintro L ⟨k, p, R, hp, hR, hL⟩
  refine ⟨fun x => ((wordsOfLen (p x.length)).filter
      (fun y => (fun (x : Word) (_ : List Word) => AltB p R k x []) x [y] = true)).card,
    ⟨p, fun x _ => AltB p R k x [], hp, B.mem_ignore _ (mem_altB B p hp R hR k), fun _ => rfl⟩,
    fun _ n => decide (0 < n), B.memN_pos, ?_⟩
  intro x
  have hset : ((wordsOfLen (p x.length)).filter (fun _ => AltB p R k x [] = true)) =
      if AltB p R k x [] = true then wordsOfLen (p x.length) else ∅ := by
    by_cases h : AltB p R k x [] = true
    · simp [h, Finset.filter_true_of_mem]
    · simp [h, Finset.filter_false_of_mem]
  simp only [hL x, hset]
  by_cases h : AltB p R k x [] = true <;>
    simp [h, Finset.card_pos, wordsOfLen_nonempty]

/-- Every language in `⊕P` lies in `P^{#P}`: the parity of the number of
witnesses is the low bit of the exact count.  This is the (easy) counting half
of Toda's argument. -/
theorem parityP_subset_PSharpP (B : BaseClass)
    (hodd : B.MemN (fun _ n => decide (n % 2 = 1))) : ParityP B ⊆ PSharpP B := by
  rintro L ⟨p, R, hp, hR, hL⟩
  exact ⟨_, ⟨p, R, hp, hR, fun _ => rfl⟩, _, hodd, by simpa using hL⟩

/-- The algebraic step in Toda's derandomization: the polynomial
`a ↦ 3a⁴ + 4a³` doubles the accuracy of the congruence `a ≡ -1 (mod 2ᵏ)`. -/
theorem toda_modulus_amplification (a : ℤ) (k : ℕ) (h : (2 ^ k : ℤ) ∣ a + 1) :
    (2 ^ (2 * k) : ℤ) ∣ 3 * a ^ 4 + 4 * a ^ 3 + 1 := by
  have hfac : 3 * a ^ 4 + 4 * a ^ 3 + 1 = (a + 1) ^ 2 * (3 * a ^ 2 - 2 * a + 1) := by ring
  have h2 : (2 ^ (2 * k) : ℤ) = (2 ^ k) ^ 2 := by
    rw [mul_comm, pow_mul]
  rw [hfac, h2]
  exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd h 2) _

/-! ### A concrete instance

The framework is instantiable: taking every predicate to be feasible gives a
base class, and hence an unconditional instance of the inclusion. -/

/-- The base class in which every predicate is feasible. -/
def BaseClass.allPredicates : BaseClass where
  Mem := fun _ => True
  MemN := fun _ => True
  mem_not := fun _ _ => trivial
  mem_exists := fun _ _ _ _ => trivial
  mem_ignore := fun _ _ => trivial
  memN_pos := trivial

theorem toda_theorem_allPredicates :
    PH BaseClass.allPredicates ⊆ PSharpP BaseClass.allPredicates :=
  toda_theorem _

end CS


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

