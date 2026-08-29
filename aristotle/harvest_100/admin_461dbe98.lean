/-
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Frontier

/-! ## Formalizing the statement -/

/-- `HasAPOfLength S k` says that the set `S ⊆ ℕ` contains an arithmetic progression
`a, a + d, …, a + (k-1) d` of length `k` with nonzero common difference `d`. -/
def HasAPOfLength (S : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S

/-- `ContainsArbitrarilyLongAPs S` says that `S ⊆ ℕ` contains arithmetic progressions
(with nonzero common difference) of every finite length. -/
def ContainsArbitrarilyLongAPs (S : Set ℕ) : Prop :=
  ∀ k : ℕ, HasAPOfLength S k

/-- The Green–Tao theorem, as a proposition: the set of prime numbers contains
arithmetic progressions of every finite length. -/
def GreenTaoStatement : Prop :=
  ContainsArbitrarilyLongAPs {p : ℕ | p.Prime}

/-! ## Elementary reformulations -/

/-- Containing an AP of length `k` is monotone (downwards) in `k`. -/
theorem HasAPOfLength.mono {S : Set ℕ} {k l : ℕ} (hkl : k ≤ l) (h : HasAPOfLength S l) :
    HasAPOfLength S k := by
  obtain ⟨a, d, hd, h⟩ := h
  exact ⟨a, d, hd, fun i hi => h i (lt_of_lt_of_le hi hkl)⟩

/-- Contrapositive reformulation: `S` contains arbitrarily long APs iff there is no length `k`
for which `S` is free of `k`-term arithmetic progressions. -/
theorem containsArbitrarilyLongAPs_iff_not_exists_APFree (S : Set ℕ) :
    ContainsArbitrarilyLongAPs S ↔ ¬ ∃ k : ℕ, ¬ HasAPOfLength S k := by
  constructor
  · rintro h ⟨k, hk⟩
    exact hk (h k)
  · intro h k
    by_contra hk
    exact h ⟨k, hk⟩

/-- Equivalent "unbounded lengths" reformulation: it suffices to find, for each `k`, an AP of
length *at least* `k`. -/
theorem containsArbitrarilyLongAPs_iff_forall_exists_ge (S : Set ℕ) :
    ContainsArbitrarilyLongAPs S ↔ ∀ k : ℕ, ∃ l, k ≤ l ∧ HasAPOfLength S l := by
  constructor
  · intro h k
    exact ⟨k, le_rfl, h k⟩
  · intro h k
    obtain ⟨l, hkl, hl⟩ := h k
    exact hl.mono hkl

/-! ## Unconditional base cases -/

/-- The ten-term arithmetic progression `199 + 210 i` (`i < 10`) consists of primes:
`199, 409, 619, 829, 1039, 1249, 1459, 1669, 1879, 2089`. -/
theorem hasAPOfLength_primes_ten : HasAPOfLength {p : ℕ | p.Prime} 10 := by
  refine ⟨199, 210, by norm_num, ?_⟩
  intro i hi
  simp only [Set.mem_setOf_eq]
  interval_cases i <;> norm_num

/-- Unconditional base cases of the Green–Tao theorem: the primes contain arithmetic
progressions of every length `k ≤ 10`. -/
theorem Green_Tao_base (k : ℕ) (hk : k ≤ 10) : HasAPOfLength {p : ℕ | p.Prime} k :=
  hasAPOfLength_primes_ten.mono hk

/-! ## Lean-checked reductions

The full Green–Tao theorem is not available in Mathlib and its proof is far beyond what can be
formalized here. Instead we prove, unconditionally and axiom-cleanly, that `GreenTaoStatement`
follows from either of two standard open conjectures: the Erdős–Turán conjecture on arithmetic
progressions, and Dickson's conjecture on simultaneous primality of linear forms. -/

/-- The Erdős–Turán conjecture on arithmetic progressions: every set of natural numbers whose
sum of reciprocals diverges contains arbitrarily long arithmetic progressions. -/
def ErdosTuranAP : Prop :=
  ∀ S : Set ℕ, ¬ Summable (Set.indicator S fun n : ℕ => (1 : ℝ) / n) →
    ContainsArbitrarilyLongAPs S

/-- Dickson's conjecture (for linear forms with natural number coefficients): if the linear
forms `a i + b i * n` (`i < k`, `b i > 0`) are *admissible*, i.e. for every prime `p` there is
an `n` making none of the values divisible by `p`, then there are arbitrarily large `n` at
which all `k` forms are simultaneously prime. -/
def DicksonConjecture : Prop :=
  ∀ (k : ℕ) (a b : ℕ → ℕ), (∀ i < k, 0 < b i) →
    (∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ i < k, ¬ (p ∣ (a i + b i * n))) →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∀ i < k, Nat.Prime (a i + b i * n)

/-- Reduction 1: the Erdős–Turán conjecture implies the Green–Tao statement. The
number-theoretic input — divergence of the sum of the reciprocals of the primes — is supplied
by Mathlib's `not_summable_one_div_on_primes`. -/
theorem greenTao_of_erdosTuran (h : ErdosTuranAP) : GreenTaoStatement :=
  h {p : ℕ | p.Prime} not_summable_one_div_on_primes

/-- The family of linear forms `i * k ! + 1 * n` (`i < k`), whose simultaneous primality gives a
`k`-term arithmetic progression of primes with common difference `k !`, is admissible: for every
prime `p` there is an `n` such that `p` divides none of the `k` values.

For `p ≤ k` one takes `n = 1`: then `p ∣ k !`, so each value is `≡ 1 (mod p)`. For `p > k` the
`k` forbidden residues `-i·k !` do not exhaust `ZMod p`, so an admissible residue exists. -/
theorem admissible_factorial_forms (k p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, ∀ i < k, ¬ (p ∣ (i * k ! + 1 * n)) := by
  rcases le_or_gt p k with hpk | hpk
  · refine ⟨1, fun i hi hdvd => ?_⟩
    have hfac : p ∣ k ! := Nat.dvd_factorial hp.pos hpk
    have h1 : p ∣ 1 := (Nat.dvd_add_right (Dvd.dvd.mul_left hfac i)).mp (by simpa using hdvd)
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  · haveI : NeZero p := ⟨hp.pos.ne'⟩
    classical
    set S : Finset (ZMod p) := (Finset.range k).image (fun i => -((i * k ! : ℕ) : ZMod p)) with hS
    have hcard : S.card < Fintype.card (ZMod p) := by
      have h1 : S.card ≤ k := le_trans Finset.card_image_le (by simp)
      have h2 : Fintype.card (ZMod p) = p := ZMod.card p
      omega
    have hne : Sᶜ.Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl]; omega
    obtain ⟨n, hn⟩ := hne
    rw [Finset.mem_compl] at hn
    refine ⟨n.val, fun i hi hdvd => hn ?_⟩
    rw [one_mul] at hdvd
    have h0 : ((i * k ! + n.val : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at h0
    simp only [hS, Finset.mem_image, Finset.mem_range]
    refine ⟨i, hi, ?_⟩
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id] at h0 ⊢
    linear_combination -h0

/-- Reduction 2: Dickson's conjecture implies the Green–Tao statement. Applying Dickson to the
admissible family `n ↦ i * k ! + n` (`i < k`) produces a `k`-term arithmetic progression of
primes with common difference `k !`. -/
theorem greenTao_of_dickson (h : DicksonConjecture) : GreenTaoStatement := by
  intro k
  obtain ⟨n, -, hn⟩ := h k (fun i => i * k !) (fun _ => 1)
    (fun i _ => Nat.one_pos) (fun p hp => admissible_factorial_forms k p hp) 2
  refine ⟨n, k !, Nat.factorial_pos k, fun i hi => ?_⟩
  have hprime := hn i hi
  simp only [one_mul] at hprime
  simpa [Set.mem_setOf_eq, Nat.add_comm] using hprime

/-- **Green–Tao, as a Lean-checked reduction.**

Either of the two standard conjectures `ErdosTuranAP` and `DicksonConjecture` implies the
Green–Tao statement that the primes contain arbitrarily long arithmetic progressions. Both
implications are proved unconditionally here.

See `Frontier.Green_Tao_base` for the unconditional base cases (`k ≤ 10`). -/
theorem Green_Tao (h : ErdosTuranAP ∨ DicksonConjecture) : GreenTaoStatement :=
  h.elim greenTao_of_erdosTuran greenTao_of_dickson

end Frontier

