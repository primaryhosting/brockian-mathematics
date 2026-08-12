/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Statement: Deutsch–Jozsa decides constant-vs-balanced with one query.
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Setup

We model the Deutsch–Jozsa algorithm on `n` qubits with real amplitudes (the algorithm
never leaves the real subspace of the state space).

* Computational basis states of the query register are bit strings `x : Fin n → Bool`.
* `sgn b = (-1)^b` is the phase produced by the phase-kickback oracle.
* `chi x y = (-1)^(x ⬝ y)` is the Walsh character, i.e. the matrix entry of the
  `n`-fold Hadamard transform (up to the global normalisation `2^(n/2)`).

The algorithm is: prepare the uniform superposition `2^(-n/2) ∑ x, |x⟩`, apply the
oracle **once** (this is the only place where `f` is used), obtaining
`2^(-n/2) ∑ x, (-1)^(f x) |x⟩`, apply the Hadamard transform again, and measure.
The resulting amplitude on the basis state `y` is `djAmp f y`, and the probability of
observing `y` is `djProb f y`.
-/

/-- The phase `(-1)^b`. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

/-- The Walsh character `(-1)^(x ⬝ y)` where `x ⬝ y = ∑ i, x i * y i` mod 2. -/
def chi {n : ℕ} (x y : Fin n → Bool) : ℝ := ∏ i, sgn (x i && y i)

/-- The amplitude of the basis state `y` at the end of the Deutsch–Jozsa algorithm:
Hadamard, one oracle query, Hadamard. -/
noncomputable def djAmp {n : ℕ} (f : (Fin n → Bool) → Bool) (y : Fin n → Bool) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x : Fin n → Bool, chi x y * sgn (f x)

/-- The probability of observing the basis state `y` at the end of the algorithm. -/
noncomputable def djProb {n : ℕ} (f : (Fin n → Bool) → Bool) (y : Fin n → Bool) : ℝ :=
  (djAmp f y) ^ 2

/-- `f` is constant. -/
def IsConstant {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop := ∃ c : Bool, ∀ x, f x = c

/-- `f` is balanced: exactly half of the `2^n` inputs are mapped to `true`. -/
def IsBalanced {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  2 * ({x : Fin n → Bool | f x = true} : Finset (Fin n → Bool)).card = 2 ^ n

/-! ## Basic facts -/

lemma sgn_sq (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> norm_num [sgn]

lemma sgn_ne_zero (b : Bool) : sgn b ≠ 0 := by
  cases b <;> norm_num [sgn]

lemma abs_sgn (b : Bool) : |sgn b| = 1 := by
  cases b <;> norm_num [sgn]

lemma chi_zero {n : ℕ} (x : Fin n → Bool) : chi x (fun _ => false) = 1 := by
  simp [chi, sgn]

lemma card_bool_pow (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

/-- Orthogonality of the Walsh characters. -/
lemma sum_chi_mul_chi {n : ℕ} (x x' : Fin n → Bool) :
    ∑ y : Fin n → Bool, chi x y * chi x' y = if x = x' then (2 : ℝ) ^ n else 0 := by
  have h1 : ∀ y : Fin n → Bool,
      chi x y * chi x' y = ∏ i, (sgn (x i && y i) * sgn (x' i && y i)) := by
    intro y
    rw [chi, chi, ← Finset.prod_mul_distrib]
  have h2 : ∑ y : Fin n → Bool, ∏ i, (sgn (x i && y i) * sgn (x' i && y i))
      = ∏ i, ∑ b : Bool, (sgn (x i && b) * sgn (x' i && b)) := by
    rw [Finset.prod_univ_sum]
    exact (Fintype.sum_equiv (Equiv.refl _) _ _ (fun y => rfl)).symm
  have h3 : ∀ i : Fin n, (∑ b : Bool, (sgn (x i && b) * sgn (x' i && b)))
      = if x i = x' i then (2 : ℝ) else 0 := by
    intro i
    rcases hx : x i with _ | _ <;> rcases hx' : x' i with _ | _ <;>
      norm_num [sgn]
  simp only [h1, h2, h3]
  by_cases hxx : x = x'
  · subst hxx
    simp
  · rw [if_neg hxx]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-! ## The circuit: Hadamard, one oracle query, Hadamard -/

/-- The `n`-fold Hadamard transform acting on real amplitude vectors. -/
noncomputable def hadamard {n : ℕ} (psi : (Fin n → Bool) → ℝ) : (Fin n → Bool) → ℝ :=
  fun y => (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * ∑ x : Fin n → Bool, chi x y * psi x

/-- The phase oracle for `f`, i.e. the standard oracle `|x, b⟩ ↦ |x, b ⊕ f x⟩` with the
target qubit prepared in the state `|-⟩` (phase kickback).  This is the *only* place
where `f` is used, and it is applied exactly once in the circuit below. -/
def oracle {n : ℕ} (f : (Fin n → Bool) → Bool) (psi : (Fin n → Bool) → ℝ) :
    (Fin n → Bool) → ℝ := fun x => sgn (f x) * psi x

/-- The initial state `|0…0⟩`. -/
def initState {n : ℕ} : (Fin n → Bool) → ℝ := fun x => if x = (fun _ => false) then 1 else 0

lemma chi_zero_left {n : ℕ} (y : Fin n → Bool) : chi (fun _ => false) y = 1 := by
  simp [chi, sgn]

/-- The Deutsch–Jozsa amplitudes are exactly those produced by the circuit
`H^{⊗n}` → one oracle query → `H^{⊗n}` applied to `|0…0⟩`. -/
theorem djAmp_eq_circuit {n : ℕ} (f : (Fin n → Bool) → Bool) :
    djAmp f = hadamard (oracle f (hadamard (initState : (Fin n → Bool) → ℝ))) := by
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
  have hs : Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt ((2 : ℝ) ^ n) = (2 : ℝ) ^ n :=
    Real.mul_self_sqrt hnn
  funext y
  have hstep1 : hadamard (initState : (Fin n → Bool) → ℝ)
      = fun _ : Fin n → Bool => (Real.sqrt ((2 : ℝ) ^ n))⁻¹ := by
    funext z
    rw [hadamard]
    rw [Finset.sum_eq_single (fun _ => false)]
    · simp [initState, chi_zero_left]
    · intro b _ hb
      simp [initState, hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hstep1]
  simp only [oracle, hadamard, djAmp]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have : ((2 : ℝ) ^ n)⁻¹
      = (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * (Real.sqrt ((2 : ℝ) ^ n))⁻¹ := by
    rw [← mul_inv, hs]
  rw [this]
  ring

/-! ## The amplitude at the all-zero outcome -/

lemma djAmp_zero {n : ℕ} (f : (Fin n → Bool) → Bool) :
    djAmp f (fun _ => false) = ((2 : ℝ) ^ n)⁻¹ * ∑ x : Fin n → Bool, sgn (f x) := by
  simp [djAmp, chi_zero]

/-- For a constant function, the all-zero outcome has amplitude `±1`. -/
lemma djAmp_zero_of_constant {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : IsConstant f) :
    |djAmp f (fun _ => false)| = 1 := by
  obtain ⟨c, hc⟩ := hf
  have hpow : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  have : djAmp f (fun _ => false) = sgn c := by
    rw [djAmp_zero]
    simp only [hc, Finset.sum_const, Finset.card_univ, card_bool_pow, nsmul_eq_mul]
    field_simp
    push_cast
    ring
  rw [this, abs_sgn]

/-- For a balanced function, the all-zero outcome has amplitude `0`. -/
lemma djAmp_zero_of_balanced {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : IsBalanced f) :
    djAmp f (fun _ => false) = 0 := by
  classical
  rw [djAmp_zero]
  set T : Finset (Fin n → Bool) := {x : Fin n → Bool | f x = true} with hT
  have hsplit : ∑ x : Fin n → Bool, sgn (f x)
      = ∑ x ∈ T, sgn (f x) + ∑ x ∈ Tᶜ, sgn (f x) := by
    rw [Finset.sum_add_sum_compl]
  have hT1 : ∀ x ∈ T, sgn (f x) = (-1 : ℝ) := by
    intro x hx
    have : f x = true := by simpa [hT] using hx
    simp [this, sgn]
  have hT2 : ∀ x ∈ Tᶜ, sgn (f x) = (1 : ℝ) := by
    intro x hx
    have hx' : x ∉ T := Finset.mem_compl.mp hx
    have : f x = false := by simpa [hT, Bool.not_eq_true] using hx'
    simp [this, sgn]
  have h1 : ∑ x ∈ T, sgn (f x) = -(T.card : ℝ) := by
    rw [Finset.sum_congr rfl hT1, Finset.sum_const]
    simp
  have h2 : ∑ x ∈ Tᶜ, sgn (f x) = (Tᶜ.card : ℝ) := by
    rw [Finset.sum_congr rfl hT2, Finset.sum_const]
    simp
  have hcard : (Tᶜ.card : ℝ) = (T.card : ℝ) := by
    have hc : Tᶜ.card = Fintype.card (Fin n → Bool) - T.card := Finset.card_compl T
    have hle : T.card ≤ Fintype.card (Fin n → Bool) := Finset.card_le_univ T
    have h2n : 2 * T.card = 2 ^ n := hf
    have : Tᶜ.card = T.card := by
      rw [hc, card_bool_pow]
      omega
    rw [this]
  rw [hsplit, h1, h2, hcard]
  ring

/-! ## Normalisation: the probabilities sum to `1` -/

lemma sq_sum_expand {n : ℕ} (f : (Fin n → Bool) → Bool) (y : Fin n → Bool) :
    (∑ x : Fin n → Bool, chi x y * sgn (f x)) ^ 2
      = ∑ x : Fin n → Bool, ∑ x' : Fin n → Bool,
          (sgn (f x) * sgn (f x')) * (chi x y * chi x' y) := by
  rw [sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => by ring

/-- The Deutsch–Jozsa output distribution is a genuine probability distribution. -/
theorem djProb_sum_eq_one {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∑ y : Fin n → Bool, djProb f y = 1 := by
  classical
  have hpow : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  have step1 : ∀ y : Fin n → Bool, djProb f y
      = (((2 : ℝ) ^ n)⁻¹) ^ 2 * ∑ x : Fin n → Bool, ∑ x' : Fin n → Bool,
          (sgn (f x) * sgn (f x')) * (chi x y * chi x' y) := by
    intro y
    rw [djProb, djAmp, mul_pow, sq_sum_expand]
  have swap : ∑ y : Fin n → Bool, ∑ x : Fin n → Bool, ∑ x' : Fin n → Bool,
        (sgn (f x) * sgn (f x')) * (chi x y * chi x' y)
      = ∑ x : Fin n → Bool, ∑ x' : Fin n → Bool, ∑ y : Fin n → Bool,
        (sgn (f x) * sgn (f x')) * (chi x y * chi x' y) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  have inner : ∀ x x' : Fin n → Bool,
      (∑ y : Fin n → Bool, (sgn (f x) * sgn (f x')) * (chi x y * chi x' y))
        = (sgn (f x) * sgn (f x')) * (if x = x' then (2 : ℝ) ^ n else 0) := by
    intro x x'
    rw [← Finset.mul_sum, sum_chi_mul_chi]
  have inner2 : ∀ x : Fin n → Bool,
      (∑ x' : Fin n → Bool, (sgn (f x) * sgn (f x')) * (if x = x' then (2 : ℝ) ^ n else 0))
        = (2 : ℝ) ^ n := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp [sgn_sq]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ x) h
  simp only [step1]
  rw [← Finset.mul_sum, swap]
  simp only [inner, inner2]
  rw [Finset.sum_const, Finset.card_univ, card_bool_pow, nsmul_eq_mul]
  field_simp
  push_cast
  ring

/-! ## Balanced and constant are mutually exclusive -/

lemma not_isBalanced_of_isConstant {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hc : IsConstant f) : ¬ IsBalanced f := by
  intro hb
  have h0 := djAmp_zero_of_constant hc
  rw [djAmp_zero_of_balanced hb] at h0
  norm_num at h0

/-! ## Main theorem -/

/-- **Deutsch–Jozsa.** For a function `f : (Fin n → Bool) → Bool` promised to be either
constant or balanced, the Deutsch–Jozsa circuit — which uses exactly **one** query to the
oracle for `f` (see `djAmp`) — decides which is the case: the probability of measuring the
all-zero bit string is `1` exactly when `f` is constant, and `0` exactly when `f` is
balanced. -/
theorem deutsch_jozsa {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hf : IsConstant f ∨ IsBalanced f) :
    (djProb f (fun _ => false) = 1 ↔ IsConstant f) ∧
    (djProb f (fun _ => false) = 0 ↔ IsBalanced f) := by
  rcases hf with hc | hb
  · have h1 : djProb f (fun _ => false) = 1 := by
      have := djAmp_zero_of_constant hc
      rw [djProb, ← sq_abs, this]
      norm_num
    refine ⟨⟨fun _ => hc, fun _ => h1⟩, ⟨fun h => by rw [h1] at h; norm_num at h, fun h =>
      absurd h (not_isBalanced_of_isConstant hc)⟩⟩
  · have h0 : djProb f (fun _ => false) = 0 := by
      rw [djProb, djAmp_zero_of_balanced hb]; norm_num
    refine ⟨⟨fun h => by rw [h0] at h; norm_num at h, fun h =>
      absurd hb (not_isBalanced_of_isConstant h)⟩, ⟨fun _ => hb, fun _ => h0⟩⟩

#print axioms QI.deutsch_jozsa
#print axioms QI.djProb_sum_eq_one
#print axioms QI.djAmp_eq_circuit

end QI

