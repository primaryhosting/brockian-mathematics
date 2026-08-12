import Mathlib
import RequestProject.QI.Spanning
import RequestProject.QI.Classical

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/--
**Simon's problem is solved with `O(n)` quantum queries but needs `Ω(2 ^ (n / 2))`
classical queries.**

The four conjuncts are:

1. *One quantum query.*  For every Simon function `f` with secret `s`, one run of the
   circuit `H ∘ U_f ∘ H` applied to `|0,0⟩` — which uses exactly one oracle query — yields
   a measurement outcome that is uniformly distributed over the hyperplane
   `s^⊥ = {y | ⟪y, s⟫ = 0}` (probability `2 / 2 ^ n` on it, `0` off it).

2. *`m` quantum queries.*  With `m` runs of the circuit (`m` queries in total), the
   outcomes determine `s` uniquely — i.e. `s` is the only nonzero solution of the linear
   system they define, so Gaussian elimination recovers it — with probability at least
   `1 - 2 ^ n / 2 ^ m`.

3. *`O(n)` queries suffice.*  Taking `m = 2 n` queries, the algorithm succeeds with
   probability at least `1 - 2 ^ (-n)`.

4. *Classical lower bound.*  Any deterministic classical query algorithm (decision tree)
   that outputs the correct secret for every Simon function on `n ≥ 2` bits has depth at
   least `2 ^ (n / 2)`, i.e. makes `Ω(2 ^ (n / 2))` queries in the worst case.
-/
theorem simon_algorithm :
    (∀ (n : ℕ) (f : V n → V n) (s : V n), IsSimon f s →
        ∀ y : V n, simonProb f y = if dot y s = 0 then 2 / 2 ^ n else 0) ∧
    (∀ (n m : ℕ) (f : V n → V n) (s : V n), IsSimon f s →
        1 - 2 ^ n / 2 ^ m ≤ simonSuccess f m s) ∧
    (∀ (n : ℕ) (f : V n → V n) (s : V n), IsSimon f s →
        1 - (1 / 2 : ℝ) ^ n ≤ simonSuccess f (2 * n) s) ∧
    (∀ (n : ℕ), 2 ≤ n → ∀ t : DTree n,
        (∀ (f : V n → V n) (s : V n), IsSimon f s → t.run f = s) →
        2 ^ (n / 2) ≤ t.depth) :=
  ⟨fun _ _ _ h y => simonProb_eq h y,
   fun _ m _ _ h => simon_success_bound h m,
   fun _ _ _ h => simon_success_two_n h,
   fun _ hn t hc => simon_classical_lower_bound hn t hc⟩

end QI

import RequestProject.QI.Basic

/-!
# Simon's quantum algorithm: one query

We model the two-register quantum state space `V n × V n → ℂ` (query register tensored
with answer register), the Hadamard transform `had` on the first register, and the
standard (phase-free) oracle `orac f : |x, b⟩ ↦ |x, b ⊕ f x⟩`, which is the *single*
query to `f` made by the circuit.

The Simon circuit is `H ∘ U_f ∘ H` applied to `|0, 0⟩`; `simonProb f y` is the
probability of observing `y` in the first register.  The main result
`simonProb_eq` says that for a Simon function with secret `s` the outcome is uniformly
distributed on the hyperplane `s^⊥`.
-/

namespace QI

set_option autoImplicit false

/-- The Hadamard transform `H^{⊗ n}` acting on the first (query) register. -/
noncomputable def had {n : ℕ} (psi : V n × V n → ℂ) : V n × V n → ℂ :=
  fun p => ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * ∑ x : V n, (chi (dot x p.1) : ℂ) * psi (x, p.2)

/-- The standard quantum oracle for `f`, `|x, b⟩ ↦ |x, b ⊕ f x⟩`. -/
def orac {n : ℕ} (f : V n → V n) (psi : V n × V n → ℂ) : V n × V n → ℂ :=
  fun p => psi (p.1, p.2 + f p.1)

/-- The initial state `|0, 0⟩`. -/
def initState {n : ℕ} : V n × V n → ℂ := fun p => if p = (0, 0) then 1 else 0

/-- The state produced by Simon's circuit: `H ∘ U_f ∘ H` applied to `|0,0⟩`.
It uses exactly one query to `f`. -/
noncomputable def simonState {n : ℕ} (f : V n → V n) : V n × V n → ℂ :=
  had (orac f (had (initState)))

/-- The probability of observing `y` in the query register. -/
noncomputable def simonProb {n : ℕ} (f : V n → V n) (y : V n) : ℝ :=
  ∑ b : V n, ‖simonState f (y, b)‖ ^ 2

/-- The real amplitude of the final state. -/
noncomputable def simonAmp {n : ℕ} (f : V n → V n) (y b : V n) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x : V n, chi (dot x y) * (if f x = b then (1 : ℝ) else 0)

lemma sqrt_two_pow_inv_sq (n : ℕ) :
    (((Real.sqrt (2 ^ n) : ℝ) : ℂ))⁻¹ * (((Real.sqrt (2 ^ n) : ℝ) : ℂ))⁻¹
      = ((2 : ℂ) ^ n)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast
  ring

lemma add_eq_zero_iff_V {n : ℕ} (a b : V n) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun z => z + b) h
    simpa [add_add_cancel_V] using this
  · rintro rfl; exact add_self_V _

/-- The state after the first Hadamard layer. -/
lemma had_init {n : ℕ} (p : V n × V n) :
    had (initState) p = ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * (if p.2 = 0 then 1 else 0) := by
  unfold had initState
  congr 1
  rw [Finset.sum_eq_single (0 : V n)]
  · simp [dot_zero_left, chi_zero, Prod.ext_iff]
  · intro c _ hc; simp [Prod.ext_iff, hc]
  · intro hc; exact absurd (Finset.mem_univ _) hc

/-- The state after the (single) oracle query. -/
lemma orac_had_init {n : ℕ} (f : V n → V n) :
    orac f (had (initState (n := n)))
      = fun p : V n × V n => ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * (if f p.1 = p.2 then 1 else 0) := by
  funext p
  rw [orac, had_init]
  congr 1
  simp [add_eq_zero_iff_V, eq_comm]

/-- The amplitudes of the final state are the real numbers `simonAmp f y b`. -/
lemma simonState_eq {n : ℕ} (f : V n → V n) (y b : V n) :
    simonState f (y, b) = ((simonAmp f y b : ℝ) : ℂ) := by
  rw [simonState, orac_had_init, had]
  simp only [simonAmp]
  push_cast [apply_ite (fun r : ℝ => (r : ℂ))]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  calc ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * ((chi (dot x y) : ℂ) *
        (((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * (if f x = b then 1 else 0)))
      = ((((Real.sqrt (2 ^ n) : ℝ) : ℂ))⁻¹ * (((Real.sqrt (2 ^ n) : ℝ) : ℂ))⁻¹) *
        ((chi (dot x y) : ℂ) * (if f x = b then 1 else 0)) := by ring
    _ = ((2:ℂ)^n)⁻¹ * ((chi (dot x y) : ℂ) * (if f x = b then 1 else 0)) := by
        rw [sqrt_two_pow_inv_sq]

lemma simonProb_eq_sum_sq {n : ℕ} (f : V n → V n) (y : V n) :
    simonProb f y = ∑ b : V n, (simonAmp f y b) ^ 2 := by
  unfold simonProb
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [simonState_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The key interference computation. -/
lemma fiber_sum {n : ℕ} {f : V n → V n} {s : V n} (h : IsSimon f s) (y : V n) :
    ∑ b : V n, (∑ x : V n, chi (dot x y) * (if f x = b then (1 : ℝ) else 0)) ^ 2
      = 2 ^ n * (1 + chi (dot s y)) := by
  obtain ⟨hs, hfib⟩ := h
  have step1 : ∀ b : V n,
      (∑ x : V n, chi (dot x y) * (if f x = b then (1 : ℝ) else 0)) ^ 2
        = ∑ x : V n, ∑ x' : V n,
          (chi (dot x y) * (if f x = b then (1:ℝ) else 0)) *
          (chi (dot x' y) * (if f x' = b then (1:ℝ) else 0)) := by
    intro b
    rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl (fun b _ => step1 b), Finset.sum_comm]
  have step2 : ∀ x : V n, ∑ b : V n, ∑ x' : V n,
      (chi (dot x y) * (if f x = b then (1:ℝ) else 0)) *
      (chi (dot x' y) * (if f x' = b then (1:ℝ) else 0))
      = ∑ x' : V n, chi (dot x y) * chi (dot x' y) * (if f x = f x' then (1:ℝ) else 0) := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [Finset.sum_eq_single (f x)]
    · by_cases hx : f x' = f x
      · simp [hx]
      · simp [hx, Ne.symm hx]
    · intro b _ hb; simp [Ne.symm hb]
    · intro hb; exact absurd (Finset.mem_univ _) hb
  rw [Finset.sum_congr rfl (fun x _ => step2 x)]
  have step3 : ∀ x : V n,
      (∑ x' : V n, chi (dot x y) * chi (dot x' y) * (if f x = f x' then (1:ℝ) else 0))
        = 1 + chi (dot s y) := by
    intro x
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    have hset : (Finset.univ.filter (fun x' : V n => f x = f x')) = {x, x + s} := by
      ext x'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact hfib x x'
    rw [hset, Finset.sum_pair (Ne.symm (add_right_ne_self hs))]
    have h1 : chi (dot x y) * chi (dot x y) = 1 := chi_mul_self _
    have h2 : chi (dot (x + s) y) = chi (dot x y) * chi (dot s y) := by
      rw [dot_add_left, chi_add]
    rw [h2]
    linear_combination (1 + chi (dot s y)) * h1
  rw [Finset.sum_congr rfl (fun x _ => step3 x)]
  simp [Finset.card_univ]
  ring

/-- **Simon's measurement law**: the outcome of one run of the circuit is uniformly
distributed over the hyperplane orthogonal to the secret `s`. -/
theorem simonProb_eq {n : ℕ} {f : V n → V n} {s : V n} (h : IsSimon f s) (y : V n) :
    simonProb f y = if dot y s = 0 then 2 / 2 ^ n else 0 := by
  have hpow : ((2:ℝ) ^ n) ≠ 0 := by positivity
  rw [simonProb_eq_sum_sq]
  have hexp : ∀ b : V n, (simonAmp f y b) ^ 2
      = (((2:ℝ) ^ n)⁻¹) ^ 2 * (∑ x : V n, chi (dot x y) * (if f x = b then (1 : ℝ) else 0)) ^ 2 := by
    intro b; rw [simonAmp, mul_pow]
  rw [Finset.sum_congr rfl (fun b _ => hexp b), ← Finset.mul_sum, fiber_sum h y]
  rw [dot_comm s y]
  by_cases hy : dot y s = 0
  · rw [if_pos hy, hy, chi_zero]
    field_simp
    ring
  · rw [if_neg hy, chi]
    rw [if_neg hy]
    ring

lemma simonProb_nonneg {n : ℕ} (f : V n → V n) (y : V n) : 0 ≤ simonProb f y := by
  apply Finset.sum_nonneg
  intro b _
  positivity

/-- The measurement outcomes form a probability distribution. -/
theorem simonProb_sum {n : ℕ} {f : V n → V n} {s : V n} (h : IsSimon f s) :
    ∑ y : V n, simonProb f y = 1 := by
  have hs := h.1
  have hcard := card_perp s hs
  have hpow : ((2:ℝ) ^ n) ≠ 0 := by positivity
  rw [Finset.sum_congr rfl (fun y _ => simonProb_eq h y)]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have h2 : ((Finset.univ.filter (fun y : V n => dot y s = 0)).card : ℝ) * 2 = 2 ^ n := by
    have h3 : ((2 * (Finset.univ.filter (fun y : V n => dot y s = 0)).card : ℕ) : ℝ)
        = ((2^n : ℕ) : ℝ) := by exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hcard
    push_cast at h3
    linarith
  field_simp
  linarith

end QI

import Mathlib

/-!
# Simon's problem: basic setup

We work with the `n`-bit vector space `V n = Fin n → ZMod 2` (bit strings of length `n`
with XOR as addition), the `ZMod 2`-valued inner product `dot`, and the associated
`±1`-valued character `chi`.

A function `f : V n → V n` *is a Simon function with secret `s`* (`IsSimon f s`) when
`s ≠ 0` and `f x = f y ↔ y = x ∨ y = x + s`; i.e. `f` is two-to-one and its fibers are
the cosets of `{0, s}`.
-/

namespace QI

set_option autoImplicit false

/-- Bit strings of length `n`, an `n`-dimensional vector space over `ZMod 2`. -/
abbrev V (n : ℕ) : Type := Fin n → ZMod 2

/-- The `ZMod 2`-valued inner product on bit strings. -/
def dot {n : ℕ} (x y : V n) : ZMod 2 := ∑ i, x i * y i

/-- The nontrivial character of `ZMod 2`, with values `±1`. -/
def chi (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

/-- `f` is a Simon function with secret `s`: `s ≠ 0` and the fibers of `f` are the
cosets `{x, x + s}`. -/
def IsSimon {n : ℕ} (f : V n → V n) (s : V n) : Prop :=
  s ≠ 0 ∧ ∀ x y : V n, f x = f y ↔ (y = x ∨ y = x + s)

/-! ### Elementary arithmetic in `ZMod 2` and in `V n` -/

lemma zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

lemma add_self_V {n : ℕ} (x : V n) : x + x = 0 := by
  funext i; exact CharTwo.add_self_eq_zero _

lemma add_add_cancel_V {n : ℕ} (x s : V n) : x + s + s = x := by
  rw [add_assoc, add_self_V, add_zero]

lemma add_right_ne_self {n : ℕ} {x s : V n} (hs : s ≠ 0) : x + s ≠ x := by
  intro h
  exact hs (by simpa using h)

/-! ### The character `chi` -/

lemma chi_zero : chi 0 = 1 := by simp [chi]

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  rcases zmod_two_cases a with ha | ha <;> rcases zmod_two_cases b with hb | hb <;>
    subst ha <;> subst hb
  · norm_num [chi]
  · norm_num [chi]
  · norm_num [chi]
  · rw [show (1 + 1 : ZMod 2) = 0 from by decide]; norm_num [chi]

lemma chi_ne_zero (a : ZMod 2) : chi a ≠ 0 := by
  rcases zmod_two_cases a with ha | ha <;> subst ha <;> norm_num [chi]

lemma chi_mul_self (a : ZMod 2) : chi a * chi a = 1 := by
  rcases zmod_two_cases a with ha | ha <;> subst ha <;> norm_num [chi]

/-! ### Bilinearity of `dot` -/

lemma dot_comm {n : ℕ} (x y : V n) : dot x y = dot y x := by
  simp [dot, mul_comm]

lemma dot_add_left {n : ℕ} (x y z : V n) : dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_add_right {n : ℕ} (x y z : V n) : dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_zero_left {n : ℕ} (x : V n) : dot 0 x = 0 := by simp [dot]

lemma dot_zero_right {n : ℕ} (x : V n) : dot x 0 = 0 := by simp [dot]

/-! ### Character sums -/

lemma chi_dot_prod {n : ℕ} (x u : V n) : chi (dot x u) = ∏ i, chi (x i * u i) := by
  unfold dot
  induction (Finset.univ : Finset (Fin n)) using Finset.induction with
  | empty => simp [chi]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

/-- The basic character sum: it vanishes unless `u = 0`. -/
lemma char_sum {n : ℕ} (u : V n) :
    (∑ x : V n, chi (dot x u)) = if u = 0 then (2:ℝ)^n else 0 := by
  have h1 : (∑ x : V n, chi (dot x u)) = ∏ i, (∑ b : ZMod 2, chi (b * u i)) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    exact Finset.sum_congr rfl (fun x _ => chi_dot_prod x u)
  rw [h1]
  by_cases hu : u = 0
  · subst hu
    rw [if_pos rfl]
    simp [chi]
  · rw [if_neg hu]
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hu (funext h)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rcases zmod_two_cases (u i) with h | h
    · exact absurd h hi
    · rw [h, show ((Finset.univ : Finset (ZMod 2))) = {0,1} from by decide]
      norm_num [chi]

/-! ### Counting solutions of linear equations -/

/-- The indicator of `dot y u = 0`, expressed via the character. -/
lemma indicator_eq {n : ℕ} (y u : V n) :
    (if dot y u = 0 then (1:ℝ) else 0) = (1 + chi (dot y u)) / 2 := by
  by_cases h : dot y u = 0 <;> simp [h, chi]

/-- A nonzero linear form on `V n` vanishes on exactly half of the space. -/
lemma card_perp {n : ℕ} (u : V n) (hu : u ≠ 0) :
    2 * (Finset.univ.filter (fun y : V n => dot y u = 0)).card = 2 ^ n := by
  have key : ((Finset.univ.filter (fun y : V n => dot y u = 0)).card : ℝ) * 2 = 2 ^ n := by
    have h1 : ((Finset.univ.filter (fun y : V n => dot y u = 0)).card : ℝ)
        = ∑ y : V n, (if dot y u = 0 then (1:ℝ) else 0) := by
      simp
    rw [h1]
    have h2 : ∑ y : V n, (if dot y u = 0 then (1:ℝ) else 0)
        = (∑ y : V n, (1 + chi (dot y u))) / 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun y _ => indicator_eq y u
    rw [h2, Finset.sum_add_distrib, char_sum u, if_neg hu]
    simp
  have : ((2 * (Finset.univ.filter (fun y : V n => dot y u = 0)).card : ℕ) : ℝ)
      = ((2 ^ n : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

/-- Two distinct nonzero linear forms cut out a subspace of index four. -/
lemma card_perp_two {n : ℕ} (u v : V n) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    4 * (Finset.univ.filter (fun y : V n => dot y u = 0 ∧ dot y v = 0)).card = 2 ^ n := by
  have huv' : u + v ≠ 0 := by
    intro h
    apply huv
    have : u + v + v = 0 + v := by rw [h]
    rwa [add_add_cancel_V, zero_add] at this
  have key : ((Finset.univ.filter (fun y : V n => dot y u = 0 ∧ dot y v = 0)).card : ℝ) * 4
      = 2 ^ n := by
    have h1 : ((Finset.univ.filter (fun y : V n => dot y u = 0 ∧ dot y v = 0)).card : ℝ)
        = ∑ y : V n, ((if dot y u = 0 then (1:ℝ) else 0) * (if dot y v = 0 then (1:ℝ) else 0)) := by
      rw [Finset.sum_congr rfl (fun y _ => by
        by_cases h1 : dot y u = 0 <;> by_cases h2 : dot y v = 0 <;>
          simp [h1, h2] :
        ∀ y ∈ (Finset.univ : Finset (V n)), _ = if (dot y u = 0 ∧ dot y v = 0) then (1:ℝ) else 0)]
      simp
    rw [h1]
    have h2 : ∀ y : V n,
        (if dot y u = 0 then (1:ℝ) else 0) * (if dot y v = 0 then (1:ℝ) else 0)
          = (1 + chi (dot y u) + chi (dot y v) + chi (dot y (u + v))) / 4 := by
      intro y
      rw [indicator_eq, indicator_eq, dot_add_right, chi_add]
      ring
    rw [Finset.sum_congr rfl (fun y _ => h2 y)]
    rw [← Finset.sum_div]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [char_sum u, char_sum v, char_sum (u + v), if_neg hu, if_neg hv, if_neg huv']
    simp
  have : ((4 * (Finset.univ.filter (fun y : V n => dot y u = 0 ∧ dot y v = 0)).card : ℕ) : ℝ)
      = ((2 ^ n : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

end QI

import RequestProject.QI.Quantum

/-!
# Simon's quantum algorithm: `O(n)` queries suffice

Each run of the Simon circuit costs one query and returns a uniformly random element of
`s^⊥`.  A list `v : Fin m → V n` of outcomes *determines* `s` when the only solutions `t`
of the linear system `⟪v i, t⟫ = 0` are `t = 0` and `t = s`; in that case the classical
post-processing (Gaussian elimination) recovers `s`.

The main result is that `m` runs (hence `m` queries) determine `s` with probability at
least `1 - 2 ^ n / 2 ^ m`; with `m = 2 n` queries the failure probability is at most
`2 ^ (-n)`.
-/

namespace QI

set_option autoImplicit false

/-- The measurement outcomes `v` determine the secret `s`: the only solutions of the
homogeneous linear system they define are `0` and `s`. -/
def Determines {n m : ℕ} (v : Fin m → V n) (s : V n) : Prop :=
  ∀ t : V n, (∀ i, dot (v i) t = 0) → (t = 0 ∨ t = s)

instance {n m : ℕ} (v : Fin m → V n) (s : V n) : Decidable (Determines v s) := by
  unfold Determines; infer_instance

/-- The probability that `m` independent runs of Simon's circuit (i.e. `m` queries to `f`)
produce outcomes that determine the secret. -/
noncomputable def simonSuccess {n : ℕ} (f : V n → V n) (m : ℕ) (s : V n) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v : Fin m → V n => Determines v s), ∏ i, simonProb f (v i)

/-- The outcomes of `m` runs form a probability distribution on `(V n) ^ m`. -/
lemma sum_prod_simonProb {n : ℕ} {f : V n → V n} {s : V n} (h : IsSimon f s) (m : ℕ) :
    ∑ v : Fin m → V n, ∏ i, simonProb f (v i) = 1 := by
  have hp := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset (V n)))
      (fun (_ : Fin m) (y : V n) => simonProb f y)
  rw [Fintype.piFinset_univ] at hp
  rw [← hp]
  simp [simonProb_sum h]

/-- The set of failing outcome tuples. -/
def badSet (n m : ℕ) (s : V n) : Finset (Fin m → V n) :=
  Finset.univ.filter (fun v : Fin m → V n => (∀ i, dot (v i) s = 0) ∧ ¬ Determines v s)

/-- Union bound: a failing tuple lies in a hyperplane of `s^⊥`. -/
lemma badSet_card_le {n m : ℕ} (s : V n) (hs : s ≠ 0) :
    (badSet n m s).card * 4 ^ m ≤ (2 ^ n - 2) * (2 ^ n) ^ m := by
  classical
  set I : Finset (V n) := Finset.univ.filter (fun t : V n => t ≠ 0 ∧ t ≠ s) with hI
  set Bt : V n → Finset (Fin m → V n) := fun t =>
    Fintype.piFinset (fun _ : Fin m =>
      Finset.univ.filter (fun y : V n => dot y s = 0 ∧ dot y t = 0)) with hBt
  have hsub : badSet n m s ⊆ I.biUnion Bt := by
    intro v hv
    simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨hv1, hv2⟩ := hv
    unfold Determines at hv2
    push_neg at hv2
    obtain ⟨t, ht, ht0, hts⟩ := hv2
    refine Finset.mem_biUnion.mpr ⟨t, ?_, ?_⟩
    · simp [hI, ht0, hts]
    · simp only [hBt, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun i => ⟨hv1 i, ht i⟩
  have hcardI : I.card ≤ 2 ^ n - 2 := by
    have h1 : I ⊆ (Finset.univ : Finset (V n)) \ {0, s} := by
      intro t ht
      simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      simp [Finset.mem_sdiff, ht.1, ht.2]
    have h2 := Finset.card_le_card h1
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_pair (Ne.symm hs)] at h2
    simpa using h2
  have hcardBt : ∀ t ∈ I, (Bt t).card * 4 ^ m = (2 ^ n) ^ m := by
    intro t ht
    simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    have hc : 4 * (Finset.univ.filter (fun y : V n => dot y s = 0 ∧ dot y t = 0)).card = 2 ^ n :=
      card_perp_two s t hs ht.1 (Ne.symm ht.2)
    have hcard : (Bt t).card
        = ((Finset.univ.filter (fun y : V n => dot y s = 0 ∧ dot y t = 0)).card) ^ m := by
      simp [hBt, Fintype.card_piFinset]
    rw [hcard, ← mul_pow, mul_comm, hc]
  calc (badSet n m s).card * 4 ^ m ≤ (I.biUnion Bt).card * 4 ^ m :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (∑ t ∈ I, (Bt t).card) * 4 ^ m := Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ t ∈ I, ((Bt t).card * 4 ^ m) := by rw [Finset.sum_mul]
    _ = ∑ t ∈ I, (2 ^ n) ^ m := Finset.sum_congr rfl hcardBt
    _ = I.card * (2 ^ n) ^ m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 ^ n - 2) * (2 ^ n) ^ m := Nat.mul_le_mul_right _ hcardI

/-- **Simon's algorithm succeeds with `m` queries except with probability `2 ^ n / 2 ^ m`.** -/
theorem simon_success_bound {n : ℕ} {f : V n → V n} {s : V n} (h : IsSimon f s) (m : ℕ) :
    1 - 2 ^ n / 2 ^ m ≤ simonSuccess f m s := by
  classical
  have hs := h.1
  have hprob : ∀ v : Fin m → V n, ∏ i, simonProb f (v i)
      = if (∀ i, dot (v i) s = 0) then ((2:ℝ)/2^n)^m else 0 := by
    intro v
    by_cases hv : ∀ i, dot (v i) s = 0
    · rw [if_pos hv]
      rw [Finset.prod_congr rfl (fun i _ => by rw [simonProb_eq h, if_pos (hv i)])]
      simp [div_pow]
    · rw [if_neg hv]
      push_neg at hv
      obtain ⟨i, hi⟩ := hv
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [simonProb_eq h, if_neg hi]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin m → V n))
      (fun v => Determines v s) (fun v => ∏ i, simonProb f (v i))
  rw [sum_prod_simonProb h m] at hsplit
  have hbadsum : ∑ v ∈ Finset.univ.filter (fun v : Fin m → V n => ¬ Determines v s),
      ∏ i, simonProb f (v i) = (badSet n m s).card * ((2:ℝ)/2^n)^m := by
    rw [← Finset.sum_subset (s₁ := badSet n m s)]
    · rw [Finset.sum_congr rfl (fun v hv => ?_), Finset.sum_const, nsmul_eq_mul]
      simp only [badSet, Finset.mem_filter] at hv
      rw [hprob v, if_pos hv.2.1]
    · intro v hv
      simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp [hv.2]
    · intro v hvF hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvF
      simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hv
      rw [hprob v, if_neg (fun hall => (hv hall) hvF)]
  have hcard := badSet_card_le (m := m) s hs
  have hcast : ((badSet n m s).card : ℝ) * 4 ^ m ≤ 2 ^ n * (2 ^ n) ^ m := by
    have h1 : (((badSet n m s).card * 4 ^ m : ℕ) : ℝ) ≤ (((2 ^ n - 2) * (2 ^ n) ^ m : ℕ) : ℝ) := by
      exact_mod_cast hcard
    have h2 : (((2 ^ n - 2) * (2 ^ n) ^ m : ℕ) : ℝ) ≤ ((2 ^ n * (2 ^ n) ^ m : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    push_cast at h1 h2
    linarith
  have hfinal : ((badSet n m s).card : ℝ) * ((2:ℝ)/2^n)^m ≤ 2 ^ n / 2 ^ m := by
    rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    calc ((badSet n m s).card : ℝ) * 2 ^ m * 2 ^ m
        = ((badSet n m s).card : ℝ) * 4 ^ m := by rw [mul_assoc, ← mul_pow]; norm_num
      _ ≤ 2 ^ n * (2 ^ n) ^ m := hcast
  rw [hbadsum] at hsplit
  unfold simonSuccess
  linarith

/-- With `2 n` queries, Simon's algorithm determines the secret except with probability
`2 ^ (-n)`. -/
theorem simon_success_two_n {n : ℕ} {f : V n → V n} {s : V n} (h : IsSimon f s) :
    1 - (1 / 2 : ℝ) ^ n ≤ simonSuccess f (2 * n) s := by
  have hb := simon_success_bound h (2 * n)
  have heq : (2:ℝ) ^ n / 2 ^ (2 * n) = (1 / 2 : ℝ) ^ n := by
    rw [pow_mul, div_pow]
    rw [show ((2:ℝ) ^ 2) ^ n = 2 ^ n * 2 ^ n by rw [← pow_mul, ← pow_add]; ring_nf]
    rw [one_pow]
    field_simp
  rwa [heq] at hb

end QI

import RequestProject.QI.Basic

/-!
# Simon's problem: the classical `Ω(2 ^ (n / 2))` lower bound

A deterministic classical query algorithm is a decision tree `DTree n`: each internal node
queries a point `x : V n` and branches on the answer `f x : V n`; leaves output a guess for
the secret.  `DTree.depth` is the worst-case number of queries.

The lower bound: if a tree outputs the correct secret for *every* Simon function on `n`
bits (`n ≥ 2`), then its depth is at least `2 ^ (n / 2)`.
-/

namespace QI

set_option autoImplicit false

/-- A deterministic classical query algorithm for Simon's problem: a decision tree whose
internal nodes query a point and branch on the answer. -/
inductive DTree (n : ℕ) : Type
  | leaf : V n → DTree n
  | node : V n → (V n → DTree n) → DTree n

namespace DTree

/-- The worst-case number of queries made by the tree. -/
def depth {n : ℕ} : DTree n → ℕ
  | .leaf _ => 0
  | .node _ k => 1 + Finset.univ.sup (fun b => (k b).depth)

/-- The output of the tree on the oracle `f`. -/
def run {n : ℕ} : DTree n → (V n → V n) → V n
  | .leaf a, _ => a
  | .node x k, f => (k (f x)).run f

/-- The set of points queried by the tree along its run on `f`. -/
def queries {n : ℕ} : DTree n → (V n → V n) → Finset (V n)
  | .leaf _, _ => ∅
  | .node x k, f => insert x ((k (f x)).queries f)

lemma card_queries_le_depth {n : ℕ} (t : DTree n) (f : V n → V n) :
    (t.queries f).card ≤ t.depth := by
  induction t with
  | leaf a => simp [queries, depth]
  | node x k ih =>
    rw [queries, depth]
    have hsup : (k (f x)).depth ≤ (Finset.univ.sup fun b => (k b).depth) :=
      Finset.le_sup (f := fun b => (k b).depth) (Finset.mem_univ (f x))
    calc (insert x ((k (f x)).queries f)).card ≤ ((k (f x)).queries f).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ (k (f x)).depth + 1 := Nat.add_le_add_right (ih (f x)) 1
      _ ≤ (Finset.univ.sup fun b => (k b).depth) + 1 := Nat.add_le_add_right hsup 1
      _ = 1 + Finset.univ.sup fun b => (k b).depth := by ring

/-- Two oracles agreeing on the queried points give the same output. -/
lemma run_congr {n : ℕ} (t : DTree n) (f g : V n → V n)
    (hfg : ∀ x ∈ t.queries f, g x = f x) : t.run g = t.run f := by
  induction t with
  | leaf a => rfl
  | node x k ih =>
    have hx : g x = f x := hfg x (by simp [queries])
    rw [run, run, hx]
    exact ih (f x) (fun y hy => hfg y (by simp [queries, hy]))

end DTree

/-! ### Building Simon functions consistent with a transcript -/

/-- A fixed injective indexing of `V n`, used to choose a representative of each coset
`{x, x + s}`. -/
noncomputable def idx {n : ℕ} (x : V n) : ℕ := (Fintype.equivFin (V n) x : ℕ)

lemma idx_injective {n : ℕ} : Function.Injective (idx (n := n)) := by
  intro x y hxy
  have : Fintype.equivFin (V n) x = Fintype.equivFin (V n) y := Fin.ext hxy
  exact (Fintype.equivFin (V n)).injective this

/-- The Simon function with secret `s` that agrees with the identity on `Q`, provided no
two points of `Q` differ by `s`.  It sends `x` to the chosen representative of the coset
`{x, x + s}`, preferring the representative lying in `Q`. -/
noncomputable def repQ {n : ℕ} (Q : Finset (V n)) (s : V n) (x : V n) : V n :=
  if x ∈ Q then x else if x + s ∈ Q then x + s
  else if idx x ≤ idx (x + s) then x else x + s

lemma repQ_mem_pair {n : ℕ} (Q : Finset (V n)) (s x : V n) :
    repQ Q s x = x ∨ repQ Q s x = x + s := by
  unfold repQ
  split_ifs <;> simp

lemma repQ_eq_of_mem {n : ℕ} {Q : Finset (V n)} {s x : V n} (hx : x ∈ Q) :
    repQ Q s x = x := by
  unfold repQ; rw [if_pos hx]

lemma repQ_shift {n : ℕ} {Q : Finset (V n)} {s : V n} (hs : s ≠ 0)
    (hQ : ∀ x ∈ Q, x + s ∉ Q) (x : V n) : repQ Q s (x + s) = repQ Q s x := by
  have hcancel : x + s + s = x := add_add_cancel_V x s
  have hne : x + s ≠ x := add_right_ne_self hs
  unfold repQ
  rw [hcancel]
  by_cases h1 : x ∈ Q
  · have h2 : x + s ∉ Q := hQ x h1
    rw [if_neg h2, if_pos h1, if_pos h1]
  · by_cases h2 : x + s ∈ Q
    · rw [if_pos h2, if_neg h1, if_pos h2]
    · rw [if_neg h2, if_neg h1, if_neg h2, if_neg h1]
      have hidx : idx x ≠ idx (x + s) := fun hh => hne (idx_injective hh).symm
      rcases lt_or_gt_of_ne hidx with hlt | hgt
      · rw [if_pos (le_of_lt hlt), if_neg (not_le.mpr hlt)]
      · rw [if_neg (not_le.mpr hgt), if_pos (le_of_lt hgt)]

lemma repQ_isSimon {n : ℕ} {Q : Finset (V n)} {s : V n} (hs : s ≠ 0)
    (hQ : ∀ x ∈ Q, x + s ∉ Q) : IsSimon (repQ Q s) s := by
  refine ⟨hs, fun x y => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rcases repQ_mem_pair Q s x with hx | hx <;> rcases repQ_mem_pair Q s y with hy | hy
    · left; rw [hx, hy] at h; exact h.symm
    · right
      rw [hx, hy] at h
      have h' := congrArg (fun z => z + s) h
      simp only [add_add_cancel_V] at h'
      exact h'.symm
    · right
      rw [hx, hy] at h
      exact h.symm
    · left
      rw [hx, hy] at h
      exact (add_right_cancel h).symm
  · rcases h with rfl | rfl
    · rfl
    · exact (repQ_shift hs hQ x).symm

/-- Simon functions exist for every nonzero secret, so the statements about them are not
vacuous. -/
lemma exists_isSimon {n : ℕ} (s : V n) (hs : s ≠ 0) : IsSimon (repQ ∅ s) s :=
  repQ_isSimon hs (by simp)

/-! ### The lower bound -/

/-- **Classical lower bound for Simon's problem.**  Any deterministic query algorithm that
outputs the secret of every Simon function on `n ≥ 2` bits must make at least `2 ^ (n / 2)`
queries in the worst case. -/
theorem simon_classical_lower_bound {n : ℕ} (hn : 2 ≤ n) (t : DTree n)
    (hcorrect : ∀ (f : V n → V n) (s : V n), IsSimon f s → t.run f = s) :
    2 ^ (n / 2) ≤ t.depth := by
  classical
  set Q : Finset (V n) := t.queries id with hQdef
  set D : Finset (V n) := insert 0 ((Q ×ˢ Q).image (fun p => p.1 + p.2)) with hDdef
  have hDcard : D.card ≤ 1 + Q.card * Q.card := by
    calc D.card ≤ ((Q ×ˢ Q).image (fun p => p.1 + p.2)).card + 1 := Finset.card_insert_le _ _
      _ ≤ (Q ×ˢ Q).card + 1 := Nat.add_le_add_right (Finset.card_image_le) 1
      _ = Q.card * Q.card + 1 := by rw [Finset.card_product]
      _ = 1 + Q.card * Q.card := by ring
  have key : ∀ s ∈ (Finset.univ \ D), t.run id = s := by
    intro s hsD
    rw [Finset.mem_sdiff] at hsD
    have hsD := hsD.2
    have hs0 : s ≠ 0 := by
      intro hz
      exact hsD (by rw [hDdef, hz]; exact Finset.mem_insert_self _ _)
    have hQs : ∀ x ∈ Q, x + s ∉ Q := by
      intro x hx hxs
      apply hsD
      rw [hDdef]
      refine Finset.mem_insert_of_mem ?_
      refine Finset.mem_image.mpr ⟨(x, x + s), Finset.mem_product.mpr ⟨hx, hxs⟩, ?_⟩
      simp only
      rw [← add_assoc, add_self_V, zero_add]
    have hsim := repQ_isSimon hs0 hQs
    have h1 : t.run (repQ Q s) = s := hcorrect _ _ hsim
    have h2 : t.run (repQ Q s) = t.run id :=
      DTree.run_congr t id (repQ Q s) (fun x hx => repQ_eq_of_mem (by rw [hQdef]; exact hx))
    rw [← h2, h1]
  have h1 : (Finset.univ \ D).card ≤ 1 :=
    Finset.card_le_one.mpr (fun a ha b hb => (key a ha).symm.trans (key b hb))
  have h2 : (Finset.univ \ D).card + D.card = 2 ^ n := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)]
    simp
  have h3 : 2 ^ n ≤ 2 + Q.card * Q.card := by omega
  have h4 : Q.card ≤ t.depth := DTree.card_queries_le_depth t id
  have h5 : 2 ^ n ≤ 2 + t.depth * t.depth :=
    h3.trans (Nat.add_le_add_left (Nat.mul_le_mul h4 h4) 2)
  by_contra hcon
  push_neg at hcon
  have hq : 2 ^ (n / 2) * 2 ^ (n / 2) ≤ 2 ^ n := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsq : (t.depth + 1) * (t.depth + 1) ≤ 2 ^ (n / 2) * 2 ^ (n / 2) :=
    Nat.mul_le_mul hcon hcon
  have h4n : (4:ℕ) ≤ 2 ^ n := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  nlinarith [h5, hsq, hq, h4n]

end QI

