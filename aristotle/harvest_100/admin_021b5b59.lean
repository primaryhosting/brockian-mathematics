/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Simon.Defs
import RequestProject.Simon.Quantum
import RequestProject.Simon.Classical
import RequestProject.Simon.Sampling
import RequestProject.Simon.Upper

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QI

open Finset

/-- The measurement outcomes of Simon's circuit form a probability distribution. -/
theorem simonProb_sum_eq_one {n : ℕ} {f : BV n → BV n} {s : BV n} (h : SimonPromise f s) :
    ∑ y : BV n, simonProb f y = 1 := by
  classical
  have hcong : ∀ y : BV n, simonProb f y = if y ∈ Orth s then (2 : ℝ) / 2 ^ n else 0 := by
    intro y
    rw [simonProb_eq h y]
    by_cases hy : dot y s = 0
    · rw [if_pos (by rw [dot_comm]; exact hy), if_pos (mem_Orth s y |>.mpr hy)]
    · rw [if_neg (by rw [dot_comm]; exact hy), if_neg (fun hc => hy ((mem_Orth s y).mp hc))]
  simp only [hcong]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hcard : 2 * (Orth s).card = 2 ^ n := card_Orth s h.ne_zero
  have hcardR : ((Orth s).card : ℝ) * 2 = 2 ^ n := by
    have : ((2 * (Orth s).card : ℕ) : ℝ) = ((2 ^ n : ℕ) : ℝ) := by rw [hcard]
    push_cast at this
    linarith
  have hpos : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  field_simp
  linarith [hcardR]

/-- The samples pin down the period uniquely among nonzero vectors. -/
theorem Determines.unique {n m : ℕ} {y : Fin m → BV n} {s : BV n} (h : Determines y s)
    {t : BV n} (ht : t ≠ 0) (hty : ∀ i, dot (y i) t = 0) : t = s := by
  rcases h t hty with h0 | hs
  · exact absurd h0 ht
  · exact hs

/-- **Simon's problem: quantum upper bound and classical lower bound.**

1. *(Quantum, one query per run.)*  For every instance `f` satisfying Simon's promise with hidden
   period `s`, the circuit `QI.simonState` — which makes a single oracle query — produces a
   genuine probability distribution on measurement outcomes which is uniform on the `2ⁿ⁻¹`
   vectors orthogonal to `s` and vanishes elsewhere.

2. *(Quantum, `O(n)` queries suffice.)*  Among all `2n`-tuples of such samples, the proportion
   that fails to determine `s` is at most `2⁻ⁿ`; and whenever a tuple does determine `s`, the
   period is the unique nonzero vector orthogonal to all the samples, so it can be read off by
   solving a linear system.  Hence `2n = O(n)` quantum queries solve Simon's problem with
   success probability at least `1 - 2⁻ⁿ`.

3. *(Classical, `Ω(2^{n/2})` queries are necessary.)*  Every deterministic classical algorithm
   that outputs the hidden period on all promise instances must make at least `2^{(n-1)/2}`
   queries.

4. *(Non-vacuity.)*  Promise instances exist for every nonzero period, and some deterministic
   classical algorithm does solve the problem (with `2ⁿ` queries), so the model of part 3 is not
   vacuous. -/
theorem simon_algorithm (n : ℕ) :
    (∀ (f : BV n → BV n) (s : BV n), SimonPromise f s →
        (∑ y : BV n, simonProb f y = 1) ∧
        (∀ y : BV n, simonProb f y = if dot s y = 0 then 2 / 2 ^ n else 0)) ∧
    (∀ s : BV n,
        ((badSamples s (2 * n)).card : ℝ) / ((allSamples s (2 * n)).card : ℝ) ≤ 1 / 2 ^ n) ∧
    (∀ (s : BV n) (y : Fin (2 * n) → BV n), Determines y s →
        ∀ t : BV n, t ≠ 0 → (∀ i, dot (y i) t = 0) → t = s) ∧
    (2 ≤ n → ∀ (A : ClassicalAlg n) (m : ℕ), A.Solves m → 2 ^ ((n - 1) / 2) ≤ m) ∧
    ((∀ s : BV n, s ≠ 0 → ∃ f : BV n → BV n, SimonPromise f s) ∧
      ∃ A : ClassicalAlg n, A.Solves (2 ^ n)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f s h
    exact ⟨simonProb_sum_eq_one h, fun y => simonProb_eq h y⟩
  · intro s
    exact sampling_failure_prob s
  · intro s y h t ht hty
    exact h.unique ht hty
  · intro hn A m hA
    exact classical_query_lower_bound A m hn hA
  · intro s hs
    exact exists_simonPromise s hs
  · exact exists_classical_solver n

end QI

import RequestProject.Simon.Defs

/-!
# Recovering the period from the quantum samples

Each run of Simon's quantum circuit costs one oracle query and returns a uniformly random vector
of the hyperplane `Orth s = {y | y ⬝ s = 0}`.  Here we show that `O(n)` such samples determine `s`:
the proportion of sample tuples `y : Fin m → Orth s` that fail to pin down `s` is at most
`2ⁿ / 2ᵐ`, so `m = 2n` samples suffice to make the failure probability at most `2⁻ⁿ`.
-/

namespace QI

open Finset

/-- The hyperplane of vectors orthogonal to `s`. -/
def Orth {n : ℕ} (s : BV n) : Finset (BV n) := Finset.univ.filter (fun y => dot y s = 0)

@[simp] lemma mem_Orth {n : ℕ} (s y : BV n) : y ∈ Orth s ↔ dot y s = 0 := by
  simp [Orth]

/-- The standard basis vector. -/
def basisVec {n : ℕ} (k : Fin n) : BV n := Pi.single k 1

lemma dot_basisVec {n : ℕ} (k : Fin n) (y : BV n) : dot (basisVec k) y = y k := by
  classical
  unfold dot basisVec
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- If a set is invariant under translation by `w` and `w ⬝ u = 1`, then exactly half of it is
orthogonal to `u`. -/
lemma card_filter_dot_eq_zero {n : ℕ} (A : Finset (BV n)) (w u : BV n)
    (hA : ∀ y : BV n, y + w ∈ A ↔ y ∈ A) (hw : dot w u = 1) :
    2 * (A.filter (fun y => dot y u = 0)).card = A.card := by
  classical
  set A0 := A.filter (fun y => dot y u = 0) with hA0
  set A1 := A.filter (fun y => dot y u = 1) with hA1
  have hbij : A0.card = A1.card := by
    refine Finset.card_bij (fun y _ => y + w) ?_ ?_ ?_
    · intro y hy
      simp only [hA1, hA0, Finset.mem_filter] at hy ⊢
      refine ⟨(hA y).2 hy.1, ?_⟩
      rw [dot_add_left, hy.2, hw, zero_add]
    · intro y hy z hz hyz
      exact add_right_cancel hyz
    · intro z hz
      simp only [hA1, Finset.mem_filter] at hz
      refine ⟨z + w, ?_, ?_⟩
      · simp only [hA0, Finset.mem_filter]
        refine ⟨(hA z).2 hz.1, ?_⟩
        rw [dot_add_left, hz.2, hw]
        decide
      · show z + w + w = z
        rw [add_assoc]
        simp
  have hfe : A.filter (fun y => ¬ (dot y u = 0)) = A1 := by
    refine Finset.filter_congr ?_
    intro y _
    rcases zmod2_cases (dot y u) with h | h <;> simp [h]
  have hunion : A0.card + A1.card = A.card := by
    rw [hA0, ← hfe]
    exact Finset.card_filter_add_card_filter_not (fun y => dot y u = 0)
  omega

/-- For `s ≠ 0`, exactly half of all bit strings are orthogonal to `s`. -/
lemma card_Orth {n : ℕ} (s : BV n) (hs : s ≠ 0) : 2 * (Orth s).card = 2 ^ n := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, s k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hs (funext hc)
  have hk1 : s k = 1 := zmod2_eq_one hk
  have := card_filter_dot_eq_zero (Finset.univ : Finset (BV n)) (basisVec k) s
    (by intro y; simp) (by rw [dot_basisVec, hk1])
  simpa [Orth, Finset.card_univ] using this

/-- Given `t ≠ 0` and `s ≠ t`, some vector is orthogonal to `s` but not to `t`. -/
lemma exists_dot_zero_one {n : ℕ} (s t : BV n) (hst : s ≠ t) (ht : t ≠ 0) :
    ∃ v : BV n, dot v s = 0 ∧ dot v t = 1 := by
  classical
  by_cases hex : ∃ k, s k = 0 ∧ t k = 1
  · obtain ⟨k, hk0, hk1⟩ := hex
    exact ⟨basisVec k, by rw [dot_basisVec, hk0], by rw [dot_basisVec, hk1]⟩
  · push_neg at hex
    obtain ⟨b, hb⟩ : ∃ b, t b ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact ht (funext hc)
    have hb1 : t b = 1 := zmod2_eq_one hb
    have hsb : s b = 1 := by
      rcases zmod2_cases (s b) with h | h
      · exact absurd hb1 (hex b h)
      · exact h
    obtain ⟨k, hk⟩ : ∃ k, s k ≠ t k := by
      by_contra hc
      push_neg at hc
      exact hst (funext hc)
    have hsk : s k = 1 := by
      rcases zmod2_cases (s k) with h | h
      · rcases zmod2_cases (t k) with h' | h'
        · exact absurd (h.trans h'.symm) hk
        · exact absurd h' (hex k h)
      · exact h
    have htk : t k = 0 := by
      rcases zmod2_cases (t k) with h | h
      · exact h
      · exact absurd (hsk.trans h.symm) hk
    refine ⟨basisVec b + basisVec k, ?_, ?_⟩
    · rw [dot_add_left, dot_basisVec, dot_basisVec, hsb, hsk]
      decide
    · rw [dot_add_left, dot_basisVec, dot_basisVec, hb1, htk]
      simp

/-- For two distinct nonzero vectors, exactly a quarter of all bit strings are orthogonal to
both. -/
lemma card_Orth_inter {n : ℕ} (s t : BV n) (ht : t ≠ 0) (hst : s ≠ t) :
    2 * (Orth s ∩ Orth t).card = (Orth s).card := by
  classical
  obtain ⟨v, hvs, hvt⟩ := exists_dot_zero_one s t hst ht
  have hinv : ∀ y : BV n, y + v ∈ Orth s ↔ y ∈ Orth s := by
    intro y
    simp only [mem_Orth, dot_add_left, hvs, add_zero]
  have hfilter : (Orth s).filter (fun y => dot y t = 0) = Orth s ∩ Orth t := by
    ext y
    simp [Finset.mem_filter, Finset.mem_inter]
  have := card_filter_dot_eq_zero (Orth s) v t hinv hvt
  rwa [hfilter] at this

/-- The samples `y` determine the period `s`: the only vectors orthogonal to all of them are
`0` and `s`. -/
def Determines {n m : ℕ} (y : Fin m → BV n) (s : BV n) : Prop :=
  ∀ t : BV n, (∀ i, dot (y i) t = 0) → t = 0 ∨ t = s

/-- All possible outcomes of `m` runs of Simon's circuit (each run returns a vector of
`Orth s`). -/
def allSamples {n : ℕ} (s : BV n) (m : ℕ) : Finset (Fin m → BV n) :=
  Fintype.piFinset (fun _ : Fin m => Orth s)

open Classical in
/-- The outcomes that fail to determine the period. -/
noncomputable def badSamples {n : ℕ} (s : BV n) (m : ℕ) : Finset (Fin m → BV n) :=
  (allSamples s m).filter (fun y => ¬ Determines y s)

lemma card_allSamples {n : ℕ} (s : BV n) (m : ℕ) :
    (allSamples s m).card = (Orth s).card ^ m := by
  classical
  rw [allSamples, Fintype.card_piFinset]
  simp

/-- **The samples determine the period with high probability.**  Out of all `m`-tuples of
vectors orthogonal to `s`, the proportion failing to determine `s` is at most `2ⁿ / 2ᵐ`. -/
theorem sampling_failure_bound {n : ℕ} (s : BV n) (m : ℕ) :
    (badSamples s m).card * 2 ^ m ≤ 2 ^ n * (allSamples s m).card := by
  classical
  set S : Finset (BV n) := Finset.univ \ {0, s} with hS
  have hsub : badSamples s m ⊆
      S.biUnion (fun t => Fintype.piFinset (fun _ : Fin m => Orth s ∩ Orth t)) := by
    intro y hy
    simp only [badSamples, Finset.mem_filter] at hy
    obtain ⟨hyall, hybad⟩ := hy
    rw [Determines] at hybad
    push_neg at hybad
    obtain ⟨t, hto, ht0, hts⟩ := hybad
    refine Finset.mem_biUnion.mpr ⟨t, ?_, ?_⟩
    · simp [hS, ht0, hts]
    · refine Fintype.mem_piFinset.mpr (fun i => ?_)
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · exact (Fintype.mem_piFinset.mp hyall) i
      · exact mem_Orth _ _ |>.mpr (hto i)
  have hcard : (badSamples s m).card
      ≤ ∑ t ∈ S, (Orth s ∩ Orth t).card ^ m := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_biUnion_le) ?_
    refine Finset.sum_le_sum (fun t _ => ?_)
    rw [Fintype.card_piFinset]
    simp
  have hterm : ∀ t ∈ S, (Orth s ∩ Orth t).card ^ m * 2 ^ m = (Orth s).card ^ m := by
    intro t htS
    have ht0 : t ≠ 0 := by
      intro h; rw [hS] at htS; simp [h] at htS
    have hts : s ≠ t := by
      intro h; rw [hS] at htS; simp [← h] at htS
    have h2 := card_Orth_inter s t ht0 hts
    calc (Orth s ∩ Orth t).card ^ m * 2 ^ m
        = (2 * (Orth s ∩ Orth t).card) ^ m := by rw [mul_pow]; ring
      _ = (Orth s).card ^ m := by rw [h2]
  calc (badSamples s m).card * 2 ^ m
      ≤ (∑ t ∈ S, (Orth s ∩ Orth t).card ^ m) * 2 ^ m := Nat.mul_le_mul_right _ hcard
    _ = ∑ t ∈ S, (Orth s ∩ Orth t).card ^ m * 2 ^ m := by rw [Finset.sum_mul]
    _ = ∑ _t ∈ S, (Orth s).card ^ m := Finset.sum_congr rfl hterm
    _ = S.card * (Orth s).card ^ m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 ^ n * (Orth s).card ^ m := by
        refine Nat.mul_le_mul_right _ ?_
        calc S.card ≤ (Finset.univ : Finset (BV n)).card := Finset.card_le_card (by simp [hS])
          _ = 2 ^ n := by simp [Finset.card_univ]
    _ = 2 ^ n * (allSamples s m).card := by rw [card_allSamples]

lemma card_Orth_pos {n : ℕ} (s : BV n) : 0 < (Orth s).card := by
  refine Finset.card_pos.mpr ⟨0, ?_⟩
  simp

/-- **`2n` runs of Simon's circuit determine the period with probability at least `1 - 2⁻ⁿ`.**
Each run costs a single oracle query, so `O(n)` quantum queries suffice. -/
theorem sampling_failure_prob {n : ℕ} (s : BV n) :
    ((badSamples s (2 * n)).card : ℝ) / ((allSamples s (2 * n)).card : ℝ) ≤ 1 / 2 ^ n := by
  have hb := sampling_failure_bound s (2 * n)
  have hpos : 0 < (allSamples s (2 * n)).card := by
    rw [card_allSamples]
    exact pow_pos (card_Orth_pos s) _
  have hposR : (0:ℝ) < ((allSamples s (2 * n)).card : ℝ) := by exact_mod_cast hpos
  rw [div_le_div_iff₀ hposR (by positivity)]
  have hbR : ((badSamples s (2*n)).card : ℝ) * 2 ^ (2 * n) ≤ 2 ^ n * ((allSamples s (2*n)).card : ℝ) := by
    exact_mod_cast hb
  have hsplit : (2:ℝ) ^ (2 * n) = 2 ^ n * 2 ^ n := by
    rw [← pow_add]; ring_nf
  nlinarith [hbR, hposR, pow_pos (show (0:ℝ) < 2 by norm_num) n]

end QI

import RequestProject.Simon.Defs

/-!
# The quantum part of Simon's algorithm

We describe the quantum circuit of Simon's algorithm on `2n` qubits explicitly, at the level of
amplitudes: a state is a function `BV n → BV n → ℂ` assigning an amplitude to every computational
basis state `|x⟩|v⟩`.

The circuit is:

* start in `|0⟩|0⟩`;
* apply a Hadamard transform to the first register;
* apply the (single) oracle query `|x⟩|v⟩ ↦ |x⟩|v + f x⟩`;
* apply a Hadamard transform to the first register;
* measure the first register.

The main result, `QI.simonProb_eq`, states that the outcome distribution of the measurement is
uniform on the hyperplane `{y | dot y s = 0}`; in particular a single query already yields a
uniformly random vector orthogonal to the hidden period `s`.
-/

namespace QI

open Finset

/-- The real character `(-1)^a` of `ZMod 2`. -/
def rsgn (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

/-- The character `(-1)^a` of `ZMod 2`, with values in `ℂ`. -/
noncomputable def sgn (a : ZMod 2) : ℂ := ((rsgn a : ℝ) : ℂ)

@[simp] lemma rsgn_zero : rsgn 0 = 1 := by simp [rsgn]

@[simp] lemma sgn_zero : sgn 0 = 1 := by simp [sgn]

lemma rsgn_add (a b : ZMod 2) : rsgn (a + b) = rsgn a * rsgn b := by
  fin_cases a <;> fin_cases b <;>
    norm_num [rsgn, show ((1 : ZMod 2) + 1) = 0 from by decide]

lemma rsgn_mul_self (a : ZMod 2) : rsgn a * rsgn a = 1 := by
  fin_cases a <;> norm_num [rsgn]

/-- A (pure) state of the two `n`-qubit registers, given by its amplitudes. -/
abbrev State (n : ℕ) := BV n → BV n → ℂ

/-- The initial state `|0⟩|0⟩`. -/
noncomputable def initState (n : ℕ) : State n := fun x v => if x = 0 ∧ v = 0 then 1 else 0

/-- The Hadamard transform `H^{⊗n}` applied to the first register. -/
noncomputable def hadamardFirst {n : ℕ} (psi : State n) : State n :=
  fun y v => ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * ∑ x : BV n, sgn (dot x y) * psi x v

/-- The oracle query `|x⟩|v⟩ ↦ |x⟩|v + f x⟩`, expressed on amplitudes. -/
noncomputable def oracleApply {n : ℕ} (f : BV n → BV n) (psi : State n) : State n :=
  fun x v => psi x (v + f x)

/-- The state of Simon's circuit just before the final measurement.  It uses exactly one
oracle query. -/
noncomputable def simonState {n : ℕ} (f : BV n → BV n) : State n :=
  hadamardFirst (oracleApply f (hadamardFirst (initState n)))

/-- The probability of measuring `y` in the first register at the end of Simon's circuit. -/
noncomputable def simonProb {n : ℕ} (f : BV n → BV n) (y : BV n) : ℝ :=
  ∑ v : BV n, Complex.normSq (simonState f y v)

lemma hadamard_initState {n : ℕ} (x v : BV n) :
    hadamardFirst (initState n) x v
      = ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * (if v = 0 then 1 else 0) := by
  classical
  unfold hadamardFirst initState
  congr 1
  rw [Finset.sum_eq_single (0 : BV n)]
  · by_cases hv : v = 0 <;> simp [hv]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ (0 : BV n)) h

lemma oracle_hadamard_initState {n : ℕ} (f : BV n → BV n) (x v : BV n) :
    oracleApply f (hadamardFirst (initState n)) x v
      = ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * (if f x = v then 1 else 0) := by
  classical
  unfold oracleApply
  rw [hadamard_initState]
  congr 1
  simp only [bv_add_eq_zero_iff]

lemma sqrt_two_pow_inv_sq (n : ℕ) :
    ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹
      = (((2 : ℝ) ^ n : ℝ) : ℂ)⁻¹ := by
  have h : Real.sqrt ((2:ℝ) ^ n) * Real.sqrt ((2:ℝ) ^ n) = (2:ℝ) ^ n :=
    Real.mul_self_sqrt (by positivity)
  have h2 : ((Real.sqrt ((2:ℝ) ^ n) : ℝ) : ℂ) * ((Real.sqrt ((2:ℝ) ^ n) : ℝ) : ℂ)
      = (((2:ℝ) ^ n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, h]
  rw [← mul_inv, h2]

/-- The (real) amplitude, up to the normalisation factor `2⁻ⁿ`, of the basis state `|y⟩|v⟩`
at the end of Simon's circuit. -/
noncomputable def ramp {n : ℕ} (f : BV n → BV n) (y v : BV n) : ℝ :=
  ∑ x : BV n, rsgn (dot x y) * (if f x = v then 1 else 0)

/-- Explicit formula for the amplitudes at the end of Simon's circuit. -/
lemma simonState_apply {n : ℕ} (f : BV n → BV n) (y v : BV n) :
    simonState f y v = (((((2 : ℝ) ^ n)⁻¹ * ramp f y v : ℝ)) : ℂ) := by
  classical
  rw [simonState]
  show ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ *
      ∑ x : BV n, sgn (dot x y) * oracleApply f (hadamardFirst (initState n)) x v = _
  simp only [oracle_hadamard_initState]
  simp only [mul_comm (sgn (dot _ y))]
  simp only [mul_assoc]
  rw [← Finset.mul_sum, ← mul_assoc, sqrt_two_pow_inv_sq]
  push_cast [ramp, sgn]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : f x = v <;> simp [hx]

lemma simonProb_eq_sum_sq {n : ℕ} (f : BV n → BV n) (y : BV n) :
    simonProb f y = ((2 : ℝ) ^ n)⁻¹ ^ 2 * ∑ v : BV n, (ramp f y v) ^ 2 := by
  unfold simonProb
  simp only [simonState_apply, Complex.normSq_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  ring

/-- Key computation: the squared amplitudes sum to `2ⁿ (1 + (-1)^{s·y})`. -/
lemma sum_ramp_sq {n : ℕ} {f : BV n → BV n} {s : BV n} (h : SimonPromise f s) (y : BV n) :
    ∑ v : BV n, (ramp f y v) ^ 2 = 2 ^ n * (1 + rsgn (dot s y)) := by
  classical
  have hstep1 : ∀ v : BV n, (ramp f y v) ^ 2
      = ∑ x : BV n, ∑ x' : BV n,
          (rsgn (dot x y) * (if f x = v then (1:ℝ) else 0)) *
          (rsgn (dot x' y) * (if f x' = v then (1:ℝ) else 0)) := by
    intro v
    rw [sq, ramp, Finset.sum_mul_sum]
  simp only [hstep1]
  rw [Finset.sum_comm]
  have hstep2 : ∀ x : BV n, ∑ v : BV n, ∑ x' : BV n,
      (rsgn (dot x y) * (if f x = v then (1:ℝ) else 0)) *
      (rsgn (dot x' y) * (if f x' = v then (1:ℝ) else 0))
      = ∑ x' : BV n, rsgn (dot x y) * rsgn (dot x' y) * (if f x = f x' then (1:ℝ) else 0) := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    have : ∀ v : BV n,
        (rsgn (dot x y) * (if f x = v then (1:ℝ) else 0)) *
        (rsgn (dot x' y) * (if f x' = v then (1:ℝ) else 0))
        = (rsgn (dot x y) * rsgn (dot x' y)) *
            ((if f x = v then (1:ℝ) else 0) * (if f x' = v then (1:ℝ) else 0)) := by
      intro v; ring
    simp only [this]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_eq_single (f x)]
    · by_cases hx : f x' = f x
      · simp [hx]
      · simp [hx, Ne.symm hx]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hb
      exact absurd (Finset.mem_univ (f x)) hb
  simp only [hstep2]
  have hstep3 : ∀ x : BV n,
      ∑ x' : BV n, rsgn (dot x y) * rsgn (dot x' y) * (if f x = f x' then (1:ℝ) else 0)
      = 1 + rsgn (dot s y) := by
    intro x
    have hcond : ∀ x' : BV n, (if f x = f x' then (1:ℝ) else 0)
        = if x' ∈ ({x, x + s} : Finset (BV n)) then (1:ℝ) else 0 := by
      intro x'
      have : (f x = f x') ↔ (x' ∈ ({x, x + s} : Finset (BV n))) := by
        rw [h.fibre x x']
        simp [Finset.mem_insert, Finset.mem_singleton]
      simp only [this]
    simp only [hcond, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    have hne : x ≠ x + s := by
      intro hc
      apply h.ne_zero
      have := congrArg (fun w => w + x) hc
      simpa [add_comm, add_left_comm, add_assoc] using this.symm
    rw [Finset.sum_pair hne]
    rw [dot_add_left, rsgn_add]
    rw [← mul_assoc, rsgn_mul_self]
    ring
  simp only [hstep3]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card, Fintype.card_fun,
    Fintype.card_fin]
  push_cast
  ring

/-- **Simon's algorithm, quantum part.**  With a single oracle query, the measured value `y` is
uniformly distributed over the `2ⁿ⁻¹` vectors orthogonal to the hidden period `s`. -/
theorem simonProb_eq {n : ℕ} {f : BV n → BV n} {s : BV n} (h : SimonPromise f s) (y : BV n) :
    simonProb f y = if dot s y = 0 then 2 / 2 ^ n else 0 := by
  rw [simonProb_eq_sum_sq, sum_ramp_sq h y]
  by_cases hy : dot s y = 0
  · rw [if_pos hy, hy, rsgn_zero]
    have h2 : ((2:ℝ) ^ n) ≠ 0 := by positivity
    field_simp
    ring
  · rw [if_neg hy, rsgn, if_neg hy]
    ring

end QI

import Mathlib

/-!
# Simon's problem: basic definitions

We model `n`-bit strings as vectors over the two-element field `ZMod 2`.
-/

namespace QI

open Finset

/-- `n`-bit strings, viewed as vectors over `𝔽₂`. -/
abbrev BV (n : ℕ) := Fin n → ZMod 2

/-- The standard `𝔽₂`-bilinear form ("inner product mod 2") on bit strings. -/
def dot {n : ℕ} (x y : BV n) : ZMod 2 := ∑ i, x i * y i

lemma dot_comm {n : ℕ} (x y : BV n) : dot x y = dot y x := by
  simp [dot, mul_comm]

lemma dot_add_left {n : ℕ} (x y z : BV n) : dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_add_right {n : ℕ} (x y z : BV n) : dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

@[simp] lemma dot_zero_left {n : ℕ} (y : BV n) : dot 0 y = 0 := by simp [dot]

@[simp] lemma dot_zero_right {n : ℕ} (x : BV n) : dot x 0 = 0 := by simp [dot]

@[simp] lemma bv_add_self {n : ℕ} (v : BV n) : v + v = 0 := by
  funext i; exact CharTwo.add_self_eq_zero (v i)

@[simp] lemma bv_neg_self {n : ℕ} (v : BV n) : -v = v := by
  funext i; exact CharTwo.neg_eq (v i)

lemma bv_add_eq_zero_iff {n : ℕ} (v w : BV n) : v + w = 0 ↔ w = v := by
  rw [add_eq_zero_iff_eq_neg, bv_neg_self, eq_comm]

/-- Every `ZMod 2` element is `0` or `1`. -/
lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

/-- Every `ZMod 2` element other than `0` equals `1`. -/
lemma zmod2_eq_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  revert ha; revert a; decide

/-- Simon's promise: `f` is invariant under the shift by the nonzero period `s`, and its
fibres are exactly the pairs `{x, x + s}`. -/
structure SimonPromise {n : ℕ} (f : BV n → BV n) (s : BV n) : Prop where
  ne_zero : s ≠ 0
  fibre : ∀ x y : BV n, f x = f y ↔ (y = x ∨ y = x + s)

lemma SimonPromise.period {n : ℕ} {f : BV n → BV n} {s : BV n} (h : SimonPromise f s)
    (x : BV n) : f (x + s) = f x := by
  exact ((h.fibre x (x + s)).2 (Or.inr rfl)).symm

end QI

import RequestProject.Simon.Defs

/-!
# The classical lower bound for Simon's problem

A deterministic classical algorithm with oracle access to `f` is modelled by two functions:
given the history of query/answer pairs seen so far, it either asks a new query or produces its
output.  `QI.ClassicalAlg.Solves` says that after `m` queries the algorithm outputs the hidden
period for *every* instance satisfying Simon's promise.

The main result, `QI.classical_query_lower_bound`, is the adversary argument showing that such
an algorithm needs `m ≥ 2^{(n-1)/2}` queries.
-/

namespace QI

open Finset

/-- A deterministic classical query algorithm: `query h` is the next query to make after seeing
the history `h` of query/answer pairs, and `output h` is the answer it returns. -/
structure ClassicalAlg (n : ℕ) where
  /-- The next query, as a function of the history. -/
  query : List (BV n × BV n) → BV n
  /-- The final output, as a function of the history. -/
  output : List (BV n × BV n) → BV n

/-- The history of query/answer pairs produced by running `A` on the oracle `f` for `k` steps. -/
def transcript {n : ℕ} (A : ClassicalAlg n) (f : BV n → BV n) : ℕ → List (BV n × BV n)
  | 0 => []
  | (k + 1) =>
      transcript A f k ++ [(A.query (transcript A f k), f (A.query (transcript A f k)))]

/-- The set of points queried during the first `m` steps. -/
def queried {n : ℕ} (A : ClassicalAlg n) (f : BV n → BV n) (m : ℕ) : Finset (BV n) :=
  ((transcript A f m).map Prod.fst).toFinset

/-- `A` solves Simon's problem with `m` queries: on every instance satisfying the promise it
outputs the hidden period after `m` queries. -/
def ClassicalAlg.Solves {n : ℕ} (A : ClassicalAlg n) (m : ℕ) : Prop :=
  ∀ (f : BV n → BV n) (s : BV n), SimonPromise f s → A.output (transcript A f m) = s

lemma transcript_length {n : ℕ} (A : ClassicalAlg n) (f : BV n → BV n) (k : ℕ) :
    (transcript A f k).length = k := by
  induction k with
  | zero => simp [transcript]
  | succ k ih => simp [transcript, ih]

lemma queried_card_le {n : ℕ} (A : ClassicalAlg n) (f : BV n → BV n) (m : ℕ) :
    (queried A f m).card ≤ m := by
  refine le_trans (List.toFinset_card_le _) ?_
  simp [transcript_length]

lemma transcript_prefix {n : ℕ} (A : ClassicalAlg n) (f : BV n → BV n) {k m : ℕ} (h : k ≤ m) :
    transcript A f k <+: transcript A f m := by
  induction m with
  | zero =>
      have : k = 0 := Nat.le_zero.mp h
      subst this
      exact List.prefix_rfl
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hk | hk
      · exact (ih (Nat.lt_succ_iff.mp hk)).trans (List.prefix_append _ _)
      · have : k = m + 1 := le_antisymm h hk
        subst this
        exact List.prefix_rfl

lemma query_mem_queried {n : ℕ} (A : ClassicalAlg n) (f : BV n → BV n) {k m : ℕ} (h : k < m) :
    A.query (transcript A f k) ∈ queried A f m := by
  classical
  have hpair : (A.query (transcript A f k), f (A.query (transcript A f k)))
      ∈ transcript A f (k + 1) := by
    rw [transcript]
    simp
  have hsub : transcript A f (k + 1) <+: transcript A f m := transcript_prefix A f h
  have : (A.query (transcript A f k), f (A.query (transcript A f k))) ∈ transcript A f m :=
    hsub.subset hpair
  unfold queried
  simp only [List.mem_toFinset, List.mem_map]
  exact ⟨_, this, rfl⟩

/-- If an oracle `f` agrees with the identity on all points queried during the identity run,
then the whole run against `f` is identical to the run against the identity. -/
lemma transcript_eq_of_agree {n : ℕ} (A : ClassicalAlg n) (f : BV n → BV n) (m : ℕ)
    (hf : ∀ x ∈ queried A id m, f x = x) :
    ∀ k, k ≤ m → transcript A f k = transcript A id k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have hkm : k ≤ m := Nat.le_of_succ_le hk
      have hT : transcript A f k = transcript A id k := ih hkm
      have hq : f (A.query (transcript A id k)) = A.query (transcript A id k) :=
        hf _ (query_mem_queried A id (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk))
      rw [transcript, transcript, hT, hq]
      simp

/-- For `s ≠ 0` there is a canonical choice of representative in each pair `{x, x + s}`. -/
lemma exists_canonical_rep {n : ℕ} (s : BV n) (hs : s ≠ 0) :
    ∃ c : BV n → BV n, (∀ x, c x = x ∨ c x = x + s) ∧ (∀ x, c (x + s) = c x) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, s k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hs (funext hc)
  have hk1 : s k = 1 := zmod2_eq_one hk
  refine ⟨fun x => if x k = 0 then x else x + s, ?_, ?_⟩
  · intro x
    by_cases h : x k = 0
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])
  · intro x
    have hxx : x + s + s = x := by
      rw [add_assoc]; simp
    by_cases h : x k = 0
    · have h1 : (x + s) k = 1 := by simp [h, hk1]
      have h1' : ¬ ((x + s) k = 0) := by rw [h1]; exact one_ne_zero
      simp only [if_neg h1', if_pos h, hxx]
    · have hx1 : x k = 1 := zmod2_eq_one h
      have h0 : (x + s) k = 0 := by
        show x k + s k = 0
        rw [hx1, hk1]
        decide
      simp only [if_pos h0, if_neg h]

/-- The adversary's family of instances: for every `s` that is not a sum of two queried
points, there is an oracle satisfying Simon's promise with period `s` that answers all queried
points by the identity. -/
lemma exists_promise_agreeing {n : ℕ} (X : Finset (BV n)) (s : BV n) (hs : s ≠ 0)
    (hX : ∀ x ∈ X, ∀ y ∈ X, x + y ≠ s) :
    ∃ f : BV n → BV n, SimonPromise f s ∧ ∀ x ∈ X, f x = x := by
  classical
  obtain ⟨c, hc_mem, hc_shift⟩ := exists_canonical_rep s hs
  set f : BV n → BV n := fun x => if x ∈ X then x else if x + s ∈ X then x + s else c x with hf
  have hxx : ∀ x : BV n, x + s + s = x := by
    intro x; rw [add_assoc]; simp
  have hmem : ∀ x : BV n, f x = x ∨ f x = x + s := by
    intro x
    by_cases h1 : x ∈ X
    · exact Or.inl (by simp [hf, h1])
    · by_cases h2 : x + s ∈ X
      · exact Or.inr (by simp [hf, h1, h2])
      · rcases hc_mem x with h | h
        · exact Or.inl (by simp [hf, h1, h2, h])
        · exact Or.inr (by simp [hf, h1, h2, h])
  have hshift : ∀ x : BV n, f (x + s) = f x := by
    intro x
    have hnotboth : ¬ (x ∈ X ∧ x + s ∈ X) := by
      rintro ⟨h1, h2⟩
      have hsum : x + (x + s) = s := by
        rw [← add_assoc]; simp
      exact hX x h1 (x + s) h2 hsum
    simp only [hf]
    rw [hxx x, hc_shift x]
    by_cases h1 : x ∈ X
    · have h2 : x + s ∉ X := fun h2 => hnotboth ⟨h1, h2⟩
      simp [h1, h2]
    · by_cases h2 : x + s ∈ X
      · simp [h1, h2]
      · simp [h1, h2]
  refine ⟨f, ⟨hs, ?_⟩, ?_⟩
  · intro x y
    constructor
    · intro hxy
      rcases hmem x with hx | hx <;> rcases hmem y with hy | hy
      · exact Or.inl (by rw [← hx, ← hy, hxy])
      · refine Or.inr ?_
        have h : x = y + s := by rw [← hx, ← hy, hxy]
        rw [h, hxx]
      · refine Or.inr ?_
        have h : x + s = y := by rw [← hx, ← hy, hxy]
        rw [← h]
      · refine Or.inl ?_
        have h : x + s = y + s := by rw [← hx, ← hy, hxy]
        exact (add_right_cancel h).symm
    · rintro (h | h)
      · rw [h]
      · rw [h, hshift]
  · intro x hx
    simp [hf, hx]

/-- **Classical lower bound (adversary argument).**  If a deterministic classical algorithm
solves Simon's problem with `m` queries then `2ⁿ ≤ m² + 2`. -/
theorem classical_query_bound {n : ℕ} (A : ClassicalAlg n) (m : ℕ) (hA : A.Solves m) :
    2 ^ n ≤ m * m + 2 := by
  classical
  by_contra hlt
  push_neg at hlt
  set X : Finset (BV n) := queried A id m with hXdef
  have hXcard : X.card ≤ m := queried_card_le A id m
  -- the excluded periods
  set D : Finset (BV n) := insert 0 ((X ×ˢ X).image (fun p => p.1 + p.2)) with hDdef
  have hDcard : D.card ≤ m * m + 1 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h1 : ((X ×ˢ X).image (fun p => p.1 + p.2)).card ≤ (X ×ˢ X).card :=
      Finset.card_image_le
    have h2 : (X ×ˢ X).card = X.card * X.card := Finset.card_product X X
    have h3 : X.card * X.card ≤ m * m := Nat.mul_le_mul hXcard hXcard
    omega
  have hcard_univ : (Finset.univ : Finset (BV n)).card = 2 ^ n := by
    simp [Finset.card_univ]
  -- at least two admissible periods remain
  have hcompl : 2 ≤ (Finset.univ \ D).card := by
    have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
    rw [hcard_univ] at hsum
    have hDc : D.card ≤ m * m + 1 := hDcard
    have : m * m + 2 < 2 ^ n := hlt
    omega
  obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := Finset.one_lt_card.mp hcompl
  -- for any admissible period there is an instance the algorithm cannot distinguish
  have key : ∀ s ∈ Finset.univ \ D, A.output (transcript A id m) = s := by
    intro s hsmem
    have hsD : s ∉ D := (Finset.mem_sdiff.mp hsmem).2
    have hs0 : s ≠ 0 := by
      intro h; exact hsD (by rw [h]; exact Finset.mem_insert_self _ _)
    have hXs : ∀ x ∈ X, ∀ y ∈ X, x + y ≠ s := by
      intro x hx y hy hxy
      refine hsD (Finset.mem_insert_of_mem ?_)
      refine Finset.mem_image.mpr ⟨(x, y), ?_, hxy⟩
      exact Finset.mem_product.mpr ⟨hx, hy⟩
    obtain ⟨f, hf, hfid⟩ := exists_promise_agreeing X s hs0 hXs
    have hT : transcript A f m = transcript A id m :=
      transcript_eq_of_agree A f m (fun x hx => hfid x hx) m le_rfl
    have := hA f s hf
    rw [hT] at this
    exact this
  exact hne ((key s₁ hs₁).symm.trans (key s₂ hs₂))

/-- **Ω(2^{n/2}) classical queries are necessary.** -/
theorem classical_query_lower_bound {n : ℕ} (A : ClassicalAlg n) (m : ℕ) (hn : 2 ≤ n)
    (hA : A.Solves m) : 2 ^ ((n - 1) / 2) ≤ m := by
  have hb := classical_query_bound A m hA
  by_contra hlt
  push_neg at hlt
  set k := (n - 1) / 2 with hk
  have hmk : m + 1 ≤ 2 ^ k := hlt
  have h2k : 2 * k ≤ n - 1 := by omega
  have hkn : 2 ^ (2 * k) ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) h2k
  have hpow : 2 ^ k * 2 ^ k = 2 ^ (2 * k) := by
    rw [← pow_add]; ring_nf
  have h1 : (m + 1) * (m + 1) ≤ 2 ^ (n - 1) := by
    calc (m + 1) * (m + 1) ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul hmk hmk
      _ = 2 ^ (2 * k) := hpow
      _ ≤ 2 ^ (n - 1) := hkn
  have h2 : 2 ^ (n - 1) * 2 = 2 ^ n := by
    have hn1 : n - 1 + 1 = n := by omega
    rw [← pow_succ, hn1]
  have h3 : (4 : ℕ) ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  nlinarith [h1, h2, h3, hb]

end QI

import RequestProject.Simon.Classical

/-!
# Non-vacuity: promise instances exist, and Simon's problem is classically solvable

To make sure that the statements of the classical model are not vacuous we check that

* for every nonzero `s` there is an oracle satisfying Simon's promise with period `s`
  (`QI.exists_simonPromise`), and
* there *is* a deterministic classical algorithm solving Simon's problem, namely the brute-force
  one querying all `2ⁿ` points (`QI.exists_classical_solver`).

Together with `QI.classical_query_lower_bound` this shows that the classical query complexity of
Simon's problem lies between `2^{(n-1)/2}` and `2ⁿ`.
-/

namespace QI

open Finset

/-- Simon's promise is satisfiable for every nonzero period. -/
theorem exists_simonPromise {n : ℕ} (s : BV n) (hs : s ≠ 0) : ∃ f : BV n → BV n, SimonPromise f s :=
  let ⟨f, hf, _⟩ := exists_promise_agreeing (∅ : Finset (BV n)) s hs (by simp)
  ⟨f, hf⟩

/-- An enumeration of all bit strings. -/
noncomputable def enumBV (n : ℕ) (i : ℕ) : BV n := ((Finset.univ : Finset (BV n)).toList).getD i 0

lemma exists_enumBV (n : ℕ) (v : BV n) : ∃ i < 2 ^ n, enumBV n i = v := by
  classical
  have hmem : v ∈ (Finset.univ : Finset (BV n)).toList := by simp
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  have hlen : ((Finset.univ : Finset (BV n)).toList).length = 2 ^ n := by
    rw [Finset.length_toList, Finset.card_univ]
    simp
  refine ⟨i, by omega, ?_⟩
  rw [enumBV, List.getD_eq_getElem _ _ hi, hget]

open Classical in
/-- The brute-force classical algorithm: query all points, then output the unique nonzero
difference of two points with equal values. -/
noncomputable def bruteForce (n : ℕ) : ClassicalAlg n where
  query := fun h => enumBV n h.length
  output := fun h =>
    ∑ t ∈ (Finset.univ : Finset (BV n)).filter
      (fun t => t ≠ 0 ∧ ∃ p ∈ h, ∃ q ∈ h, p.2 = q.2 ∧ p.1 + q.1 = t), t

lemma bruteForce_transcript {n : ℕ} (f : BV n → BV n) (k : ℕ) :
    transcript (bruteForce n) f k = (List.range k).map (fun i => (enumBV n i, f (enumBV n i))) := by
  induction k with
  | zero => simp [transcript]
  | succ k ih =>
      have hlen : ((List.range k).map (fun i => (enumBV n i, f (enumBV n i)))).length = k := by
        simp
      have hquery : (bruteForce n).query
          ((List.range k).map (fun i => (enumBV n i, f (enumBV n i)))) = enumBV n k := by
        show enumBV n ((List.range k).map (fun i => (enumBV n i, f (enumBV n i)))).length = _
        rw [hlen]
      rw [transcript, ih, hquery, List.range_succ]
      simp

/-- The brute-force algorithm solves Simon's problem with `2ⁿ` queries. -/
theorem bruteForce_solves (n : ℕ) : (bruteForce n).Solves (2 ^ n) := by
  classical
  intro f s hf
  set h := transcript (bruteForce n) f (2 ^ n) with hh
  have hmem : ∀ p ∈ h, p = (p.1, f p.1) := by
    intro p hp
    rw [hh, bruteForce_transcript] at hp
    simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨i, _, hi⟩ := hp
    rw [← hi]
  have hq : ∀ v : BV n, (v, f v) ∈ h := by
    intro v
    obtain ⟨i, hi, hv⟩ := exists_enumBV n v
    rw [hh, bruteForce_transcript]
    simp only [List.mem_map, List.mem_range]
    exact ⟨i, hi, by rw [hv]⟩
  have hfilter : (Finset.univ : Finset (BV n)).filter
      (fun t => t ≠ 0 ∧ ∃ p ∈ h, ∃ q ∈ h, p.2 = q.2 ∧ p.1 + q.1 = t) = {s} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨ht0, p, hp, q, hqm, hpq, hsum⟩
      have hp' := hmem p hp
      have hq' := hmem q hqm
      have hval : f p.1 = f q.1 := by
        have h1 : p.2 = f p.1 := by rw [hp']
        have h2 : q.2 = f q.1 := by rw [hq']
        rw [← h1, ← h2, hpq]
      rcases (hf.fibre p.1 q.1).1 hval with hc | hc
      · exfalso
        apply ht0
        rw [← hsum, hc]
        simp
      · rw [← hsum, hc, ← add_assoc]
        simp
    · intro hts
      rw [hts]
      refine ⟨hf.ne_zero, (0, f 0), hq 0, (0 + s, f (0 + s)), hq _, ?_, ?_⟩
      · exact (hf.period 0).symm
      · simp
  show (bruteForce n).output h = s
  rw [bruteForce]
  simp only
  rw [hfilter, Finset.sum_singleton]

/-- There is a deterministic classical algorithm solving Simon's problem (with `2ⁿ` queries), so
the lower bound `QI.classical_query_lower_bound` is not vacuous. -/
theorem exists_classical_solver (n : ℕ) : ∃ A : ClassicalAlg n, A.Solves (2 ^ n) :=
  ⟨bruteForce n, bruteForce_solves n⟩

end QI

