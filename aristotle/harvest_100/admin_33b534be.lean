/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

/-! ### Arithmetic in `ZMod 2` -/

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

lemma zmod2_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

lemma zmod2_add_one_ne_self (a : ZMod 2) : a + 1 ≠ a := by revert a; decide

lemma zmod2_add_eq_zero (a b : ZMod 2) : a + b = 0 ↔ a = b := by revert a b; decide

/-! ### The hypercube graph -/

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2

/-- Flip the `i`-th coordinate of a hypercube vertex. -/
def flipAt {k : ℕ} (x : Cube k) (i : Fin k) : Cube k := Function.update x i (x i + 1)

lemma flipAt_self {k : ℕ} (x : Cube k) (i : Fin k) : flipAt x i i = x i + 1 := by
  simp [flipAt]

lemma flipAt_of_ne {k : ℕ} (x : Cube k) {i j : Fin k} (h : j ≠ i) : flipAt x i j = x j := by
  simp [flipAt, h]

lemma flipAt_flipAt {k : ℕ} (x : Cube k) (i : Fin k) : flipAt (flipAt x i) i = x := by
  funext j
  by_cases h : j = i
  · subst h
    rw [flipAt_self, flipAt_self, add_assoc, zmod2_one_add_one, add_zero]
  · rw [flipAt_of_ne _ h, flipAt_of_ne _ h]

lemma flipAt_ne {k : ℕ} (x : Cube k) (i : Fin k) : flipAt x i ≠ x := by
  intro h
  have h1 := congrFun h i
  rw [flipAt_self] at h1
  exact zmod2_add_one_ne_self (x i) h1

lemma flipAt_injective {k : ℕ} (x : Cube k) : Function.Injective (flipAt x) := by
  intro i j h
  by_contra hij
  have h1 := congrFun h i
  rw [flipAt_self, flipAt_of_ne x hij] at h1
  exact zmod2_add_one_ne_self (x i) h1

/-- The hypercube graph `Q k`: two binary strings of length `k` are adjacent iff they differ in
exactly one coordinate. -/
def hypercube (k : ℕ) : SimpleGraph (Cube k) where
  Adj x y := ∃ i, y = flipAt x i
  symm := by
    rintro x y ⟨i, rfl⟩
    exact ⟨i, (flipAt_flipAt x i).symm⟩
  loopless := ⟨by
    rintro x ⟨i, h⟩
    exact flipAt_ne x i h.symm⟩

instance (k : ℕ) : DecidableRel (hypercube k).Adj :=
  fun x y => inferInstanceAs (Decidable (∃ i, y = flipAt x i))

lemma hypercube_adj_iff {k : ℕ} (x y : Cube k) :
    (hypercube k).Adj x y ↔ ∃ i, y = flipAt x i := Iff.rfl

lemma hypercube_neighborFinset {k : ℕ} (x : Cube k) :
    (hypercube k).neighborFinset x = Finset.image (flipAt x) Finset.univ := by
  ext y
  simp [SimpleGraph.mem_neighborFinset, hypercube_adj_iff, eq_comm]

lemma hypercube_degree {k : ℕ} (x : Cube k) : (hypercube k).degree x = k := by
  rw [SimpleGraph.degree, hypercube_neighborFinset,
    Finset.card_image_of_injective _ (flipAt_injective x)]
  simp

lemma lap_mulVec_apply {k : ℕ} (f : Cube k → ℝ) (x : Cube k) :
    ((hypercube k).lapMatrix ℝ *ᵥ f) x = k * f x - ∑ i, f (flipAt x i) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply, hypercube_degree, hypercube_neighborFinset,
    Finset.sum_image (fun i _ j _ h => flipAt_injective x h)]

/-! ### Characters of the hypercube -/

/-- The `±1`-valued sign of an element of `ZMod 2`. -/
def sgn (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

lemma sgn_zero : sgn 0 = 1 := by simp [sgn]

lemma sgn_one : sgn 1 = -1 := by simp [sgn]

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [sgn, zmod2_one_add_one]

lemma sgn_ne_zero (a : ZMod 2) : sgn a ≠ 0 := by
  rcases zmod2_cases a with rfl | rfl <;> simp [sgn]

lemma sum_sgn_mul (b : ZMod 2) : ∑ a : ZMod 2, sgn (a * b) = if b = 0 then 2 else 0 := by
  rcases zmod2_cases b with rfl | rfl
  · simp [sgn]
  · rw [if_neg zmod2_one_ne_zero,
      show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide,
      Finset.sum_insert (by decide), Finset.sum_singleton, mul_one, mul_one,
      sgn_zero, sgn_one]
    ring

/-- The character `χ_s` of the hypercube associated with `s`. -/
def chi {k : ℕ} (s x : Cube k) : ℝ := ∏ i, sgn (s i * x i)

lemma chi_ne_zero {k : ℕ} (s x : Cube k) : chi s x ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => sgn_ne_zero _

lemma chi_flipAt {k : ℕ} (s x : Cube k) (i : Fin k) :
    chi s (flipAt x i) = sgn (s i) * chi s x := by
  classical
  unfold chi
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => sgn (s j * x j)) (Finset.mem_univ i)]
  have h1 : sgn (s i * flipAt x i i) = sgn (s i) * sgn (s i * x i) := by
    rw [flipAt_self, mul_add, mul_one, add_comm, sgn_add]
  rw [h1]
  have h2 : ∀ j ∈ Finset.univ.erase i, sgn (s j * flipAt x i j) = sgn (s j * x j) := by
    intro j hj
    rw [flipAt_of_ne _ (Finset.mem_erase.mp hj).1]
  rw [Finset.prod_congr rfl h2]
  ring

lemma chi_mul {k : ℕ} (s x y : Cube k) : chi s x * chi s y = chi s (x + y) := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← sgn_add]
  congr 1
  simp only [Pi.add_apply]
  ring

/-- The Hamming weight of `s`, i.e. the number of nonzero coordinates. -/
def wt {k : ℕ} (s : Cube k) : ℕ := (Finset.univ.filter (fun i => s i ≠ 0)).card

lemma sum_sgn {k : ℕ} (s : Cube k) : ∑ i, sgn (s i) = (k : ℝ) - 2 * wt s := by
  classical
  have h : ∀ i : Fin k, sgn (s i) = 1 - 2 * (if s i ≠ 0 then (1 : ℝ) else 0) := by
    intro i
    by_cases hi : s i = 0
    · simp [sgn, hi]
    · simp [sgn, hi]
      norm_num
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_boole]
  simp [wt]

/-- `χ_s` is an eigenvector of the hypercube Laplacian with eigenvalue `2 * wt s`. -/
lemma lap_chi {k : ℕ} (s : Cube k) :
    (hypercube k).lapMatrix ℝ *ᵥ (chi s) = (2 * wt s : ℝ) • (chi s) := by
  funext x
  rw [lap_mulVec_apply]
  have h : ∑ i, chi s (flipAt x i) = (∑ i, sgn (s i)) * chi s x := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => chi_flipAt s x i
  rw [h, sum_sgn]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The Fourier transform on the hypercube -/

/-- The Fourier coefficient of `f` at `s`. -/
def hat {k : ℕ} (f : Cube k → ℝ) (s : Cube k) : ℝ := ∑ x, f x * chi s x

lemma hat_lap {k : ℕ} (f : Cube k → ℝ) (s : Cube k) :
    hat ((hypercube k).lapMatrix ℝ *ᵥ f) s = (2 * wt s : ℝ) * hat f s := by
  classical
  have key : ∀ i : Fin k, ∑ x, f (flipAt x i) * chi s x = sgn (s i) * hat f s := by
    intro i
    let e : Equiv.Perm (Cube k) :=
      Function.Involutive.toPerm (fun x => flipAt x i) (fun x => flipAt_flipAt x i)
    have he : ∀ x : Cube k, e x = flipAt x i := fun _ => rfl
    calc ∑ x, f (flipAt x i) * chi s x
        = ∑ x, (fun y => f y * chi s (flipAt y i)) (e x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [he, flipAt_flipAt]
      _ = ∑ y, f y * chi s (flipAt y i) := Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = sgn (s i) * hat f s := by
          rw [hat, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [chi_flipAt]
          ring
  unfold hat
  have hterm : ∀ x : Cube k, ((hypercube k).lapMatrix ℝ *ᵥ f) x * chi s x
      = (k : ℝ) * (f x * chi s x) - ∑ i, f (flipAt x i) * chi s x := by
    intro x
    rw [lap_mulVec_apply, sub_mul, Finset.sum_mul]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_comm, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => key i),
    ← Finset.sum_mul, sum_sgn]
  simp only [hat]
  ring

lemma sum_chi {k : ℕ} (z : Cube k) :
    ∑ s : Cube k, chi s z = if z = 0 then (2 ^ k : ℝ) else 0 := by
  classical
  have h : ∑ s : Cube k, chi s z = ∏ i : Fin k, (∑ a : ZMod 2, sgn (a * z i)) := by
    rw [Fintype.prod_sum (fun (i : Fin k) (a : ZMod 2) => sgn (a * z i))]
    rfl
  rw [h]
  by_cases hz : z = 0
  · subst hz
    have : ∀ i : Fin k, (∑ a : ZMod 2, sgn (a * (0 : Cube k) i)) = 2 := by
      intro i
      rw [sum_sgn_mul]
      simp
    rw [Finset.prod_congr rfl (fun i _ => this i)]
    simp
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hz (funext hc)
    rw [if_neg hz]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [sum_sgn_mul, if_neg hi]

lemma hat_eq_zero_imp {k : ℕ} (f : Cube k → ℝ) (h : ∀ s, hat f s = 0) : f = 0 := by
  classical
  funext x
  simp only [Pi.zero_apply]
  have key : ∑ s : Cube k, hat f s * chi s x = (2 ^ k : ℝ) * f x := by
    have h1 : ∑ s : Cube k, hat f s * chi s x
        = ∑ s : Cube k, ∑ y : Cube k, f y * chi s (y + x) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hat, Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => by rw [mul_assoc, chi_mul]
    have h3 : ∀ y : Cube k, (y + x = 0) ↔ y = x := by
      intro y
      constructor
      · intro hy
        funext i
        have hyi := congrFun hy i
        simp only [Pi.add_apply, Pi.zero_apply] at hyi
        exact (zmod2_add_eq_zero (y i) (x i)).mp hyi
      · rintro rfl
        funext i
        simp only [Pi.add_apply, Pi.zero_apply]
        exact (zmod2_add_eq_zero _ _).mpr rfl
    have h2 : ∀ y : Cube k, ∑ s : Cube k, f y * chi s (y + x)
        = if y = x then f y * (2 ^ k : ℝ) else 0 := by
      intro y
      rw [← Finset.mul_sum, sum_chi]
      simp only [h3 y]
      by_cases hy : y = x <;> simp [hy]
    rw [h1, Finset.sum_comm, Finset.sum_congr rfl (fun y _ => h2 y),
      Finset.sum_ite_eq' Finset.univ x (fun y => f y * (2 ^ k : ℝ))]
    simp only [Finset.mem_univ, if_true]
    ring
  simp only [h, zero_mul, Finset.sum_const_zero] at key
  have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
  rcases mul_eq_zero.mp key.symm with h' | h'
  · exact absurd h' h2
  · exact h'

/-! ### The spectral gap -/

/-- Every nonzero eigenvalue of the hypercube Laplacian is at least `2`. -/
lemma eigenvalue_ge_two {k : ℕ} {mu : ℝ} (hmu : mu ≠ 0) {f : Cube k → ℝ} (hf : f ≠ 0)
    (heig : (hypercube k).lapMatrix ℝ *ᵥ f = mu • f) : 2 ≤ mu := by
  classical
  obtain ⟨s, hs⟩ : ∃ s, hat f s ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf (hat_eq_zero_imp f hc)
  have h1 : (2 * wt s : ℝ) * hat f s = mu * hat f s := by
    have hl := hat_lap f s
    rw [heig] at hl
    rw [← hl, hat, hat, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have h2 : (2 * wt s : ℝ) = mu := mul_right_cancel₀ hs h1
  have h3 : wt s ≠ 0 := by
    intro h
    rw [h] at h2
    simp only [Nat.cast_zero, mul_zero] at h2
    exact hmu h2.symm
  have h4 : (1 : ℝ) ≤ (wt s : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h3
  rw [← h2]
  linarith

/-- **Uniform spectral gap for the hypercube family.**
For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian of the hypercube graph
`Q k` (on `2 ^ k` vertices) equals `2`. Since the bound `2` does not depend on `k`, the family
`(Q k)_{k ≥ 1}` has a uniform spectral gap. -/
theorem expander_uniform_gap_witness (k : ℕ) (hk : 1 ≤ k) :
    IsLeast {mu : ℝ | mu ≠ 0 ∧ ∃ f : Cube k → ℝ, f ≠ 0 ∧
      (hypercube k).lapMatrix ℝ *ᵥ f = mu • f} 2 := by
  classical
  constructor
  · -- `2` is an eigenvalue, witnessed by the character of a weight-one vector.
    refine ⟨two_ne_zero, chi (Pi.single ⟨0, hk⟩ 1), ?_, ?_⟩
    · intro hc
      have hz := congrFun hc 0
      simp only [Pi.zero_apply] at hz
      exact chi_ne_zero _ _ hz
    · have hw : wt (Pi.single (⟨0, hk⟩ : Fin k) (1 : ZMod 2)) = 1 := by
        rw [wt, Finset.card_eq_one]
        refine ⟨⟨0, hk⟩, ?_⟩
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hi
          by_contra hne
          exact hi (by simp [Pi.single_eq_of_ne hne])
        · rintro rfl
          simp
      have hl := lap_chi (Pi.single (⟨0, hk⟩ : Fin k) (1 : ZMod 2))
      rw [hw] at hl
      simpa using hl
  · rintro mu ⟨hmu, f, hf, heig⟩
    exact eigenvalue_ge_two hmu hf heig

/-- **Existence of a uniform-gap family.** There is a positive constant `c` (namely `c = 2`)
such that for every `k ≥ 1` the smallest nonzero Laplacian eigenvalue of the hypercube graph
`Q k` equals `c`; in particular the gap is bounded below independently of the number `2 ^ k`
of vertices. -/
theorem exists_uniform_spectral_gap_family :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      IsLeast {mu : ℝ | mu ≠ 0 ∧ ∃ f : Cube k → ℝ, f ≠ 0 ∧
        (hypercube k).lapMatrix ℝ *ᵥ f = mu • f} c :=
  ⟨2, two_pos, expander_uniform_gap_witness⟩

end Frontier.Spectral

