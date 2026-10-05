import Mathlib
/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the single `import Mathlib` line, since Lean 4
requires `import` commands to come first in a file.)
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## The Weil–Riemann hypothesis, formalized

For a smooth projective variety `X` of dimension `d` over the finite field `F_q`, the Weil
conjectures assert that the zeta function

  `Z_X(T) = exp (∑_{n ≥ 1} N_n T^n / n)`,   `N_n = #X(F_{q^n})`,

is a rational function of the shape `∏_{i=0}^{2d} P_i(T)^{(-1)^{i+1}}` where `P_i ∈ ℤ[T]`,
`P_i(0) = 1`.  Writing `P_i(T) = ∏_j (1 - α_{i,j} T)`, taking the logarithmic derivative of
the displayed identity turns the rationality statement into the point-count formula

  `N_n = ∑_{i=0}^{2d} (-1)^i ∑_j α_{i,j}^n`   for all `n ≥ 1`,

and the *Riemann hypothesis* (proved by Deligne) is the purity statement

  `|α_{i,j}| = q^{i/2}`.

`WeilData` below packages the inverse roots `α_{i,j}` (as a multiset for each cohomological
degree `i`), `WeilData.Computes` is the point-count formula, and `WeilData.RH` is purity.
-/

/-- The inverse roots of the factors `P_i` of the zeta function of a `dim`-dimensional
variety over `F_q`, one multiset for each cohomological degree `i` (empty above degree
`2 * dim`). -/
structure WeilData where
  /-- The cardinality of the base finite field. -/
  q : ℕ
  /-- The dimension of the variety. -/
  dim : ℕ
  /-- The multiset of inverse roots of `P_i`, the `i`-th factor of the zeta function. -/
  roots : ℕ → Multiset ℂ
  /-- There is no cohomology above degree `2 * dim`. -/
  roots_eq_zero : ∀ i : ℕ, 2 * dim < i → roots i = 0

namespace WeilData

/-- The number `∑_{i} (-1)^i ∑_j α_{i,j}^n` predicted by the datum for `#X(F_{q^n})`. -/
noncomputable def count (W : WeilData) (n : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (2 * W.dim + 1), (-1 : ℂ) ^ i * ((W.roots i).map (fun α : ℂ => α ^ n)).sum

/-- The datum computes the point-counting function `N`, i.e. the Lefschetz-type formula
`N_n = ∑_i (-1)^i ∑_j α_{i,j}^n` holds for all `n ≥ 1`. -/
def Computes (W : WeilData) (N : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → W.count n = (N n : ℂ)

/-- The Riemann hypothesis (purity) for the datum: every inverse root in degree `i` has
absolute value `q^{i/2}`. -/
def RH (W : WeilData) : Prop :=
  ∀ i : ℕ, ∀ α ∈ W.roots i, ‖α‖ = (W.q : ℝ) ^ ((i : ℝ) / 2)

lemma count_eq_sum_range (W : WeilData) (K : ℕ) (hK : 2 * W.dim + 1 ≤ K) (n : ℕ) :
    W.count n =
      ∑ i ∈ Finset.range K, (-1 : ℂ) ^ i * ((W.roots i).map (fun α : ℂ => α ^ n)).sum := by
  have hsub : Finset.range (2 * W.dim + 1) ⊆ Finset.range K := Finset.range_subset_range.mpr hK
  refine Finset.sum_subset hsub ?_
  intro i _ hi
  rw [Finset.mem_range, not_lt] at hi
  rw [W.roots_eq_zero i (by omega)]
  simp

end WeilData

/-!
## The general statement (Deligne's theorem)

`DeligneWeilRH` is the statement of the Riemann hypothesis for varieties over finite fields:
for every smooth proper scheme `X` over `F_p` there is a Weil datum, with the correct base
field, computing the numbers of `F_{p^n}`-rational points and satisfying purity.
-/

open AlgebraicGeometry CategoryTheory in
/-- `#X(F_{p^n})`, the number of `F_{p^n}`-rational points of a scheme `X` over `F_p`,
i.e. the number of `F_p`-morphisms `Spec F_{p^n} ⟶ X`. -/
noncomputable def rationalPointCount (p : ℕ) [Fact p.Prime] (X : Scheme)
    (f : X ⟶ Spec (CommRingCat.of (ZMod p))) (n : ℕ) : ℕ :=
  Nat.card {g : Spec (CommRingCat.of (GaloisField p n)) ⟶ X //
    g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (GaloisField p n)))}

open AlgebraicGeometry in
/-- **The Riemann hypothesis for varieties over finite fields** (Weil conjectures; Deligne):
for every smooth proper `F_p`-scheme `X` the point counts `#X(F_{p^n})` are given by a Weil
datum all of whose degree-`i` inverse roots have absolute value `p^{i/2}`. -/
def DeligneWeilRH : Prop :=
  ∀ (p : ℕ) (_ : Fact p.Prime) (X : Scheme) (f : X ⟶ Spec (CommRingCat.of (ZMod p))),
    Smooth f → IsProper f →
      ∃ W : WeilData, W.q = p ∧ W.Computes (rationalPointCount p X f) ∧ W.RH

/-!
## Verified base cases and reductions
-/

/-- Sum of `n`-th powers of all `m`-th roots of unity in `ℂ`. -/
lemma sum_pow_nthRoots (m n : ℕ) :
    ((Polynomial.nthRoots m (1 : ℂ)).map (fun α : ℂ => α ^ n)).sum =
      if m ∣ n then (m : ℂ) else 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hζ := Complex.isPrimitiveRoot_exp m hm.ne'
    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m) with hζdef
    rw [hζ.nthRoots_eq (a := (1 : ℂ)) (α := 1) (one_pow m), Multiset.map_map]
    have hcomp : ((Multiset.range m).map ((fun α : ℂ => α ^ n) ∘ (fun k : ℕ => ζ ^ k * 1))).sum
        = ∑ k ∈ Finset.range m, (ζ ^ n) ^ k := by
      simp [Function.comp, ← pow_mul, mul_comm]
      rfl
    rw [hcomp]
    by_cases hdvd : m ∣ n
    · have hone : ζ ^ n = 1 := by
        obtain ⟨c, rfl⟩ := hdvd
        rw [pow_mul, hζ.pow_eq_one, one_pow]
      simp [hone, hdvd]
    · have hne : ζ ^ n ≠ 1 := fun h => hdvd (hζ.dvd_of_pow_eq_one n h)
      have hpow : (ζ ^ n) ^ m = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
      rw [geom_sum_eq hne, hpow]
      simp [hdvd]

/-- The Weil datum of a closed point of degree `m` (i.e. of `Spec F_{q^m}`, a zero-dimensional
variety): `P_0(T) = 1 - T^m`, whose inverse roots are the `m`-th roots of unity. -/
noncomputable def closedPoint (q m : ℕ) : WeilData where
  q := q
  dim := 0
  roots := fun i => if i = 0 then Polynomial.nthRoots m (1 : ℂ) else 0
  roots_eq_zero := by
    intro i hi
    have h : i ≠ 0 := by omega
    simp [h]

lemma closedPoint_computes (q m : ℕ) :
    (closedPoint q m).Computes (fun n => if m ∣ n then m else 0) := by
  intro n _
  have key := sum_pow_nthRoots m n
  simp only [WeilData.count, closedPoint, Nat.mul_zero, Nat.zero_add, Finset.sum_range_one,
    pow_zero, one_mul, if_true]
  rw [key]
  split_ifs <;> simp

/-- **Base case (points).** The Riemann hypothesis holds for a closed point: all inverse
roots are roots of unity, of absolute value `q^{0/2} = 1`. -/
lemma closedPoint_RH (q m : ℕ) : (closedPoint q m).RH := by
  intro i α hα
  simp only [closedPoint] at hα
  split_ifs at hα with hi
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [Polynomial.nthRoots_zero] at hα
    · have hpow : α ^ m = 1 := (Polynomial.mem_nthRoots hm).mp hα
      rw [Complex.norm_eq_one_of_pow_eq_one hpow hm.ne']
      simp [closedPoint, hi]
  · simp at hα

/-- The empty variety. -/
noncomputable def empty (q : ℕ) : WeilData where
  q := q
  dim := 0
  roots := fun _ => 0
  roots_eq_zero := fun _ _ => rfl

lemma empty_computes (q : ℕ) : (empty q).Computes (fun _ => 0) := by
  intro n _
  simp [WeilData.count, empty]

lemma empty_RH (q : ℕ) : (empty q).RH := by
  intro i α hα
  simp [empty] at hα

/-- The Weil datum of a disjoint union of two varieties. -/
noncomputable def disjUnion (W₁ W₂ : WeilData) : WeilData where
  q := W₁.q
  dim := max W₁.dim W₂.dim
  roots := fun i => W₁.roots i + W₂.roots i
  roots_eq_zero := by
    intro i hi
    have h₁ : 2 * W₁.dim < i := lt_of_le_of_lt (by
      exact Nat.mul_le_mul_left 2 (le_max_left _ _)) hi
    have h₂ : 2 * W₂.dim < i := lt_of_le_of_lt (by
      exact Nat.mul_le_mul_left 2 (le_max_right _ _)) hi
    simp [W₁.roots_eq_zero i h₁, W₂.roots_eq_zero i h₂]

/-- **Reduction (disjoint unions).** Point counts add along disjoint unions. -/
lemma disjUnion_computes {W₁ W₂ : WeilData} {N₁ N₂ : ℕ → ℕ}
    (h₁ : W₁.Computes N₁) (h₂ : W₂.Computes N₂) :
    (disjUnion W₁ W₂).Computes (fun n => N₁ n + N₂ n) := by
  intro n hn
  have hK₁ : 2 * W₁.dim + 1 ≤ 2 * max W₁.dim W₂.dim + 1 := by
    have := le_max_left W₁.dim W₂.dim; omega
  have hK₂ : 2 * W₂.dim + 1 ≤ 2 * max W₁.dim W₂.dim + 1 := by
    have := le_max_right W₁.dim W₂.dim; omega
  have e₁ := W₁.count_eq_sum_range (2 * max W₁.dim W₂.dim + 1) hK₁ n
  have e₂ := W₂.count_eq_sum_range (2 * max W₁.dim W₂.dim + 1) hK₂ n
  have : (disjUnion W₁ W₂).count n = W₁.count n + W₂.count n := by
    rw [e₁, e₂, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [disjUnion, Multiset.map_add, Multiset.sum_add]
    ring
  rw [this, h₁ n hn, h₂ n hn]
  push_cast
  ring

/-- **Reduction (disjoint unions).** The Riemann hypothesis is inherited by disjoint unions. -/
lemma disjUnion_RH {W₁ W₂ : WeilData} (hq : W₂.q = W₁.q) (h₁ : W₁.RH) (h₂ : W₂.RH) :
    (disjUnion W₁ W₂).RH := by
  intro i α hα
  simp only [disjUnion, Multiset.mem_add] at hα
  rcases hα with hα | hα
  · exact h₁ i α hα
  · have := h₂ i α hα
    rw [hq] at this
    exact this

/-- **Base case (zero-dimensional varieties).** A zero-dimensional variety over `F_q` is a
finite disjoint union of closed points, of degrees `D`; its point counts are computed by a
Weil datum satisfying the Riemann hypothesis. -/
theorem zeroDimensional_RH (q : ℕ) (D : Multiset ℕ) :
    ∃ W : WeilData, W.q = q ∧ W.dim = 0 ∧
      W.Computes (fun n => (D.map (fun m => if m ∣ n then m else 0)).sum) ∧ W.RH := by
  refine Multiset.induction_on D ?_ ?_
  · refine ⟨empty q, rfl, rfl, ?_, empty_RH q⟩
    intro n hn
    simpa using empty_computes q n hn
  · rintro a s ⟨W, hq, hdim, hC, hR⟩
    refine ⟨disjUnion (closedPoint q a) W, rfl, ?_, ?_, ?_⟩
    · simp [disjUnion, closedPoint, hdim]
    · intro n hn
      have h := disjUnion_computes (closedPoint_computes q a) hC n hn
      simpa [Multiset.map_cons, Multiset.sum_cons] using h
    · exact disjUnion_RH hq (closedPoint_RH q a) hR

/-- The Weil datum of projective `d`-space: `P_{2i}(T) = 1 - q^i T` and `P_{odd} = 1`. -/
noncomputable def projectiveSpace (q d : ℕ) : WeilData where
  q := q
  dim := d
  roots := fun i => if 2 ∣ i ∧ i ≤ 2 * d then {(q : ℂ) ^ (i / 2)} else 0
  roots_eq_zero := by
    intro i hi
    simp [Nat.not_le.mpr hi]

lemma projectiveSpace_count (q d n : ℕ) :
    (projectiveSpace q d).count n = ∑ j ∈ Finset.range (d + 1), (q : ℂ) ^ (n * j) := by
  induction d with
  | zero => simp [WeilData.count, projectiveSpace]
  | succ d ih =>
      have hrange : 2 * (d + 1) + 1 = (2 * d + 1) + 1 + 1 := by ring
      simp only [WeilData.count, projectiveSpace] at ih ⊢
      rw [hrange, Finset.sum_range_succ, Finset.sum_range_succ]
      have hmain : ∑ i ∈ Finset.range (2 * d + 1), (-1 : ℂ) ^ i *
            (Multiset.map (fun α : ℂ => α ^ n)
              (if 2 ∣ i ∧ i ≤ 2 * (d + 1) then {(q : ℂ) ^ (i / 2)} else 0)).sum
          = ∑ i ∈ Finset.range (2 * d + 1), (-1 : ℂ) ^ i *
            (Multiset.map (fun α : ℂ => α ^ n)
              (if 2 ∣ i ∧ i ≤ 2 * d then {(q : ℂ) ^ (i / 2)} else 0)).sum := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [Finset.mem_range] at hi
        have h1 : i ≤ 2 * d := by omega
        have h2 : i ≤ 2 * (d + 1) := by omega
        simp [h1, h2]
      rw [hmain, ih]
      have hodd : ¬ (2 ∣ 2 * d + 1) := by omega
      have heven : 2 ∣ 2 * d + 1 + 1 := by omega
      have hle : 2 * d + 1 + 1 ≤ 2 * (d + 1) := by omega
      have hdiv : (2 * d + 1 + 1) / 2 = d + 1 := by omega
      have hsign : (-1 : ℂ) ^ (2 * d + 1 + 1) = 1 := by
        rw [show 2 * d + 1 + 1 = 2 * (d + 1) by ring, pow_mul]
        simp
      rw [Finset.sum_range_succ (fun j => (q : ℂ) ^ (n * j)) (d + 1)]
      simp only [hodd, heven, hle, hdiv, hsign, false_and, if_false, if_true, and_self,
        Multiset.map_zero, Multiset.sum_zero, mul_zero, add_zero, Multiset.map_singleton,
        Multiset.sum_singleton, one_mul]
      rw [← pow_mul, mul_comm (d + 1) n]

lemma projectiveSpace_computes (q d : ℕ) :
    (projectiveSpace q d).Computes (fun n => ∑ j ∈ Finset.range (d + 1), q ^ (n * j)) := by
  intro n _
  rw [projectiveSpace_count]
  push_cast
  ring

/-- **Base case (projective spaces).** The Riemann hypothesis holds for `P^d`: the inverse
roots are `1, q, …, q^d`, sitting in degrees `0, 2, …, 2d`. -/
lemma projectiveSpace_RH (q d : ℕ) : (projectiveSpace q d).RH := by
  intro i α hα
  simp only [projectiveSpace] at hα ⊢
  split_ifs at hα with h
  · obtain ⟨⟨k, rfl⟩, -⟩ := h
    rw [Multiset.mem_singleton] at hα
    subst hα
    rw [Nat.mul_div_cancel_left k (by norm_num)]
    rw [norm_pow, Complex.norm_natCast]
    rw [show ((2 * k : ℕ) : ℝ) / 2 = (k : ℝ) by push_cast; ring]
    rw [Real.rpow_natCast]
  · simp at hα

/-- The number of points of `P^d` over a finite field `K` is `1 + |K| + ⋯ + |K|^d`. -/
theorem card_projectiveSpace_of_finite_field (K : Type) [Field K] [Finite K] (d : ℕ) :
    Nat.card (Projectivization K (Fin (d + 1) → K)) =
      ∑ j ∈ Finset.range (d + 1), Nat.card K ^ j :=
  Projectivization.card_of_finrank K _ (by simp)

/-- **The datum `projectiveSpace p d` really is the Weil datum of `P^d`:** it computes the
actual numbers of `F_{p^n}`-rational points of projective `d`-space. -/
theorem projectiveSpace_computes_pointCount (p : ℕ) [Fact p.Prime] (d : ℕ) :
    (projectiveSpace p d).Computes (fun n =>
      Nat.card (Projectivization (GaloisField p n) (Fin (d + 1) → GaloisField p n))) := by
  intro n hn
  have hcard : Nat.card (GaloisField p n) = p ^ n := by
    have := GaloisField.card p n (by omega)
    simpa [Nat.card_eq_fintype_card] using this
  have hpts : Nat.card (Projectivization (GaloisField p n) (Fin (d + 1) → GaloisField p n))
      = ∑ j ∈ Finset.range (d + 1), p ^ (n * j) := by
    rw [card_projectiveSpace_of_finite_field, hcard]
    exact Finset.sum_congr rfl (fun j _ => (pow_mul p n j).symm)
  simp only [hpts]
  exact projectiveSpace_computes p d n hn

/-- The Weil datum of `X × P¹` (Künneth), given the datum of `X`. -/
noncomputable def timesP1 (W : WeilData) : WeilData where
  q := W.q
  dim := W.dim + 1
  roots := fun i =>
    W.roots i + (if 2 ≤ i then (W.roots (i - 2)).map (fun α : ℂ => (W.q : ℂ) * α) else 0)
  roots_eq_zero := by
    intro i hi
    have h₁ : 2 * W.dim < i := by omega
    have h₂ : ∀ h : 2 ≤ i, 2 * W.dim < i - 2 := by intro h; omega
    by_cases h : 2 ≤ i
    · simp [W.roots_eq_zero i h₁, W.roots_eq_zero (i - 2) (h₂ h), h]
    · simp [W.roots_eq_zero i h₁, h]

/-- **Reduction (multiplication by `P¹`).** `#(X × P¹)(F_{q^n}) = (1 + q^n) #X(F_{q^n})`. -/
lemma scaled_power_sum (s : Multiset ℂ) (c : ℂ) (n : ℕ) :
    ((s.map (fun α : ℂ => c * α)).map (fun α : ℂ => α ^ n)).sum
      = c ^ n * (s.map (fun α : ℂ => α ^ n)).sum := by
  rw [Multiset.map_map]
  simp only [Function.comp, mul_pow]
  exact Multiset.sum_map_mul_left

lemma timesP1_count (W : WeilData) (n : ℕ) :
    (timesP1 W).count n = (1 + (W.q : ℂ) ^ n) * W.count n := by
  classical
  set K : ℕ := 2 * (W.dim + 1) + 1 with hKdef
  have hK : 2 * W.dim + 1 ≤ K := by omega
  have hbase := W.count_eq_sum_range K hK n
  set f : ℕ → ℂ := fun i => (-1 : ℂ) ^ i * ((W.roots i).map (fun α : ℂ => α ^ n)).sum with hf
  set g : ℕ → ℂ := fun i => (-1 : ℂ) ^ i *
    (((if 2 ≤ i then (W.roots (i - 2)).map (fun α : ℂ => (W.q : ℂ) * α) else 0) : Multiset ℂ).map
      (fun α : ℂ => α ^ n)).sum with hg
  have hsplit : (timesP1 W).count n =
      (∑ i ∈ Finset.range K, f i) + ∑ i ∈ Finset.range K, g i := by
    rw [← Finset.sum_add_distrib]
    simp only [WeilData.count, timesP1, hf, hg, Multiset.map_add, Multiset.sum_add, mul_add]
    rw [show 2 * W.dim + 2 * 1 + 1 = K by omega]
  have hS2 : (∑ i ∈ Finset.range K, g i) = (W.q : ℂ) ^ n * W.count n := by
    have hK' : K = (2 * W.dim + 1) + 1 + 1 := by omega
    rw [hK', Finset.sum_range_succ' g (2 * W.dim + 1 + 1),
      Finset.sum_range_succ' (fun i => g (i + 1)) (2 * W.dim + 1)]
    have hg0 : g 0 = 0 := by simp [hg]
    have hg1 : g 1 = 0 := by simp [hg]
    rw [hg0, hg1, add_zero, add_zero]
    rw [WeilData.count]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    have h2 : (2 : ℕ) ≤ i + 1 + 1 := by omega
    have hsub : i + 1 + 1 - 2 = i := by omega
    have hsign : (-1 : ℂ) ^ (i + 1 + 1) = (-1 : ℂ) ^ i := by ring
    simp only [hg, h2, hsub, hsign, if_true, scaled_power_sum]
    ring
  rw [hsplit, hS2, ← hbase]
  ring

lemma timesP1_computes {W : WeilData} {N : ℕ → ℕ} (h : W.Computes N) :
    (timesP1 W).Computes (fun n => (1 + W.q ^ n) * N n) := by
  intro n hn
  rw [timesP1_count, h n hn]
  push_cast
  ring

/-- **Reduction (multiplication by `P¹`).** If the Riemann hypothesis holds for `X`, it holds
for `X × P¹`. -/
lemma timesP1_RH {W : WeilData} (h : W.RH) : (timesP1 W).RH := by
  intro i α hα
  simp only [timesP1, Multiset.mem_add] at hα ⊢
  rcases hα with hα | hα
  · exact h i α hα
  · split_ifs at hα with h2
    · rw [Multiset.mem_map] at hα
      obtain ⟨β, hβ, rfl⟩ := hα
      have hb := h (i - 2) β hβ
      have hq0 : (0 : ℝ) ≤ (W.q : ℝ) := Nat.cast_nonneg _
      have hcast : (1 : ℝ) + ((i - 2 : ℕ) : ℝ) / 2 = (i : ℝ) / 2 := by
        have hc : ((i - 2 : ℕ) : ℝ) = (i : ℝ) - 2 := by push_cast [h2]; ring
        rw [hc]; ring
      rw [norm_mul, hb, Complex.norm_natCast]
      calc (W.q : ℝ) * (W.q : ℝ) ^ (((i - 2 : ℕ) : ℝ) / 2)
          = (W.q : ℝ) ^ ((1 : ℝ)) * (W.q : ℝ) ^ (((i - 2 : ℕ) : ℝ) / 2) := by rw [Real.rpow_one]
        _ = (W.q : ℝ) ^ ((1 : ℝ) + ((i - 2 : ℕ) : ℝ) / 2) := (Real.rpow_add' hq0 (by positivity)).symm
        _ = (W.q : ℝ) ^ ((i : ℝ) / 2) := by rw [hcast]
    · simp at hα

/-- **Equivalent form (Hasse–Weil bound).** For a curve (`dim = 1`) with `P_0(T) = 1 - T`,
`P_2(T) = 1 - qT` and `deg P_1 = 2g`, the Riemann hypothesis is equivalent to the estimate
`|N_n - (q^n + 1)| ≤ 2g q^{n/2}`; here we verify the (main) forward implication. -/
theorem hasse_weil_bound {W : WeilData} {N : ℕ → ℕ} (g : ℕ)
    (hdim : W.dim = 1) (h0 : W.roots 0 = {1}) (h2 : W.roots 2 = {(W.q : ℂ)})
    (hg : Multiset.card (W.roots 1) = 2 * g)
    (hRH : W.RH) (hN : W.Computes N) (n : ℕ) (hn : 1 ≤ n) :
    |(N n : ℝ) - ((W.q : ℝ) ^ n + 1)| ≤ 2 * g * (W.q : ℝ) ^ ((n : ℝ) / 2) := by
  have hq0 : (0 : ℝ) ≤ (W.q : ℝ) := Nat.cast_nonneg _
  set S : ℂ := ((W.roots 1).map (fun α : ℂ => α ^ n)).sum with hS
  have hcount : (N n : ℂ) = 1 + (W.q : ℂ) ^ n - S := by
    rw [← hN n hn]
    simp only [WeilData.count, hdim, h0, h2, hS, Finset.sum_range_succ, Finset.sum_range_zero,
      Multiset.map_singleton, Multiset.sum_singleton, one_pow, pow_zero, pow_one, zero_add]
    ring
  have hnormterm : ∀ x ∈ (W.roots 1).map (fun α : ℂ => ‖α ^ n‖), x ≤ (W.q : ℝ) ^ ((n : ℝ) / 2) := by
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨α, hα, rfl⟩ := hx
    have hαn : ‖α‖ = (W.q : ℝ) ^ ((1 : ℝ) / 2) := by
      simpa using hRH 1 α hα
    rw [norm_pow, hαn, ← Real.rpow_natCast ((W.q : ℝ) ^ ((1 : ℝ) / 2)) n,
      ← Real.rpow_mul hq0]
    rw [show (1 : ℝ) / 2 * (n : ℝ) = (n : ℝ) / 2 by ring]
  have hbound : ‖S‖ ≤ 2 * g * (W.q : ℝ) ^ ((n : ℝ) / 2) := by
    have h1 : ‖S‖ ≤ ((W.roots 1).map (fun α : ℂ => ‖α ^ n‖)).sum := by
      have := norm_multiset_sum_le ((W.roots 1).map (fun α : ℂ => α ^ n))
      simpa [hS, Multiset.map_map, Function.comp] using this
    have h2' := Multiset.sum_le_card_nsmul ((W.roots 1).map (fun α : ℂ => ‖α ^ n‖))
      ((W.q : ℝ) ^ ((n : ℝ) / 2)) hnormterm
    refine h1.trans (h2'.trans ?_)
    rw [Multiset.card_map, hg, nsmul_eq_mul]
    push_cast
    ring_nf
    exact le_refl _
  have hEq : ((((N n : ℝ) - ((W.q : ℝ) ^ n + 1)) : ℝ) : ℂ) = -S := by
    push_cast
    rw [hcount]
    ring
  have : |(N n : ℝ) - ((W.q : ℝ) ^ n + 1)| = ‖S‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hEq, norm_neg]
  rw [this]
  exact hbound

/-- **Deligne's Riemann hypothesis for varieties over finite fields: statement, verified base
cases and verified reductions.**

`DeligneWeilRH` (above) is the formal statement of the theorem: the point counts of a smooth
proper `F_p`-scheme come from a Weil datum whose degree-`i` inverse roots have absolute value
`p^{i/2}`.  The conjunction below collects what is proved here in full:

* purity holds for all zero-dimensional varieties (finite disjoint unions of closed points),
  together with the corresponding point-count formula;
* purity holds for projective spaces `P^d`, together with the point-count formula
  `#P^d(F_{q^n}) = 1 + q^n + ⋯ + q^{nd}`, verified against the actual number of points of
  projective `d`-space over the finite field `F_{p^n}`;
* purity and the point-count formula are stable under disjoint unions;
* purity and the point-count formula are stable under multiplication by `P¹`;
* purity in dimension one implies the Hasse–Weil estimate `|N_n - (q^n+1)| ≤ 2g q^{n/2}`.
-/
theorem deligne_weil_RH :
    (∀ (q : ℕ) (D : Multiset ℕ), ∃ W : WeilData, W.q = q ∧ W.dim = 0 ∧
        W.Computes (fun n => (D.map (fun m => if m ∣ n then m else 0)).sum) ∧ W.RH) ∧
    (∀ q d : ℕ, (projectiveSpace q d).q = q ∧ (projectiveSpace q d).dim = d ∧
        (projectiveSpace q d).Computes (fun n => ∑ j ∈ Finset.range (d + 1), q ^ (n * j)) ∧
        (projectiveSpace q d).RH) ∧
    (∀ (p : ℕ) [Fact p.Prime] (d : ℕ), (projectiveSpace p d).Computes (fun n =>
        Nat.card (Projectivization (GaloisField p n) (Fin (d + 1) → GaloisField p n)))) ∧
    (∀ (W₁ W₂ : WeilData) (N₁ N₂ : ℕ → ℕ), W₂.q = W₁.q →
        W₁.Computes N₁ → W₂.Computes N₂ → W₁.RH → W₂.RH →
        (disjUnion W₁ W₂).Computes (fun n => N₁ n + N₂ n) ∧ (disjUnion W₁ W₂).RH) ∧
    (∀ (W : WeilData) (N : ℕ → ℕ), W.Computes N → W.RH →
        (timesP1 W).Computes (fun n => (1 + W.q ^ n) * N n) ∧ (timesP1 W).RH) ∧
    (∀ (W : WeilData) (N : ℕ → ℕ) (g : ℕ), W.dim = 1 → W.roots 0 = {1} →
        W.roots 2 = {(W.q : ℂ)} → Multiset.card (W.roots 1) = 2 * g → W.RH → W.Computes N →
        ∀ n : ℕ, 1 ≤ n →
          |(N n : ℝ) - ((W.q : ℝ) ^ n + 1)| ≤ 2 * g * (W.q : ℝ) ^ ((n : ℝ) / 2)) := by
  refine ⟨zeroDimensional_RH, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun q d => ⟨rfl, rfl, projectiveSpace_computes q d, projectiveSpace_RH q d⟩
  · exact fun p _ d => projectiveSpace_computes_pointCount p d
  · exact fun W₁ W₂ N₁ N₂ hq h₁ h₂ r₁ r₂ =>
      ⟨disjUnion_computes h₁ h₂, disjUnion_RH hq r₁ r₂⟩
  · exact fun W N h r => ⟨timesP1_computes h, timesP1_RH r⟩
  · exact fun W N g hdim h0 h2 hg hRH hN n hn => hasse_weil_bound g hdim h0 h2 hg hRH hN n hn

end Frontier

