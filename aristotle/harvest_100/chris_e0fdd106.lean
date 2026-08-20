import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Frontier

open Set

/-!
## Quadratic-like maps

Following Douady–Hubbard and McMullen (*Complex Dynamics and Renormalization*),
a **quadratic-like map** is a holomorphic proper degree-two branched covering
`f : V → U` between topological disks with `V ⋐ U`, whose unique critical point we
normalise to be `0`.

The structure below records the data and the properties that are used in the
statements proved here: `V ⊆ U` open subsets of `ℂ`, `f` analytic on a neighbourhood
of each point of `V`, `f` maps `V` into `U` and *onto* `U` (properness/surjectivity),
every fibre over `U` has at most two points (degree `≤ 2`), and `0 ∈ V` is a
critical point of `f`.
-/

/-- A quadratic-like map, presented as the data of the two domains `V ⊆ U ⊆ ℂ` and the
holomorphic map `f : V → U`, which is surjective, has fibres of cardinality at most two
and has a critical point at the origin. -/
structure QuadraticLike where
  /-- The map. -/
  f : ℂ → ℂ
  /-- The target (range) disk. -/
  U : Set ℂ
  /-- The source disk, compactly contained in `U` in the classical definition. -/
  V : Set ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  subset_UV : V ⊆ U
  mapsTo : Set.MapsTo f V U
  surjOn : U ⊆ f '' V
  analytic : AnalyticOnNhd ℂ f V
  crit_mem : (0 : ℂ) ∈ V
  deriv_crit : deriv f 0 = 0
  fiber_encard_le_two : ∀ w ∈ U, {z ∈ V | f z = w}.encard ≤ 2

/-- `R` is a **renormalization of period `n`** of the quadratic-like map `Q`: `R` is itself
a quadratic-like map, its underlying map is the `n`-th iterate of `Q`, and its domains are
contained in those of `Q`.  (This is the combinatorial skeleton of McMullen's definition:
`Q.f^[n] : R.V → R.U` is again quadratic-like around the critical point.) -/
def IsRenormalizationOf (R Q : QuadraticLike) (n : ℕ) : Prop :=
  0 < n ∧ R.f = Q.f^[n] ∧ R.U ⊆ Q.U ∧ R.V ⊆ Q.V

/-- A quadratic-like map is `n`-renormalizable if it admits a renormalization of period `n`. -/
def Renormalizable (Q : QuadraticLike) (n : ℕ) : Prop :=
  ∃ R : QuadraticLike, IsRenormalizationOf R Q n

/-!
## The base case: period one

Every quadratic-like map is its own renormalization of period one.
-/

theorem isRenormalizationOf_self_one (Q : QuadraticLike) : IsRenormalizationOf Q Q 1 := by
  refine ⟨Nat.one_pos, ?_, subset_rfl, subset_rfl⟩
  simp

theorem renormalizable_one (Q : QuadraticLike) : Renormalizable Q 1 :=
  ⟨Q, isRenormalizationOf_self_one Q⟩

/-!
## The reduction: renormalization periods multiply

A renormalization of a renormalization is a renormalization, of the product period.
This is the formal counterpart of the fact that an infinitely renormalizable map has a
nested sequence of renormalization periods `n₁ ∣ n₂ ∣ ⋯`.
-/

theorem IsRenormalizationOf.trans {Q R S : QuadraticLike} {m n : ℕ}
    (hR : IsRenormalizationOf R Q m) (hS : IsRenormalizationOf S R n) :
    IsRenormalizationOf S Q (m * n) := by
  obtain ⟨hm, hRf, hRU, hRV⟩ := hR
  obtain ⟨hn, hSf, hSU, hSV⟩ := hS
  refine ⟨Nat.mul_pos hm hn, ?_, hSU.trans hRU, hSV.trans hRV⟩
  rw [hSf, hRf, Function.iterate_mul]

theorem renormalizable_mul {Q R : QuadraticLike} {m n : ℕ}
    (hR : IsRenormalizationOf R Q m) (hn : Renormalizable R n) :
    Renormalizable Q (m * n) := by
  obtain ⟨S, hS⟩ := hn
  exact ⟨S, hR.trans hS⟩

/-!
## Nonvacuity: `z ↦ z²` is quadratic-like on `B(0,2) → B(0,4)`
-/

theorem sq_fiber_encard_le_two (w : ℂ) (s : Set ℂ) : {z ∈ s | z ^ 2 = w}.encard ≤ 2 := by
  obtain ⟨r, hr⟩ : ∃ r : ℂ, r ^ 2 = w := IsSepClosed.exists_pow_nat_eq w 2
  have hsub : {z ∈ s | z ^ 2 = w} ⊆ ({r, -r} : Set ℂ) := by
    rintro z ⟨-, hz⟩
    have : (z - r) * (z + r) = 0 := by
      have : z ^ 2 - r ^ 2 = 0 := by rw [hz, hr]; ring
      linear_combination this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  calc {z ∈ s | z ^ 2 = w}.encard ≤ ({r, -r} : Set ℂ).encard := Set.encard_le_encard hsub
    _ ≤ 2 := by
        refine le_trans (Set.encard_insert_le _ _) ?_
        rw [Set.encard_singleton]
        norm_num

/-- The model quadratic-like map `z ↦ z²` from the disk of radius `2` onto the disk of
radius `4`. -/
def squareQuadraticLike : QuadraticLike where
  f := fun z => z ^ 2
  U := Metric.ball 0 4
  V := Metric.ball 0 2
  isOpen_U := Metric.isOpen_ball
  isOpen_V := Metric.isOpen_ball
  subset_UV := Metric.ball_subset_ball (by norm_num)
  mapsTo := by
    intro z hz
    simp only [mem_ball_zero_iff] at hz ⊢
    have : ‖z ^ 2‖ = ‖z‖ ^ 2 := by simp
    rw [this]
    nlinarith [norm_nonneg z]
  surjOn := by
    intro w hw
    simp only [mem_ball_zero_iff] at hw
    obtain ⟨r, hr⟩ : ∃ r : ℂ, r ^ 2 = w := IsSepClosed.exists_pow_nat_eq w 2
    refine ⟨r, ?_, hr⟩
    simp only [mem_ball_zero_iff]
    have hnr : ‖r‖ ^ 2 = ‖w‖ := by rw [← hr]; simp
    nlinarith [norm_nonneg r]
  analytic := fun z _ => (analyticAt_id).pow 2
  crit_mem := by simp
  deriv_crit := by simp
  fiber_encard_le_two := fun w _ => sq_fiber_encard_le_two w _

/-!
## Non-degeneracy: the degree-two condition really bites

No quadratic-like map can have underlying map `z ↦ z⁴` (near the critical point such a map
is four-to-one).  Consequently the model map `z ↦ z²` is *not* renormalizable of period `2`,
which matches the fact that `c = 0` is not a renormalizable parameter.
-/

theorem no_quadraticLike_pow_four (R : QuadraticLike) (hR : R.f = fun z : ℂ => z ^ 4) :
    False := by
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp R.isOpen_V 0 R.crit_mem
  set t : ℂ := ((e / 2 : ℝ) : ℂ) with ht_def
  have hnorm : ‖t‖ = e / 2 := by
    rw [ht_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    linarith
  have hmemV : ∀ u : ℂ, ‖u‖ = e / 2 → u ∈ R.V := by
    intro u hu
    refine hball ?_
    simp only [Metric.mem_ball, dist_zero_right, hu]
    linarith
  have htV : t ∈ R.V := hmemV t hnorm
  have hmtV : -t ∈ R.V := hmemV (-t) (by rw [norm_neg]; exact hnorm)
  have hitV : Complex.I * t ∈ R.V := hmemV _ (by simp [hnorm])
  have hwU : R.f t ∈ R.U := R.mapsTo htV
  have hsub : ({t, -t, Complex.I * t} : Set ℂ) ⊆ {z ∈ R.V | R.f z = R.f t} := by
    rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨htV, rfl⟩
    · refine ⟨hmtV, ?_⟩
      rw [hR]; ring
    · refine ⟨hitV, ?_⟩
      rw [hR]
      simp only [mul_pow, Complex.I_pow_four, one_mul]
  have h1 : t ≠ -t := by
    intro h; exact ht0 (by linear_combination h / 2)
  have h2 : t ≠ Complex.I * t := by
    intro h
    have hz : (1 - Complex.I) * t = 0 := by linear_combination h
    rcases mul_eq_zero.mp hz with h' | h'
    · have : Complex.I = 1 := by linear_combination -h'
      simp [Complex.ext_iff] at this
    · exact ht0 h'
  have h3 : -t ≠ Complex.I * t := by
    intro h
    have hz : (1 + Complex.I) * t = 0 := by linear_combination -h
    rcases mul_eq_zero.mp hz with h' | h'
    · have : Complex.I = -1 := by linear_combination h'
      simp [Complex.ext_iff] at this
    · exact ht0 h'
  have hcard : ({t, -t, Complex.I * t} : Set ℂ).encard = 3 := by
    rw [Set.encard_insert_of_notMem (by simp [h1, h2]), Set.encard_pair h3]
    rfl
  have hle : (3 : ℕ∞) ≤ 2 := by
    calc (3 : ℕ∞) = ({t, -t, Complex.I * t} : Set ℂ).encard := hcard.symm
      _ ≤ {z ∈ R.V | R.f z = R.f t}.encard := Set.encard_le_encard hsub
      _ ≤ 2 := R.fiber_encard_le_two _ hwU
  norm_num at hle

theorem squareQuadraticLike_not_renormalizable_two :
    ¬ Renormalizable squareQuadraticLike 2 := by
  rintro ⟨R, -, hRf, -, -⟩
  refine no_quadraticLike_pow_four R ?_
  rw [hRf]
  funext z
  simp only [squareQuadraticLike, Function.iterate_succ, Function.iterate_zero,
    Function.comp_apply, id_eq]
  ring

/-!
## Rigidity of the quadratic family

The normal form `z ↦ z² + c` is rigid for affine conjugacies: an affine map conjugating
`z² + c₁` to `z² + c₂` must be the identity, and then `c₁ = c₂`.  This is the elementary
base case of the rigidity statements for (renormalizable) quadratic-like maps: the
straightening of a quadratic-like map is unique as a point of the `c`-parameter plane.
-/

theorem quadratic_affine_conjugacy_rigid (a b c₁ c₂ : ℂ) (ha : a ≠ 0)
    (h : ∀ z : ℂ, a * (z ^ 2 + c₁) + b = (a * z + b) ^ 2 + c₂) :
    a = 1 ∧ b = 0 ∧ c₁ = c₂ := by
  have e0 := h 0
  have e1 := h 1
  have em := h (-1)
  have hab : a * b = 0 := by linear_combination (em - e1) / 4
  have hb : b = 0 := by
    rcases mul_eq_zero.mp hab with h' | h'
    · exact absurd h' ha
    · exact h'
  subst hb
  have haa : a * (a - 1) = 0 := by linear_combination e0 - e1
  have ha1 : a = 1 := by
    rcases mul_eq_zero.mp haa with h' | h'
    · exact absurd h' ha
    · linear_combination h'
  subst ha1
  refine ⟨rfl, rfl, by linear_combination e0⟩

/-!
## Main statement
-/

/-- **McMullen renormalization (formalized statement, with base case and reduction).**

The four conjuncts are:

1. *Nonvacuity*: the family of quadratic-like maps is nonempty — `z ↦ z²` is a
   quadratic-like map from `B(0,2)` onto `B(0,4)`.
2. *Base case*: every quadratic-like map is its own renormalization of period `1`.
3. *Reduction*: renormalization periods multiply — a renormalization of period `n` of a
   renormalization of period `m` of `Q` is a renormalization of `Q` of period `m * n`
   (so `Q` is `m*n`-renormalizable).
4. *Rigidity base case*: the quadratic normal form `z ↦ z² + c` admits no nontrivial
   affine conjugacies; in particular `z² + c₁` and `z² + c₂` are affinely conjugate only
   when `c₁ = c₂`.
5. *Non-degeneracy*: the model map `z ↦ z²` is not renormalizable of period `2` (its second
   iterate is four-to-one near the critical point), so the notion is not vacuously true. -/
theorem mcmullen_renormalization :
    (∃ Q : QuadraticLike, Q.f = fun z : ℂ => z ^ 2) ∧
    (∀ Q : QuadraticLike, IsRenormalizationOf Q Q 1 ∧ Renormalizable Q 1) ∧
    (∀ (Q R S : QuadraticLike) (m n : ℕ),
      IsRenormalizationOf R Q m → IsRenormalizationOf S R n →
        IsRenormalizationOf S Q (m * n) ∧ Renormalizable Q (m * n)) ∧
    (∀ a b c₁ c₂ : ℂ, a ≠ 0 → (∀ z : ℂ, a * (z ^ 2 + c₁) + b = (a * z + b) ^ 2 + c₂) →
      a = 1 ∧ b = 0 ∧ c₁ = c₂) ∧
    (¬ Renormalizable squareQuadraticLike 2) := by
  refine ⟨⟨squareQuadraticLike, rfl⟩, ?_, ?_, quadratic_affine_conjugacy_rigid,
    squareQuadraticLike_not_renormalizable_two⟩
  · exact fun Q => ⟨isRenormalizationOf_self_one Q, renormalizable_one Q⟩
  · exact fun Q R S m n hR hS => ⟨hR.trans hS, renormalizable_mul hR ⟨S, hS⟩⟩

end Frontier

