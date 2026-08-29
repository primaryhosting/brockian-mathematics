/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

namespace Frontier

/-- The `r`-neighbourhood of a set of sites `X` inside a metric space of sites. -/
def nbhd {Site : Type*} [PseudoMetricSpace Site] (r : ℝ) (X : Set Site) : Set Site :=
  {z | ∃ x ∈ X, dist z x ≤ r}

/-- Discrete-time Heisenberg evolution of an observable `a` under `n` layers of local
gates: `evol u v n a = u (n-1) * ⋯ * u 0 * a * v 0 * ⋯ * v (n-1)`. -/
def evol {A : Type*} [Ring A] (u v : ℕ → A) : ℕ → A → A
  | 0, a => a
  | (k + 1), a => u k * evol u v k a * v k

section

variable {Site : Type*} [PseudoMetricSpace Site] {A : Type*} [NormedRing A]

theorem subset_nbhd {r : ℝ} (hr : 0 ≤ r) (X : Set Site) : X ⊆ nbhd r X := by
  intro x hx
  exact ⟨x, hx, by simpa using hr⟩

/-- If a gate region `Z` of diameter at most `1` meets the `k`-neighbourhood of `X`,
then the union of the two is contained in the `(k+1)`-neighbourhood of `X`. -/
theorem nbhd_union_subset {r : ℝ} {X Z : Set Site} {p : Site}
    (hp : p ∈ Z) (hp' : p ∈ nbhd r X)
    (hZ : ∀ z ∈ Z, ∀ w ∈ Z, dist z w ≤ 1) :
    nbhd r X ∪ Z ⊆ nbhd (r + 1) X := by
  rintro z (⟨x, hx, hzx⟩ | hz)
  · exact ⟨x, hx, by linarith⟩
  · obtain ⟨x, hx, hpx⟩ := hp'
    refine ⟨x, hx, ?_⟩
    have h1 : dist z p ≤ 1 := hZ z hz p hp
    have := dist_triangle z p x
    linarith

/-- Iterated neighbourhoods: the `1`-neighbourhood of the `r`-neighbourhood is contained in
the `(r+1)`-neighbourhood. -/
theorem nbhd_nbhd_subset {r : ℝ} {X : Set Site} :
    nbhd 1 (nbhd r X) ⊆ nbhd (r + 1) X := by
  rintro z ⟨p, ⟨x, hx, hpx⟩, hzp⟩
  refine ⟨x, hx, ?_⟩
  have := dist_triangle z p x
  linarith

variable (loc : Set Site → Set A)

/-- Locality structure: monotone family of subsets of the algebra, closed under products,
with algebras attached to disjoint regions commuting. -/
structure LocalStructure : Prop where
  mono : ∀ ⦃S T : Set Site⦄, S ⊆ T → loc S ⊆ loc T
  mul_mem : ∀ (S : Set Site), ∀ x ∈ loc S, ∀ y ∈ loc S, x * y ∈ loc S
  commute : ∀ (S T : Set Site), Disjoint S T → ∀ x ∈ loc S, ∀ y ∈ loc T, x * y = y * x

variable {loc}

/-- **Support propagation (strict light cone).** After `n` layers of gates each supported in a
region of diameter at most `1`, an observable supported in `X` is supported in the
`n`-neighbourhood of `X`. -/
theorem evol_mem_loc_nbhd (hloc : LocalStructure loc)
    (Z : ℕ → Set Site) (u v : ℕ → A)
    (hu : ∀ k, u k ∈ loc (Z k)) (hv : ∀ k, v k ∈ loc (Z k))
    (huv : ∀ k, u k * v k = 1)
    (hdiam : ∀ k, ∀ z ∈ Z k, ∀ w ∈ Z k, dist z w ≤ 1)
    {X : Set Site} {a : A} (ha : a ∈ loc X) (n : ℕ) :
    evol u v n a ∈ loc (nbhd (n : ℝ) X) := by
  induction n with
  | zero =>
      have h : a ∈ loc (nbhd ((0 : ℕ) : ℝ) X) := by
        simpa using hloc.mono (subset_nbhd (le_rfl : (0:ℝ) ≤ 0) X) ha
      simpa [evol] using h
  | succ k ih =>
      have hcast : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      by_cases hdisj : Disjoint (nbhd (k : ℝ) X) (Z k)
      · -- the gate acts trivially on the current support
        have hcomm : u k * evol u v k a = evol u v k a * u k :=
          hloc.commute (Z k) (nbhd (k : ℝ) X) hdisj.symm (u k) (hu k) _ ih
        have : evol u v (k + 1) a = evol u v k a := by
          show u k * evol u v k a * v k = evol u v k a
          rw [hcomm, mul_assoc, huv k, mul_one]
        rw [this]
        refine hloc.mono ?_ ih
        intro z hz
        obtain ⟨x, hx, hzx⟩ := hz
        exact ⟨x, hx, by push_cast; linarith⟩
      · -- the gate region meets the current support: the support grows by one
        rw [Set.not_disjoint_iff] at hdisj
        obtain ⟨p, hp1, hp2⟩ := hdisj
        have hsub : nbhd (k : ℝ) X ∪ Z k ⊆ nbhd ((k : ℝ) + 1) X :=
          nbhd_union_subset hp2 hp1 (hdiam k)
        have hmem : evol u v (k + 1) a ∈ loc (nbhd (k : ℝ) X ∪ Z k) := by
          show u k * evol u v k a * v k ∈ _
          refine hloc.mul_mem _ _ (hloc.mul_mem _ _ ?_ _ ?_) _ ?_
          · exact hloc.mono Set.subset_union_right (hu k)
          · exact hloc.mono Set.subset_union_left ih
          · exact hloc.mono Set.subset_union_right (hv k)
        have := hloc.mono hsub hmem
        rwa [hcast] at this

/-- The evolution is norm non-increasing when the gates are contractions. -/
theorem norm_evol_le (u v : ℕ → A)
    (hnu : ∀ k, ‖u k‖ ≤ 1) (hnv : ∀ k, ‖v k‖ ≤ 1) (a : A) (n : ℕ) :
    ‖evol u v n a‖ ≤ ‖a‖ := by
  induction n with
  | zero => simp [evol]
  | succ k ih =>
      have h1 : ‖evol u v (k + 1) a‖ ≤ ‖u k * evol u v k a‖ * ‖v k‖ := by
        show ‖u k * evol u v k a * v k‖ ≤ _
        exact norm_mul_le _ _
      have h2 : ‖u k * evol u v k a‖ ≤ ‖u k‖ * ‖evol u v k a‖ := norm_mul_le _ _
      have h3 : (0 : ℝ) ≤ ‖evol u v k a‖ := norm_nonneg _
      have h4 : (0 : ℝ) ≤ ‖v k‖ := norm_nonneg _
      have h6 : ‖u k‖ * ‖evol u v k a‖ ≤ ‖a‖ := by
        nlinarith [hnu k, norm_nonneg (u k)]
      have h7 : (‖u k‖ * ‖evol u v k a‖) * ‖v k‖ ≤ ‖a‖ * 1 :=
        mul_le_mul h6 (hnv k) h4 (norm_nonneg a)
      have h5 : ‖u k * evol u v k a‖ * ‖v k‖ ≤ (‖u k‖ * ‖evol u v k a‖) * ‖v k‖ :=
        mul_le_mul_of_nonneg_right h2 h4
      linarith

end

/-- **Lieb–Robinson bound (discrete-time / finite-range special case).**

Let `A` be a normed ring of observables equipped with a locality structure `loc`, assigning to
each region `S` of a metric space of sites a set of observables `loc S`, monotone in `S`, closed
under products, and such that observables attached to disjoint regions commute.

Consider a discrete-time dynamics given by `n` layers of local gates: at step `k` one conjugates
by a contraction `u k` with inverse `v k`, both supported in a region `Z k` of diameter at most
`1` (i.e. the interaction has range one, so the Lieb–Robinson velocity is `1` site per layer).

Then for observables `a` supported in `X` and `b` supported in `Y` whose regions are at distance
at least `r`, the commutator of the evolved observable with `b` obeys the light-cone bound
`‖[τₙ(a), b]‖ ≤ 2‖a‖‖b‖ exp (n - r)`.

Indeed the commutator vanishes identically outside the light cone `r ≤ n`, and inside it the
exponential factor is at least `1`. -/
theorem lieb_robinson
    {Site : Type*} [PseudoMetricSpace Site] {A : Type*} [NormedRing A]
    {loc : Set Site → Set A} (hloc : LocalStructure loc)
    (Z : ℕ → Set Site) (u v : ℕ → A)
    (hu : ∀ k, u k ∈ loc (Z k)) (hv : ∀ k, v k ∈ loc (Z k))
    (huv : ∀ k, u k * v k = 1)
    (hnu : ∀ k, ‖u k‖ ≤ 1) (hnv : ∀ k, ‖v k‖ ≤ 1)
    (hdiam : ∀ k, ∀ z ∈ Z k, ∀ w ∈ Z k, dist z w ≤ 1)
    {X Y : Set Site} {a b : A} (ha : a ∈ loc X) (hb : b ∈ loc Y)
    (n : ℕ) (r : ℝ) (hr : ∀ x ∈ X, ∀ y ∈ Y, r ≤ dist x y) :
    ‖evol u v n a * b - b * evol u v n a‖ ≤ 2 * ‖a‖ * ‖b‖ * Real.exp ((n : ℝ) - r) := by
  have hmem : evol u v n a ∈ loc (nbhd (n : ℝ) X) :=
    evol_mem_loc_nbhd hloc Z u v hu hv huv hdiam ha n
  have hnorm : ‖evol u v n a‖ ≤ ‖a‖ := norm_evol_le u v hnu hnv a n
  by_cases hcone : (n : ℝ) < r
  · -- outside the light cone the commutator vanishes
    have hdisj : Disjoint (nbhd (n : ℝ) X) Y := by
      rw [Set.disjoint_left]
      rintro z ⟨x, hx, hzx⟩ hzY
      have := hr x hx z hzY
      rw [dist_comm] at hzx
      linarith
    have := hloc.commute _ _ hdisj _ hmem _ hb
    rw [this, sub_self, norm_zero]
    positivity
  · -- inside the light cone the exponential factor is at least one
    push_neg at hcone
    have hexp : (1 : ℝ) ≤ Real.exp ((n : ℝ) - r) := by
      rw [Real.one_le_exp_iff]
      linarith
    have h1 : ‖evol u v n a * b - b * evol u v n a‖ ≤ 2 * ‖a‖ * ‖b‖ := by
      calc ‖evol u v n a * b - b * evol u v n a‖
          ≤ ‖evol u v n a * b‖ + ‖b * evol u v n a‖ := norm_sub_le _ _
        _ ≤ ‖evol u v n a‖ * ‖b‖ + ‖b‖ * ‖evol u v n a‖ :=
            add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ 2 * ‖a‖ * ‖b‖ := by
            nlinarith [norm_nonneg b, norm_nonneg a, norm_nonneg (evol u v n a)]
    nlinarith [norm_nonneg a, norm_nonneg b,
      norm_nonneg (evol u v n a * b - b * evol u v n a)]

/-! ### Non-vacuity

The hypotheses of `Frontier.lieb_robinson` are simultaneously satisfiable in a genuinely
noncommutative algebra of observables: we exhibit a locality structure on the real quaternions
indexed by regions of the lattice `ℤ`, together with admissible gates. -/

/-- A concrete locality structure: observables attached to a region containing the origin are
arbitrary quaternions, all other regions carry only the (central) real scalars. -/
noncomputable def demoLoc : Set ℤ → Set (Quaternion ℝ) := fun S =>
  if (0 : ℤ) ∈ S then Set.univ else {x | ∃ c : ℝ, x = c • (1 : Quaternion ℝ)}

theorem demoLoc_localStructure : LocalStructure demoLoc := by
  constructor
  · intro S T hST x hx
    by_cases h0 : (0 : ℤ) ∈ S
    · simp [demoLoc, hST h0]
    · simp only [demoLoc, if_neg h0] at hx
      by_cases h1 : (0 : ℤ) ∈ T
      · simp [demoLoc, h1]
      · simpa [demoLoc, if_neg h1] using hx
  · intro S x hx y hy
    by_cases h0 : (0 : ℤ) ∈ S
    · simp [demoLoc, h0]
    · simp only [demoLoc, if_neg h0] at hx hy ⊢
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨c * d, by rw [smul_mul_smul_comm, mul_one, mul_smul]⟩
  · intro S T hST x hx y hy
    by_cases h0 : (0 : ℤ) ∈ S
    · have h1 : (0 : ℤ) ∉ T := fun h => (Set.disjoint_left.mp hST h0) h
      simp only [demoLoc, if_neg h1] at hy
      obtain ⟨d, rfl⟩ := hy
      rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    · simp only [demoLoc, if_neg h0] at hx
      obtain ⟨c, rfl⟩ := hx
      rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

/-- The hypotheses of the Lieb–Robinson bound are consistent, and the locality structure used
can be genuinely noncommutative. -/
theorem lieb_robinson_hypotheses_satisfiable :
    ∃ (loc : Set ℤ → Set (Quaternion ℝ)) (Z : ℕ → Set ℤ) (u v : ℕ → Quaternion ℝ),
      LocalStructure loc ∧ (∀ k, u k ∈ loc (Z k)) ∧ (∀ k, v k ∈ loc (Z k)) ∧
      (∀ k, u k * v k = 1) ∧ (∀ k, ‖u k‖ ≤ 1) ∧ (∀ k, ‖v k‖ ≤ 1) ∧
      (∀ k, ∀ z ∈ Z k, ∀ w ∈ Z k, dist z w ≤ 1) ∧
      (∃ x y : Quaternion ℝ, x ∈ loc {0} ∧ y ∈ loc {0} ∧ x * y ≠ y * x) := by
  refine ⟨demoLoc, fun _ => {0}, fun _ => 1, fun _ => 1, demoLoc_localStructure,
    fun _ => by simp [demoLoc], fun _ => by simp [demoLoc], fun _ => by simp,
    fun _ => by simp, fun _ => by simp, ?_, ?_⟩
  · intro k z hz w hw
    simp only [Set.mem_singleton_iff] at hz hw
    subst hz; subst hw
    simp
  · refine ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, by simp [demoLoc], by simp [demoLoc], ?_⟩
    simp [Quaternion.ext_iff]
    norm_num

end Frontier

