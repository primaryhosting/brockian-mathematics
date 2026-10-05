import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-! ## Shannon entropy -/

/-- Shannon entropy (in nats) of a finitely supported weight function. -/
noncomputable def entropy {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  -∑ x : α, f x * Real.log (f x)

/-! ## Gibbs' inequality (nonnegativity of relative entropy) -/

/-- Pointwise form of Gibbs' inequality: `a - b ≤ a log a - a log b`. -/
lemma sub_le_mul_log_sub_mul_log (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : b = 0 → a = 0) : a - b ≤ a * Real.log a - a * Real.log b := by
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · have ha0 : a = 0 := h hb0.symm
    simp [ha0, ← hb0]
  · rcases eq_or_lt_of_le ha with ha0 | ha0
    · simp [← ha0]
      linarith
    · have key : Real.log (b / a) ≤ b / a - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (ne_of_gt hb0) (ne_of_gt ha0)] at key
      have h2 : a * (Real.log b - Real.log a) ≤ a * (b / a - 1) :=
        mul_le_mul_of_nonneg_left key ha
      have h3 : a * (b / a - 1) = b - a := by
        field_simp
      rw [h3] at h2
      nlinarith [h2]

/-- Gibbs' inequality / nonnegativity of the relative entropy, in the general form
where `f` has total mass at least that of `g`. -/
lemma zero_le_relEntropy {α : Type*} [Fintype α] (f g : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hsupp : ∀ x, g x = 0 → f x = 0)
    (hsum : ∑ x : α, g x ≤ ∑ x : α, f x) :
    0 ≤ (∑ x : α, f x * Real.log (f x)) - ∑ x : α, f x * Real.log (g x) := by
  have key : ∑ x : α, (f x - g x) ≤
      ∑ x : α, (f x * Real.log (f x) - f x * Real.log (g x)) :=
    Finset.sum_le_sum fun x _ =>
      sub_le_mul_log_sub_mul_log (f x) (g x) (hf x) (hg x) (hsupp x)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at key
  linarith

/-! ## Gibbs states -/

variable {M B : Type*} [Fintype M] [Fintype B]

/-- The canonical (Gibbs) distribution of a bath with energy levels `E`
at inverse temperature `beta`. -/
noncomputable def gibbs (beta : ℝ) (E : B → ℝ) (b : B) : ℝ :=
  Real.exp (-beta * E b) / ∑ b' : B, Real.exp (-beta * E b')

lemma gibbs_partition_pos [Nonempty B] (beta : ℝ) (E : B → ℝ) :
    0 < ∑ b' : B, Real.exp (-beta * E b') :=
  Finset.sum_pos (fun b _ => Real.exp_pos _) (by simp [Finset.univ_nonempty])

lemma gibbs_pos [Nonempty B] (beta : ℝ) (E : B → ℝ) (b : B) : 0 < gibbs beta E b := by
  unfold gibbs
  exact div_pos (Real.exp_pos _) (gibbs_partition_pos beta E)

lemma gibbs_sum [Nonempty B] (beta : ℝ) (E : B → ℝ) : ∑ b : B, gibbs beta E b = 1 := by
  unfold gibbs
  rw [← Finset.sum_div, div_self (ne_of_gt (gibbs_partition_pos beta E))]

lemma log_gibbs [Nonempty B] (beta : ℝ) (E : B → ℝ) (b : B) :
    Real.log (gibbs beta E b) =
      -beta * E b - Real.log (∑ b' : B, Real.exp (-beta * E b')) := by
  unfold gibbs
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt (gibbs_partition_pos beta E)),
    Real.log_exp]

/-! ## The erasure setup -/

/-- Initial joint state of memory and bath: memory in state `p`, bath in the Gibbs state. -/
noncomputable def initJoint (beta : ℝ) (E : B → ℝ) (p : M → ℝ) : M × B → ℝ :=
  fun x => p x.1 * gibbs beta E x.2

/-- Final joint state after the (energy-conserving, invertible) dynamics `U`. -/
noncomputable def finalJoint (beta : ℝ) (E : B → ℝ) (p : M → ℝ) (U : M × B ≃ M × B) :
    M × B → ℝ := fun x => initJoint beta E p (U.symm x)

/-- Final marginal state of the memory. -/
noncomputable def finalMem (beta : ℝ) (E : B → ℝ) (p : M → ℝ) (U : M × B ≃ M × B) :
    M → ℝ := fun m => ∑ b : B, finalJoint beta E p U (m, b)

/-- Heat dissipated into the bath: the increase in the bath's mean energy. -/
noncomputable def heat (beta : ℝ) (E : B → ℝ) (p : M → ℝ) (U : M × B ≃ M × B) : ℝ :=
  (∑ x : M × B, finalJoint beta E p U x * E x.2) - ∑ b : B, gibbs beta E b * E b

/-! ## Basic properties of the setup -/

section Setup

variable [Nonempty B] (beta : ℝ) (E : B → ℝ) (p : M → ℝ)
  (hp : ∀ m, 0 ≤ p m) (hp1 : ∑ m : M, p m = 1) (U : M × B ≃ M × B)

omit [Fintype M] in
include hp in
lemma finalJoint_nonneg (x : M × B) : 0 ≤ finalJoint beta E p U x :=
  mul_nonneg (hp _) (gibbs_pos beta E _).le

include hp1 in
lemma finalJoint_sum : ∑ x : M × B, finalJoint beta E p U x = 1 := by
  have h : ∑ x : M × B, finalJoint beta E p U x
      = ∑ x : M × B, initJoint beta E p x :=
    Equiv.sum_comp U.symm (initJoint beta E p)
  rw [h]
  unfold initJoint
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, gibbs_sum, mul_one]
  exact hp1

omit [Fintype M] in
include hp in
lemma finalMem_nonneg (m : M) : 0 ≤ finalMem beta E p U m :=
  Finset.sum_nonneg fun b _ => finalJoint_nonneg beta E p hp U (m, b)

include hp1 in
lemma finalMem_sum : ∑ m : M, finalMem beta E p U m = 1 := by
  unfold finalMem
  rw [← Fintype.sum_prod_type]
  exact finalJoint_sum beta E p hp1 U

omit [Fintype M] in
include hp in
lemma finalJoint_le_finalMem (m : M) (b : B) :
    finalJoint beta E p U (m, b) ≤ finalMem beta E p U m :=
  Finset.single_le_sum (f := fun b : B => finalJoint beta E p U (m, b))
    (fun b _ => finalJoint_nonneg beta E p hp U (m, b)) (Finset.mem_univ b)

-- The entropy of the initial product state splits, and is preserved by the
-- invertible dynamics.
include hp hp1 in
lemma sum_finalJoint_mul_log :
    ∑ x : M × B, finalJoint beta E p U x * Real.log (finalJoint beta E p U x)
      = (∑ m : M, p m * Real.log (p m))
        + ∑ b : B, gibbs beta E b * Real.log (gibbs beta E b) := by
  have h : ∑ x : M × B, finalJoint beta E p U x * Real.log (finalJoint beta E p U x)
      = ∑ x : M × B, initJoint beta E p x * Real.log (initJoint beta E p x) :=
    Equiv.sum_comp U.symm (fun x => initJoint beta E p x * Real.log (initJoint beta E p x))
  have step : ∀ (m : M) (b : B),
      initJoint beta E p (m, b) * Real.log (initJoint beta E p (m, b))
        = p m * Real.log (p m) * gibbs beta E b
          + p m * (gibbs beta E b * Real.log (gibbs beta E b)) := by
    intro m b
    unfold initJoint
    rcases eq_or_lt_of_le (hp m) with h0 | h0
    · simp [← h0]
    · have : Real.log ((p m) * gibbs beta E b)
          = Real.log (p m) + Real.log (gibbs beta E b) :=
        Real.log_mul (ne_of_gt h0) (ne_of_gt (gibbs_pos beta E b))
      simp only [this]
      ring
  rw [h, Fintype.sum_prod_type]
  have inner : ∀ m : M, ∑ b : B,
      initJoint beta E p (m, b) * Real.log (initJoint beta E p (m, b))
        = p m * Real.log (p m) + p m * ∑ b : B, gibbs beta E b * Real.log (gibbs beta E b) := by
    intro m
    rw [Finset.sum_congr rfl fun b _ => step m b, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, gibbs_sum, mul_one]
  rw [Finset.sum_congr rfl fun m _ => inner m, Finset.sum_add_distrib, ← Finset.sum_mul,
    hp1, one_mul]

-- Splitting the cross term of the relative entropy.
include hp in
lemma sum_finalJoint_mul_log_prod :
    ∑ x : M × B, finalJoint beta E p U x
        * Real.log (finalMem beta E p U x.1 * gibbs beta E x.2)
      = (∑ m : M, finalMem beta E p U m * Real.log (finalMem beta E p U m))
        + ∑ x : M × B, finalJoint beta E p U x * Real.log (gibbs beta E x.2) := by
  have step : ∀ (m : M) (b : B),
      finalJoint beta E p U (m, b) * Real.log (finalMem beta E p U m * gibbs beta E b)
        = finalJoint beta E p U (m, b) * Real.log (finalMem beta E p U m)
          + finalJoint beta E p U (m, b) * Real.log (gibbs beta E b) := by
    intro m b
    rcases eq_or_lt_of_le (finalMem_nonneg beta E p hp U m) with h0 | h0
    · have hx : finalJoint beta E p U (m, b) = 0 :=
        le_antisymm (by simpa [← h0] using finalJoint_le_finalMem beta E p hp U m b)
          (finalJoint_nonneg beta E p hp U (m, b))
      simp [hx]
    · have : Real.log (finalMem beta E p U m * gibbs beta E b)
          = Real.log (finalMem beta E p U m) + Real.log (gibbs beta E b) :=
        Real.log_mul (ne_of_gt h0) (ne_of_gt (gibbs_pos beta E b))
      rw [this]
      ring
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_congr rfl fun b _ => step m b, Finset.sum_add_distrib, ← Finset.sum_mul]
  rfl

omit [Fintype M] in
lemma sum_gibbs_mul_log :
    ∑ b : B, gibbs beta E b * Real.log (gibbs beta E b)
      = -beta * (∑ b : B, gibbs beta E b * E b)
        - Real.log (∑ b' : B, Real.exp (-beta * E b')) := by
  have step : ∀ b : B, gibbs beta E b * Real.log (gibbs beta E b)
      = -beta * (gibbs beta E b * E b)
        - Real.log (∑ b' : B, Real.exp (-beta * E b')) * gibbs beta E b := by
    intro b
    rw [log_gibbs]
    ring
  rw [Finset.sum_congr rfl fun b _ => step b, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, gibbs_sum, mul_one]

include hp1 in
lemma sum_finalJoint_mul_log_gibbs :
    ∑ x : M × B, finalJoint beta E p U x * Real.log (gibbs beta E x.2)
      = -beta * (∑ x : M × B, finalJoint beta E p U x * E x.2)
        - Real.log (∑ b' : B, Real.exp (-beta * E b')) := by
  have step : ∀ x : M × B, finalJoint beta E p U x * Real.log (gibbs beta E x.2)
      = -beta * (finalJoint beta E p U x * E x.2)
        - Real.log (∑ b' : B, Real.exp (-beta * E b')) * finalJoint beta E p U x := by
    intro x
    rw [log_gibbs]
    ring
  rw [Finset.sum_congr rfl fun x _ => step x, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, finalJoint_sum beta E p hp1 U, mul_one]

-- The core inequality: the drop in the memory's Shannon entropy is bounded by
-- `β` times the heat released into the bath.
include hp hp1 in
theorem entropy_drop_le_beta_mul_heat :
    entropy p - entropy (finalMem beta E p U) ≤ beta * heat beta E p U := by
  have hgnn : ∀ x : M × B, 0 ≤ finalMem beta E p U x.1 * gibbs beta E x.2 :=
    fun x => mul_nonneg (finalMem_nonneg beta E p hp U x.1) (gibbs_pos beta E x.2).le
  have hsupp : ∀ x : M × B, finalMem beta E p U x.1 * gibbs beta E x.2 = 0 →
      finalJoint beta E p U x = 0 := by
    rintro ⟨m, b⟩ hx
    have h0 : finalMem beta E p U m = 0 := by
      rcases mul_eq_zero.1 hx with h | h
      · exact h
      · exact absurd h (ne_of_gt (gibbs_pos beta E b))
    exact le_antisymm (by simpa [h0] using finalJoint_le_finalMem beta E p hp U m b)
      (finalJoint_nonneg beta E p hp U (m, b))
  have hgsum : ∑ x : M × B, finalMem beta E p U x.1 * gibbs beta E x.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, gibbs_sum, mul_one]
    exact finalMem_sum beta E p hp1 U
  have hKL := zero_le_relEntropy (finalJoint beta E p U)
    (fun x : M × B => finalMem beta E p U x.1 * gibbs beta E x.2)
    (finalJoint_nonneg beta E p hp U) hgnn hsupp
    (by rw [hgsum, finalJoint_sum beta E p hp1 U])
  rw [sum_finalJoint_mul_log beta E p hp hp1 U,
    sum_finalJoint_mul_log_prod beta E p hp U,
    sum_gibbs_mul_log beta E,
    sum_finalJoint_mul_log_gibbs beta E p hp1 U] at hKL
  unfold entropy heat
  linarith

end Setup

/-! ## The Landauer bound -/

theorem heat_ge_kT_mul_entropy_drop
    [Nonempty B] (k T : ℝ) (hk : 0 < k) (hT : 0 < T)
    (E : B → ℝ) (p : M → ℝ) (hp : ∀ m, 0 ≤ p m) (hp1 : ∑ m : M, p m = 1)
    (U : M × B ≃ M × B) :
    k * T * (entropy p - entropy (finalMem (1 / (k * T)) E p U))
      ≤ heat (1 / (k * T)) E p U := by
  have hkT : 0 < k * T := mul_pos hk hT
  have h := entropy_drop_le_beta_mul_heat (1 / (k * T)) E p hp hp1 U
  have h2 : k * T * (entropy p - entropy (finalMem (1 / (k * T)) E p U))
      ≤ k * T * (1 / (k * T) * heat (1 / (k * T)) E p U) :=
    mul_le_mul_of_nonneg_left h hkT.le
  have h3 : k * T * (1 / (k * T) * heat (1 / (k * T)) E p U)
      = heat (1 / (k * T)) E p U := by
    field_simp
  linarith

/-! ## Exact erasure is impossible: the invertible dynamics keeps full support

Because `U` is a bijection of the (finite) joint phase space and the bath's Gibbs
state is strictly positive, the final memory marginal is never a point mass.  This
is why Landauer's principle is stated below with an erasure error `eps`: the bound
`k T log 2` is approached in the limit of perfect erasure. -/

theorem finalMem_uniform_lt_one [Nonempty B] (beta : ℝ) (E : B → ℝ)
    (U : Bool × B ≃ Bool × B) (m₀ : Bool) :
    finalMem beta E (fun _ => (1 / 2 : ℝ)) U m₀ < 1 := by
  have hp1 : ∑ _m : Bool, (1 / 2 : ℝ) = 1 := by
    rw [Fintype.sum_bool]; norm_num
  have hsum := finalMem_sum beta E (fun _ => (1 / 2 : ℝ)) hp1 U
  rw [Fintype.sum_bool] at hsum
  have hpos : ∀ m : Bool, 0 < finalMem beta E (fun _ => (1 / 2 : ℝ)) U m := by
    intro m
    refine Finset.sum_pos (fun b _ => ?_) (by simp [Finset.univ_nonempty])
    unfold finalJoint initJoint
    exact mul_pos (by norm_num) (gibbs_pos beta E _)
  have h1 := hpos true
  have h2 := hpos false
  cases m₀ <;> linarith

/-! ## A concrete erasure protocol (non-vacuity of the hypothesis below)

Swapping the memory bit with a bath bit leaves the memory in the bath's Gibbs state.
Taking the bath to be a two-level system with a large energy gap makes the erasure
error `gibbs beta E (!m₀)` as small as desired, so the hypothesis `1 - eps ≤ finalMem ...`
of `Phys.landauer_principle` is satisfiable with small `eps`. -/

lemma finalMem_prodComm (beta : ℝ) (E : Bool → ℝ) (m : Bool) :
    finalMem beta E (fun _ => (1 / 2 : ℝ)) (Equiv.prodComm Bool Bool) m
      = gibbs beta E m := by
  unfold finalMem finalJoint initJoint
  simp only [Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk]
  rw [Fintype.sum_bool]
  ring

/-! ## Auxiliary entropy estimates -/

lemma neg_mul_log_le_two_sqrt (x : ℝ) (hx : 0 ≤ x) :
    -(x * Real.log x) ≤ 2 * Real.sqrt x := by
  rcases eq_or_lt_of_le hx with h | h
  · simp [← h]
  · have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 h
    have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt hx]; ring
    have hkey : Real.log (1 / Real.sqrt x) ≤ 1 / Real.sqrt x - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt hs), Real.log_one, zero_sub] at hkey
    have hmul : x * -Real.log (Real.sqrt x) ≤ x * (1 / Real.sqrt x - 1) :=
      mul_le_mul_of_nonneg_left hkey hx
    have hdiv : x * (1 / Real.sqrt x - 1) = Real.sqrt x - x := by
      have : x * (1 / Real.sqrt x) = x / Real.sqrt x := by ring
      rw [mul_sub, this, Real.div_sqrt, mul_one]
    rw [hdiv] at hmul
    rw [hlog]
    nlinarith [hmul, hx]

lemma neg_mul_log_one_sub_le (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    -((1 - v) * Real.log (1 - v)) ≤ v := by
  rcases eq_or_lt_of_le hv1 with h | h
  · subst h
    norm_num
  · have hu : 0 < 1 - v := by linarith
    have hkey : Real.log (1 / (1 - v)) ≤ 1 / (1 - v) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt hu), Real.log_one, zero_sub] at hkey
    have hmul : (1 - v) * -Real.log (1 - v) ≤ (1 - v) * (1 / (1 - v) - 1) :=
      mul_le_mul_of_nonneg_left hkey hu.le
    have hval : (1 - v) * (1 / (1 - v) - 1) = v := by
      field_simp
      ring
    rw [hval] at hmul
    nlinarith [hmul]

/-- Binary entropy is small when the distribution is close to a point mass. -/
lemma entropy_two_point_le (u v eps : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (h : 1 - eps ≤ u) :
    -(u * Real.log u + v * Real.log v) ≤ eps + 2 * Real.sqrt eps := by
  have hv_le : v ≤ eps := by linarith
  have hv1 : v ≤ 1 := by linarith
  have h1 : -(u * Real.log u) ≤ v := by
    have hu' : u = 1 - v := by linarith
    rw [hu']
    exact neg_mul_log_one_sub_le v hv hv1
  have h2 : -(v * Real.log v) ≤ 2 * Real.sqrt v := neg_mul_log_le_two_sqrt v hv
  have h3 : Real.sqrt v ≤ Real.sqrt eps := Real.sqrt_le_sqrt hv_le
  linarith

/-! ## Landauer's principle -/

/-- **Landauer's principle.**

A one-bit memory, initially in the uniform (maximally uncertain) state `(1/2, 1/2)`,
is coupled to a heat bath whose energy levels are `E` and which starts in thermal
equilibrium (the Gibbs state) at temperature `T`.  The joint memory–bath system then
evolves by an arbitrary invertible (Liouville / measure-preserving) dynamics `U`.

If the process *erases* the bit up to an error `eps`, i.e. it leaves the memory in the
definite state `m₀` with probability at least `1 - eps`, then the heat dissipated into
the bath satisfies

  `Q ≥ k T (log 2 - eps - 2 √eps)`.

In the limit of perfect erasure (`eps → 0`) this is exactly the Landauer bound
`Q ≥ k T log 2`.  (An error term is unavoidable: `Phys.finalMem_uniform_lt_one` shows
that perfect erasure is impossible for an invertible dynamics on a finite phase
space with a strictly positive bath state.) -/
theorem landauer_principle
    [Nonempty B] (k T : ℝ) (hk : 0 < k) (hT : 0 < T) (E : B → ℝ)
    (U : Bool × B ≃ Bool × B) (m₀ : Bool) (eps : ℝ)
    (herase : 1 - eps ≤ finalMem (1 / (k * T)) E (fun _ => (1 / 2 : ℝ)) U m₀) :
    k * T * (Real.log 2 - eps - 2 * Real.sqrt eps)
      ≤ heat (1 / (k * T)) E (fun _ => (1 / 2 : ℝ)) U := by
  have hkT : 0 < k * T := mul_pos hk hT
  have hp : ∀ _m : Bool, (0 : ℝ) ≤ 1 / 2 := fun _ => by norm_num
  have hp1 : ∑ _m : Bool, (1 / 2 : ℝ) = 1 := by
    rw [Fintype.sum_bool]; norm_num
  have hEp : entropy (fun _ : Bool => (1 / 2 : ℝ)) = Real.log 2 := by
    unfold entropy
    rw [Fintype.sum_bool, show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  have hpf0 : ∀ m : Bool, 0 ≤ finalMem (1 / (k * T)) E (fun _ => (1 / 2 : ℝ)) U m :=
    finalMem_nonneg (1 / (k * T)) E (fun _ => (1 / 2 : ℝ)) hp U
  have hpfsum := finalMem_sum (1 / (k * T)) E (fun _ => (1 / 2 : ℝ)) hp1 U
  rw [Fintype.sum_bool] at hpfsum
  have hent : entropy (finalMem (1 / (k * T)) E (fun _ => (1 / 2 : ℝ)) U)
      ≤ eps + 2 * Real.sqrt eps := by
    unfold entropy
    rw [Fintype.sum_bool]
    cases m₀ with
    | false =>
        have := entropy_two_point_le
          (finalMem (1 / (k * T)) E (fun _ => (1 / 2 : ℝ)) U false)
          (finalMem (1 / (k * T)) E (fun _ => (1 / 2 : ℝ)) U true)
          eps (hpf0 false) (hpf0 true) (by linarith) herase
        linarith
    | true =>
        have := entropy_two_point_le
          (finalMem (1 / (k * T)) E (fun _ => (1 / 2 : ℝ)) U true)
          (finalMem (1 / (k * T)) E (fun _ => (1 / 2 : ℝ)) U false)
          eps (hpf0 true) (hpf0 false) hpfsum herase
        linarith
  have hgen := heat_ge_kT_mul_entropy_drop k T hk hT E (fun _ : Bool => (1 / 2 : ℝ)) hp hp1 U
  rw [hEp] at hgen
  have hstep : k * T * (Real.log 2 - eps - 2 * Real.sqrt eps)
      ≤ k * T * (Real.log 2
        - entropy (finalMem (1 / (k * T)) E (fun _ => (1 / 2 : ℝ)) U)) :=
    mul_le_mul_of_nonneg_left (by linarith) hkT.le
  linarith

end Phys

