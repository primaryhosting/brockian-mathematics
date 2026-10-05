/-
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
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

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Erasing one bit of information dissipates at least `k T log 2` of heat.

The setting formalised here is the standard statistical-mechanical derivation:

* the memory is a two-state system (`Bool`), initially in the uniform state
  (one bit of information, entropy `log 2`);
* the heat bath is a finite system with energies `E`, initially in the Gibbs
  state at inverse temperature `beta = 1 / (k T)`;
* system and bath are initially uncorrelated;
* the joint system is isolated, so its Shannon entropy does not decrease
  (in particular this holds, with equality, for reversible microscopic
  dynamics, i.e. for a bijection of the joint state space);
* the process is an *erasure*: the final marginal state of the memory is a
  point mass.

Then the heat `Q` absorbed by the bath is at least `k T log 2`.

The proof uses: invariance of Shannon entropy under relabelling, additivity on
product distributions, subadditivity (both consequences of Gibbs' inequality)
and the maximum-entropy property of the Gibbs state.
-/

namespace Phys

open Finset

/-- A probability distribution on a finite type. -/
structure IsProbDist {α : Type*} [Fintype α] (p : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ p a
  sum_one : ∑ a, p a = 1

/-- Shannon entropy (in nats) of a distribution on a finite type. -/
noncomputable def shannonEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a, -(p a * Real.log (p a))

/-- First marginal of a joint distribution. -/
noncomputable def marg1 {α β : Type*} [Fintype α] [Fintype β] (r : α × β → ℝ) : α → ℝ :=
  fun a => ∑ b, r (a, b)

/-- Second marginal of a joint distribution. -/
noncomputable def marg2 {α β : Type*} [Fintype α] [Fintype β] (r : α × β → ℝ) : β → ℝ :=
  fun b => ∑ a, r (a, b)

/-- The Gibbs (canonical) state of a finite system with energies `E` at inverse
temperature `beta`. -/
noncomputable def gibbsState {B : Type*} [Fintype B] (E : B → ℝ) (beta : ℝ) : B → ℝ :=
  fun b => Real.exp (-(beta * E b)) / ∑ b', Real.exp (-(beta * E b'))

/-! ## Basic entropy facts -/

/-- Gibbs' inequality: the cross entropy dominates the Shannon entropy. -/
theorem gibbs_ineq {α : Type*} [Fintype α] (p q : α → ℝ) (hp : IsProbDist p)
    (hq0 : ∀ a, 0 ≤ q a) (hqpos : ∀ a, p a ≠ 0 → 0 < q a) (hq1 : ∑ a, q a ≤ 1) :
    shannonEntropy p ≤ ∑ a, -(p a * Real.log (q a)) := by
  have key : ∀ a ∈ (univ : Finset α),
      p a * Real.log (q a) - p a * Real.log (p a) ≤ q a - p a := by
    intro a _
    rcases eq_or_lt_of_le (hp.nonneg a) with h | h
    · simp [← h, hq0 a]
    · have hqa : 0 < q a := hqpos a (ne_of_gt h)
      have hlog : Real.log (q a / p a) ≤ q a / p a - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hqa h)
      rw [Real.log_div (ne_of_gt hqa) (ne_of_gt h)] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt h)
      calc p a * Real.log (q a) - p a * Real.log (p a)
          = p a * (Real.log (q a) - Real.log (p a)) := by ring
        _ ≤ p a * (q a / p a - 1) := hmul
        _ = q a - p a := by field_simp
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hp.sum_one] at hsum
  have hA : ∑ a, -(p a * Real.log (p a)) = -∑ a, p a * Real.log (p a) := by simp
  have hB : ∑ a, -(p a * Real.log (q a)) = -∑ a, p a * Real.log (q a) := by simp
  rw [shannonEntropy, hA, hB]
  linarith

/-- Entropy of a product distribution is the sum of entropies. -/
theorem shannonEntropy_prod {α β : Type*} [Fintype α] [Fintype β] (p : α → ℝ) (q : β → ℝ)
    (hp : IsProbDist p) (hq : IsProbDist q) :
    shannonEntropy (fun x : α × β => p x.1 * q x.2) = shannonEntropy p + shannonEntropy q := by
  have key : ∀ a : α, ∀ b : β, -(p a * q b * Real.log (p a * q b))
      = q b * -(p a * Real.log (p a)) + p a * -(q b * Real.log (q b)) := by
    intro a b
    rcases eq_or_ne (p a) 0 with h | h
    · simp [h]
    rcases eq_or_ne (q b) 0 with h' | h'
    · simp [h']
    rw [Real.log_mul h h']; ring
  have hinner : ∀ a : α, ∑ b, (q b * -(p a * Real.log (p a)) + p a * -(q b * Real.log (q b)))
      = -(p a * Real.log (p a)) + p a * shannonEntropy q := by
    intro a
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hq.sum_one, one_mul]
    rfl
  rw [shannonEntropy, Fintype.sum_prod_type]
  simp only [key, hinner]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp.sum_one, one_mul]
  rfl

/-- Shannon entropy is invariant under relabelling of the state space. -/
theorem shannonEntropy_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (p : β → ℝ) : shannonEntropy (fun a => p (e a)) = shannonEntropy p := by
  simpa [shannonEntropy] using e.sum_comp (fun b => -(p b * Real.log (p b)))

/-! ## Marginals -/

theorem marg1_nonneg {α β : Type*} [Fintype α] [Fintype β] {r : α × β → ℝ}
    (hr : IsProbDist r) (a : α) : 0 ≤ marg1 r a :=
  Finset.sum_nonneg fun b _ => hr.nonneg (a, b)

theorem marg2_nonneg {α β : Type*} [Fintype α] [Fintype β] {r : α × β → ℝ}
    (hr : IsProbDist r) (b : β) : 0 ≤ marg2 r b :=
  Finset.sum_nonneg fun a _ => hr.nonneg (a, b)

theorem marg1_isProbDist {α β : Type*} [Fintype α] [Fintype β] {r : α × β → ℝ}
    (hr : IsProbDist r) : IsProbDist (marg1 r) := by
  refine ⟨marg1_nonneg hr, ?_⟩
  rw [← hr.sum_one, Fintype.sum_prod_type]
  rfl

theorem marg2_isProbDist {α β : Type*} [Fintype α] [Fintype β] {r : α × β → ℝ}
    (hr : IsProbDist r) : IsProbDist (marg2 r) := by
  refine ⟨marg2_nonneg hr, ?_⟩
  rw [← hr.sum_one, Fintype.sum_prod_type_right]
  rfl

theorem le_marg1 {α β : Type*} [Fintype α] [Fintype β] {r : α × β → ℝ}
    (hr : IsProbDist r) (a : α) (b : β) : r (a, b) ≤ marg1 r a :=
  Finset.single_le_sum (f := fun b' => r (a, b')) (fun b' _ => hr.nonneg (a, b')) (mem_univ b)

theorem le_marg2 {α β : Type*} [Fintype α] [Fintype β] {r : α × β → ℝ}
    (hr : IsProbDist r) (a : α) (b : β) : r (a, b) ≤ marg2 r b :=
  Finset.single_le_sum (f := fun a' => r (a', b)) (fun a' _ => hr.nonneg (a', b)) (mem_univ a)

/-- Subadditivity of Shannon entropy. -/
theorem shannonEntropy_subadditive {α β : Type*} [Fintype α] [Fintype β] (r : α × β → ℝ)
    (hr : IsProbDist r) :
    shannonEntropy r ≤ shannonEntropy (marg1 r) + shannonEntropy (marg2 r) := by
  have hq0 : ∀ x : α × β, 0 ≤ marg1 r x.1 * marg2 r x.2 := fun x =>
    mul_nonneg (marg1_nonneg hr x.1) (marg2_nonneg hr x.2)
  have hpos : ∀ a : α, ∀ b : β, r (a, b) ≠ 0 → 0 < marg1 r a ∧ 0 < marg2 r b := by
    intro a b hx
    have hrx : 0 < r (a, b) := lt_of_le_of_ne (hr.nonneg (a, b)) (Ne.symm hx)
    exact ⟨lt_of_lt_of_le hrx (le_marg1 hr a b), lt_of_lt_of_le hrx (le_marg2 hr a b)⟩
  have hqpos : ∀ x : α × β, r x ≠ 0 → 0 < marg1 r x.1 * marg2 r x.2 := by
    rintro ⟨a, b⟩ hx
    obtain ⟨h1, h2⟩ := hpos a b hx
    exact mul_pos h1 h2
  have hq1 : ∑ x : α × β, marg1 r x.1 * marg2 r x.2 ≤ 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum]
    rw [← Finset.sum_mul, (marg1_isProbDist hr).sum_one, (marg2_isProbDist hr).sum_one]
    norm_num
  have hmain := gibbs_ineq r (fun x => marg1 r x.1 * marg2 r x.2) hr hq0 hqpos hq1
  refine hmain.trans_eq ?_
  have key : ∀ x : α × β, -(r x * Real.log (marg1 r x.1 * marg2 r x.2))
      = -(r x * Real.log (marg1 r x.1)) + -(r x * Real.log (marg2 r x.2)) := by
    rintro ⟨a, b⟩
    rcases eq_or_ne (r (a, b)) 0 with h | h
    · simp [h]
    · obtain ⟨h1, h2⟩ := hpos a b h
      simp only
      rw [Real.log_mul (ne_of_gt h1) (ne_of_gt h2)]
      ring
  calc ∑ x : α × β, -(r x * Real.log (marg1 r x.1 * marg2 r x.2))
      = ∑ x : α × β, (-(r x * Real.log (marg1 r x.1)) + -(r x * Real.log (marg2 r x.2))) :=
        Finset.sum_congr rfl fun x _ => key x
    _ = (∑ x : α × β, -(r x * Real.log (marg1 r x.1)))
          + ∑ x : α × β, -(r x * Real.log (marg2 r x.2)) := Finset.sum_add_distrib
    _ = shannonEntropy (marg1 r) + shannonEntropy (marg2 r) := by
        congr 1
        · rw [Fintype.sum_prod_type, shannonEntropy]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_neg_distrib]
          show -∑ x : β, r (a, x) * Real.log (marg1 r a) = -(marg1 r a * Real.log (marg1 r a))
          rw [← Finset.sum_mul]
          rfl
        · rw [Fintype.sum_prod_type_right, shannonEntropy]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_neg_distrib]
          show -∑ x : α, r (x, b) * Real.log (marg2 r b) = -(marg2 r b * Real.log (marg2 r b))
          rw [← Finset.sum_mul]
          rfl

/-! ## The Gibbs state and its maximum-entropy property -/

section GibbsState

variable {B : Type*} [Fintype B] [Nonempty B] (E : B → ℝ) (beta : ℝ)

/-- The canonical partition function. -/
noncomputable def partitionFn : ℝ := ∑ b, Real.exp (-(beta * E b))

theorem partitionFn_pos : 0 < partitionFn E beta :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

omit [Nonempty B] in
theorem gibbsState_eq (b : B) :
    gibbsState E beta b = Real.exp (-(beta * E b)) / partitionFn E beta := rfl

theorem gibbsState_pos (b : B) : 0 < gibbsState E beta b :=
  div_pos (Real.exp_pos _) (partitionFn_pos E beta)

theorem gibbsState_isProbDist : IsProbDist (gibbsState E beta) := by
  refine ⟨fun b => (gibbsState_pos E beta b).le, ?_⟩
  unfold gibbsState
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (partitionFn_pos E beta))

theorem neg_log_gibbsState (b : B) :
    -Real.log (gibbsState E beta b) = beta * E b + Real.log (partitionFn E beta) := by
  have hZ : (0 : ℝ) < partitionFn E beta := partitionFn_pos E beta
  rw [gibbsState_eq, Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZ), Real.log_exp]
  ring

/-- The Shannon entropy of the Gibbs state is `beta * ⟨E⟩ + log Z`. -/
theorem entropy_gibbsState :
    shannonEntropy (gibbsState E beta)
      = beta * (∑ b, gibbsState E beta b * E b) + Real.log (partitionFn E beta) := by
  have h : ∀ b : B, -(gibbsState E beta b * Real.log (gibbsState E beta b))
      = gibbsState E beta b * (beta * E b)
        + gibbsState E beta b * Real.log (partitionFn E beta) := by
    intro b
    calc -(gibbsState E beta b * Real.log (gibbsState E beta b))
        = gibbsState E beta b * -Real.log (gibbsState E beta b) := by ring
      _ = gibbsState E beta b * (beta * E b + Real.log (partitionFn E beta)) := by
          rw [neg_log_gibbsState]
      _ = _ := by ring
  rw [shannonEntropy]
  simp only [h]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, (gibbsState_isProbDist E beta).sum_one, one_mul,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun b _ => by ring

/-- Maximum-entropy property of the Gibbs state: any distribution has entropy at most
`beta * ⟨E⟩ + log Z`. -/
theorem entropy_le_of_isProbDist (rho : B → ℝ) (hrho : IsProbDist rho) :
    shannonEntropy rho ≤ beta * (∑ b, rho b * E b) + Real.log (partitionFn E beta) := by
  have hg := gibbs_ineq rho (gibbsState E beta) hrho (fun b => (gibbsState_pos E beta b).le)
    (fun b _ => gibbsState_pos E beta b) (le_of_eq (gibbsState_isProbDist E beta).sum_one)
  refine hg.trans_eq ?_
  have h : ∀ b : B, -(rho b * Real.log (gibbsState E beta b))
      = rho b * (beta * E b) + rho b * Real.log (partitionFn E beta) := by
    intro b
    calc -(rho b * Real.log (gibbsState E beta b)) = rho b * -Real.log (gibbsState E beta b) := by
          ring
      _ = rho b * (beta * E b + Real.log (partitionFn E beta)) := by rw [neg_log_gibbsState]
      _ = _ := by ring
  simp only [h]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hrho.sum_one, one_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun b _ => by ring

end GibbsState

/-! ## Entropy of one bit, and of an erased bit -/

/-- One unbiased bit carries `log 2` nats of entropy. -/
theorem shannonEntropy_uniform_bool : shannonEntropy (fun _ : Bool => (1 : ℝ) / 2)
    = Real.log 2 := by
  rw [shannonEntropy, Fintype.sum_bool,
    show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

/-- A deterministic (erased) state has zero entropy. -/
theorem shannonEntropy_pointMass {α : Type*} [Fintype α] [DecidableEq α] (a₀ : α) :
    shannonEntropy (fun a => if a = a₀ then (1 : ℝ) else 0) = 0 := by
  rw [shannonEntropy]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases h : a = a₀ <;> simp [h]

/-! ## Landauer's principle

### The physical setting

* The memory is a two-state system (`Bool`), initially in the uniform state `(1/2, 1/2)`,
  i.e. it stores exactly one bit.
* The heat bath is a finite system with state space `B` and energies `E`, initially in the
  Gibbs state `gam` at inverse temperature `beta = 1 / (k T)`.
* Initially memory and bath are uncorrelated: the joint state is `r0 x = (1/2) * gam x.2`.
* The joint system is isolated during the process, so the *second law* applies to it: the
  joint Shannon entropy does not decrease, `shannonEntropy r0 ≤ shannonEntropy r1`.
  (For reversible - i.e. bijective - microscopic dynamics this holds with equality; see
  `shannonEntropy_comp_equiv` and `landauer_principle_reversible`.)
* The heat absorbed by the bath is the change of its mean energy,
  `Q = ∑ b, (marg2 r1 b - gam b) * E b`.
-/

/-- **The Landauer bound.**  The heat absorbed by the bath is at least `k T` times the
entropy lost by the memory. -/
theorem heat_ge_entropy_decrease {B : Type*} [Fintype B] [Nonempty B]
    (E : B → ℝ) (k T : ℝ) (hk : 0 < k) (hT : 0 < T)
    (gam : B → ℝ) (hgam : gam = gibbsState E (1 / (k * T)))
    (r0 r1 : Bool × B → ℝ)
    (hr0 : ∀ x, r0 x = (1 / 2 : ℝ) * gam x.2)
    (hr1P : IsProbDist r1)
    (hsecond : shannonEntropy r0 ≤ shannonEntropy r1)
    (Q : ℝ) (hQ : Q = ∑ b, (marg2 r1 b - gam b) * E b) :
    k * T * (Real.log 2 - shannonEntropy (marg1 r1)) ≤ Q := by
  set beta : ℝ := 1 / (k * T) with hbeta_def
  have hkT : 0 < k * T := mul_pos hk hT
  have hpS : IsProbDist (fun _ : Bool => (1 : ℝ) / 2) := by
    refine ⟨fun _ => by norm_num, ?_⟩
    rw [Fintype.sum_bool]; norm_num
  have hgamP : IsProbDist gam := by rw [hgam]; exact gibbsState_isProbDist E beta
  -- the initial joint distribution is the product of the uniform bit and the Gibbs state
  have hr0_eq : r0 = fun x : Bool × B => (fun _ : Bool => (1 : ℝ) / 2) x.1 * gam x.2 := funext hr0
  have hH0 : shannonEntropy r0 = Real.log 2 + shannonEntropy gam := by
    rw [hr0_eq, shannonEntropy_prod _ _ hpS hgamP, shannonEntropy_uniform_bool]
  -- subadditivity of the joint entropy
  have hsub := shannonEntropy_subadditive r1 hr1P
  -- maximum-entropy property of the Gibbs state, applied to the final bath state
  have hmax := entropy_le_of_isProbDist E beta (marg2 r1) (marg2_isProbDist hr1P)
  -- the initial bath state is the Gibbs state
  have hHgam : shannonEntropy gam = beta * (∑ b, gam b * E b) + Real.log (partitionFn E beta) := by
    rw [hgam]; exact entropy_gibbsState E beta
  have hQ' : Q = (∑ b, marg2 r1 b * E b) - ∑ b, gam b * E b := by
    rw [hQ]
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib]
  have hkey : Real.log 2 - shannonEntropy (marg1 r1) ≤ beta * Q := by
    rw [hH0, hHgam] at hsecond
    rw [hQ', mul_sub]
    linarith [hsecond, hsub, hmax]
  have hmul : k * T * (Real.log 2 - shannonEntropy (marg1 r1)) ≤ k * T * (beta * Q) :=
    mul_le_mul_of_nonneg_left hkey (le_of_lt hkT)
  have hbq : k * T * (beta * Q) = Q := by
    rw [hbeta_def]; field_simp
  linarith [hmul, hbq.le, hbq.ge]

/-- **Landauer's principle.**

If a one-bit memory, initially in the uniform state and uncorrelated with a heat bath which
is in its Gibbs state at temperature `T`, is *erased* (its final marginal state is the point
mass at `s₀`) by a process during which the joint entropy of memory and bath does not
decrease, then the heat `Q` absorbed by the bath is at least `k T log 2`. -/
theorem landauer_principle {B : Type*} [Fintype B] [Nonempty B]
    (E : B → ℝ) (k T : ℝ) (hk : 0 < k) (hT : 0 < T)
    (gam : B → ℝ) (hgam : gam = gibbsState E (1 / (k * T)))
    (r0 r1 : Bool × B → ℝ)
    (hr0 : ∀ x, r0 x = (1 / 2 : ℝ) * gam x.2)
    (hr1P : IsProbDist r1)
    (hsecond : shannonEntropy r0 ≤ shannonEntropy r1)
    (s₀ : Bool) (herase : ∀ s, marg1 r1 s = if s = s₀ then 1 else 0)
    (Q : ℝ) (hQ : Q = ∑ b, (marg2 r1 b - gam b) * E b) :
    k * T * Real.log 2 ≤ Q := by
  have hHm1 : shannonEntropy (marg1 r1) = 0 := by
    have h : marg1 r1 = fun s => if s = s₀ then (1 : ℝ) else 0 := funext herase
    rw [h, shannonEntropy_pointMass]
  have := heat_ge_entropy_decrease E k T hk hT gam hgam r0 r1 hr0 hr1P hsecond Q hQ
  rwa [hHm1, sub_zero] at this

/-- Version of the Landauer bound for reversible (bijective) microscopic dynamics: there the
second law is an equality, the joint entropy being invariant under a relabelling of the joint
state space. -/
theorem landauer_principle_reversible {B : Type*} [Fintype B] [Nonempty B]
    (E : B → ℝ) (k T : ℝ) (hk : 0 < k) (hT : 0 < T)
    (gam : B → ℝ) (hgam : gam = gibbsState E (1 / (k * T)))
    (dyn : Equiv.Perm (Bool × B)) (r1 : Bool × B → ℝ)
    (hr1 : ∀ x, r1 x = (1 / 2 : ℝ) * gam (dyn.symm x).2)
    (Q : ℝ) (hQ : Q = ∑ b, (marg2 r1 b - gam b) * E b) :
    k * T * (Real.log 2 - shannonEntropy (marg1 r1)) ≤ Q := by
  set r0 : Bool × B → ℝ := fun x => (1 / 2 : ℝ) * gam x.2 with hr0_def
  have hgamP : IsProbDist gam := by rw [hgam]; exact gibbsState_isProbDist E (1 / (k * T))
  have hr0P : IsProbDist r0 := by
    refine ⟨fun x => mul_nonneg (by norm_num) (hgamP.nonneg x.2), ?_⟩
    rw [hr0_def, Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hgamP.sum_one, mul_one]
    rw [Fintype.sum_bool]; norm_num
  have hr1_eq : r1 = fun x => r0 (dyn.symm x) := funext hr1
  have hr1P : IsProbDist r1 := by
    refine ⟨fun x => by rw [hr1_eq]; exact hr0P.nonneg _, ?_⟩
    rw [hr1_eq, ← hr0P.sum_one]
    exact dyn.symm.sum_comp r0
  have hsecond : shannonEntropy r0 ≤ shannonEntropy r1 := by
    rw [hr1_eq, shannonEntropy_comp_equiv dyn.symm r0]
  exact heat_ge_entropy_decrease E k T hk hT gam hgam r0 r1 (fun _ => rfl) hr1P hsecond Q hQ

/-! ### Non-vacuity

The hypotheses of `landauer_principle` are satisfiable: a memory bit really can be erased
into a sufficiently cold four-state bath without decreasing the joint entropy. -/

/-- Energies of the witness bath: one ground state and three states of energy `10`. -/
def witnessEnergy : Fin 4 → ℝ := fun b => if b = 0 then 0 else 10

theorem landauer_principle_hypotheses_satisfiable :
    ∃ (k T : ℝ) (E gam : Fin 4 → ℝ) (r0 r1 : Bool × Fin 4 → ℝ) (s₀ : Bool) (Q : ℝ),
      0 < k ∧ 0 < T ∧
      gam = gibbsState E (1 / (k * T)) ∧
      (∀ x, r0 x = (1 / 2 : ℝ) * gam x.2) ∧
      IsProbDist r1 ∧
      shannonEntropy r0 ≤ shannonEntropy r1 ∧
      (∀ s, marg1 r1 s = if s = s₀ then 1 else 0) ∧
      Q = ∑ b, (marg2 r1 b - gam b) * E b := by
  classical
  set gam : Fin 4 → ℝ := gibbsState witnessEnergy 1 with hgam_def
  set r1 : Bool × Fin 4 → ℝ := fun x => if x.1 = false then (1 / 4 : ℝ) else 0 with hr1_def
  -- basic estimates on `exp (-10)`
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
    have h := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hexp10 : (243 : ℝ) ≤ Real.exp 10 := by
    have h : Real.exp 10 = Real.exp 2 * (Real.exp 2 * (Real.exp 2 * (Real.exp 2 * Real.exp 2))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      norm_num
    have a2 : (9 : ℝ) ≤ Real.exp 2 * Real.exp 2 := by nlinarith
    have a3 : (27 : ℝ) ≤ Real.exp 2 * (Real.exp 2 * Real.exp 2) := by nlinarith
    have a4 : (81 : ℝ) ≤ Real.exp 2 * (Real.exp 2 * (Real.exp 2 * Real.exp 2)) := by nlinarith
    rw [h]
    nlinarith
  have heps : Real.exp (-10) ≤ 1 / 243 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hexp10
  have hepspos : 0 < Real.exp (-10) := Real.exp_pos _
  -- values of the witness energies
  have hE0 : witnessEnergy 0 = 0 := by simp [witnessEnergy]
  have hE1 : witnessEnergy 1 = 10 := by simp [witnessEnergy]
  have hE2 : witnessEnergy 2 = 10 := by simp [witnessEnergy]
  have hE3 : witnessEnergy 3 = 10 := by simp [witnessEnergy]
  -- the partition function of the witness bath
  have hZ : partitionFn witnessEnergy 1 = 1 + 3 * Real.exp (-10) := by
    rw [partitionFn, Fin.sum_univ_four, hE0, hE1, hE2, hE3]
    simp only [mul_zero, neg_zero, Real.exp_zero, one_mul]
    ring
  have hZ1 : (1 : ℝ) ≤ partitionFn witnessEnergy 1 := by rw [hZ]; linarith
  have hZpos : (0 : ℝ) < partitionFn witnessEnergy 1 := by linarith
  have hZinv : (partitionFn witnessEnergy 1)⁻¹ ≤ 1 := by
    have h1 : (partitionFn witnessEnergy 1)⁻¹ * partitionFn witnessEnergy 1 = 1 :=
      inv_mul_cancel₀ (ne_of_gt hZpos)
    nlinarith [inv_pos.mpr hZpos, hZ1, h1]
  -- mean energy of the bath in the Gibbs state
  have hmean : ∑ b, gam b * witnessEnergy b
      = 30 * Real.exp (-10) * (partitionFn witnessEnergy 1)⁻¹ := by
    simp only [hgam_def, gibbsState_eq, div_eq_mul_inv]
    rw [Fin.sum_univ_four, hE0, hE1, hE2, hE3]
    simp only [mul_zero, neg_zero, Real.exp_zero, one_mul]
    ring
  have hmean_le : ∑ b, gam b * witnessEnergy b ≤ 30 * Real.exp (-10) := by
    rw [hmean]
    nlinarith [hepspos, hZinv]
  have hlogZ : Real.log (partitionFn witnessEnergy 1) ≤ 3 * Real.exp (-10) := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < partitionFn witnessEnergy 1 by linarith)
    rw [hZ] at h ⊢
    linarith
  -- entropy of the Gibbs state is tiny
  have hHgam : shannonEntropy gam ≤ 33 * Real.exp (-10) := by
    rw [hgam_def, entropy_gibbsState]
    linarith [hmean_le, hlogZ]
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hHgam_le : shannonEntropy gam ≤ Real.log 2 := by
    have : 33 * Real.exp (-10) ≤ 33 * (1 / 243) := by linarith
    linarith
  -- entropy of the final joint state
  have hHr1 : shannonEntropy r1 = 2 * Real.log 2 := by
    have h4 : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
      rw [show (1 / 4 : ℝ) = ((2 : ℝ) ^ (2 : ℕ))⁻¹ by norm_num, Real.log_inv, Real.log_pow]
      push_cast
      ring
    rw [shannonEntropy, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [hr1_def, Fin.sum_univ_four]
    norm_num [h4]
    ring
  refine ⟨1, 1, witnessEnergy, gam, fun x => (1 / 2 : ℝ) * gam x.2, r1, false,
    ∑ b, (marg2 r1 b - gam b) * witnessEnergy b, one_pos, one_pos, by
      rw [hgam_def]; norm_num, fun x => rfl, ⟨?_, ?_⟩, ?_, ?_, rfl⟩
  · intro x
    rw [hr1_def]
    dsimp only
    split <;> norm_num
  · rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [hr1_def, Fin.sum_univ_four]
    norm_num
  · -- the second law holds (with room to spare) for this process
    have hprod : shannonEntropy (fun x : Bool × Fin 4 => (1 / 2 : ℝ) * gam x.2)
        = Real.log 2 + shannonEntropy gam := by
      have hpS : IsProbDist (fun _ : Bool => (1 : ℝ) / 2) := by
        refine ⟨fun _ => by norm_num, ?_⟩
        rw [Fintype.sum_bool]; norm_num
      have hgamP : IsProbDist gam := by rw [hgam_def]; exact gibbsState_isProbDist witnessEnergy 1
      have := shannonEntropy_prod (fun _ : Bool => (1 : ℝ) / 2) gam hpS hgamP
      rw [shannonEntropy_uniform_bool] at this
      exact this
    rw [hprod, hHr1]
    linarith
  · intro s
    cases s <;> simp [hr1_def, marg1]

end Phys

