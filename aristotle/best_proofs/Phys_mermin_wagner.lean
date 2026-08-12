/-
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is repeated below as a module docstring; Lean requires `import` commands to
-- precede any module docstring.)

import Mathlib

/-!
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalized

We formalize the Mermin–Wagner theorem for the classical XY model, the standard model with a
continuous internal symmetry group (rotations of the spin circle `Spin = ℝ / 2πℤ`).

*The model.*  Sites are the lattice points of the box `Λ_L = {x ∈ ℤ^d : ‖x‖_∞ ≤ L}`; a
configuration assigns a spin angle to each site; the a priori measure is the uniform (Haar)
measure on `Λ_L → Spin`.  The energy is
`H(θ) = - ∑_{x,y} J x y * cos (θ x - θ y) + W θ`,
where `J` is an arbitrary nearest-neighbour coupling of strength at most `1` and `W` is an
arbitrary continuous boundary term depending only on the spins of the outermost shell of the box
(this encodes an arbitrary boundary condition, possibly strongly favouring one direction).
The thermal average of an observable is `gibbsAvg β H f`.

*The theorem* (`Phys.mermin_wagner`).  For `d ≤ 2`, any `β = 1/T < ∞` and any `ε > 0`, there is
`L₀` such that for all `L ≥ L₀` the magnetization at the centre of the box in any direction `c`
satisfies `|⟨cos (θ x₀ - c)⟩| ≤ ε`, uniformly in the coupling and in the boundary condition:
there is no spontaneous breaking of the rotation symmetry.  `Phys.mermin_wagner_magnetization`
restates this for the magnetization vector.

*The proof* is the spin-wave (twisting) argument.  Twisting a configuration by a slowly varying
radial profile `a` which equals `π` at the centre and `0` on the boundary shell costs, in the
symmetrized sense, at most the Dirichlet energy `K` of the profile, and one deduces from
`H(θ+a) + H(θ-a) ≤ 2 H(θ) + K` together with the arithmetic–geometric mean inequality that
`|magnetization| ≤ β K / 2`.  In dimension `d ≤ 2` the profile built from partial sums of the
harmonic series has Dirichlet energy `O(1 / harm L) → 0`, because the number of sites at distance
`r` grows at most like `r`, whereas the harmonic series diverges.
-/

open scoped BigOperators
open scoped Real
open MeasureTheory

set_option maxHeartbeats 1000000

namespace Phys

instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The single–spin space: the circle `ℝ / 2πℤ`.  The continuous internal symmetry group of the
model is this circle acting on itself by rotations. -/
abbrev Spin := AddCircle (2 * Real.pi)

/-! ## Part 1: an abstract twisting (spin–wave) inequality -/

section Abstract

variable {V : Type*} [Fintype V]

/-- Every continuous function on the (compact) configuration space is integrable. -/
lemma cont_integrable (f : (V → Spin) → ℝ) (hf : Continuous f) : Integrable f volume :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma volume_univ_pos : (0 : ENNReal) < volume (Set.univ : Set (V → Spin)) := by
  rw [MeasureTheory.volume_pi, Measure.pi_univ, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  rw [AddCircle.measure_univ]
  simp [Real.pi_pos]

lemma integral_pos_of_pos (f : (V → Spin) → ℝ) (hf : Continuous f) (hpos : ∀ θ, 0 < f θ) :
    0 < ∫ θ, f θ := by
  rw [integral_pos_iff_support_of_nonneg (fun θ => (hpos θ).le) (cont_integrable f hf)]
  have h : Function.support f = Set.univ := by
    ext θ; simp [Function.mem_support, (hpos θ).ne']
  rw [h]; exact volume_univ_pos

/-- The Gibbs (thermal) average of an observable `f` for the Hamiltonian `H` at inverse
temperature `β`, with respect to the Haar (uniform) a priori measure on spin configurations. -/
noncomputable def gibbsAvg (β : ℝ) (H f : (V → Spin) → ℝ) : ℝ :=
  (∫ θ, f θ * Real.exp (-β * H θ)) / (∫ θ, Real.exp (-β * H θ))

lemma exp_amgm (A B : ℝ) : 2 * Real.exp ((A + B) / 2) ≤ Real.exp A + Real.exp B := by
  have hA : Real.exp A = Real.exp (A / 2) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  have hB : Real.exp B = Real.exp (B / 2) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  have hAB : Real.exp ((A + B) / 2) = Real.exp (A / 2) * Real.exp (B / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [hA, hB, hAB]
  nlinarith [sq_nonneg (Real.exp (A / 2) - Real.exp (B / 2))]

/-- **Spin-wave (twisting) inequality.**  If twisting a configuration by `± a` costs at most `K`
in the symmetrized sense `H (θ + a) + H (θ - a) ≤ 2 H θ + K`, then the average of a nonnegative
observable cannot drop by more than the factor `exp (-βK/2)` when the twist is applied. -/
lemma twist_ineq (β : ℝ) (hβ : 0 ≤ β) (H : (V → Spin) → ℝ) (hH : Continuous H)
    (a : V → Spin) (K : ℝ) (hK : ∀ θ, H (θ + a) + H (θ - a) ≤ 2 * H θ + K)
    (f : (V → Spin) → ℝ) (hf : Continuous f) (hf0 : ∀ θ, 0 ≤ f θ) :
    2 * Real.exp (-(β * K) / 2) * ∫ θ, f θ * Real.exp (-β * H θ) ≤
      (∫ θ, f (θ + a) * Real.exp (-β * H θ)) + (∫ θ, f (θ - a) * Real.exp (-β * H θ)) := by
  have e1 : (∫ θ, f (θ + a) * Real.exp (-β * H θ)) = ∫ θ, f θ * Real.exp (-β * H (θ - a)) := by
    have := integral_add_right_eq_self (μ := (volume : Measure (V → Spin)))
      (fun θ : V → Spin => f θ * Real.exp (-β * H (θ - a))) a
    simpa using this
  have e2 : (∫ θ, f (θ - a) * Real.exp (-β * H θ)) = ∫ θ, f θ * Real.exp (-β * H (θ + a)) := by
    have := integral_add_right_eq_self (μ := (volume : Measure (V → Spin)))
      (fun θ : V → Spin => f θ * Real.exp (-β * H (θ + a))) (-a)
    simpa [sub_eq_add_neg] using this
  rw [e1, e2]
  have hc1 : Continuous fun θ : V → Spin => f θ * Real.exp (-β * H (θ - a)) := by fun_prop
  have hc2 : Continuous fun θ : V → Spin => f θ * Real.exp (-β * H (θ + a)) := by fun_prop
  have hc0 : Continuous fun θ : V → Spin =>
      2 * Real.exp (-(β * K) / 2) * (f θ * Real.exp (-β * H θ)) := by fun_prop
  rw [← integral_add (cont_integrable _ hc1) (cont_integrable _ hc2), ← integral_const_mul]
  refine integral_mono (cont_integrable _ hc0) (cont_integrable _ (hc1.add hc2)) ?_
  intro θ
  have h1 : 2 * Real.exp (-(β * K) / 2) * Real.exp (-β * H θ) ≤
      Real.exp (-β * H (θ - a)) + Real.exp (-β * H (θ + a)) := by
    refine le_trans ?_ (exp_amgm (-β * H (θ - a)) (-β * H (θ + a)))
    rw [mul_assoc, ← Real.exp_add]
    have hle : -(β * K) / 2 + -β * H θ ≤ (-β * H (θ - a) + -β * H (θ + a)) / 2 := by
      nlinarith [hK θ]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) (by norm_num)
  have h2 := mul_le_mul_of_nonneg_left h1 (hf0 θ)
  simp only []
  nlinarith [h2]

lemma cos_pi_shift (u : Spin) :
    Real.Angle.cos (u + ((Real.pi : ℝ) : Spin)) = -Real.Angle.cos u := by
  rw [show ((Real.pi : ℝ) : Spin) = ((Real.pi : ℝ) : Real.Angle) from rfl, Real.Angle.cos_add]
  simp

lemma neg_pi_spin : -((Real.pi : ℝ) : Spin) = ((Real.pi : ℝ) : Spin) := by
  rw [show ((Real.pi : ℝ) : Spin) = ((Real.pi : ℝ) : Real.Angle) from rfl, ← Real.Angle.coe_neg,
    Real.Angle.angle_eq_iff_two_pi_dvd_sub]
  exact ⟨-1, by ring⟩

lemma neg_one_le_angle_cos (u : Spin) : -1 ≤ Real.Angle.cos u := by
  induction u using Real.Angle.induction_on with
  | h x => rw [Real.Angle.cos_coe]; exact Real.neg_one_le_cos x

/-- One-sided bound on the magnetization in the direction `c` at the site `x₀`, in terms of the
cost `K` of a twist which rotates the spin at `x₀` by the angle `π`. -/
lemma gibbs_cos_le (β : ℝ) (hβ : 0 ≤ β) (H : (V → Spin) → ℝ) (hH : Continuous H)
    (a : V → Spin) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ θ, H (θ + a) + H (θ - a) ≤ 2 * H θ + K)
    (x₀ : V) (hx₀ : a x₀ = ((Real.pi : ℝ) : Spin)) (c : Spin) :
    gibbsAvg β H (fun θ => Real.Angle.cos ((θ x₀ - c : Spin))) ≤ β * K / 2 := by
  have hwc : Continuous (fun θ : V → Spin => Real.exp (-β * H θ)) := by fun_prop
  have hgc : Continuous (fun θ : V → Spin => Real.Angle.cos ((θ x₀ - c : Spin))) :=
    Real.Angle.continuous_cos.comp ((continuous_apply x₀).sub continuous_const)
  have hZ : 0 < ∫ θ : V → Spin, Real.exp (-β * H θ) :=
    integral_pos_of_pos _ hwc (fun θ => Real.exp_pos _)
  have hfc : Continuous (fun θ : V → Spin => 1 + Real.Angle.cos ((θ x₀ - c : Spin))) :=
    continuous_const.add hgc
  have hf0 : ∀ θ : V → Spin, 0 ≤ 1 + Real.Angle.cos ((θ x₀ - c : Spin)) := by
    intro θ; have := neg_one_le_angle_cos ((θ x₀ - c : Spin)); linarith
  have hplus : ∀ θ : V → Spin,
      (1 + Real.Angle.cos (((θ + a) x₀ - c : Spin))) = 1 - Real.Angle.cos ((θ x₀ - c : Spin)) := by
    intro θ
    have h : ((θ + a) x₀ - c : Spin) = (θ x₀ - c : Spin) + ((Real.pi : ℝ) : Spin) := by
      show θ x₀ + a x₀ - c = _
      rw [hx₀]; abel
    rw [h, cos_pi_shift]; ring
  have hminus : ∀ θ : V → Spin,
      (1 + Real.Angle.cos (((θ - a) x₀ - c : Spin))) = 1 - Real.Angle.cos ((θ x₀ - c : Spin)) := by
    intro θ
    have h : ((θ - a) x₀ - c : Spin) = (θ x₀ - c : Spin) + ((Real.pi : ℝ) : Spin) := by
      show θ x₀ - a x₀ - c = _
      rw [hx₀, sub_eq_add_neg (θ x₀), neg_pi_spin]; abel
    rw [h, cos_pi_shift]; ring
  have key := twist_ineq β hβ H hH a K hK _ hfc hf0
  simp only [hplus, hminus] at key
  have i1 : (∫ θ : V → Spin, (1 + Real.Angle.cos ((θ x₀ - c : Spin))) * Real.exp (-β * H θ))
      = (∫ θ : V → Spin, Real.exp (-β * H θ))
        + ∫ θ : V → Spin, Real.Angle.cos ((θ x₀ - c : Spin)) * Real.exp (-β * H θ) := by
    rw [← integral_add (cont_integrable _ hwc) (cont_integrable _ (by fun_prop))]
    congr 1; funext θ; ring
  have i2 : (∫ θ : V → Spin, (1 - Real.Angle.cos ((θ x₀ - c : Spin))) * Real.exp (-β * H θ))
      = (∫ θ : V → Spin, Real.exp (-β * H θ))
        - ∫ θ : V → Spin, Real.Angle.cos ((θ x₀ - c : Spin)) * Real.exp (-β * H θ) := by
    rw [← integral_sub (cont_integrable _ hwc) (cont_integrable _ (by fun_prop))]
    congr 1; funext θ; ring
  rw [i1, i2] at key
  set Z := ∫ θ : V → Spin, Real.exp (-β * H θ)
  set N := ∫ θ : V → Spin, Real.Angle.cos ((θ x₀ - c : Spin)) * Real.exp (-β * H θ)
  have hq1 : Real.exp (-(β * K) / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hq0 : 0 < Real.exp (-(β * K) / 2) := Real.exp_pos _
  have hq2 : 1 - Real.exp (-(β * K) / 2) ≤ β * K / 2 := by
    have := Real.add_one_le_exp (-(β * K) / 2)
    linarith
  rw [gibbsAvg, div_le_iff₀ hZ]
  rcases le_or_gt N 0 with h | h
  · nlinarith
  · nlinarith

lemma gibbsAvg_neg (β : ℝ) (H f : (V → Spin) → ℝ) :
    gibbsAvg β H (fun θ => -f θ) = -gibbsAvg β H f := by
  simp only [gibbsAvg, neg_mul, integral_neg, neg_div]

/-- **No spontaneous magnetization from a cheap twist.**  Two-sided version of `gibbs_cos_le`. -/
lemma abs_gibbs_cos_le (β : ℝ) (hβ : 0 ≤ β) (H : (V → Spin) → ℝ) (hH : Continuous H)
    (a : V → Spin) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ θ, H (θ + a) + H (θ - a) ≤ 2 * H θ + K)
    (x₀ : V) (hx₀ : a x₀ = ((Real.pi : ℝ) : Spin)) (c : Spin) :
    |gibbsAvg β H (fun θ => Real.Angle.cos ((θ x₀ - c : Spin)))| ≤ β * K / 2 := by
  have h1 := gibbs_cos_le β hβ H hH a K hK0 hK x₀ hx₀ c
  have h2 := gibbs_cos_le β hβ H hH a K hK0 hK x₀ hx₀ (c + ((Real.pi : ℝ) : Spin))
  have hrw : ∀ θ : V → Spin, Real.Angle.cos ((θ x₀ - (c + ((Real.pi : ℝ) : Spin)) : Spin))
      = -Real.Angle.cos ((θ x₀ - c : Spin)) := by
    intro θ
    have h : (θ x₀ - (c + ((Real.pi : ℝ) : Spin)) : Spin)
        = (θ x₀ - c : Spin) + ((Real.pi : ℝ) : Spin) := by
      rw [sub_add_eq_sub_sub, sub_eq_add_neg (θ x₀ - c), neg_pi_spin]
    rw [h, cos_pi_shift]
  simp only [hrw] at h2
  rw [gibbsAvg_neg] at h2
  exact abs_le.2 ⟨by linarith, h1⟩

end Abstract

/-! ## Part 2: the lattice XY model in a box of `ℤ^d` -/

/-- The sup-norm of a lattice point. -/
def latticeNorm {d : ℕ} (x : Fin d → ℤ) : ℕ := Finset.univ.sup fun i => (x i).natAbs

/-- The box of side `2L+1` centred at the origin in `ℤ^d`. -/
def box (d L : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ)

/-- Nearest–neighbour relation on `ℤ^d`. -/
def Adj {d : ℕ} (x y : Fin d → ℤ) : Prop := (∑ i, (x i - y i).natAbs) = 1

instance {d : ℕ} (x y : Fin d → ℤ) : Decidable (Adj x y) := by
  unfold Adj; infer_instance

/-- The sites of the model: the lattice points of the box. -/
abbrev Site (d L : ℕ) := {x : Fin d → ℤ // x ∈ box d L}

/-- The XY Hamiltonian in the box with couplings `J` and a boundary term `W`. -/
noncomputable def xyHamiltonian {d L : ℕ} (J : Site d L → Site d L → ℝ)
    (W : (Site d L → Spin) → ℝ) (θ : Site d L → Spin) : ℝ :=
  (-∑ x, ∑ y, J x y * Real.Angle.cos ((θ x - θ y : Spin))) + W θ

/-- Partial sums of the harmonic series. -/
noncomputable def harm (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, (1 : ℝ) / (i + 1)

/-- The (radial) spin–wave profile used to twist the configuration: it equals `π` at the origin
and `0` on the boundary shell of the box, and its discrete gradient is `π / ((r+1) * harm L)`. -/
noncomputable def profile (L r : ℕ) : ℝ := Real.pi * (1 - harm r / harm L)

/-- The twist applied to a configuration in the box. -/
noncomputable def twist (d L : ℕ) (x : Site d L) : Spin :=
  ((profile L (latticeNorm (x : Fin d → ℤ)) : ℝ) : Spin)

/-! ### Geometry and the Dirichlet energy of the profile -/

lemma mem_box_iff {d L : ℕ} (x : Fin d → ℤ) : x ∈ box d L ↔ latticeNorm x ≤ L := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc, latticeNorm, Finset.sup_le_iff,
    Finset.mem_univ, forall_true_left]
  exact ⟨fun h i => by have := h i; omega, fun h i => by have := h i; omega⟩

lemma card_box (d r : ℕ) : (box d r).card = (2 * r + 1) ^ d := by
  rw [box, Fintype.card_piFinset]
  rw [Finset.prod_congr rfl
    (fun i _ => by rw [Int.card_Icc]; norm_num; omega :
      ∀ i ∈ (Finset.univ : Finset (Fin d)), (Finset.Icc (-(r : ℤ)) (r : ℤ)).card = 2 * r + 1)]
  simp

lemma harm_pos {L : ℕ} (hL : 1 ≤ L) : 0 < harm L := by
  unfold harm
  exact Finset.sum_pos (fun i _ => by positivity) ⟨0, Finset.mem_range.2 hL⟩

lemma harm_succ (k : ℕ) : harm (k + 1) = harm k + 1 / (k + 1) := by
  simp [harm, Finset.sum_range_succ]

lemma harm_tendsto : Filter.Tendsto harm Filter.atTop Filter.atTop := by
  have := Real.tendsto_sum_range_one_div_nat_succ_atTop
  convert this using 2

lemma profile_zero_of_norm_eq {L : ℕ} (hL : 1 ≤ L) : profile L L = 0 := by
  simp [profile, div_self (harm_pos hL).ne']

lemma profile_origin (L : ℕ) : profile L 0 = Real.pi := by
  simp [profile, harm]

/-- Adjacent lattice points have sup-norms differing by at most one. -/
lemma latticeNorm_adj {d : ℕ} {x y : Fin d → ℤ} (h : Adj x y) :
    latticeNorm y ≤ latticeNorm x + 1 := by
  unfold latticeNorm
  rw [Finset.sup_le_iff]
  intro i _
  have hi : (x i - y i).natAbs ≤ 1 := by
    unfold Adj at h
    have : (x i - y i).natAbs ≤ ∑ j, (x j - y j).natAbs :=
      Finset.single_le_sum (f := fun j => (x j - y j).natAbs) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  have hx : (x i).natAbs ≤ Finset.univ.sup fun j => (x j).natAbs :=
    Finset.le_sup (f := fun j => (x j).natAbs) (Finset.mem_univ i)
  omega

/-- Increments of the harmonic partial sums along an edge of the radial profile. -/
lemma harm_diff_le {m n : ℕ} (h1 : n ≤ m + 1) (h2 : m ≤ n + 1) :
    |harm m - harm n| ≤ 1 / max 1 (m : ℝ) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmax : (0 : ℝ) < max 1 (m : ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hmaxle : max 1 (m : ℝ) ≤ (m : ℝ) + 1 := max_le (by linarith) (by linarith)
  have hinv : 1 / ((m : ℝ) + 1) ≤ 1 / max 1 (m : ℝ) := one_div_le_one_div_of_le hmax hmaxle
  rcases Nat.lt_trichotomy m n with h | h | h
  · have hn : n = m + 1 := by omega
    subst hn
    rw [harm_succ, abs_le]
    refine ⟨by linarith, ?_⟩
    have h0 : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
    linarith
  · subst h; rw [sub_self, abs_zero]; positivity
  · have hm : m = n + 1 := by omega
    subst hm
    rw [harm_succ, abs_le]
    push_cast
    have hmax' : max 1 ((n : ℝ) + 1) = (n : ℝ) + 1 := by
      refine max_eq_right ?_
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [hmax']
    have h0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    exact ⟨by linarith, by linarith⟩

/-- The key Lipschitz bound for the profile along an edge. -/
lemma profile_diff_le {L : ℕ} (hL : 1 ≤ L) {m n : ℕ} (h1 : n ≤ m + 1) (h2 : m ≤ n + 1) :
    |profile L m - profile L n| ≤ Real.pi / (max 1 (m : ℝ) * harm L) := by
  have hA := harm_pos hL
  have hmax : (0 : ℝ) < max 1 (m : ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hd := harm_diff_le h1 h2
  have hrw : profile L m - profile L n = Real.pi * (harm n - harm m) / harm L := by
    unfold profile; field_simp; ring
  rw [hrw, abs_div, abs_mul, abs_of_pos hA, abs_of_pos Real.pi_pos, abs_sub_comm]
  calc Real.pi * |harm m - harm n| / harm L
      ≤ Real.pi * (1 / max 1 (m : ℝ)) / harm L := by gcongr
    _ = Real.pi / (max 1 (m : ℝ) * harm L) := by field_simp

/-- In dimension `d ≤ 2`, a site has at most `9` lattice neighbours. -/
lemma card_neighbours_le {d L : ℕ} (hd : d ≤ 2) (x : Site d L) :
    ({y : Site d L | Adj (x : Fin d → ℤ) (y : Fin d → ℤ)} : Finset (Site d L)).card ≤ 9 := by
  classical
  set S : Finset (Site d L) := {y : Site d L | Adj (x : Fin d → ℤ) (y : Fin d → ℤ)} with hS
  have himg : S.image (fun y : Site d L => (y : Fin d → ℤ))
      ⊆ Fintype.piFinset (fun i : Fin d => ({(x : Fin d → ℤ) i - 1, (x : Fin d → ℤ) i,
          (x : Fin d → ℤ) i + 1} : Finset ℤ)) := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [hS] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [Fintype.mem_piFinset]
    intro i
    have hi : ((x : Fin d → ℤ) i - (y : Fin d → ℤ) i).natAbs ≤ 1 := by
      unfold Adj at hy
      have : ((x : Fin d → ℤ) i - (y : Fin d → ℤ) i).natAbs
          ≤ ∑ j, ((x : Fin d → ℤ) j - (y : Fin d → ℤ) j).natAbs :=
        Finset.single_le_sum (f := fun j => ((x : Fin d → ℤ) j - (y : Fin d → ℤ) j).natAbs)
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hcard : S.card = (S.image (fun y : Site d L => (y : Fin d → ℤ))).card :=
    (Finset.card_image_of_injective _ Subtype.val_injective).symm
  rw [hcard]
  refine le_trans (Finset.card_le_card himg) ?_
  rw [Fintype.card_piFinset]
  have hthree : ∀ i : Fin d, (({(x : Fin d → ℤ) i - 1, (x : Fin d → ℤ) i,
      (x : Fin d → ℤ) i + 1} : Finset ℤ)).card ≤ 3 := by
    intro i
    refine le_trans (Finset.card_insert_le _ _) ?_
    have : (({(x : Fin d → ℤ) i, (x : Fin d → ℤ) i + 1} : Finset ℤ)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    omega
  calc (∏ i, (({(x : Fin d → ℤ) i - 1, (x : Fin d → ℤ) i,
          (x : Fin d → ℤ) i + 1} : Finset ℤ)).card)
      ≤ ∏ _i : Fin d, 3 := Finset.prod_le_prod' (fun i _ => hthree i)
    _ = 3 ^ d := by simp
    _ ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hd
    _ ≤ 9 := by norm_num

/-- In dimension `d ≤ 2`, the sphere of radius `r ≥ 1` for the sup-norm has at most `8r` points. -/
lemma card_sphere_le {d : ℕ} (hd : d ≤ 2) (L m : ℕ) :
    ({x ∈ box d L | latticeNorm x = m + 1}).card ≤ 8 * (m + 1) := by
  have hsub : {x ∈ box d L | latticeNorm x = m + 1} ⊆ box d (m + 1) \ box d m := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    rw [Finset.mem_sdiff, mem_box_iff, mem_box_iff]
    exact ⟨by omega, by omega⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Finset.card_sdiff_of_subset (by intro x hx; rw [mem_box_iff] at *; omega)]
  rw [card_box, card_box]
  interval_cases d <;> simp <;> nlinarith [Nat.zero_le m]

lemma adj_symm {d : ℕ} {x y : Fin d → ℤ} (h : Adj x y) : Adj y x := by
  unfold Adj at *
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => by omega

/-- The number of sites at sup-norm distance `r` from the origin, weighted by `1 / max 1 r ^ 2`,
sums to at most `1 + 8 * harm L`:  this is the (only) place where `d ≤ 2` enters. -/
lemma sum_inv_sq_norm_le {d : ℕ} (hd : d ≤ 2) (L : ℕ) :
    ∑ x : Site d L, (1 / max 1 ((latticeNorm (x : Fin d → ℤ)) : ℝ)) ^ 2 ≤ 1 + 8 * harm L := by
  classical
  have h1 : ∑ x : Site d L, (1 / max 1 ((latticeNorm (x : Fin d → ℤ)) : ℝ)) ^ 2
      = ∑ x ∈ box d L, (1 / max 1 ((latticeNorm x : ℕ) : ℝ)) ^ 2 :=
    Finset.sum_coe_sort (box d L) (fun x => (1 / max 1 ((latticeNorm x : ℕ) : ℝ)) ^ 2)
  rw [h1]
  have hmaps : ∀ x ∈ box d L, latticeNorm x ∈ Finset.range (L + 1) := by
    intro x hx
    rw [Finset.mem_range]
    rw [mem_box_iff] at hx
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun x => (1 / max 1 ((latticeNorm x : ℕ) : ℝ)) ^ 2)]
  have hterm : ∀ r ∈ Finset.range (L + 1),
      (∑ x ∈ box d L with latticeNorm x = r, (1 / max 1 ((latticeNorm x : ℕ) : ℝ)) ^ 2)
        = ({x ∈ box d L | latticeNorm x = r}).card * (1 / max 1 (r : ℝ)) ^ 2 := by
    intro r _
    rw [Finset.sum_congr rfl (fun x hx => by
      simp only [Finset.mem_filter] at hx
      rw [hx.2])]
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_succ']
  have hzero : (({x ∈ box d L | latticeNorm x = 0}).card : ℝ)
      * (1 / max 1 ((0 : ℕ) : ℝ)) ^ 2 ≤ 1 := by
    have hsub : {x ∈ box d L | latticeNorm x = 0} ⊆ {(0 : Fin d → ℤ)} := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      simp only [Finset.mem_singleton]
      funext i
      have hle : (x i).natAbs ≤ latticeNorm x :=
        Finset.le_sup (f := fun j => (x j).natAbs) (Finset.mem_univ i)
      rw [hx.2] at hle
      simp only [Pi.zero_apply]
      omega
    have hcard : ({x ∈ box d L | latticeNorm x = 0}).card ≤ 1 :=
      le_trans (Finset.card_le_card hsub) (by simp)
    have hcast : (({x ∈ box d L | latticeNorm x = 0}).card : ℝ) ≤ 1 := by exact_mod_cast hcard
    norm_num
    linarith
  have hrest : ∀ m ∈ Finset.range L,
      (({x ∈ box d L | latticeNorm x = m + 1}).card : ℝ) * (1 / max 1 ((m + 1 : ℕ) : ℝ)) ^ 2
        ≤ 8 * (1 / ((m : ℝ) + 1)) := by
    intro m _
    have hc : (({x ∈ box d L | latticeNorm x = m + 1}).card : ℝ) ≤ 8 * ((m : ℝ) + 1) := by
      have h8 := card_sphere_le hd L m
      have hcast : (({x ∈ box d L | latticeNorm x = m + 1}).card : ℝ) ≤ ((8 * (m + 1) : ℕ) : ℝ) := by
        exact_mod_cast h8
      push_cast at hcast
      linarith
    have hmax : max 1 (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by
      push_cast
      refine max_eq_right ?_
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hgoal : ((m : ℝ) + 1) ^ 2 * (8 * (1 / ((m : ℝ) + 1))) = 8 * ((m : ℝ) + 1) := by
      field_simp
    rw [hmax, div_pow, one_pow, mul_one_div, div_le_iff₀ (by positivity)]
    linarith [hc, hgoal]
  have hfinal := add_le_add (Finset.sum_le_sum hrest) hzero
  refine le_trans hfinal ?_
  rw [← Finset.mul_sum]
  have hh : harm L = ∑ m ∈ Finset.range L, (1 : ℝ) / ((m : ℝ) + 1) := rfl
  rw [hh]
  linarith

/-- The Dirichlet energy of the spin-wave profile is small in dimension `d ≤ 2`. -/
lemma dirichlet_energy_bound {d : ℕ} (hd : d ≤ 2) {L : ℕ} (hL : 1 ≤ L) :
    (∑ x : Site d L, ∑ y : Site d L,
        if Adj (x : Fin d → ℤ) (y : Fin d → ℤ)
          then (profile L (latticeNorm (x : Fin d → ℤ))
                  - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2 else 0)
      ≤ 9 * Real.pi ^ 2 * (1 + 8 * harm L) / harm L ^ 2 := by
  classical
  have hA := harm_pos hL
  have hinner : ∀ x : Site d L,
      (∑ y : Site d L, if Adj (x : Fin d → ℤ) (y : Fin d → ℤ)
          then (profile L (latticeNorm (x : Fin d → ℤ))
                  - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2 else 0)
        ≤ 9 * (Real.pi / (max 1 ((latticeNorm (x : Fin d → ℤ) : ℕ) : ℝ) * harm L)) ^ 2 := by
    intro x
    rw [← Finset.sum_filter]
    have hbd : ∀ y ∈ ({y : Site d L | Adj (x : Fin d → ℤ) (y : Fin d → ℤ)} : Finset (Site d L)),
        (profile L (latticeNorm (x : Fin d → ℤ))
            - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2
          ≤ (Real.pi / (max 1 ((latticeNorm (x : Fin d → ℤ) : ℕ) : ℝ) * harm L)) ^ 2 := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      have h1 : latticeNorm (y : Fin d → ℤ) ≤ latticeNorm (x : Fin d → ℤ) + 1 :=
        latticeNorm_adj hy
      have h2 : latticeNorm (x : Fin d → ℤ) ≤ latticeNorm (y : Fin d → ℤ) + 1 :=
        latticeNorm_adj (adj_symm hy)
      have hp := profile_diff_le hL h1 h2
      have habs := abs_nonneg (profile L (latticeNorm (x : Fin d → ℤ))
        - profile L (latticeNorm (y : Fin d → ℤ)))
      calc (profile L (latticeNorm (x : Fin d → ℤ)) - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2
          = |profile L (latticeNorm (x : Fin d → ℤ))
              - profile L (latticeNorm (y : Fin d → ℤ))| ^ 2 := (sq_abs _).symm
        _ ≤ (Real.pi / (max 1 ((latticeNorm (x : Fin d → ℤ) : ℕ) : ℝ) * harm L)) ^ 2 :=
            pow_le_pow_left₀ habs hp 2
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hbd) ?_
    rw [nsmul_eq_mul]
    have hcard := card_neighbours_le hd x
    have hcast : ((({y : Site d L | Adj (x : Fin d → ℤ) (y : Fin d → ℤ)} :
        Finset (Site d L)).card : ℝ)) ≤ 9 := by exact_mod_cast hcard
    have hnn : (0 : ℝ) ≤ (Real.pi / (max 1 ((latticeNorm (x : Fin d → ℤ) : ℕ) : ℝ) * harm L)) ^ 2 :=
      sq_nonneg _
    nlinarith
  calc (∑ x : Site d L, ∑ y : Site d L,
        if Adj (x : Fin d → ℤ) (y : Fin d → ℤ)
          then (profile L (latticeNorm (x : Fin d → ℤ))
                  - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2 else 0)
      ≤ ∑ x : Site d L,
          9 * (Real.pi / (max 1 ((latticeNorm (x : Fin d → ℤ) : ℕ) : ℝ) * harm L)) ^ 2 :=
        Finset.sum_le_sum fun x _ => hinner x
    _ = (9 * Real.pi ^ 2 / harm L ^ 2)
          * ∑ x : Site d L, (1 / max 1 ((latticeNorm (x : Fin d → ℤ) : ℕ) : ℝ)) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        have hmax : (0 : ℝ) < max 1 ((latticeNorm (x : Fin d → ℤ) : ℕ) : ℝ) :=
          lt_of_lt_of_le zero_lt_one (le_max_left _ _)
        field_simp
    _ ≤ (9 * Real.pi ^ 2 / harm L ^ 2) * (1 + 8 * harm L) :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_norm_le hd L) (by positivity)
    _ = 9 * Real.pi ^ 2 * (1 + 8 * harm L) / harm L ^ 2 := by ring

/-- The elementary trigonometric identity behind the spin-wave estimate. -/
lemma cos_add_cos_sub (v : Spin) (t : ℝ) :
    Real.Angle.cos (v + ((t : ℝ) : Spin)) + Real.Angle.cos (v - ((t : ℝ) : Spin))
      = 2 * Real.Angle.cos v * Real.cos t := by
  have h1 : Real.Angle.cos (v + ((t : ℝ) : Spin))
      = Real.Angle.cos v * Real.cos t - Real.Angle.sin v * Real.sin t := by
    rw [show ((t : ℝ) : Spin) = ((t : ℝ) : Real.Angle) from rfl, Real.Angle.cos_add,
      Real.Angle.cos_coe, Real.Angle.sin_coe]
  have h2 : Real.Angle.cos (v - ((t : ℝ) : Spin))
      = Real.Angle.cos v * Real.cos t + Real.Angle.sin v * Real.sin t := by
    rw [sub_eq_add_neg, show -((t : ℝ) : Spin) = (((-t) : ℝ) : Real.Angle) by
      rw [Real.Angle.coe_neg]; rfl, Real.Angle.cos_add, Real.Angle.cos_coe, Real.Angle.sin_coe]
    simp
  rw [h1, h2]; ring

/-- The symmetrized cost of twisting a single bond by the angle `t` is at most `t ^ 2`. -/
lemma pair_bound (Jv : ℝ) (hJ : |Jv| ≤ 1) (v : Spin) (t : ℝ) :
    -(Jv * Real.Angle.cos (v + ((t : ℝ) : Spin))) - (Jv * Real.Angle.cos (v - ((t : ℝ) : Spin)))
      + 2 * (Jv * Real.Angle.cos v) ≤ t ^ 2 := by
  have hsum := cos_add_cos_sub v t
  have hc : |Real.Angle.cos v| ≤ 1 := by
    induction v using Real.Angle.induction_on with
    | h x => rw [Real.Angle.cos_coe]; exact Real.abs_cos_le_one x
  have hcos : 1 - Real.cos t ≤ t ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := t); linarith
  have hcos0 : 0 ≤ 1 - Real.cos t := by
    have := Real.cos_le_one t; linarith
  have key : -(Jv * Real.Angle.cos (v + ((t : ℝ) : Spin)))
      - (Jv * Real.Angle.cos (v - ((t : ℝ) : Spin))) + 2 * (Jv * Real.Angle.cos v)
      = 2 * (Jv * Real.Angle.cos v) * (1 - Real.cos t) := by
    linear_combination (-Jv) * hsum
  rw [key]
  have habs : |2 * (Jv * Real.Angle.cos v)| ≤ 2 := by
    rw [abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg Jv, abs_nonneg (Real.Angle.cos v)]
  have h1 := abs_le.1 habs
  nlinarith [h1.1, h1.2]

/-- The symmetrized energy cost of the twist is bounded by the Dirichlet energy of the profile. -/
lemma xy_twist_cost {d L : ℕ} (J : Site d L → Site d L → ℝ)
    (W : (Site d L → Spin) → ℝ)
    (hJ1 : ∀ x y, |J x y| ≤ 1)
    (hJ0 : ∀ x y : Site d L, ¬ Adj (x : Fin d → ℤ) (y : Fin d → ℤ) → J x y = 0)
    (hW : ∀ θ θ' : Site d L → Spin,
      (∀ x : Site d L, latticeNorm (x : Fin d → ℤ) = L → θ x = θ' x) → W θ = W θ')
    (hL : 1 ≤ L) (θ : Site d L → Spin) :
    xyHamiltonian J W (θ + twist d L) + xyHamiltonian J W (θ - twist d L)
      ≤ 2 * xyHamiltonian J W θ
        + ∑ x : Site d L, ∑ y : Site d L,
            (if Adj (x : Fin d → ℤ) (y : Fin d → ℤ)
              then (profile L (latticeNorm (x : Fin d → ℤ))
                      - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2 else 0) := by
  have hu : ∀ x : Site d L, latticeNorm (x : Fin d → ℤ) = L → twist d L x = 0 := by
    intro x hx
    rw [twist, hx, profile_zero_of_norm_eq hL]
    simp
  have hW1 : W (θ + twist d L) = W θ := hW _ _ (fun x hx => by simp [hu x hx])
  have hW2 : W (θ - twist d L) = W θ := hW _ _ (fun x hx => by simp [hu x hx])
  have hdiffp : ∀ x y : Site d L, ((θ + twist d L) x - (θ + twist d L) y : Spin)
      = (θ x - θ y : Spin) + (((profile L (latticeNorm (x : Fin d → ℤ))
          - profile L (latticeNorm (y : Fin d → ℤ))) : ℝ) : Spin) := by
    intro x y
    show θ x + twist d L x - (θ y + twist d L y) = _
    rw [twist, twist, show ((((profile L (latticeNorm (x : Fin d → ℤ))
          - profile L (latticeNorm (y : Fin d → ℤ))) : ℝ) : Spin))
        = ((profile L (latticeNorm (x : Fin d → ℤ)) : ℝ) : Spin)
          - ((profile L (latticeNorm (y : Fin d → ℤ)) : ℝ) : Spin) from
      (Real.Angle.coe_sub _ _)]
    abel
  have hdiffm : ∀ x y : Site d L, ((θ - twist d L) x - (θ - twist d L) y : Spin)
      = (θ x - θ y : Spin) - (((profile L (latticeNorm (x : Fin d → ℤ))
          - profile L (latticeNorm (y : Fin d → ℤ))) : ℝ) : Spin) := by
    intro x y
    show θ x - twist d L x - (θ y - twist d L y) = _
    rw [twist, twist, show ((((profile L (latticeNorm (x : Fin d → ℤ))
          - profile L (latticeNorm (y : Fin d → ℤ))) : ℝ) : Spin))
        = ((profile L (latticeNorm (x : Fin d → ℤ)) : ℝ) : Spin)
          - ((profile L (latticeNorm (y : Fin d → ℤ)) : ℝ) : Spin) from
      (Real.Angle.coe_sub _ _)]
    abel
  have hterm : ∀ x y : Site d L,
      -(J x y * Real.Angle.cos ((θ + twist d L) x - (θ + twist d L) y))
        - (J x y * Real.Angle.cos ((θ - twist d L) x - (θ - twist d L) y))
        + 2 * (J x y * Real.Angle.cos ((θ x - θ y : Spin)))
      ≤ (if Adj (x : Fin d → ℤ) (y : Fin d → ℤ)
          then (profile L (latticeNorm (x : Fin d → ℤ))
                  - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2 else 0) := by
    intro x y
    by_cases hadj : Adj (x : Fin d → ℤ) (y : Fin d → ℤ)
    · rw [if_pos hadj, hdiffp, hdiffm]
      exact pair_bound (J x y) (hJ1 x y) _ _
    · rw [if_neg hadj, hJ0 x y hadj]
      simp
  have hsum : (∑ x : Site d L, ∑ y : Site d L,
      (-(J x y * Real.Angle.cos ((θ + twist d L) x - (θ + twist d L) y))
        - (J x y * Real.Angle.cos ((θ - twist d L) x - (θ - twist d L) y))
        + 2 * (J x y * Real.Angle.cos ((θ x - θ y : Spin)))))
      ≤ ∑ x : Site d L, ∑ y : Site d L,
          (if Adj (x : Fin d → ℤ) (y : Fin d → ℤ)
            then (profile L (latticeNorm (x : Fin d → ℤ))
                    - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2 else 0) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
  have hexp : (∑ x : Site d L, ∑ y : Site d L,
      (-(J x y * Real.Angle.cos ((θ + twist d L) x - (θ + twist d L) y))
        - (J x y * Real.Angle.cos ((θ - twist d L) x - (θ - twist d L) y))
        + 2 * (J x y * Real.Angle.cos ((θ x - θ y : Spin)))))
      = -(∑ x : Site d L, ∑ y : Site d L,
            J x y * Real.Angle.cos ((θ + twist d L) x - (θ + twist d L) y))
        - (∑ x : Site d L, ∑ y : Site d L,
            J x y * Real.Angle.cos ((θ - twist d L) x - (θ - twist d L) y))
        + 2 * ∑ x : Site d L, ∑ y : Site d L, J x y * Real.Angle.cos ((θ x - θ y : Spin)) := by
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hexp] at hsum
  unfold xyHamiltonian
  rw [hW1, hW2]
  linarith

lemma xyHamiltonian_continuous {d L : ℕ} (J : Site d L → Site d L → ℝ)
    (W : (Site d L → Spin) → ℝ) (hW : Continuous W) : Continuous (xyHamiltonian J W) := by
  unfold xyHamiltonian
  refine Continuous.add (continuous_neg.comp ?_) hW
  refine continuous_finset_sum _ fun x _ => continuous_finset_sum _ fun y _ => ?_
  exact continuous_const.mul (Real.Angle.continuous_cos.comp
    ((continuous_apply x).sub (continuous_apply y)))

/-! ## Part 3: the Mermin–Wagner theorem -/

/-- **Mermin–Wagner theorem.**  In dimension `d ≤ 2` and at any positive temperature
(`β = 1/T < ∞`), the classical XY model — a model with the continuous symmetry group of rotations
of the spin circle — exhibits no spontaneous breaking of that symmetry: the magnetization at the
centre of the box, in any direction `c`, tends to `0` as the box grows, *uniformly* over all
nearest-neighbour couplings of strength at most one and over all boundary conditions (encoded by
an arbitrary continuous boundary term `W` which depends only on the spins of the boundary
shell of the box, and which may try to align the spins along a fixed direction). -/
theorem mermin_wagner {d : ℕ} (hd : d ≤ 2) (β : ℝ) (hβ : 0 ≤ β) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ (J : Site d L → Site d L → ℝ) (W : (Site d L → Spin) → ℝ) (c : Spin) (x₀ : Site d L),
        (∀ x y, |J x y| ≤ 1) →
        (∀ x y : Site d L, ¬ Adj (x : Fin d → ℤ) (y : Fin d → ℤ) → J x y = 0) →
        Continuous W →
        (∀ θ θ' : Site d L → Spin,
          (∀ x : Site d L, latticeNorm (x : Fin d → ℤ) = L → θ x = θ' x) → W θ = W θ') →
        (x₀ : Fin d → ℤ) = 0 →
        |gibbsAvg β (xyHamiltonian J W) fun θ => Real.Angle.cos ((θ x₀ - c : Spin))| ≤ ε := by
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1
    (harm_tendsto.eventually_ge_atTop (max 1 (81 * Real.pi ^ 2 * β / (2 * ε))))
  refine ⟨L₀, ?_⟩
  intro L hL J W c x₀ hJ1 hJ0 hWc hW hx₀
  have hA := hL₀ L hL
  have hA1 : (1 : ℝ) ≤ harm L := le_trans (le_max_left _ _) hA
  have hA2 : 81 * Real.pi ^ 2 * β / (2 * ε) ≤ harm L := le_trans (le_max_right _ _) hA
  have hA0 : 0 < harm L := lt_of_lt_of_le zero_lt_one hA1
  have hL1 : 1 ≤ L := by
    by_contra h
    have : L = 0 := by omega
    rw [this] at hA1
    simp [harm] at hA1
    linarith [hA1]
  set K : ℝ := ∑ x : Site d L, ∑ y : Site d L,
      (if Adj (x : Fin d → ℤ) (y : Fin d → ℤ)
        then (profile L (latticeNorm (x : Fin d → ℤ))
                - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2 else 0) with hKdef
  have hK0 : 0 ≤ K := by
    refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
    split <;> positivity
  have hKb : K ≤ 9 * Real.pi ^ 2 * (1 + 8 * harm L) / harm L ^ 2 :=
    dirichlet_energy_bound hd hL1
  have hcost := xy_twist_cost J W hJ1 hJ0 hW hL1
  have hx₀t : twist d L x₀ = ((Real.pi : ℝ) : Spin) := by
    have : latticeNorm (x₀ : Fin d → ℤ) = 0 := by
      rw [hx₀]; simp [latticeNorm]
    rw [twist, this, profile_origin]
  have hmain := abs_gibbs_cos_le β hβ (xyHamiltonian J W)
    (xyHamiltonian_continuous J W hWc) (twist d L) K hK0 hcost x₀ hx₀t c
  refine hmain.trans ?_
  -- quantitative estimate: β K / 2 ≤ ε
  have hstep : 9 * Real.pi ^ 2 * (1 + 8 * harm L) / harm L ^ 2 ≤ 81 * Real.pi ^ 2 / harm L := by
    rw [div_le_div_iff₀ (by positivity) hA0]
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 9 * Real.pi ^ 2) hA0.le)
      (by linarith : (0:ℝ) ≤ harm L - 1)]
  have hKfin : K ≤ 81 * Real.pi ^ 2 / harm L := hKb.trans hstep
  have : β * K / 2 ≤ β * (81 * Real.pi ^ 2 / harm L) / 2 := by
    have := mul_le_mul_of_nonneg_left hKfin hβ
    linarith
  refine this.trans ?_
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)] at *
  have h2 : 81 * Real.pi ^ 2 * β ≤ harm L * (2 * ε) := by
    rw [div_le_iff₀ (by positivity)] at hA2
    linarith
  rw [mul_div_assoc'] at *
  rw [div_le_iff₀ hA0]
  nlinarith

/-- **Mermin–Wagner theorem, vector form.**  In dimension `d ≤ 2` and at any positive temperature,
the mean magnetization vector `(⟨cos θ₀⟩, ⟨sin θ₀⟩)` at the centre of the box has length at most
`ε` once the box is large enough, uniformly over couplings and boundary conditions. -/
theorem mermin_wagner_magnetization {d : ℕ} (hd : d ≤ 2) (β : ℝ) (hβ : 0 ≤ β) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ (J : Site d L → Site d L → ℝ) (W : (Site d L → Spin) → ℝ) (x₀ : Site d L),
        (∀ x y, |J x y| ≤ 1) →
        (∀ x y : Site d L, ¬ Adj (x : Fin d → ℤ) (y : Fin d → ℤ) → J x y = 0) →
        Continuous W →
        (∀ θ θ' : Site d L → Spin,
          (∀ x : Site d L, latticeNorm (x : Fin d → ℤ) = L → θ x = θ' x) → W θ = W θ') →
        (x₀ : Fin d → ℤ) = 0 →
        Real.sqrt ((gibbsAvg β (xyHamiltonian J W) fun θ => Real.Angle.cos (θ x₀)) ^ 2
            + (gibbsAvg β (xyHamiltonian J W) fun θ => Real.Angle.sin (θ x₀)) ^ 2) ≤ ε := by
  obtain ⟨L₀, hL₀⟩ := mermin_wagner hd β hβ (ε := ε / 2) (by linarith)
  refine ⟨L₀, fun L hL J W x₀ hJ1 hJ0 hWc hW hx₀ => ?_⟩
  have hcos := hL₀ L hL J W 0 x₀ hJ1 hJ0 hWc hW hx₀
  have hsin := hL₀ L hL J W (((Real.pi / 2 : ℝ) : Spin)) x₀ hJ1 hJ0 hWc hW hx₀
  simp only [sub_zero] at hcos
  have hrw : (fun θ : Site d L → Spin =>
      Real.Angle.cos ((θ x₀ - ((Real.pi / 2 : ℝ) : Spin) : Spin)))
      = fun θ : Site d L → Spin => Real.Angle.sin (θ x₀) := by
    funext θ
    exact Real.Angle.cos_sub_pi_div_two (θ x₀)
  rw [hrw] at hsin
  set a := gibbsAvg β (xyHamiltonian J W) fun θ => Real.Angle.cos (θ x₀)
  set b := gibbsAvg β (xyHamiltonian J W) fun θ => Real.Angle.sin (θ x₀)
  have hle : Real.sqrt (a ^ 2 + b ^ 2) ≤ |a| + |b| := by
    rw [show |a| + |b| = Real.sqrt ((|a| + |b|) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    nlinarith [abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b]
  linarith

end Phys

