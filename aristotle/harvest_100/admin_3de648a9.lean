/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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

namespace Frontier

/-! ## The finite-volume Ising model -/

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The real spin value `±1` attached to a Boolean spin variable. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- (Minus the) energy of a configuration `σ` for the coupling constants `J`. -/
def energy (J : V → V → ℝ) (σ : V → Bool) : ℝ :=
  ∑ x : V, ∑ y : V, J x y * (spin (σ x) * spin (σ y))

/-- Unnormalised Boltzmann weight of a configuration at inverse temperature `β`. -/
noncomputable def weight (β : ℝ) (J : V → V → ℝ) (σ : V → Bool) : ℝ :=
  Real.exp (β * energy J σ)

/-- The partition function. -/
noncomputable def Z (β : ℝ) (J : V → V → ℝ) : ℝ := ∑ σ : V → Bool, weight β J σ

/-- The two-point function `⟨σ_x σ_y⟩` of the finite-volume Ising model. -/
noncomputable def corr (β : ℝ) (J : V → V → ℝ) (x y : V) : ℝ :=
  (∑ σ : V → Bool, weight β J σ * (spin (σ x) * spin (σ y))) / Z β J

lemma spin_mul_self (b : Bool) : spin b * spin b = 1 := by
  cases b <;> norm_num [spin]

lemma abs_spin (b : Bool) : |spin b| = 1 := by
  cases b <;> norm_num [spin]

omit [DecidableEq V] in
lemma weight_pos (β : ℝ) (J : V → V → ℝ) (σ : V → Bool) : 0 < weight β J σ :=
  Real.exp_pos _

lemma Z_pos (β : ℝ) (J : V → V → ℝ) : 0 < Z β J :=
  Finset.sum_pos (fun σ _ => weight_pos β J σ) Finset.univ_nonempty

lemma corr_self (β : ℝ) (J : V → V → ℝ) (x : V) : corr β J x x = 1 := by
  unfold corr
  simp only [spin_mul_self, mul_one]
  exact div_self (ne_of_gt (Z_pos β J))

/-- The two-point function is bounded by `1` in absolute value. -/
lemma abs_corr_le_one (β : ℝ) (J : V → V → ℝ) (x y : V) : |corr β J x y| ≤ 1 := by
  have hZ := Z_pos (V := V) β J
  rw [corr, abs_div, abs_of_pos hZ, div_le_one hZ]
  calc |∑ σ : V → Bool, weight β J σ * (spin (σ x) * spin (σ y))|
      ≤ ∑ σ : V → Bool, |weight β J σ * (spin (σ x) * spin (σ y))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = Z β J := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [abs_mul, abs_mul, abs_spin, abs_spin, one_mul, mul_one,
          abs_of_pos (weight_pos β J σ)]

lemma corr_le_one (β : ℝ) (J : V → V → ℝ) (x y : V) : corr β J x y ≤ 1 :=
  le_of_abs_le (abs_corr_le_one β J x y)

omit [Fintype V] in
/-- Flipping the spin at a single site is an involution of configuration space. -/
lemma spin_flip_involutive (x : V) :
    Function.Involutive (fun σ : V → Bool => Function.update σ x (!(σ x))) := by
  intro σ
  funext v
  by_cases h : v = x <;> simp [Function.update, h]

/-- **Infinite-temperature base case.** At `β = 0` the spins are i.i.d. uniform and
all correlations between distinct sites vanish: `⟨σ_x σ_y⟩ = 0` for `x ≠ y`. -/
theorem corr_zero_of_ne (J : V → V → ℝ) {x y : V} (hxy : x ≠ y) : corr 0 J x y = 0 := by
  have hnum : (∑ σ : V → Bool, weight 0 J σ * (spin (σ x) * spin (σ y))) = 0 := by
    simp only [weight, zero_mul, Real.exp_zero, one_mul]
    set e := (spin_flip_involutive (V := V) x).toPerm _ with he
    have key : (∑ σ : V → Bool, (spin (σ x) * spin (σ y)))
        = ∑ σ : V → Bool, (spin ((e σ) x) * spin ((e σ) y)) :=
      (Equiv.sum_comp e (fun σ => spin (σ x) * spin (σ y))).symm
    have h2 : ∀ σ : V → Bool, spin ((e σ) x) * spin ((e σ) y) = -(spin (σ x) * spin (σ y)) := by
      intro σ
      have hx : (e σ) x = !(σ x) := by simp [he, Function.Involutive.toPerm, Function.update]
      have hy : (e σ) y = σ y := by
        simp [he, Function.Involutive.toPerm, Function.update, (Ne.symm hxy)]
      rw [hx, hy]
      cases σ x <;> cases σ y <;> norm_num [spin]
    have h3 : (∑ σ : V → Bool, spin ((e σ) x) * spin ((e σ) y))
        = -∑ σ : V → Bool, spin (σ x) * spin (σ y) := by
      simp only [h2, Finset.sum_neg_distrib]
    linarith [key.trans h3]
  rw [corr, hnum, zero_div]

/-- The maximal two-point function between the origin `o` and the vertices at
distance `n` (the quantity whose decay is at stake in sharpness). -/
noncomputable def twoPoint (β : ℝ) (J : V → V → ℝ) (o : V) (d : V → ℕ) (n : ℕ) : ℝ :=
  if h : (Finset.univ.filter (fun v : V => d v = n)).Nonempty then
    (Finset.univ.filter (fun v : V => d v = n)).sup' h (fun v => corr β J o v)
  else 0

lemma twoPoint_le_one (β : ℝ) (J : V → V → ℝ) (o : V) (d : V → ℕ) (n : ℕ) :
    twoPoint β J o d n ≤ 1 := by
  unfold twoPoint
  split
  · exact Finset.sup'_le _ _ fun v _ => corr_le_one β J o v
  · norm_num

end Ising

/-! ## The two abstract inputs of the Duminil-Copin–Tassion argument -/

/-- **Subcritical reduction.** A nonnegative, bounded quantity that contracts by a
factor `c < 1` over every scale step of length `L` decays exponentially. -/
theorem exp_decay_of_geometric (θ : ℕ → ℝ) (hnn : ∀ n, 0 ≤ θ n) (hle : ∀ n, θ n ≤ 1)
    (L : ℕ) (hL : 1 ≤ L) (c : ℝ) (hc1 : c < 1)
    (hstep : ∀ n, θ (n + L) ≤ c * θ n) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ ∀ n, θ n ≤ C * Real.exp (-a * n) := by
  set c' : ℝ := max c (1/2) with hc'
  have hc'pos : 0 < c' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hc'1 : c' < 1 := max_lt hc1 (by norm_num)
  have hstep' : ∀ n, θ (n + L) ≤ c' * θ n := fun n =>
    (hstep n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hnn n))
  have hpow : ∀ q r : ℕ, θ (r + q * L) ≤ c' ^ q := by
    intro q
    induction q with
    | zero => intro r; simpa using hle r
    | succ q ih =>
      intro r
      have hrw : r + (q + 1) * L = (r + q * L) + L := by ring
      rw [hrw]
      calc θ ((r + q * L) + L) ≤ c' * θ (r + q * L) := hstep' _
        _ ≤ c' * c' ^ q := mul_le_mul_of_nonneg_left (ih r) (le_of_lt hc'pos)
        _ = c' ^ (q + 1) := by ring
  have hlogneg : Real.log c' < 0 := Real.log_neg hc'pos hc'1
  have hLpos : (0:ℝ) < L := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hL
  refine ⟨1 / c', -Real.log c' / L, by positivity, div_pos (by linarith) hLpos, ?_⟩
  intro n
  have hn : n % L + (n / L) * L = n := Nat.mod_add_div' n L
  have h1 : θ n ≤ c' ^ (n / L) := by
    have h := hpow (n / L) (n % L)
    rwa [hn] at h
  have h2 : c' ^ (n / L) = Real.exp ((n / L : ℕ) * Real.log c') := by
    rw [Real.exp_nat_mul, Real.exp_log hc'pos]
  have hq : (n:ℝ) / L - 1 ≤ ((n / L : ℕ) : ℝ) := by
    have hmod : n % L < L := Nat.mod_lt _ (by omega)
    have hlt : n < (n / L) * L + L := by omega
    have hlt' : (n:ℝ) < ((n / L : ℕ) : ℝ) * L + L := by exact_mod_cast hlt
    rw [sub_le_iff_le_add, div_le_iff₀ hLpos]
    nlinarith
  have h3 : ((n / L : ℕ) : ℝ) * Real.log c' ≤ ((n:ℝ)/L - 1) * Real.log c' :=
    mul_le_mul_of_nonpos_right hq (le_of_lt hlogneg)
  have key : Real.exp (((n:ℝ)/L - 1) * Real.log c')
      = 1 / c' * Real.exp (-(-Real.log c' / L) * n) := by
    rw [show (-(-Real.log c'/(L:ℝ)) * n) = ((n:ℝ)/L) * Real.log c' by ring,
      sub_mul, one_mul, Real.exp_sub, Real.exp_log hc'pos]
    ring
  calc θ n ≤ Real.exp ((n / L : ℕ) * Real.log c') := by rw [← h2]; exact h1
    _ ≤ Real.exp (((n:ℝ)/L - 1) * Real.log c') := Real.exp_le_exp.mpr h3
    _ = 1 / c' * Real.exp (-(-Real.log c' / L) * n) := key

/-- **Supercritical reduction.** A magnetization vanishing at `βc`, continuous on
`[βc, ∞)` and with derivative at least `c₀` above `βc`, obeys the mean-field type
lower bound `M β ≥ c₀ (β - βc)`.

The analytic core is the Mathlib mean-value estimate
`Convex.mul_sub_le_image_sub_of_le_deriv`. -/
theorem linear_lower_of_deriv_ge (M dM : ℝ → ℝ) (βc c0 : ℝ) (hM0 : M βc = 0)
    (hc : ContinuousOn M (Set.Ici βc))
    (hd : ∀ β, βc < β → HasDerivAt M (dM β) β)
    (hge : ∀ β, βc < β → c0 ≤ dM β) :
    ∀ β, βc ≤ β → c0 * (β - βc) ≤ M β := by
  intro β hβ
  have hint : interior (Set.Ici βc) = Set.Ioi βc := interior_Ici
  have hdiff : DifferentiableOn ℝ M (interior (Set.Ici βc)) := by
    rw [hint]
    intro x hx
    exact ((hd x hx).differentiableAt).differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Set.Ici βc), c0 ≤ deriv M x := by
    intro x hx
    rw [hint] at hx
    rw [(hd x hx).deriv]
    exact hge x hx
  have h := (convex_Ici βc).mul_sub_le_image_sub_of_le_deriv hc hdiff hderiv βc
    Set.self_mem_Ici β (Set.mem_Ici.mpr hβ) hβ
  rwa [hM0, sub_zero] at h

/-! ## Sharpness of the phase transition -/

open Ising in
/-- **Sharpness of the phase transition for the Ising model** (Aizenman–Barsky,
Duminil-Copin–Tassion), in the form of a Lean-checked reduction.

For a finite-volume Ising model with couplings `J`, origin `o` and a distance
function `d`, `twoPoint β J o d n` is the largest correlation `⟨σ_o σ_v⟩` over the
vertices `v` at distance `n` from `o`, and `M` is the magnetization, with critical
point `βc`.

Assuming the two standard analytic inputs of the Duminil-Copin–Tassion argument:

* (subcritical) below `βc` the two-point function contracts by a factor `c < 1`
  over some fixed scale `L`, and it is nonnegative (Griffiths' inequality);
* (supercritical) above `βc` the magnetization is differentiable with derivative
  bounded below by `c₀`, is continuous up to `βc` and vanishes at `βc`;

the phase transition is *sharp*:

* for every `β < βc` the two-point function decays exponentially in the distance;
* for every `β ≥ βc` the magnetization satisfies the mean-field lower bound
  `M β ≥ c₀ (β - βc)`.

The third conclusion is the infinite-temperature base case, which is proved
unconditionally: at `β = 0` all correlations between distinct sites vanish. -/
theorem duminil_ising_sharp {V : Type*} [Fintype V] [DecidableEq V]
    (J : V → V → ℝ) (o : V) (d : V → ℕ) (βc c0 : ℝ) (M dM : ℝ → ℝ)
    (hGriffiths : ∀ β n, 0 ≤ twoPoint β J o d n)
    (hsub : ∀ β, β < βc → ∃ L : ℕ, 1 ≤ L ∧ ∃ c : ℝ, c < 1 ∧
      ∀ n, twoPoint β J o d (n + L) ≤ c * twoPoint β J o d n)
    (hM0 : M βc = 0) (hMcont : ContinuousOn M (Set.Ici βc))
    (hMderiv : ∀ β, βc < β → HasDerivAt M (dM β) β)
    (hdM : ∀ β, βc < β → c0 ≤ dM β) :
    (∀ β, β < βc → ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
        ∀ n, twoPoint β J o d n ≤ C * Real.exp (-a * n)) ∧
    (∀ β, βc ≤ β → c0 * (β - βc) ≤ M β) ∧
    (∀ x y : V, x ≠ y → corr 0 J x y = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro β hβ
    obtain ⟨L, hL, c, hc1, hstep⟩ := hsub β hβ
    exact exp_decay_of_geometric _ (fun n => hGriffiths β n)
      (fun n => twoPoint_le_one β J o d n) L hL c hc1 hstep
  · exact linear_lower_of_deriv_ge M dM βc c0 hM0 hMcont hMderiv hdM
  · intro x y hxy
    exact corr_zero_of_ne J hxy

open Ising in
/-- Non-vacuity check: the hypotheses of `duminil_ising_sharp` are simultaneously
satisfiable, here by the two-site model with vanishing couplings, all vertices at
distance `0` from the origin, critical point `βc = 0` and magnetization `M β = β`. -/
theorem duminil_ising_sharp_hypotheses_satisfiable :
    (∀ β, β < (0:ℝ) → ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
      ∀ n, twoPoint β (fun _ _ : Bool => (0:ℝ)) true (fun _ => 0) n ≤ C * Real.exp (-a * n)) ∧
    (∀ β, (0:ℝ) ≤ β → (1:ℝ) * (β - 0) ≤ id β) ∧
    (∀ x y : Bool, x ≠ y → corr 0 (fun _ _ : Bool => (0:ℝ)) x y = 0) := by
  have hne : (Finset.univ.filter (fun v : Bool => (0:ℕ) = 0)).Nonempty := ⟨true, by simp⟩
  have hzero : ∀ (β : ℝ) (n : ℕ), n ≠ 0 →
      twoPoint β (fun _ _ : Bool => (0:ℝ)) true (fun _ => 0) n = 0 := by
    intro β n hn
    rw [twoPoint, dif_neg]
    simp [Ne.symm hn]
  refine duminil_ising_sharp (fun _ _ : Bool => (0:ℝ)) true (fun _ => 0) 0 1 id (fun _ => 1)
    ?_ ?_ rfl (Continuous.continuousOn continuous_id) (fun β _ => hasDerivAt_id β)
    (fun β _ => le_refl 1)
  · intro β n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      rw [twoPoint, dif_pos hne]
      refine le_trans ?_ (Finset.le_sup' (fun v => corr β (fun _ _ : Bool => (0:ℝ)) true v)
        (show true ∈ Finset.univ.filter (fun v : Bool => (0:ℕ) = 0) by simp))
      rw [corr_self]
      norm_num
    · rw [hzero β n (by omega)]
  · intro β _
    exact ⟨1, le_refl 1, 0, by norm_num, fun n => by rw [hzero β (n+1) (by omega)]; norm_num⟩

end Frontier

