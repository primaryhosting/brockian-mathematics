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

set_option grind.warning false

/-!
## Overview

This file formalises the *sharpness of the phase transition* for the ferromagnetic Ising
model, in the form established by Duminil-Copin (with Tassion): below the critical
inverse temperature the two-point function decays exponentially fast, while above it the
two-point function does not tend to zero.  There is no intermediate regime.

The development is organised as follows.

* `Frontier.IsingBox` : a finite volume ferromagnetic Ising model, with an explicit
  Gibbs weight, partition function, expectation and two-point function.  We prove the
  basic structural facts: the partition function is positive, expectations of bounded
  observables are bounded, the two-point function is bounded by `1` and is a
  differentiable function of the inverse temperature, the spontaneous magnetisation with
  free boundary conditions vanishes (global spin-flip symmetry) and the two-point
  function vanishes at `β = 0` (single-site spin-flip symmetry).

* `Frontier.gronwall_bound` : the analytic heart of the Duminil-Copin–Tassion argument.
  From the differential inequality
  `n * θ n s ≤ (∑ k < n, θ k s) * (θ n)' s`
  one deduces, by integrating the logarithmic derivative, the quantitative bound
  `θ n β ≤ exp ( - (β' - β) * n / ∑ k < n, θ k β')` for `β < β'`.

* `Frontier.exp_decay_of_bounded_sums` : if in addition the partial sums
  `∑ k < n, θ k β'` are bounded, the previous bound is genuine exponential decay.

* `Frontier.IsingSharpnessSetup` : the Ising two-point functions of a sequence of finite
  volumes, together with the two monotonicity/positivity inputs (Griffiths' inequalities)
  and the Duminil-Copin–Tassion differential inequality (the deep input coming from the
  random-current representation, which is taken as a hypothesis here).

* `Frontier.duminil_ising_sharp` : the sharpness dichotomy for the critical parameter
  `Frontier.IsingSharpnessSetup.betaC`.

Finally `Frontier.trivialSetup` exhibits a concrete `IsingSharpnessSetup`, so that the
hypotheses of the main theorem are consistent.
-/

namespace Frontier

/-! ## Spins and spin flips -/

/-- The real value `±1` of a Boolean spin variable. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma spin_not (b : Bool) : spin (!b) = - spin b := by cases b <;> simp [spin]

@[simp] lemma abs_spin (b : Bool) : |spin b| = 1 := by cases b <;> simp [spin]

section Flips

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Flip the spin at a single site. -/
def flipAt (x : S) (σ : S → Bool) : S → Bool := Function.update σ x (!σ x)

omit [Fintype S] in
lemma flipAt_involutive (x : S) : Function.Involutive (flipAt (S := S) x) := by
  intro σ
  funext z
  by_cases h : z = x <;> simp [flipAt, h, Function.update]

/-- Flipping the spin at a site, as a permutation of the configuration space. -/
noncomputable def flipAtEquiv (x : S) : (S → Bool) ≃ (S → Bool) :=
  (flipAt_involutive x).toPerm _

/-- Flip all spins. -/
def flipAll (σ : S → Bool) : S → Bool := fun z => !σ z

omit [Fintype S] [DecidableEq S] in
lemma flipAll_involutive : Function.Involutive (flipAll (S := S)) := by
  intro σ; funext z; simp [flipAll]

/-- The global spin flip, as a permutation of the configuration space. -/
noncomputable def flipAllEquiv : (S → Bool) ≃ (S → Bool) :=
  (flipAll_involutive (S := S)).toPerm _

/-- If a weight is invariant under flipping the spin at `x`, then the weighted sum of
`σ x * σ y` vanishes for `y ≠ x`. -/
lemma sum_flipAt_zero (x y : S) (hxy : x ≠ y) (w : (S → Bool) → ℝ)
    (hw : ∀ σ, w (flipAt x σ) = w σ) :
    ∑ σ : S → Bool, spin (σ x) * spin (σ y) * w σ = 0 := by
  set F : (S → Bool) → ℝ := fun σ => spin (σ x) * spin (σ y) * w σ with hF
  have h1 : ∑ σ : S → Bool, F σ = ∑ σ : S → Bool, F (flipAtEquiv x σ) :=
    (Equiv.sum_comp (flipAtEquiv x) F).symm
  have h2 : ∀ σ : S → Bool, F (flipAtEquiv x σ) = - F σ := by
    intro σ
    have hx : (flipAt x σ) x = !σ x := by simp [flipAt]
    have hy : (flipAt x σ) y = σ y := by simp [flipAt, Function.update, (Ne.symm hxy)]
    simp only [hF, flipAtEquiv, Function.Involutive.coe_toPerm, hx, hy, hw σ, spin_not]
    ring
  have h3 : ∑ σ : S → Bool, F (flipAtEquiv x σ) = - ∑ σ : S → Bool, F σ := by
    simp only [h2, Finset.sum_neg_distrib]
  rw [h3] at h1
  linarith

/-- If a weight is invariant under the global spin flip, then the weighted sum of `σ x`
vanishes. -/
lemma sum_flipAll_zero (x : S) (w : (S → Bool) → ℝ) (hw : ∀ σ, w (flipAll σ) = w σ) :
    ∑ σ : S → Bool, spin (σ x) * w σ = 0 := by
  set F : (S → Bool) → ℝ := fun σ => spin (σ x) * w σ with hF
  have h1 : ∑ σ : S → Bool, F σ = ∑ σ : S → Bool, F (flipAllEquiv σ) :=
    (Equiv.sum_comp (flipAllEquiv) F).symm
  have h2 : ∀ σ : S → Bool, F (flipAllEquiv σ) = - F σ := by
    intro σ
    simp only [hF, flipAllEquiv, Function.Involutive.coe_toPerm, flipAll, hw σ, spin_not]
    ring
  have h3 : ∑ σ : S → Bool, F (flipAllEquiv σ) = - ∑ σ : S → Bool, F σ := by
    simp only [h2, Finset.sum_neg_distrib]
  rw [h3] at h1
  linarith

end Flips

/-! ## Finite volume Ising models -/

/-- A finite volume ferromagnetic Ising model: a finite set of sites, a symmetric
nonnegative coupling constant `J`, and two marked sites `o ≠ t` (the origin and the
"far away" site whose correlation with the origin we study). -/
structure IsingBox where
  /-- The (finite) set of sites of the box. -/
  site : Type
  [siteFintype : Fintype site]
  [siteDecEq : DecidableEq site]
  /-- The coupling constants. -/
  J : site → site → ℝ
  /-- The couplings are symmetric. -/
  J_symm : ∀ x y, J x y = J y x
  /-- Ferromagnetic couplings. -/
  J_nonneg : ∀ x y, 0 ≤ J x y
  /-- The origin. -/
  o : site
  /-- The marked "far" site. -/
  t : site
  /-- The two marked sites are distinct. -/
  o_ne_t : o ≠ t

attribute [instance] IsingBox.siteFintype IsingBox.siteDecEq

namespace IsingBox

variable (M : IsingBox)

/-- The Ising energy of a configuration (free boundary conditions). -/
noncomputable def energy (σ : M.site → Bool) : ℝ :=
  - ∑ x, ∑ y, M.J x y * spin (σ x) * spin (σ y)

/-- The (unnormalised) Gibbs weight at inverse temperature `β`. -/
noncomputable def weight (β : ℝ) (σ : M.site → Bool) : ℝ := Real.exp (-β * M.energy σ)

/-- The partition function. -/
noncomputable def partition (β : ℝ) : ℝ := ∑ σ : M.site → Bool, M.weight β σ

/-- The Gibbs expectation of an observable. -/
noncomputable def expect (β : ℝ) (f : (M.site → Bool) → ℝ) : ℝ :=
  (∑ σ : M.site → Bool, f σ * M.weight β σ) / M.partition β

/-- The two-point function `⟨σ_x σ_y⟩_β`. -/
noncomputable def twoPoint (β : ℝ) (x y : M.site) : ℝ :=
  M.expect β (fun σ => spin (σ x) * spin (σ y))

/-- The magnetisation `⟨σ_x⟩_β`. -/
noncomputable def magnetization (β : ℝ) (x : M.site) : ℝ := M.expect β (fun σ => spin (σ x))

lemma weight_pos (β : ℝ) (σ : M.site → Bool) : 0 < M.weight β σ := Real.exp_pos _

lemma partition_pos (β : ℝ) : 0 < M.partition β :=
  Finset.sum_pos (fun σ _ => M.weight_pos β σ) Finset.univ_nonempty

/-- Expectations of observables bounded by `1` are bounded by `1`. -/
lemma abs_expect_le_one (β : ℝ) (f : (M.site → Bool) → ℝ) (hf : ∀ σ, |f σ| ≤ 1) :
    |M.expect β f| ≤ 1 := by
  rw [expect, abs_div, div_le_one (abs_pos.mpr (M.partition_pos β).ne')]
  calc |∑ σ : M.site → Bool, f σ * M.weight β σ| ≤ ∑ σ : M.site → Bool, |f σ * M.weight β σ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : M.site → Bool, M.weight β σ := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [abs_mul, abs_of_pos (M.weight_pos β σ)]
        exact mul_le_of_le_one_left (M.weight_pos β σ).le (hf σ)
    _ = |M.partition β| := by rw [abs_of_pos (M.partition_pos β)]; rfl

/-- The two-point function is bounded by `1` in absolute value. -/
lemma abs_twoPoint_le_one (β : ℝ) (x y : M.site) : |M.twoPoint β x y| ≤ 1 := by
  refine M.abs_expect_le_one β _ fun σ => ?_
  rw [abs_mul, abs_spin, abs_spin]
  norm_num

lemma twoPoint_le_one (β : ℝ) (x y : M.site) : M.twoPoint β x y ≤ 1 :=
  (abs_le.mp (M.abs_twoPoint_le_one β x y)).2

/-- The two-point function is a differentiable function of the inverse temperature. -/
lemma differentiable_twoPoint (x y : M.site) :
    Differentiable ℝ (fun β => M.twoPoint β x y) := by
  have hne : ∀ β : ℝ, (∑ σ : M.site → Bool, Real.exp (-β * M.energy σ)) ≠ 0 := by
    intro β
    have := M.partition_pos β
    simpa [partition, weight] using this.ne'
  have h1 : Differentiable ℝ (fun β : ℝ =>
      ∑ σ : M.site → Bool, (spin (σ x) * spin (σ y)) * Real.exp (-β * M.energy σ)) := by
    fun_prop
  have h2 : Differentiable ℝ (fun β : ℝ => ∑ σ : M.site → Bool, Real.exp (-β * M.energy σ)) := by
    fun_prop
  simp only [twoPoint, expect, partition, weight]
  exact h1.div h2 hne

/-! ### Spin flip symmetries -/

/-- The energy is invariant under the global spin flip. -/
lemma energy_flipAll (σ : M.site → Bool) : M.energy (flipAll σ) = M.energy σ := by
  simp only [energy, flipAll, spin_not]
  congr 1
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- **Spin-flip symmetry.** With free boundary conditions the magnetisation vanishes at
every inverse temperature. -/
theorem magnetization_eq_zero (β : ℝ) (x : M.site) : M.magnetization β x = 0 := by
  have hw : ∀ σ, M.weight β (flipAll σ) = M.weight β σ := by
    intro σ; simp [weight, M.energy_flipAll σ]
  simp [magnetization, expect, sum_flipAll_zero x (M.weight β) hw]

/-- If the Gibbs weight is invariant under flipping the spin at `x`, the two-point
function `⟨σ_x σ_y⟩` vanishes for `y ≠ x`. -/
lemma twoPoint_eq_zero_of_flipAt_invariant (β : ℝ) (x y : M.site) (hxy : x ≠ y)
    (hw : ∀ σ, M.weight β (flipAt x σ) = M.weight β σ) : M.twoPoint β x y = 0 := by
  simp [twoPoint, expect, sum_flipAt_zero x y hxy (M.weight β) hw]

/-- **Infinite temperature.** At `β = 0` the spins are independent and unbiased, so the
two-point function of two distinct sites vanishes. -/
theorem twoPoint_zero_beta (x y : M.site) (hxy : x ≠ y) : M.twoPoint 0 x y = 0 := by
  refine M.twoPoint_eq_zero_of_flipAt_invariant 0 x y hxy fun σ => ?_
  simp [weight]

/-- **No interaction.** If all couplings vanish, the two-point function of two distinct
sites vanishes at every inverse temperature. -/
theorem twoPoint_of_J_eq_zero (hJ : ∀ x y, M.J x y = 0) (β : ℝ) (x y : M.site)
    (hxy : x ≠ y) : M.twoPoint β x y = 0 := by
  refine M.twoPoint_eq_zero_of_flipAt_invariant β x y hxy fun σ => ?_
  have h : ∀ τ : M.site → Bool, M.energy τ = 0 := by
    intro τ; simp [energy, hJ]
  simp [weight, h]

end IsingBox

/-! ## The analytic core of the Duminil-Copin–Tassion argument -/

/-- **Grönwall-type bound.**  If a family `θ n` of functions of the inverse temperature
takes values in `[0,1]`, is nondecreasing on `[0,B]`, is differentiable, and satisfies
the Duminil-Copin–Tassion differential inequality
`n * θ n s ≤ (∑ k < n, θ k s) * (θ n)' s` on `(0,B)`,
then for `0 ≤ β < β' ≤ B` one has the quantitative bound
`θ n β ≤ exp (-(β' - β) * n / ∑ k < n, θ k β')`.

This is obtained by integrating the logarithmic derivative of `θ n` between `β` and `β'`. -/
theorem gronwall_bound
    (θ : ℕ → ℝ → ℝ) (B : ℝ)
    (hnonneg : ∀ n, ∀ β ∈ Set.Icc (0:ℝ) B, 0 ≤ θ n β)
    (hle : ∀ n, ∀ β ∈ Set.Icc (0:ℝ) B, θ n β ≤ 1)
    (hmono : ∀ n, MonotoneOn (θ n) (Set.Icc 0 B))
    (hdiff : ∀ n, Differentiable ℝ (θ n))
    (hdct : ∀ (n : ℕ), 1 ≤ n → ∀ s ∈ Set.Ioo 0 B,
      (n : ℝ) * θ n s ≤ (∑ k ∈ Finset.range n, θ k s) * deriv (θ n) s)
    {β β' : ℝ} (hβ : 0 ≤ β) (hlt : β < β') (hβ' : β' ≤ B) (n : ℕ) :
    θ n β ≤ Real.exp (-((β' - β) * n) / (∑ k ∈ Finset.range n, θ k β')) := by
  have hmemβ : β ∈ Set.Icc (0:ℝ) B := ⟨hβ, le_trans hlt.le hβ'⟩
  have hmemβ' : β' ∈ Set.Icc (0:ℝ) B := ⟨le_trans hβ hlt.le, hβ'⟩
  set Sg : ℝ := ∑ k ∈ Finset.range n, θ k β' with hSg
  have hSg0 : 0 ≤ Sg := Finset.sum_nonneg fun k _ => hnonneg k β' hmemβ'
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [hle 0 β hmemβ]
  rcases eq_or_lt_of_le hSg0 with h0 | hpos
  · rw [← h0]; simp [hle n β hmemβ]
  rcases eq_or_lt_of_le (hnonneg n β hmemβ) with h0 | hθpos
  · rw [← h0]; positivity
  have hncast : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hpos_on : ∀ s ∈ Set.Icc β β', 0 < θ n s := by
    intro s hs
    exact lt_of_lt_of_le hθpos (hmono n hmemβ ⟨le_trans hβ hs.1, le_trans hs.2 hβ'⟩ hs.1)
  have hcont : ContinuousOn (fun s => Real.log (θ n s)) (Set.Icc β β') :=
    ((hdiff n).continuous.continuousOn).log (fun s hs => (hpos_on s hs).ne')
  have hdon : DifferentiableOn ℝ (fun s => Real.log (θ n s)) (interior (Set.Icc β β')) := by
    rw [interior_Icc]
    intro s hs
    exact (((hdiff n) s).log (hpos_on s ⟨hs.1.le, hs.2.le⟩).ne').differentiableWithinAt
  have hderiv : ∀ s ∈ interior (Set.Icc β β'),
      (n : ℝ) / Sg ≤ deriv (fun s => Real.log (θ n s)) s := by
    rw [interior_Icc]
    intro s hs
    have hsmem : s ∈ Set.Ioo (0:ℝ) B := ⟨lt_of_le_of_lt hβ hs.1, lt_of_lt_of_le hs.2 hβ'⟩
    have hθs : 0 < θ n s := hpos_on s ⟨hs.1.le, hs.2.le⟩
    have hd := hdct n hn s hsmem
    set Ss : ℝ := ∑ k ∈ Finset.range n, θ k s with hSs
    have hSsle : Ss ≤ Sg :=
      Finset.sum_le_sum fun k _ => hmono k ⟨hsmem.1.le, hsmem.2.le⟩ hmemβ' hs.2.le
    have hSs0 : 0 ≤ Ss :=
      Finset.sum_nonneg fun k _ => hnonneg k s ⟨hsmem.1.le, hsmem.2.le⟩
    have hnum : 0 < (n:ℝ) * θ n s := by positivity
    have hd0 : 0 < deriv (θ n) s := by nlinarith
    have hderiv_eq : deriv (fun s => Real.log (θ n s)) s = deriv (θ n) s / θ n s :=
      deriv.log ((hdiff n) s) hθs.ne'
    rw [hderiv_eq, div_le_div_iff₀ hpos hθs]
    nlinarith [mul_le_mul_of_nonneg_left hSsle hd0.le]
  have key := (convex_Icc β β').mul_sub_le_image_sub_of_le_deriv hcont hdon hderiv β
    (Set.left_mem_Icc.mpr hlt.le) β' (Set.right_mem_Icc.mpr hlt.le) hlt.le
  have hlogβ' : Real.log (θ n β') ≤ 0 :=
    Real.log_nonpos (hnonneg n β' hmemβ') (hle n β' hmemβ')
  have heq : -((β' - β) * (n:ℝ)) / Sg = -(((n:ℝ) / Sg) * (β' - β)) := by field_simp
  have hlog : Real.log (θ n β) ≤ -((β' - β) * (n:ℝ)) / Sg := by
    rw [heq]; simp only at key; linarith
  calc θ n β = Real.exp (Real.log (θ n β)) := (Real.exp_log hθpos).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog

/-- **Exponential decay.**  Under the hypotheses of `Frontier.gronwall_bound`, if moreover
the partial sums `∑ k < n, θ k β'` are bounded by some constant `C > 0`, then `θ n β`
decays exponentially in `n`, with rate `(β' - β) / C`. -/
theorem exp_decay_of_bounded_sums
    (θ : ℕ → ℝ → ℝ) (B : ℝ)
    (hnonneg : ∀ n, ∀ β ∈ Set.Icc (0:ℝ) B, 0 ≤ θ n β)
    (hle : ∀ n, ∀ β ∈ Set.Icc (0:ℝ) B, θ n β ≤ 1)
    (hmono : ∀ n, MonotoneOn (θ n) (Set.Icc 0 B))
    (hdiff : ∀ n, Differentiable ℝ (θ n))
    (hdct : ∀ (n : ℕ), 1 ≤ n → ∀ s ∈ Set.Ioo 0 B,
      (n : ℝ) * θ n s ≤ (∑ k ∈ Finset.range n, θ k s) * deriv (θ n) s)
    {β β' C : ℝ} (hβ : 0 ≤ β) (hlt : β < β') (hβ' : β' ≤ B)
    (hbdd : ∀ n, (∑ k ∈ Finset.range n, θ k β') ≤ C) (n : ℕ) :
    θ n β ≤ Real.exp (-((β' - β) / C) * n) := by
  have hmemβ : β ∈ Set.Icc (0:ℝ) B := ⟨hβ, le_trans hlt.le hβ'⟩
  have hmemβ' : β' ∈ Set.Icc (0:ℝ) B := ⟨le_trans hβ hlt.le, hβ'⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simpa using hle 0 β hmemβ
  set Sg : ℝ := ∑ k ∈ Finset.range n, θ k β' with hSg
  have hSg0 : 0 ≤ Sg := Finset.sum_nonneg fun k _ => hnonneg k β' hmemβ'
  have hncast : (0:ℝ) < n := Nat.cast_pos.mpr hn
  rcases eq_or_lt_of_le hSg0 with h0 | hpos
  · -- degenerate case: all the `θ k β'`, `k < n`, vanish; then `θ n` vanishes below `β'`
    have hmid : β < (β + β') / 2 := by linarith
    have hmid2 : (β + β') / 2 < β' := by linarith
    have hsmem : (β + β') / 2 ∈ Set.Ioo (0:ℝ) B :=
      ⟨lt_of_le_of_lt hβ hmid, lt_of_lt_of_le hmid2 hβ'⟩
    have hSs0 : (∑ k ∈ Finset.range n, θ k ((β + β') / 2)) = 0 := by
      refine le_antisymm ?_
        (Finset.sum_nonneg fun k _ => hnonneg k _ ⟨hsmem.1.le, hsmem.2.le⟩)
      calc (∑ k ∈ Finset.range n, θ k ((β + β') / 2))
          ≤ Sg := Finset.sum_le_sum fun k _ =>
            hmono k ⟨hsmem.1.le, hsmem.2.le⟩ ⟨le_trans hβ hlt.le, hβ'⟩ hmid2.le
        _ = 0 := h0.symm
    have hd := hdct n hn _ hsmem
    rw [hSs0, zero_mul] at hd
    have hθmid : θ n ((β + β') / 2) ≤ 0 := by nlinarith
    have hθβ : θ n β ≤ 0 :=
      le_trans (hmono n ⟨hβ, le_trans hlt.le hβ'⟩ ⟨hsmem.1.le, hsmem.2.le⟩ hmid.le) hθmid
    exact le_trans hθβ (Real.exp_pos _).le
  · have hbase := gronwall_bound θ B hnonneg hle hmono hdiff hdct hβ hlt hβ' n
    refine le_trans hbase (Real.exp_le_exp.mpr ?_)
    rw [← hSg]
    rw [neg_div, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div]
    have h1 : Sg ≤ C := hbdd n
    have h2 : 0 ≤ (β' - β) * (n:ℝ) := mul_nonneg (by linarith) hncast.le
    gcongr

/-! ## Sharpness for the Ising model -/

/-- The two-point function between the two marked sites of the `n`-th box, as a function
of the inverse temperature. -/
noncomputable def isingTheta (box : ℕ → IsingBox) (n : ℕ) (β : ℝ) : ℝ :=
  (box n).twoPoint β (box n).o (box n).t

lemma isingTheta_le_one (box : ℕ → IsingBox) (n : ℕ) (β : ℝ) : isingTheta box n β ≤ 1 :=
  (box n).twoPoint_le_one β _ _

lemma differentiable_isingTheta (box : ℕ → IsingBox) (n : ℕ) :
    Differentiable ℝ (isingTheta box n) :=
  (box n).differentiable_twoPoint _ _

@[simp] lemma isingTheta_zero (box : ℕ → IsingBox) (n : ℕ) : isingTheta box n 0 = 0 :=
  (box n).twoPoint_zero_beta _ _ (box n).o_ne_t

/-- The data entering the Duminil-Copin–Tassion sharpness theorem for the Ising model:
a sequence of finite volumes, a range `[0,B]` of inverse temperatures, and the three
analytic inputs about the two-point functions `θ n β = ⟨σ_o σ_t⟩_{Λ_n, β}`:

* `theta_nonneg`: positivity of correlations (Griffiths' first inequality);
* `theta_mono`: monotonicity of correlations in `β` (Griffiths' second inequality);
* `theta_dct`: the Duminil-Copin–Tassion differential inequality
  `n θ_n ≤ (∑_{k<n} θ_k) θ_n'`, the deep input which in the literature is derived from
  the random-current representation.

(That the two-point functions are bounded by `1` and are differentiable in `β` is *not*
assumed: both facts are proved above, see `Frontier.IsingBox.twoPoint_le_one` and
`Frontier.IsingBox.differentiable_twoPoint`.) -/
structure IsingSharpnessSetup where
  /-- The sequence of finite volumes. -/
  box : ℕ → IsingBox
  /-- The right endpoint of the range of inverse temperatures under consideration. -/
  B : ℝ
  /-- The range of inverse temperatures is nondegenerate. -/
  B_pos : 0 < B
  /-- Griffiths' first inequality: correlations are nonnegative. -/
  theta_nonneg : ∀ n β, 0 ≤ isingTheta box n β
  /-- Griffiths' second inequality: correlations increase with `β`. -/
  theta_mono : ∀ n, MonotoneOn (isingTheta box n) (Set.Icc 0 B)
  /-- The Duminil-Copin–Tassion differential inequality. -/
  theta_dct : ∀ (n : ℕ), 1 ≤ n → ∀ s ∈ Set.Ioo 0 B,
    (n : ℝ) * isingTheta box n s ≤
      (∑ k ∈ Finset.range n, isingTheta box k s) * deriv (isingTheta box n) s

namespace IsingSharpnessSetup

variable (S : IsingSharpnessSetup)

/-- The set of inverse temperatures in `[0,B]` at which the two-point functions tend
to zero. -/
def subcriticalSet : Set ℝ :=
  {β | β ∈ Set.Icc 0 S.B ∧
    Filter.Tendsto (fun n => isingTheta S.box n β) Filter.atTop (nhds 0)}

lemma zero_mem_subcriticalSet : (0:ℝ) ∈ S.subcriticalSet := by
  refine ⟨⟨le_refl 0, S.B_pos.le⟩, ?_⟩
  simp

lemma bddAbove_subcriticalSet : BddAbove S.subcriticalSet :=
  ⟨S.B, fun _ hβ => hβ.1.2⟩

/-- The critical inverse temperature. -/
noncomputable def betaC : ℝ := sSup S.subcriticalSet

lemma betaC_nonneg : 0 ≤ S.betaC :=
  le_csSup S.bddAbove_subcriticalSet S.zero_mem_subcriticalSet

lemma betaC_le_B : S.betaC ≤ S.B :=
  csSup_le ⟨0, S.zero_mem_subcriticalSet⟩ fun _ hβ => hβ.1.2

lemma exists_mem_subcritical_gt {β : ℝ} (hβ : β < S.betaC) :
    ∃ β' ∈ S.subcriticalSet, β < β' :=
  exists_lt_of_lt_csSup ⟨0, S.zero_mem_subcriticalSet⟩ hβ

end IsingSharpnessSetup

/-- **Sharpness of the phase transition for the Ising model** (Duminil-Copin–Tassion).

Given the analytic inputs recorded in `Frontier.IsingSharpnessSetup` — nonnegativity and
monotonicity of the two-point functions `θ n β = ⟨σ_o σ_t⟩_{Λ_n, β}` (Griffiths'
inequalities) and the Duminil-Copin–Tassion differential inequality — the critical
inverse temperature `βc` splits `[0,B]` sharply:

1. `βc ∈ [0, B]`;
2. *(quantitative subcritical bound)* for `0 ≤ β < β' < βc` and every `n`,
   `θ n β ≤ exp(-(β'-β) n / ∑_{k<n} θ k β')`;
3. *(exponential decay)* if in addition the partial sums at some `β' ∈ (β, βc)` are
   bounded, then `θ n β ≤ exp(-c n)` for some `c > 0`;
4. for every `β < βc` the two-point functions tend to `0`;
5. *(no intermediate phase)* for every `β ∈ (βc, B]` the two-point functions do **not**
   tend to `0`. -/
theorem duminil_ising_sharp (S : IsingSharpnessSetup) :
    S.betaC ∈ Set.Icc 0 S.B ∧
    (∀ β ∈ Set.Ico 0 S.betaC, ∀ β' ∈ Set.Ioo β S.betaC, ∀ n : ℕ,
      isingTheta S.box n β ≤
        Real.exp (-((β' - β) * n) / ∑ k ∈ Finset.range n, isingTheta S.box k β')) ∧
    (∀ β ∈ Set.Ico 0 S.betaC, ∀ β' ∈ Set.Ioo β S.betaC, ∀ C : ℝ, 0 < C →
      (∀ n, (∑ k ∈ Finset.range n, isingTheta S.box k β') ≤ C) →
      ∃ c > 0, ∀ n : ℕ, isingTheta S.box n β ≤ Real.exp (-c * n)) ∧
    (∀ β ∈ Set.Ico 0 S.betaC,
      Filter.Tendsto (fun n => isingTheta S.box n β) Filter.atTop (nhds 0)) ∧
    (∀ β ∈ Set.Ioc S.betaC S.B,
      ¬ Filter.Tendsto (fun n => isingTheta S.box n β) Filter.atTop (nhds 0)) := by
  have hle : ∀ n, ∀ β ∈ Set.Icc (0:ℝ) S.B, isingTheta S.box n β ≤ 1 :=
    fun n β _ => isingTheta_le_one S.box n β
  have hnonneg : ∀ n, ∀ β ∈ Set.Icc (0:ℝ) S.B, 0 ≤ isingTheta S.box n β :=
    fun n β _ => S.theta_nonneg n β
  have hdiff : ∀ n, Differentiable ℝ (isingTheta S.box n) := differentiable_isingTheta S.box
  refine ⟨⟨S.betaC_nonneg, S.betaC_le_B⟩, ?_, ?_, ?_, ?_⟩
  · rintro β ⟨hβ0, -⟩ β' ⟨hββ', hβ'c⟩ n
    exact gronwall_bound (isingTheta S.box) S.B hnonneg hle S.theta_mono hdiff
      S.theta_dct hβ0 hββ' (le_trans hβ'c.le S.betaC_le_B) n
  · rintro β ⟨hβ0, -⟩ β' ⟨hββ', hβ'c⟩ C hC hbdd
    refine ⟨(β' - β) / C, div_pos (sub_pos.mpr hββ') hC, fun n => ?_⟩
    exact exp_decay_of_bounded_sums (isingTheta S.box) S.B hnonneg hle S.theta_mono
      hdiff S.theta_dct hβ0 hββ' (le_trans hβ'c.le S.betaC_le_B) hbdd n
  · rintro β ⟨hβ0, hβc⟩
    obtain ⟨β', ⟨⟨hβ'0, hβ'B⟩, hβ'lim⟩, hlt⟩ := S.exists_mem_subcritical_gt hβc
    refine squeeze_zero (fun n => S.theta_nonneg n β) (fun n => ?_) hβ'lim
    exact S.theta_mono n ⟨hβ0, le_trans hlt.le hβ'B⟩ ⟨hβ'0, hβ'B⟩ hlt.le
  · rintro β ⟨hβc, hβB⟩ hlim
    have : β ∈ S.subcriticalSet := ⟨⟨le_trans S.betaC_nonneg hβc.le, hβB⟩, hlim⟩
    exact absurd (le_csSup S.bddAbove_subcriticalSet this) (not_le.mpr hβc)

/-! ## Consistency: a concrete setup -/

/-- The Ising model on two sites with vanishing couplings. -/
def emptyBox : IsingBox where
  site := Bool
  J := fun _ _ => 0
  J_symm := fun _ _ => rfl
  J_nonneg := fun _ _ => le_refl 0
  o := false
  t := true
  o_ne_t := by decide

@[simp] lemma isingTheta_emptyBox (n : ℕ) (β : ℝ) : isingTheta (fun _ => emptyBox) n β = 0 :=
  emptyBox.twoPoint_of_J_eq_zero (fun _ _ => rfl) β _ _ emptyBox.o_ne_t

/-- The hypotheses of `Frontier.duminil_ising_sharp` are consistent: they are satisfied by
the (degenerate) model with vanishing couplings. -/
def trivialSetup : IsingSharpnessSetup where
  box := fun _ => emptyBox
  B := 1
  B_pos := one_pos
  theta_nonneg := by intro n β; simp
  theta_mono := by
    intro n
    have : isingTheta (fun _ => emptyBox) n = fun _ => (0:ℝ) := by funext β; simp
    rw [this]
    exact monotoneOn_const
  theta_dct := by
    intro n _ s _
    have h : isingTheta (fun _ => emptyBox) n = fun _ => (0:ℝ) := by funext β; simp
    simp [h]

/-! ## A non-degenerate instance of the analytic hypotheses

The family `θ n β = exp (-n (1 - β))` on `[0,1]` satisfies all the analytic hypotheses of
`Frontier.gronwall_bound` and `Frontier.exp_decay_of_bounded_sums`, and exhibits a genuine
transition at `β = 1`: the functions decay exponentially for `β < 1` and are identically
`1` at `β = 1`.  This shows that the analytic core of the argument is not vacuous. -/

/-- A model family of "two-point functions" with critical parameter `1`. -/
noncomputable def expTheta (n : ℕ) (β : ℝ) : ℝ := Real.exp (-((n:ℝ) * (1 - β)))

lemma hasDerivAt_expTheta (n : ℕ) (s : ℝ) :
    HasDerivAt (expTheta n) ((n:ℝ) * expTheta n s) s := by
  have h1 : HasDerivAt (fun s : ℝ => -((n:ℝ) * (1 - s))) (n:ℝ) s := by
    simpa using (((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).const_mul ((n:ℝ))).neg
  simpa [expTheta, mul_comm] using h1.exp

lemma deriv_expTheta (n : ℕ) (s : ℝ) : deriv (expTheta n) s = (n:ℝ) * expTheta n s :=
  (hasDerivAt_expTheta n s).deriv

lemma differentiable_expTheta (n : ℕ) : Differentiable ℝ (expTheta n) :=
  fun s => (hasDerivAt_expTheta n s).differentiableAt

lemma expTheta_nonneg (n : ℕ) (β : ℝ) : 0 ≤ expTheta n β := (Real.exp_pos _).le

lemma expTheta_le_one (n : ℕ) (β : ℝ) (hβ : β ≤ 1) : expTheta n β ≤ 1 := by
  rw [expTheta, Real.exp_le_one_iff]
  have : (0:ℝ) ≤ (n:ℝ) * (1 - β) := mul_nonneg (Nat.cast_nonneg n) (by linarith)
  linarith

lemma expTheta_mono (n : ℕ) : MonotoneOn (expTheta n) (Set.Icc (0:ℝ) 1) := by
  intro a _ b _ hab
  rw [expTheta, expTheta, Real.exp_le_exp]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma one_le_sum_expTheta (n : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    1 ≤ ∑ k ∈ Finset.range n, expTheta k s := by
  have h0 : expTheta 0 s = 1 := by simp [expTheta]
  calc (1:ℝ) = expTheta 0 s := h0.symm
    _ ≤ ∑ k ∈ Finset.range n, expTheta k s := by
        refine Finset.single_le_sum (f := fun k => expTheta k s)
          (fun k _ => expTheta_nonneg k s) ?_
        simpa using hn

/-- The model family satisfies the Duminil-Copin–Tassion differential inequality. -/
lemma expTheta_dct (n : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    (n : ℝ) * expTheta n s ≤ (∑ k ∈ Finset.range n, expTheta k s) * deriv (expTheta n) s := by
  rw [deriv_expTheta]
  have h1 := one_le_sum_expTheta n hn s
  have h2 : 0 ≤ (n : ℝ) * expTheta n s :=
    mul_nonneg (Nat.cast_nonneg n) (expTheta_nonneg n s)
  nlinarith

lemma expTheta_eq_pow (n : ℕ) (β : ℝ) : expTheta n β = (Real.exp (-(1 - β))) ^ n := by
  rw [expTheta, ← Real.exp_nat_mul]
  ring_nf

lemma sum_expTheta_le (β' : ℝ) (hβ' : β' < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, expTheta k β' ≤ (1 - Real.exp (-(1 - β')))⁻¹ := by
  set r : ℝ := Real.exp (-(1 - β')) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]; linarith
  have hsum : ∑ k ∈ Finset.range n, expTheta k β' = ∑ k ∈ Finset.range n, r ^ k :=
    Finset.sum_congr rfl fun k _ => expTheta_eq_pow k β'
  have hgeom : (∑ k ∈ Finset.range n, r ^ k) * (r - 1) = r ^ n - 1 := geom_sum_mul r n
  have hrn : 0 < r ^ n := pow_pos hr0 n
  rw [hsum, inv_eq_one_div, le_div_iff₀ (by linarith)]
  nlinarith

/-- Exponential decay for the model family, obtained by feeding the differential
inequality into `Frontier.exp_decay_of_bounded_sums`. -/
theorem expTheta_exp_decay {β β' : ℝ} (hβ : 0 ≤ β) (hlt : β < β') (hβ'1 : β' < 1) (n : ℕ) :
    expTheta n β ≤ Real.exp (-((β' - β) * (1 - Real.exp (-(1 - β')))) * n) := by
  have h := exp_decay_of_bounded_sums expTheta 1
    (fun n β _ => expTheta_nonneg n β) (fun n β hβ => expTheta_le_one n β hβ.2)
    expTheta_mono differentiable_expTheta (fun n hn s _ => expTheta_dct n hn s)
    hβ hlt hβ'1.le (sum_expTheta_le β' hβ'1) n
  rwa [div_inv_eq_mul] at h

end Frontier

