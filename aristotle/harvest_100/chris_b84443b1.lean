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

/-!
## The finite-volume Ising model

We set up the ferromagnetic Ising model on a finite graph `G` at inverse temperature `β`
with external field `h`: spins `σ : V → Bool` with values `spinVal (σ x) ∈ {-1, +1}`,
Gibbs weights `exp (-β * energy + h * ∑ spins)`, and the associated expectations,
two-point functions and magnetisation.
-/

section IsingFinite

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The spin value `±1` attached to a Boolean spin variable. -/
def spinVal (b : Bool) : ℝ := if b then 1 else -1

lemma spinVal_abs (b : Bool) : |spinVal b| = 1 := by
  cases b <;> simp [spinVal]

lemma abs_spinVal_mul_spinVal (a b : Bool) : |spinVal a * spinVal b| = 1 := by
  rw [abs_mul, spinVal_abs, spinVal_abs, one_mul]

lemma spinVal_mul_self (b : Bool) : spinVal b * spinVal b = 1 := by
  cases b <;> norm_num [spinVal]

/-- The Ising energy (Hamiltonian without external field) of a configuration on a finite
graph: `-∑_{x ~ y} σ_x σ_y`, the sum being over unordered edges (hence the factor `1/2`). -/
noncomputable def isingEnergy (G : SimpleGraph V) [DecidableRel G.Adj] (σ : V → Bool) : ℝ :=
  -(1 / 2) * ∑ x : V, ∑ y ∈ G.neighborFinset x, spinVal (σ x) * spinVal (σ y)

/-- The (unnormalised) Gibbs weight of a configuration at inverse temperature `β`
and external field `h`. -/
noncomputable def isingWeight (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ)
    (σ : V → Bool) : ℝ :=
  Real.exp (-β * isingEnergy G σ + h * ∑ x : V, spinVal (σ x))

omit [DecidableEq V] in
lemma isingWeight_pos (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (σ : V → Bool) :
    0 < isingWeight G β h σ := Real.exp_pos _

/-- The partition function. -/
noncomputable def isingPartition (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) : ℝ :=
  ∑ σ : V → Bool, isingWeight G β h σ

lemma isingPartition_pos (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) :
    0 < isingPartition G β h := by
  refine Finset.sum_pos (fun σ _ => isingWeight_pos G β h σ) ?_
  exact ⟨fun _ => true, Finset.mem_univ _⟩

/-- The Gibbs expectation of an observable. -/
noncomputable def isingExpect (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ)
    (f : (V → Bool) → ℝ) : ℝ :=
  (∑ σ : V → Bool, isingWeight G β h σ * f σ) / isingPartition G β h

/-- The two-point function `⟨σ_x σ_y⟩` at zero external field. -/
noncomputable def isingTwoPoint (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (x y : V) : ℝ :=
  isingExpect G β 0 (fun σ => spinVal (σ x) * spinVal (σ y))

/-- The magnetisation `⟨σ_x⟩` at inverse temperature `β` and external field `h`. -/
noncomputable def isingMagAt (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (x : V) : ℝ :=
  isingExpect G β h (fun σ => spinVal (σ x))

/-- Expectations of observables bounded by `M` are bounded by `M`. -/
lemma abs_isingExpect_le (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ)
    (f : (V → Bool) → ℝ) (M : ℝ) (hf : ∀ σ, |f σ| ≤ M) :
    |isingExpect G β h f| ≤ M := by
  have hZ : 0 < isingPartition G β h := isingPartition_pos G β h
  rw [isingExpect, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  calc |∑ σ : V → Bool, isingWeight G β h σ * f σ|
      ≤ ∑ σ : V → Bool, |isingWeight G β h σ * f σ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : V → Bool, isingWeight G β h σ * M := by
        refine Finset.sum_le_sum (fun σ _ => ?_)
        rw [abs_mul, abs_of_pos (isingWeight_pos G β h σ)]
        exact mul_le_mul_of_nonneg_left (hf σ) (isingWeight_pos G β h σ).le
    _ = M * isingPartition G β h := by
        rw [isingPartition, ← Finset.sum_mul, mul_comm]

/-- Two-point functions of the Ising model are bounded by `1` in absolute value. -/
lemma abs_isingTwoPoint_le_one (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (x y : V) :
    |isingTwoPoint G β x y| ≤ 1 :=
  abs_isingExpect_le G β 0 _ 1 (fun _ => (abs_spinVal_mul_spinVal _ _).le)

/-- The two-point function at coinciding points equals `1`. -/
lemma isingTwoPoint_self (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (x : V) :
    isingTwoPoint G β x x = 1 := by
  have hZ : 0 < isingPartition G β 0 := isingPartition_pos G β 0
  simp only [isingTwoPoint, isingExpect, spinVal_mul_self, mul_one]
  rw [← isingPartition, div_self hZ.ne']

end IsingFinite

/-!
## The lattice model

The Ising model on the discrete torus-free box of side `2 * N + 1` in `ℤ ^ d`, and the
infinite-volume two-point function and spontaneous magnetisation obtained as limits.
-/

section Lattice

/-- Sites of the box of side `2 * N + 1` in dimension `d`. -/
abbrev BoxSite (d N : ℕ) : Type := Fin d → Fin (2 * N + 1)

/-- Nearest-neighbour graph on the box: two sites are adjacent when their `ℓ¹`-distance
is `1`. -/
def boxGraph (d N : ℕ) : SimpleGraph (BoxSite d N) where
  Adj x y := (∑ i : Fin d, |(x i : ℤ) - (y i : ℤ)|) = 1
  symm := by
    intro x y h
    rw [← h]
    exact Finset.sum_congr rfl (fun i _ => abs_sub_comm _ _)
  loopless := by
    constructor
    intro x h
    simp at h

instance (d N : ℕ) : DecidableRel (boxGraph d N).Adj := fun _ _ => by
  unfold boxGraph; infer_instance

/-- The centre of the box. -/
def boxCentre (d N : ℕ) : BoxSite d N := fun _ => ⟨N, by omega⟩

/-- The site at distance `min n N` from the centre in the direction `i₀`. -/
def boxPoint (d N : ℕ) (i₀ : Fin d) (n : ℕ) : BoxSite d N :=
  Function.update (boxCentre d N) i₀ ⟨N + min n N, by omega⟩

/-- The finite-volume Ising two-point function between the centre of the box of side
`2 * N + 1` and the site at distance `n` in the direction `i₀`. -/
noncomputable def isingBoxCorr (d N : ℕ) (i₀ : Fin d) (β : ℝ) (n : ℕ) : ℝ :=
  isingTwoPoint (boxGraph d N) β (boxCentre d N) (boxPoint d N i₀ n)

/-- The infinite-volume two-point function, as the limit (here: `limsup`) of the
finite-volume two-point functions as the box grows. -/
noncomputable def isingCorr (d : ℕ) (i₀ : Fin d) (β : ℝ) (n : ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => isingBoxCorr d N i₀ β n) Filter.atTop

/-- The spontaneous magnetisation: the infinite-volume magnetisation at the centre of the
box, in the limit of vanishing positive external field. -/
noncomputable def isingSpontaneousMag (d : ℕ) (β : ℝ) : ℝ :=
  Filter.limsup
    (fun h : ℝ => Filter.limsup
      (fun N : ℕ => isingMagAt (boxGraph d N) β h (boxCentre d N)) Filter.atTop)
    (nhdsWithin 0 (Set.Ioi 0))

end Lattice

/-!
## The two analytic cores of the Duminil-Copin–Tassion argument

Below `corr β n` stands for the infinite-volume two-point function at distance `n`
and `mag β` for the spontaneous magnetisation.
-/

/-- **Geometric bound from the subcritical recursion.** If a nonnegative sequence bounded
by `1` satisfies the `L`-step contraction `a (n + L) ≤ c * a n`, then `a n ≤ c ^ ⌊n / L⌋`. -/
theorem le_pow_div_of_recursive_bound (a : ℕ → ℝ) (L : ℕ) (hL : 0 < L) (c : ℝ) (hc0 : 0 ≤ c)
    (ha1 : ∀ n, a n ≤ 1) (hrec : ∀ n, a (n + L) ≤ c * a n) :
    ∀ n, a n ≤ c ^ (n / L) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < L
    · rw [Nat.div_eq_of_lt h, pow_zero]
      exact ha1 n
    · push_neg at h
      have hn : n - L + L = n := Nat.sub_add_cancel h
      have h1 : a n ≤ c * a (n - L) := by
        have := hrec (n - L)
        rwa [hn] at this
      have h2 : a (n - L) ≤ c ^ ((n - L) / L) := ih _ (by omega)
      have h3 : c * a (n - L) ≤ c * c ^ ((n - L) / L) := mul_le_mul_of_nonneg_left h2 hc0
      have hdiv : n / L = (n - L) / L + 1 := Nat.div_eq_sub_div hL h
      calc a n ≤ c * c ^ ((n - L) / L) := le_trans h1 h3
        _ = c ^ ((n - L) / L + 1) := by ring
        _ = c ^ (n / L) := by rw [hdiv]

/-- **Exponential decay from the subcritical recursion.** This is the analytic core of the
subcritical half of sharpness: the Duminil-Copin–Tassion finite-criterion `φ_β(S) < 1`
produces exactly such a contraction for the two-point function, and it upgrades to genuine
exponential decay. -/
theorem exp_decay_of_recursive_bound (a : ℕ → ℝ) (L : ℕ) (hL : 0 < L) (c : ℝ) (hc1 : c < 1)
    (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1) (hrec : ∀ n, a (n + L) ≤ c * a n) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ n : ℕ, a n ≤ C * Real.exp (-α * n) := by
  set c' : ℝ := max c (1 / 2) with hc'def
  have hc'pos : 0 < c' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hc'lt : c' < 1 := max_lt hc1 (by norm_num)
  have hcc' : c ≤ c' := le_max_left _ _
  have hrec' : ∀ n, a (n + L) ≤ c' * a n := fun n =>
    le_trans (hrec n) (mul_le_mul_of_nonneg_right hcc' (ha0 n))
  have hpow : ∀ n, a n ≤ c' ^ (n / L) :=
    le_pow_div_of_recursive_bound a L hL c' hc'pos.le ha1 hrec'
  have hlog : Real.log c' < 0 := Real.log_neg hc'pos hc'lt
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  refine ⟨1 / c', -Real.log c' / L, by positivity,
    div_pos (neg_pos.mpr hlog) hLR, fun n => ?_⟩
  -- key: `c' ^ (n / L + 1) ≤ exp (-α n)`
  have hnle : (n : ℝ) / (L : ℝ) ≤ ((n / L : ℕ) : ℝ) + 1 := by
    have hn : n < (n / L + 1) * L := by
      have hmod := Nat.div_add_mod n L
      have hltm := Nat.mod_lt n hL
      calc n = L * (n / L) + n % L := hmod.symm
        _ < L * (n / L) + L := by omega
        _ = (n / L + 1) * L := by ring
    have : (n : ℝ) < ((n / L : ℕ) + 1) * (L : ℝ) := by exact_mod_cast hn
    rw [div_le_iff₀ hLR]
    linarith
  have hexp : c' ^ (n / L + 1) ≤ Real.exp (-(-Real.log c' / L) * n) := by
    have h1 : c' ^ (n / L + 1) = Real.exp (((n / L : ℕ) + 1 : ℕ) * Real.log c') := by
      rw [Real.exp_nat_mul, Real.exp_log hc'pos]
    rw [h1]
    apply Real.exp_le_exp.mpr
    have h2 : ((((n / L : ℕ) + 1 : ℕ) : ℝ)) * Real.log c' ≤ ((n : ℝ) / L) * Real.log c' := by
      have := mul_le_mul_of_nonpos_right hnle hlog.le
      push_cast
      push_cast at this
      linarith
    have h3 : ((n : ℝ) / L) * Real.log c' = -(-Real.log c' / L) * n := by
      field_simp
    linarith [h2, h3]
  calc a n ≤ c' ^ (n / L) := hpow n
    _ = (1 / c') * c' ^ (n / L + 1) := by
        field_simp [pow_succ]
        ring
    _ ≤ (1 / c') * Real.exp (-(-Real.log c' / L) * n) := by
        exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **Supercritical lower bound on the magnetisation.** This is the analytic core of the
supercritical half of sharpness: the Duminil-Copin–Tassion differential inequality
`∂_β M ≥ (1 - M) / β` for `β > β_c` integrates to the mean-field-type lower bound
`M (β) ≥ (β - β_c) / β`, in particular `M (β) > 0` strictly above `β_c`. -/
theorem magnetization_lower_bound (mag : ℝ → ℝ) (betaC : ℝ) (hbc : 0 < betaC)
    (hcont : ContinuousOn mag (Set.Ici betaC))
    (hdiff : ∀ β ∈ Set.Ioi betaC, DifferentiableAt ℝ mag β)
    (hineq : ∀ β ∈ Set.Ioi betaC, (1 - mag β) / β ≤ deriv mag β)
    (hmag0 : 0 ≤ mag betaC) :
    ∀ β, betaC < β → (β - betaC) / β ≤ mag β := by
  set g : ℝ → ℝ := fun t => t * (1 - mag t) with hgdef
  have hderiv : ∀ x ∈ Set.Ioi betaC,
      HasDerivAt g (1 * (1 - mag x) + x * (0 - deriv mag x)) x := by
    intro x hx
    exact (hasDerivAt_id x).mul ((hasDerivAt_const x (1 : ℝ)).sub ((hdiff x hx).hasDerivAt))
  have hgc : ContinuousOn g (Set.Ici betaC) :=
    continuousOn_id.mul (continuousOn_const.sub hcont)
  have hganti : AntitoneOn g (Set.Ici betaC) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici _) hgc ?_ ?_
    · intro x hx
      rw [interior_Ici] at hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := lt_trans hbc hx
      have hkey : 1 - mag x ≤ x * deriv mag x := by
        have := hineq x hx
        rwa [div_le_iff₀ hx0, mul_comm] at this
      rw [(hderiv x hx).deriv]
      nlinarith
  intro β hβ
  have hβ0 : 0 < β := lt_trans hbc hβ
  have hle : g β ≤ g betaC :=
    hganti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hβ.le) hβ.le
  have hgc' : g betaC ≤ betaC := by
    have : betaC * (1 - mag betaC) ≤ betaC * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) hbc.le
    simpa [hgdef] using this
  have hfin : β * (1 - mag β) ≤ betaC := le_trans hle hgc'
  rw [div_le_iff₀ hβ0]
  nlinarith

/-- **Sharpness of the phase transition for the Ising model (Duminil-Copin).**

`corr β n` denotes the infinite-volume two-point function `⟨σ_0 σ_x⟩_β` at distance `n`
(a nonnegative quantity bounded by `1`, by Griffiths' inequality) and `mag β` denotes the
spontaneous magnetisation `⟨σ_0⟩_β^+`, with critical inverse temperature `betaC > 0`.

The two model-dependent inputs of the Duminil-Copin–Tassion proof are assumed:

* below `betaC`, the finite criterion `φ_β(S) < 1` gives a strict `L`-step contraction
  `corr β (n + L) ≤ c * corr β n` with `c < 1`;
* above `betaC`, the differential inequality `∂_β mag ≥ (1 - mag) / β` holds, together with
  continuity of `mag` up to `betaC` and nonnegativity at `betaC`.

The conclusion is sharpness: the transition at `betaC` is sharp, i.e. correlations decay
exponentially fast strictly below `betaC`, while the spontaneous magnetisation is strictly
positive — with the explicit mean-field lower bound `(β - betaC) / β` — strictly above
`betaC`. -/
theorem duminil_ising_sharp (corr : ℝ → ℕ → ℝ) (mag : ℝ → ℝ) (betaC : ℝ) (hbc : 0 < betaC)
    (hcorr0 : ∀ β n, 0 ≤ corr β n) (hcorr1 : ∀ β n, corr β n ≤ 1)
    (hsub : ∀ β, 0 ≤ β → β < betaC → ∃ L : ℕ, 0 < L ∧ ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      ∀ n : ℕ, corr β (n + L) ≤ c * corr β n)
    (hcont : ContinuousOn mag (Set.Ici betaC))
    (hdiff : ∀ β ∈ Set.Ioi betaC, DifferentiableAt ℝ mag β)
    (hineq : ∀ β ∈ Set.Ioi betaC, (1 - mag β) / β ≤ deriv mag β)
    (hmag0 : 0 ≤ mag betaC) :
    (∀ β, 0 ≤ β → β < betaC → ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
        ∀ n : ℕ, corr β n ≤ C * Real.exp (-α * n)) ∧
      (∀ β, betaC < β → (β - betaC) / β ≤ mag β ∧ 0 < mag β) := by
  constructor
  · intro β hβ0 hβ
    obtain ⟨L, hL, c, hc0, hc1, hrec⟩ := hsub β hβ0 hβ
    exact exp_decay_of_recursive_bound (corr β) L hL c hc1 (hcorr0 β) (hcorr1 β) hrec
  · intro β hβ
    have hβ0 : 0 < β := lt_trans hbc hβ
    have h := magnetization_lower_bound mag betaC hbc hcont hdiff hineq hmag0 β hβ
    refine ⟨h, lt_of_lt_of_le ?_ h⟩
    exact div_pos (by linarith) hβ0

/-- **Sharpness of the phase transition, for the nearest-neighbour Ising model on `ℤ ^ d`.**

This is the specialisation of `Frontier.duminil_ising_sharp` to the concrete lattice model:
`isingCorr d i₀ β n` is the infinite-volume two-point function between the origin and the
site at distance `n` in the direction `i₀`, obtained as a limit of the finite-volume Ising
two-point functions in boxes, and `isingSpontaneousMag d β` is the spontaneous
magnetisation. The two model inputs of the Duminil-Copin–Tassion argument are assumed. -/
theorem duminil_ising_sharp_lattice (d : ℕ) (i₀ : Fin d) (betaC : ℝ) (hbc : 0 < betaC)
    (hcorr0 : ∀ (β : ℝ) (n : ℕ), 0 ≤ isingCorr d i₀ β n)
    (hcorr1 : ∀ (β : ℝ) (n : ℕ), isingCorr d i₀ β n ≤ 1)
    (hsub : ∀ β, 0 ≤ β → β < betaC → ∃ L : ℕ, 0 < L ∧ ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      ∀ n : ℕ, isingCorr d i₀ β (n + L) ≤ c * isingCorr d i₀ β n)
    (hcont : ContinuousOn (isingSpontaneousMag d) (Set.Ici betaC))
    (hdiff : ∀ β ∈ Set.Ioi betaC, DifferentiableAt ℝ (isingSpontaneousMag d) β)
    (hineq : ∀ β ∈ Set.Ioi betaC,
      (1 - isingSpontaneousMag d β) / β ≤ deriv (isingSpontaneousMag d) β)
    (hmag0 : 0 ≤ isingSpontaneousMag d betaC) :
    (∀ β, 0 ≤ β → β < betaC → ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
        ∀ n : ℕ, isingCorr d i₀ β n ≤ C * Real.exp (-α * n)) ∧
      (∀ β, betaC < β → (β - betaC) / β ≤ isingSpontaneousMag d β ∧
        0 < isingSpontaneousMag d β) :=
  duminil_ising_sharp (isingCorr d i₀) (isingSpontaneousMag d) betaC hbc hcorr0 hcorr1 hsub
    hcont hdiff hineq hmag0

end Frontier

