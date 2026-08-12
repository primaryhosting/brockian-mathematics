import Mathlib

/-!
# The Fermi–Dirac integral `∫_0^∞ t/(1+e^t) dt = π²/12`

This auxiliary file establishes the elementary integral underlying Mirzakhani's
integration kernel, via the Mellin transform of the Dirichlet eta function.
-/


open Real MeasureTheory Set Complex
open scoped Real

namespace Mirzakhani

/-- Coefficients of the Dirichlet eta series, with the (irrelevant) `n = 0` term set to `0`. -/
noncomputable def etaCoeff (n : ℕ) : ℂ := if n = 0 then 0 else (-1) ^ (n + 1)

/-- The Fermi–Dirac function `t ↦ 1/(1+e^t)`, viewed as a complex-valued function. -/
noncomputable def fermiDirac : ℝ → ℂ := fun t => ((1 / (1 + rexp t) : ℝ) : ℂ)

/-- `∑_{n≥1} (-1)^{n+1}/n² = π²/12`. -/
theorem hasSum_eta_two : HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 2) (π ^ 2 / 12) := by
  have hz : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (π ^ 2 / 6) := hasSum_zeta_two
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b h; dsimp only at h; omega
  have hev : HasSum (fun n : ℕ => if Even n then (2 : ℝ) / (n : ℝ) ^ 2 else 0) (π ^ 2 / 12) := by
    rw [← Function.Injective.hasSum_iff hinj]
    · have h2 : HasSum (fun k : ℕ => (1 / 2 : ℝ) * (1 / (k : ℝ) ^ 2)) ((1 / 2) * (π ^ 2 / 6)) :=
        hz.mul_left _
      have hval : (1 / 2 : ℝ) * (π ^ 2 / 6) = π ^ 2 / 12 := by ring
      rw [hval] at h2
      refine h2.congr_fun ?_
      intro k
      simp only [Function.comp_def]
      split_ifs with h
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · norm_num
        · have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
          push_cast
          field_simp
      · exact absurd (even_two_mul k) h
    · intro x hx
      simp only [Set.mem_range, not_exists] at hx
      have hodd : ¬ Even x := by
        rintro ⟨r, hr⟩; exact hx r (by omega)
      simp [hodd]
  have hsub := hz.sub hev
  have hval : π ^ 2 / 6 - π ^ 2 / 12 = π ^ 2 / 12 := by ring
  rw [hval] at hsub
  refine hsub.congr_fun ?_
  intro n
  split_ifs with h
  · rw [(h.add_one).neg_one_pow]; ring
  · rw [(Nat.not_even_iff_odd.mp h).add_one.neg_one_pow]; ring

/-- The eta series expansion of the Fermi–Dirac function. -/
theorem hasSum_fermiDirac {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => etaCoeff n * (rexp (-(n : ℝ) * t) : ℝ)) (fermiDirac t) := by
  set r : ℂ := -(rexp (-t) : ℝ) with hr
  have hrn : ‖r‖ < 1 := by
    rw [hr]
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hg : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ := hasSum_geometric_of_norm_lt_one hrn
  have hg2 := (hg.neg).add (hasSum_ite_eq (0 : ℕ) (1 : ℂ))
  have hval : -(1 - r)⁻¹ + 1 = fermiDirac t := by
    rw [hr, fermiDirac]
    have h1 : (rexp t) ≠ 0 := (Real.exp_pos t).ne'
    have h2 : (1 : ℝ) + rexp t ≠ 0 := by positivity
    have h3 : Real.exp (-t) = (rexp t)⁻¹ := by rw [Real.exp_neg]
    rw [h3]
    push_cast
    have h5 : (1 : ℂ) + Complex.exp (t : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_exp]
      exact_mod_cast Complex.ofReal_ne_zero.mpr h2
    have h4 : Complex.exp (t : ℂ) ≠ 0 := Complex.exp_ne_zero _
    field_simp
    rw [show Complex.exp (t : ℂ) - -1 = 1 + Complex.exp (t : ℂ) from by ring]
    field_simp
    ring
  rw [hval] at hg2
  refine hg2.congr_fun ?_
  intro n
  by_cases hn : n = 0
  · subst hn; simp [etaCoeff]
  · have hrp : r ^ n = (-1) ^ n * ((rexp (-(n : ℝ) * t) : ℝ) : ℂ) := by
      rw [hr, neg_pow]
      congr 1
      rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
      norm_num
    rw [hrp]
    simp only [etaCoeff, if_neg hn]
    rw [pow_succ]
    ring

theorem summable_etaCoeff : Summable (fun n : ℕ => ‖etaCoeff n‖ / (n : ℝ) ^ ((2 : ℂ).re)) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℝ)) := by
    rw [Real.summable_one_div_nat_rpow]; norm_num
  refine h.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  simp only [Complex.re_ofNat]
  gcongr
  simp only [etaCoeff]
  split_ifs with h0
  · simp
  · simp [norm_pow]

/-- **The Fermi–Dirac integral**: `∫_0^∞ t/(1+e^t) dt = π²/12`. -/
theorem integral_id_div_one_add_exp :
    (∫ t in Ioi (0 : ℝ), t / (1 + rexp t)) = π ^ 2 / 12 := by
  have hp : ∀ i : ℕ, etaCoeff i = 0 ∨ 0 < (i : ℝ) := by
    intro i
    by_cases h : i = 0
    · left; simp [etaCoeff, h]
    · right; exact_mod_cast Nat.pos_of_ne_zero h
  have hs : 0 < (2 : ℂ).re := by norm_num
  have key := hasSum_mellin hp hs (fun t ht => hasSum_fermiDirac ht) summable_etaCoeff
  have hGamma : Complex.Gamma 2 = 1 := by simp
  have hterm : ∀ n : ℕ, Complex.Gamma 2 * etaCoeff n / (n : ℂ) ^ (2 : ℂ)
      = (((-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    intro n
    rw [hGamma, one_mul]
    by_cases h : n = 0
    · subst h; simp [etaCoeff]
    · rw [Complex.cpow_two]
      simp only [etaCoeff, if_neg h]
      push_cast
      ring
  have key2 : HasSum (fun n : ℕ => (((-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 2 : ℝ) : ℂ)) (mellin fermiDirac 2) :=
    key.congr_fun (fun n => (hterm n).symm)
  have key3 : HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 2) (π ^ 2 / 12) := hasSum_eta_two
  have hmel : mellin fermiDirac 2 = ((π ^ 2 / 12 : ℝ) : ℂ) :=
    key2.unique (Complex.hasSum_ofReal.mpr key3)
  rw [mellin] at hmel
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      (t : ℂ) ^ ((2 : ℂ) - 1) • fermiDirac t = (((t / (1 + rexp t) : ℝ)) : ℂ) := by
    intro t _
    simp only [fermiDirac, smul_eq_mul]
    rw [show (2 : ℂ) - 1 = 1 by ring, Complex.cpow_one]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_complex_ofReal] at hmel
  exact_mod_cast hmel

end Mirzakhani

/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.EtaIntegral
import RequestProject.Kernel

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

We formalize Mirzakhani's recursion for the Weil–Petersson volumes
`V_{g,n}(L_1, …, L_n)` of moduli spaces of bordered hyperbolic surfaces of genus `g`
with `n` geodesic boundary components of lengths `L_1, …, L_n`.

Since `V_{g,n}` is a symmetric function of the boundary lengths, a volume function is
modelled here as a map `V : ℕ → Multiset ℝ → ℝ`, where `V g s` stands for
`V_{g, |s|}` evaluated at the boundary lengths listed by the multiset `s`.
The stability condition `2g - 2 + n > 0` is written `3 ≤ 2 * g + |s|`.

Mirzakhani's recursion is the identity

`∂/∂L₁ (L₁ · V_{g,n}(L₁, L̂)) = A^con + A^dcon + B`

with

* `A^con = ½ ∫∫ x y H(x+y, L₁) V_{g-1,n+1}(x, y, L̂) dx dy`,
* `A^dcon = ½ ∫∫ x y H(x+y, L₁) Σ_{stable} V_{g₁}(x, I) V_{g₂}(y, J) dx dy`,
* `B = ½ Σ_j ∫ x (H(x, L₁+L_j) + H(x, L₁-L_j)) V_{g,n-1}(x, L̂_j) dx`,

where `H(x,y) = 1/(1+e^{(x+y)/2}) + 1/(1+e^{(x-y)/2})` and the sum in `A^dcon` runs over
all stable splittings `g₁ + g₂ = g`, `I ⊎ J = L̂`.  We use the integrated
(equivalent) form of the identity, which avoids differentiability side conditions:
`L₁ V_{g,n}(L₁, L̂) = ∫_0^{L₁} (A^con + A^dcon + B)(t) dt`.

The main results are:

* `Frontier.WPVolumeRecursion`: the formalized recursion (a predicate on volume functions),
* `Frontier.mirzakhani_WP_volume`: the base cases `V_{0,3} = 1`, `V_{1,1}(L) = (L²+4π²)/24`
  are propagated by the recursion to the Lean-checked reduction
  `V_{0,4}(L₁,…,L₄) = 2π² + ½ Σ L_i²`, and the recursion together with the base cases
  determines all Weil–Petersson volumes uniquely,
* `Frontier.mirzakhani_recursion_consistent`: the hypotheses feeding the four-holed sphere
  reduction are satisfiable, so that reduction is not vacuous.

The analytic input is the moment integral `Mirzakhani.integral_id_mul_H`,
`∫_0^∞ x H(x,y) dx = y²/2 + 2π²/3`, proved from `∫_0^∞ t/(1+e^t) dt = π²/12`, which in turn is
obtained as the Mellin transform of the Dirichlet eta function at `s = 2` (see the files
`RequestProject/Kernel.lean` and `RequestProject/EtaIntegral.lean`).

Full existence of a solution of the recursion in all stable ranges is Mirzakhani's theorem and
is not formalized here; all statements about volume functions are therefore conditional on
`WPVolumeRecursion`.
-/

open Real MeasureTheory Set Multiset
open scoped Real
open scoped BigOperators
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

namespace Frontier

/-- The `A^con` term of Mirzakhani's recursion: the contribution of the surfaces obtained by
removing a pair of pants that meets the distinguished boundary in one boundary circle and whose
two other boundary circles are glued to a *connected* surface of genus `g-1`. -/
noncomputable def AconTerm (V : ℕ → Multiset ℝ → ℝ) (g : ℕ) (rest : Multiset ℝ) (t : ℝ) : ℝ :=
  if 1 ≤ g then
    (1 / 2) * ∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ),
      x * y * Mirzakhani.H (x + y) t * V (g - 1) (x ::ₘ y ::ₘ rest)
  else 0

/-- The sum over stable splittings occurring in the `A^dcon` term. -/
noncomputable def splitSum (V : ℕ → Multiset ℝ → ℝ) (g : ℕ) (rest : Multiset ℝ) (x y : ℝ) : ℝ :=
  ∑ g₁ ∈ Finset.range (g + 1),
    (rest.powerset.map fun I =>
      if 3 ≤ 2 * g₁ + (Multiset.card I + 1) ∧
          3 ≤ 2 * (g - g₁) + (Multiset.card (rest - I) + 1) then
        V g₁ (x ::ₘ I) * V (g - g₁) (y ::ₘ (rest - I))
      else 0).sum

/-- The `A^dcon` term of Mirzakhani's recursion: the contribution of the surfaces obtained by
removing a pair of pants that meets the distinguished boundary in one boundary circle and whose
two other boundary circles are glued to a *disconnected* surface. -/
noncomputable def AdconTerm (V : ℕ → Multiset ℝ → ℝ) (g : ℕ) (rest : Multiset ℝ) (t : ℝ) : ℝ :=
  (1 / 2) * ∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ),
    x * y * Mirzakhani.H (x + y) t * splitSum V g rest x y

/-- The `B` term of Mirzakhani's recursion: the contribution of the pairs of pants having the
distinguished boundary and one further boundary component of the surface as boundary circles. -/
noncomputable def BTerm (V : ℕ → Multiset ℝ → ℝ) (g : ℕ) (rest : Multiset ℝ) (t : ℝ) : ℝ :=
  (1 / 2) * (rest.map fun Lj => ∫ x in Ioi (0:ℝ),
      x * (Mirzakhani.H x (t + Lj) + Mirzakhani.H x (t - Lj)) * V g (x ::ₘ rest.erase Lj)).sum

/-- **Mirzakhani's recursion for Weil–Petersson volumes.**

`V g s` models the Weil–Petersson volume `V_{g,n}(s)` of the moduli space of genus `g`
hyperbolic surfaces with `n = |s|` geodesic boundary components of lengths given by `s`.
The predicate collects the two base cases (a pair of pants and a one-holed torus) together with
Mirzakhani's integral recursion, in its integrated form, for all stable `(g, n)` beyond the base
cases; the continuity requirement records that volumes depend continuously (indeed
polynomially) on the boundary lengths. -/
structure WPVolumeRecursion (V : ℕ → Multiset ℝ → ℝ) : Prop where
  /-- Volumes depend continuously on each boundary length. -/
  continuous_boundary : ∀ (g : ℕ) (s : Multiset ℝ), Continuous fun L => V g (L ::ₘ s)
  /-- Base case: the moduli space of pairs of pants is a point, `V_{0,3} = 1`. -/
  pair_of_pants : ∀ a b c : ℝ, V 0 {a, b, c} = 1
  /-- Base case: `V_{1,1}(L) = (L² + 4π²)/24`. -/
  one_holed_torus : ∀ a : ℝ, V 1 {a} = (a ^ 2 + 4 * π ^ 2) / 24
  /-- Mirzakhani's recursion, in integrated form, in the stable range beyond the base cases. -/
  recursion : ∀ (g : ℕ) (rest : Multiset ℝ) (L : ℝ), 4 ≤ 2 * g + (Multiset.card rest + 1) →
      L * V g (L ::ₘ rest) =
        ∫ t in (0:ℝ)..L, (AconTerm V g rest t + AdconTerm V g rest t + BTerm V g rest t)

/-- Any volume function obeying the recursion assigns the value `1` to every three-holed
sphere. -/
theorem WPVolumeRecursion.volume_card_three {V : ℕ → Multiset ℝ → ℝ} (h : WPVolumeRecursion V)
    {s : Multiset ℝ} (hs : Multiset.card s = 3) : V 0 s = 1 := by
  obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp hs
  exact h.pair_of_pants a b c

/-- In genus `0` with three remaining boundary components there is no stable splitting, so the
`A^dcon` integrand vanishes identically. -/
theorem splitSum_genus_zero_card_three (V : ℕ → Multiset ℝ → ℝ) (rest : Multiset ℝ)
    (hcard : Multiset.card rest = 3) (x y : ℝ) : splitSum V 0 rest x y = 0 := by
  refine Finset.sum_eq_zero ?_
  intro g₁ hg₁
  have hg : g₁ = 0 := by simpa using Finset.mem_range.mp hg₁
  subst hg
  refine Multiset.sum_eq_zero ?_
  intro z hz
  obtain ⟨I, hI, rfl⟩ := Multiset.mem_map.mp hz
  rw [Multiset.mem_powerset] at hI
  have hc : Multiset.card (rest - I) = 3 - Multiset.card I := by
    rw [Multiset.card_sub hI, hcard]
  have hIle : Multiset.card I ≤ 3 := by
    rw [← hcard]; exact Multiset.card_le_card hI
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rw [hc] at h2
  omega

/-- Evaluation of the `B` term of the recursion in the case `g = 0`, `n = 4`, where all the
volumes occurring are pair-of-pants volumes. -/
theorem BTerm_genus_zero_card_three {V : ℕ → Multiset ℝ → ℝ}
    (hV3 : ∀ s : Multiset ℝ, Multiset.card s = 3 → V 0 s = 1)
    (rest : Multiset ℝ) (hcard : Multiset.card rest = 3) (t : ℝ) :
    BTerm V 0 rest t = (1 / 2) * (rest.map fun Lj => t ^ 2 + Lj ^ 2 + 4 * π ^ 2 / 3).sum := by
  unfold BTerm
  congr 2
  refine Multiset.map_congr rfl ?_
  intro Lj hLj
  have hV : ∀ x : ℝ, V 0 (x ::ₘ rest.erase Lj) = 1 := by
    intro x
    refine hV3 _ ?_
    simp [Multiset.card_cons, Multiset.card_erase_of_mem hLj, hcard]
  calc (∫ x in Ioi (0:ℝ), x * (Mirzakhani.H x (t + Lj) + Mirzakhani.H x (t - Lj))
        * V 0 (x ::ₘ rest.erase Lj))
      = ∫ x in Ioi (0:ℝ), x * (Mirzakhani.H x (t + Lj) + Mirzakhani.H x (t - Lj)) :=
        setIntegral_congr_fun measurableSet_Ioi (fun x _ => by rw [hV x]; ring)
    _ = (t + Lj) ^ 2 / 2 + (t - Lj) ^ 2 / 2 + 4 * π ^ 2 / 3 :=
        Mirzakhani.integral_id_mul_H_pair _ _
    _ = t ^ 2 + Lj ^ 2 + 4 * π ^ 2 / 3 := by ring

/-- The four-holed sphere volume, computed from the recursion: `V_{0,4} = 2π² + ½ Σ Lᵢ²`. -/
theorem WPVolumeRecursion.volume_four_holed_sphere {V : ℕ → Multiset ℝ → ℝ}
    (h : WPVolumeRecursion V) (L₁ L₂ L₃ L₄ : ℝ) :
    V 0 {L₁, L₂, L₃, L₄} = 2 * π ^ 2 + (L₁ ^ 2 + L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2 := by
  set rest : Multiset ℝ := {L₂, L₃, L₄} with hrest
  set c : ℝ := (L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2 + 2 * π ^ 2 with hc
  have hcard : Multiset.card rest = 3 := by simp [hrest]
  have hB : ∀ t : ℝ, BTerm V 0 rest t = 3 * t ^ 2 / 2 + c := by
    intro t
    rw [BTerm_genus_zero_card_three (fun s hs => h.volume_card_three hs) rest hcard, hrest, hc]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton]
    ring
  have hA : ∀ t : ℝ, AconTerm V 0 rest t = 0 := fun t => by simp [AconTerm]
  have hAd : ∀ t : ℝ, AdconTerm V 0 rest t = 0 := by
    intro t
    unfold AdconTerm
    have hz : ∀ x y : ℝ, x * y * Mirzakhani.H (x + y) t * splitSum V 0 rest x y = 0 := by
      intro x y
      rw [splitSum_genus_zero_card_three V rest hcard]
      ring
    simp [hz]
  have hrec : ∀ L : ℝ, L * V 0 (L ::ₘ rest) = L * (L ^ 2 / 2 + c) := by
    intro L
    rw [h.recursion 0 rest L (by simp [hcard])]
    have hint : ∀ t ∈ Set.uIcc (0:ℝ) L,
        AconTerm V 0 rest t + AdconTerm V 0 rest t + BTerm V 0 rest t = 3 / 2 * t ^ 2 + c := by
      intro t _
      rw [hA t, hAd t, hB t]; ring
    rw [intervalIntegral.integral_congr hint,
      intervalIntegral.integral_add
        ((intervalIntegral.intervalIntegrable_pow 2).const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, integral_pow]
    simp
    ring
  have hne : ∀ L : ℝ, L ≠ 0 → V 0 (L ::ₘ rest) = L ^ 2 / 2 + c :=
    fun L hL => mul_left_cancel₀ hL (hrec L)
  have hcont : Continuous fun L : ℝ => V 0 (L ::ₘ rest) := h.continuous_boundary 0 rest
  have hpoly : Continuous fun L : ℝ => L ^ 2 / 2 + c := by fun_prop
  have heq := Continuous.ext_on (dense_compl_singleton (0:ℝ)) hcont hpoly
    (fun x hx => hne x (Set.mem_compl_singleton_iff.mp hx))
  have hval : V 0 (L₁ ::ₘ rest) = L₁ ^ 2 / 2 + c := congrFun heq L₁
  have hgoal : V 0 {L₁, L₂, L₃, L₄} = V 0 (L₁ ::ₘ rest) := by rw [hrest]; rfl
  rw [hgoal, hval, hc]
  ring

/-- Agreement of two volume functions below a given complexity `M = 2g + n`. -/
def AgreeBelow (V W : ℕ → Multiset ℝ → ℝ) (M : ℕ) : Prop :=
  ∀ (g' : ℕ) (s' : Multiset ℝ), 2 * g' + Multiset.card s' < M → 3 ≤ 2 * g' + Multiset.card s' →
    s' ≠ 0 → V g' s' = W g' s'

theorem AconTerm_congr {V W : ℕ → Multiset ℝ → ℝ} {g : ℕ} {rest : Multiset ℝ}
    (hag : AgreeBelow V W (2 * g + Multiset.card rest + 1))
    (hM : 4 ≤ 2 * g + Multiset.card rest + 1) (t : ℝ) :
    AconTerm V g rest t = AconTerm W g rest t := by
  unfold AconTerm
  split_ifs with hg
  · congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    rw [hag (g - 1) (x ::ₘ y ::ₘ rest) (by simp [Multiset.card_cons]; omega)
      (by simp [Multiset.card_cons]; omega) (by simp)]
  · rfl

theorem BTerm_congr {V W : ℕ → Multiset ℝ → ℝ} {g : ℕ} {rest : Multiset ℝ}
    (hag : AgreeBelow V W (2 * g + Multiset.card rest + 1))
    (hM : 4 ≤ 2 * g + Multiset.card rest + 1) (t : ℝ) :
    BTerm V g rest t = BTerm W g rest t := by
  unfold BTerm
  congr 2
  refine Multiset.map_congr rfl (fun Lj hLj => ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  have hc : Multiset.card (rest.erase Lj) = Multiset.card rest - 1 :=
    Multiset.card_erase_of_mem hLj
  have hpos : 0 < Multiset.card rest := Multiset.card_pos.mpr (fun hz => by simp [hz] at hLj)
  rw [hag g (x ::ₘ rest.erase Lj) (by simp [Multiset.card_cons, hc]; omega)
    (by simp [Multiset.card_cons, hc]; omega) (by simp)]

theorem splitSum_congr {V W : ℕ → Multiset ℝ → ℝ} {g : ℕ} {rest : Multiset ℝ}
    (hag : AgreeBelow V W (2 * g + Multiset.card rest + 1)) (x y : ℝ) :
    splitSum V g rest x y = splitSum W g rest x y := by
  unfold splitSum
  refine Finset.sum_congr rfl (fun g₁ hg₁ => ?_)
  have hg1 : g₁ ≤ g := by have := Finset.mem_range.mp hg₁; omega
  refine congrArg Multiset.sum (Multiset.map_congr rfl (fun I hI => ?_))
  rw [Multiset.mem_powerset] at hI
  have hcI : Multiset.card (rest - I) = Multiset.card rest - Multiset.card I :=
    Multiset.card_sub hI
  have hIle : Multiset.card I ≤ Multiset.card rest := Multiset.card_le_card hI
  split_ifs with hcond
  · obtain ⟨h1, h2⟩ := hcond
    rw [hcI] at h2
    rw [hag g₁ (x ::ₘ I) (by simp [Multiset.card_cons]; omega)
        (by simp [Multiset.card_cons]; omega) (by simp),
      hag (g - g₁) (y ::ₘ (rest - I)) (by simp [Multiset.card_cons, hcI]; omega)
        (by simp [Multiset.card_cons, hcI]; omega) (by simp)]
  · rfl

theorem AdconTerm_congr {V W : ℕ → Multiset ℝ → ℝ} {g : ℕ} {rest : Multiset ℝ}
    (hag : AgreeBelow V W (2 * g + Multiset.card rest + 1)) (t : ℝ) :
    AdconTerm V g rest t = AdconTerm W g rest t := by
  unfold AdconTerm
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  rw [splitSum_congr hag x y]

/-- The recursion, together with the two base cases, determines the Weil–Petersson volumes
uniquely in the whole stable range (for surfaces with at least one boundary component). -/
theorem WPVolumeRecursion.unique {V W : ℕ → Multiset ℝ → ℝ} (hV : WPVolumeRecursion V)
    (hW : WPVolumeRecursion W) (g : ℕ) (s : Multiset ℝ) (hs : 3 ≤ 2 * g + Multiset.card s)
    (hne : s ≠ 0) : V g s = W g s := by
  suffices H : ∀ m : ℕ, ∀ (g : ℕ) (s : Multiset ℝ), 2 * g + Multiset.card s = m → 3 ≤ m →
      s ≠ 0 → V g s = W g s from H _ g s rfl hs hne
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro g s hm h3 hne
    rcases eq_or_lt_of_le h3 with h3eq | h3lt
    · have hcases : (g = 0 ∧ Multiset.card s = 3) ∨ (g = 1 ∧ Multiset.card s = 1) := by omega
      rcases hcases with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
      · rw [hV.volume_card_three hc, hW.volume_card_three hc]
      · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hc
        rw [hV.one_holed_torus, hW.one_holed_torus]
    · obtain ⟨L0, hL0⟩ := Multiset.exists_mem_of_ne_zero hne
      obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem hL0
      have hcard : 2 * g + Multiset.card rest + 1 = m := by
        rw [Multiset.card_cons] at hm; omega
      have hM : 4 ≤ 2 * g + Multiset.card rest + 1 := by omega
      have hag : AgreeBelow V W (2 * g + Multiset.card rest + 1) := by
        intro g' s' hlt h3' hne'
        exact ih (2 * g' + Multiset.card s') (by omega) g' s' rfl h3' hne'
      have hall : ∀ L : ℝ, L ≠ 0 → V g (L ::ₘ rest) = W g (L ::ₘ rest) := by
        intro L hL
        have e1 := hV.recursion g rest L (by omega)
        have e2 := hW.recursion g rest L (by omega)
        have hint : ∀ t ∈ Set.uIcc (0:ℝ) L,
            AconTerm V g rest t + AdconTerm V g rest t + BTerm V g rest t
              = AconTerm W g rest t + AdconTerm W g rest t + BTerm W g rest t := by
          intro t _
          rw [AconTerm_congr hag hM t, BTerm_congr hag hM t, AdconTerm_congr hag t]
        rw [intervalIntegral.integral_congr hint] at e1
        exact mul_left_cancel₀ hL (e1.trans e2.symm)
      have heq := Continuous.ext_on (dense_compl_singleton (0:ℝ))
        (hV.continuous_boundary g rest) (hW.continuous_boundary g rest)
        (fun x hx => hall x (Set.mem_compl_singleton_iff.mp hx))
      exact congrFun heq L0

/-! ### A consistency check

The results above are conditional on a volume function satisfying `WPVolumeRecursion`.
Producing such a function in all stable ranges is precisely Mirzakhani's theorem, which we do
not formalize.  The following construction nevertheless shows that the hypotheses used in the
four-holed sphere reduction are consistent: there is a function satisfying the continuity
requirement, both base cases, and every instance of Mirzakhani's recursion with `g = 0` and
`n = 4`; and this function has the four-holed sphere volume predicted above. -/

/-- The sum of the squares of the entries of a multiset of boundary lengths. -/
noncomputable def sqSum (s : Multiset ℝ) : ℝ := (s.map fun L => L ^ 2).sum

lemma sqSum_cons (L : ℝ) (s : Multiset ℝ) : sqSum (L ::ₘ s) = L ^ 2 + sqSum s := by
  simp [sqSum]

lemma sum_map_const_add_sq (c : ℝ) (s : Multiset ℝ) :
    (s.map fun L => c + L ^ 2).sum = (Multiset.card s : ℝ) * c + sqSum s := by
  induction s using Multiset.induction_on with
  | empty => simp [sqSum]
  | cons a s ih => simp [sqSum, ih] at *; ring

/-- A function carrying the known small Weil–Petersson volumes: the pair of pants, the
one-holed torus and the four-holed sphere. -/
noncomputable def modelV (g : ℕ) (s : Multiset ℝ) : ℝ :=
  if g = 0 ∧ Multiset.card s = 3 then 1
  else if g = 0 ∧ Multiset.card s = 4 then 2 * π ^ 2 + sqSum s / 2
  else if g = 1 ∧ Multiset.card s = 1 then (sqSum s + 4 * π ^ 2) / 24
  else 0

lemma modelV_card_three {s : Multiset ℝ} (hs : Multiset.card s = 3) : modelV 0 s = 1 := by
  simp [modelV, hs]

lemma continuous_modelV (g : ℕ) (s : Multiset ℝ) : Continuous fun L => modelV g (L ::ₘ s) := by
  by_cases h1 : g = 0 ∧ Multiset.card s + 1 = 3
  · have he : (fun L : ℝ => modelV g (L ::ₘ s)) = fun _ => 1 := by
      funext L; simp [modelV, Multiset.card_cons, h1.1, h1.2]
    rw [he]; exact continuous_const
  · by_cases h2 : g = 0 ∧ Multiset.card s + 1 = 4
    · have he : (fun L : ℝ => modelV g (L ::ₘ s))
          = fun L => 2 * π ^ 2 + (L ^ 2 + sqSum s) / 2 := by
        funext L
        simp only [modelV, Multiset.card_cons, sqSum_cons]
        rw [if_neg (by simpa [Multiset.card_cons] using h1), if_pos ⟨h2.1, h2.2⟩]
      rw [he]; fun_prop
    · by_cases h3 : g = 1 ∧ Multiset.card s + 1 = 1
      · have he : (fun L : ℝ => modelV g (L ::ₘ s))
            = fun L => ((L ^ 2 + sqSum s) + 4 * π ^ 2) / 24 := by
          funext L
          simp only [modelV, Multiset.card_cons, sqSum_cons]
          rw [if_neg (by simpa using h1), if_neg (by simpa using h2), if_pos ⟨h3.1, h3.2⟩]
        rw [he]; fun_prop
      · have he : (fun L : ℝ => modelV g (L ::ₘ s)) = fun _ => 0 := by
          funext L
          simp only [modelV, Multiset.card_cons, sqSum_cons]
          rw [if_neg (by simpa using h1), if_neg (by simpa using h2), if_neg (by simpa using h3)]
        rw [he]; exact continuous_const

/-- The hypotheses used in the four-holed sphere reduction are consistent: `modelV` satisfies the
continuity requirement, the two base cases, and every `g = 0`, `n = 4` instance of Mirzakhani's
recursion, and its four-holed sphere volume is `2π² + ½ Σ Lᵢ²`. -/
theorem mirzakhani_recursion_consistent :
    (∀ (g : ℕ) (s : Multiset ℝ), Continuous fun L => modelV g (L ::ₘ s)) ∧
    (∀ a b c : ℝ, modelV 0 {a, b, c} = 1) ∧
    (∀ a : ℝ, modelV 1 {a} = (a ^ 2 + 4 * π ^ 2) / 24) ∧
    (∀ (rest : Multiset ℝ) (L : ℝ), Multiset.card rest = 3 →
      L * modelV 0 (L ::ₘ rest) =
        ∫ t in (0:ℝ)..L, (AconTerm modelV 0 rest t + AdconTerm modelV 0 rest t
          + BTerm modelV 0 rest t)) ∧
    (∀ L₁ L₂ L₃ L₄ : ℝ,
      modelV 0 {L₁, L₂, L₃, L₄} = 2 * π ^ 2 + (L₁ ^ 2 + L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2) := by
  refine ⟨continuous_modelV, fun a b c => by simp [modelV],
    fun a => by simp [modelV, sqSum], ?_, ?_⟩
  · intro rest L hcard
    set c : ℝ := sqSum rest / 2 + 2 * π ^ 2 with hc
    have hB : ∀ t : ℝ, BTerm modelV 0 rest t = 3 / 2 * t ^ 2 + c := by
      intro t
      rw [BTerm_genus_zero_card_three (fun s hs => modelV_card_three hs) rest hcard]
      have hmap : (rest.map fun Lj => t ^ 2 + Lj ^ 2 + 4 * π ^ 2 / 3)
          = rest.map fun Lj => (t ^ 2 + 4 * π ^ 2 / 3) + Lj ^ 2 :=
        Multiset.map_congr rfl (fun Lj _ => by ring)
      rw [hmap, sum_map_const_add_sq, hcard, hc]
      push_cast
      ring
    have hA : ∀ t : ℝ, AconTerm modelV 0 rest t = 0 := fun t => by simp [AconTerm]
    have hAd : ∀ t : ℝ, AdconTerm modelV 0 rest t = 0 := by
      intro t
      unfold AdconTerm
      have hz : ∀ x y : ℝ, x * y * Mirzakhani.H (x + y) t * splitSum modelV 0 rest x y = 0 := by
        intro x y
        rw [splitSum_genus_zero_card_three modelV rest hcard]; ring
      simp [hz]
    have hint : ∀ t ∈ Set.uIcc (0:ℝ) L,
        AconTerm modelV 0 rest t + AdconTerm modelV 0 rest t + BTerm modelV 0 rest t
          = 3 / 2 * t ^ 2 + c := by
      intro t _; rw [hA t, hAd t, hB t]; ring
    rw [intervalIntegral.integral_congr hint,
      intervalIntegral.integral_add
        ((intervalIntegral.intervalIntegrable_pow 2).const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, integral_pow]
    have hlhs : modelV 0 (L ::ₘ rest) = 2 * π ^ 2 + (L ^ 2 + sqSum rest) / 2 := by
      simp only [modelV, Multiset.card_cons, hcard, sqSum_cons]
      norm_num
    rw [hlhs, hc]
    simp
    ring
  · intro L₁ L₂ L₃ L₄
    simp only [modelV, Multiset.insert_eq_cons, sqSum]
    norm_num
    ring

/-- **Mirzakhani's recursion for Weil–Petersson volumes of moduli of bordered surfaces.**

For every volume function `V` satisfying Mirzakhani's recursion `WPVolumeRecursion`:

* the pair of pants has volume `1` and the one-holed torus has volume `(L² + 4π²)/24`
  (the base cases);
* the recursion reduces the four-holed sphere to the base cases, yielding
  `V_{0,4}(L₁,…,L₄) = 2π² + ½ (L₁² + L₂² + L₃² + L₄²)`;
* the recursion together with the base cases pins down every Weil–Petersson volume of a
  stable bordered surface: two solutions of the recursion agree. -/
theorem mirzakhani_WP_volume :
    (∀ V : ℕ → Multiset ℝ → ℝ, WPVolumeRecursion V →
        (∀ a b c : ℝ, V 0 {a, b, c} = 1) ∧
        (∀ a : ℝ, V 1 {a} = (a ^ 2 + 4 * π ^ 2) / 24) ∧
        (∀ L₁ L₂ L₃ L₄ : ℝ,
          V 0 {L₁, L₂, L₃, L₄} = 2 * π ^ 2 + (L₁ ^ 2 + L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2)) ∧
    (∀ V W : ℕ → Multiset ℝ → ℝ, WPVolumeRecursion V → WPVolumeRecursion W →
        ∀ (g : ℕ) (s : Multiset ℝ), 3 ≤ 2 * g + Multiset.card s → s ≠ 0 → V g s = W g s) :=
  ⟨fun _ hV => ⟨hV.pair_of_pants, hV.one_holed_torus, hV.volume_four_holed_sphere⟩,
    fun _ _ hV hW => hV.unique hW⟩

end Frontier

import Mathlib
import RequestProject.EtaIntegral

/-!
# Mirzakhani's integration kernel

This file introduces Mirzakhani's kernel

`H x y = 1/(1 + exp ((x+y)/2)) + 1/(1 + exp ((x-y)/2))`

and computes the basic moment integral

`∫_0^∞ x * H x y dx = y^2/2 + 2π²/3`,

which is the analytic input to Mirzakhani's recursion in the first nontrivial cases.
-/

open Real MeasureTheory Set
open scoped Real

namespace Mirzakhani

/-- The Fermi–Dirac type function `w u = 1/(1 + e^{u/2})`. -/
noncomputable def w (u : ℝ) : ℝ := 1 / (1 + rexp (u / 2))

/-- Mirzakhani's kernel `H x y = w (x+y) + w (x-y)`. -/
noncomputable def H (x y : ℝ) : ℝ := w (x + y) + w (x - y)

lemma H_symm (x y : ℝ) : H x (-y) = H x y := by
  simp only [H, sub_neg_eq_add, ← sub_eq_add_neg]
  ring

lemma w_pos (u : ℝ) : 0 < w u := by
  have : 0 < 1 + rexp (u / 2) := by positivity
  simpa [w] using div_pos one_pos this

lemma w_add_w_neg (u : ℝ) : w u + w (-u) = 1 := by
  have h1 : (0:ℝ) < 1 + rexp (u / 2) := by positivity
  have h2 : (0:ℝ) < 1 + rexp (-u / 2) := by positivity
  have hne : rexp (-u/2) = (rexp (u/2))⁻¹ := by
    rw [show (-u/2) = -(u/2) by ring, Real.exp_neg]
  have hx : (0:ℝ) < rexp (u/2) := Real.exp_pos _
  simp only [w]
  rw [hne]
  field_simp
  ring

lemma continuous_w : Continuous w := by
  unfold w
  fun_prop (disch := intro x; positivity)

lemma w_le_exp (u : ℝ) : w u ≤ rexp (-(u / 2)) := by
  have hx : (0:ℝ) < rexp (u / 2) := Real.exp_pos _
  have h1 : (0:ℝ) < 1 + rexp (u / 2) := by positivity
  rw [Real.exp_neg]
  rw [w, div_le_iff₀ h1]
  rw [inv_mul_eq_div, le_div_iff₀ hx]
  nlinarith

lemma w_neg (u : ℝ) : w (-u) = 1 - w u := by
  have := w_add_w_neg u; linarith

/-- Translation invariance of the integral over a half-line. -/
theorem integral_Ioi_comp_add_right (f : ℝ → ℝ) (a c : ℝ) :
    (∫ x in Ioi a, f (x + c)) = ∫ u in Ioi (a + c), f u := by
  have h := MeasureTheory.MeasurePreserving.setIntegral_preimage_emb
    (MeasureTheory.measurePreserving_add_right (volume : Measure ℝ) c)
    ((Homeomorph.addRight c).measurableEmbedding) f (Ioi (a + c))
  simpa [Set.preimage_add_const_Ioi] using h

/-- Any affine multiple of a translate of `w` is integrable on a half-line. -/
theorem integrableOn_affine_mul_w_shift (a c d s : ℝ) :
    IntegrableOn (fun u => (c * u + d) * w (u + s)) (Ioi a) := by
  refine integrable_of_isBigO_exp_neg (b := 1/4) (by norm_num) ?_ ?_
  · exact Continuous.continuousOn
      (((continuous_const.mul continuous_id).add continuous_const).mul
        (continuous_w.comp (continuous_id.add continuous_const)))
  · rw [Asymptotics.isBigO_iff]
    refine ⟨rexp (-(s/2)) * (4 * |c| + |d|), ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with u hu
    have hw : w (u + s) ≤ rexp (-(s/2)) * rexp (-(u/2)) := by
      have := w_le_exp (u + s)
      rw [← Real.exp_add] at *
      calc w (u + s) ≤ rexp (-((u + s)/2)) := w_le_exp (u + s)
        _ = rexp (-(s/2) + -(u/2)) := by ring_nf
    have hwpos := (w_pos (u + s)).le
    have h1 : |(c * u + d) * w (u + s)| ≤ (|c| * u + |d|) * (rexp (-(s/2)) * rexp (-(u/2))) := by
      rw [abs_mul, abs_of_nonneg hwpos]
      have hle : |c * u + d| ≤ |c| * u + |d| := by
        calc |c * u + d| ≤ |c * u| + |d| := abs_add_le _ _
          _ = |c| * u + |d| := by rw [abs_mul, abs_of_nonneg hu]
      have h2 : (0:ℝ) ≤ |c| * u + |d| := by positivity
      exact mul_le_mul hle hw hwpos h2
    have h3 : (|c| * u + |d|) * rexp (-(u/2)) ≤ (4 * |c| + |d|) * rexp (-(1/4) * u) := by
      have hexp : 1 + u/4 ≤ rexp (u/4) := by
        have := Real.add_one_le_exp (u/4); linarith
      have hkey : |c| * u + |d| ≤ (4 * |c| + |d|) * rexp (u/4) := by
        nlinarith [abs_nonneg c, abs_nonneg d]
      have hpos : (0:ℝ) < rexp (-(u/2)) := Real.exp_pos _
      calc (|c| * u + |d|) * rexp (-(u/2)) ≤ ((4 * |c| + |d|) * rexp (u/4)) * rexp (-(u/2)) :=
            mul_le_mul_of_nonneg_right hkey hpos.le
        _ = (4 * |c| + |d|) * rexp (-(1/4) * u) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf
    have hnorm : ‖rexp (-(1/4) * u)‖ = rexp (-(1/4) * u) :=
      Real.norm_of_nonneg (Real.exp_pos _).le
    rw [hnorm, Real.norm_eq_abs]
    have hspos : (0:ℝ) < rexp (-(s/2)) := Real.exp_pos _
    calc |(c * u + d) * w (u + s)| ≤ (|c| * u + |d|) * (rexp (-(s/2)) * rexp (-(u/2))) := h1
      _ = rexp (-(s/2)) * ((|c| * u + |d|) * rexp (-(u/2))) := by ring
      _ ≤ rexp (-(s/2)) * ((4 * |c| + |d|) * rexp (-(1/4) * u)) := by
          exact mul_le_mul_of_nonneg_left h3 hspos.le
      _ = rexp (-(s/2)) * (4 * |c| + |d|) * rexp (-(1/4) * u) := by ring

/-- Any affine multiple of `w` is integrable on a half-line. -/
theorem integrableOn_affine_mul_w (a c d : ℝ) :
    IntegrableOn (fun u => (c * u + d) * w u) (Ioi a) := by
  simpa using integrableOn_affine_mul_w_shift a c d 0

/-- `∫_0^∞ u * w u du = π²/3`. -/
theorem integral_id_mul_w : (∫ u in Ioi (0:ℝ), u * w u) = π ^ 2 / 3 := by
  have h := integral_comp_mul_left_Ioi (fun u : ℝ => u * w u) 0 (by norm_num : (0:ℝ) < 2)
  simp only [mul_zero, smul_eq_mul] at h
  have h2 : (∫ x in Ioi (0:ℝ), (2 * x) * w (2 * x)) = 2 * (π ^ 2 / 12) := by
    have hpt : ∀ x : ℝ, (2 * x) * w (2 * x) = 2 * (x / (1 + rexp x)) := by
      intro x
      simp only [w]
      rw [show (2 * x) / 2 = x by ring]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpt x), integral_const_mul,
      integral_id_div_one_add_exp]
  rw [h2] at h
  linarith [h]

theorem integrableOn_id_mul_H (y : ℝ) :
    IntegrableOn (fun x => x * H x y) (Ioi (0:ℝ)) := by
  have h1 := integrableOn_affine_mul_w_shift (0:ℝ) 1 0 y
  have h2 := integrableOn_affine_mul_w_shift (0:ℝ) 1 0 (-y)
  have h3 : IntegrableOn
      (fun u => (1 * u + 0) * w (u + y) + (1 * u + 0) * w (u + -y)) (Ioi (0:ℝ)) :=
    Integrable.add h1 h2
  refine h3.congr_fun ?_ measurableSet_Ioi
  intro x _
  simp only [H, sub_eq_add_neg]
  ring

lemma intervalIntegrable_w (a b : ℝ) : IntervalIntegrable w volume a b :=
  continuous_w.intervalIntegrable a b

lemma intervalIntegrable_id_mul_w (a b : ℝ) :
    IntervalIntegrable (fun u => u * w u) volume a b :=
  (continuous_id.mul continuous_w).intervalIntegrable a b

lemma integral_symm_w (y : ℝ) : (∫ u in (-y)..y, w u) = y := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals (a := -y) (b := 0) (c := y)
    (intervalIntegrable_w _ _) (intervalIntegrable_w _ _)
  have hneg : (∫ u in (-y)..(0:ℝ), w u) = ∫ x in (0:ℝ)..y, w (-x) := by
    rw [intervalIntegral.integral_comp_neg (fun x => w x)]
    norm_num
  have hval : (∫ x in (0:ℝ)..y, w (-x)) = y - ∫ x in (0:ℝ)..y, w x := by
    have h1 : (∫ x in (0:ℝ)..y, w (-x)) = ∫ x in (0:ℝ)..y, (1 - w x) :=
      intervalIntegral.integral_congr (fun x _ => w_neg x)
    rw [h1, intervalIntegral.integral_sub (_root_.intervalIntegrable_const)
      (intervalIntegrable_w _ _)]
    simp
  rw [hneg, hval] at hadd
  linarith

lemma integral_symm_id_mul_w (y : ℝ) :
    (∫ u in (-y)..y, u * w u) = 2 * (∫ u in (0:ℝ)..y, u * w u) - y ^ 2 / 2 := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals (a := -y) (b := 0) (c := y)
    (intervalIntegrable_id_mul_w _ _) (intervalIntegrable_id_mul_w _ _)
  have hneg : (∫ u in (-y)..(0:ℝ), u * w u) = ∫ x in (0:ℝ)..y, (-x) * w (-x) := by
    rw [intervalIntegral.integral_comp_neg (fun x => x * w x)]
    norm_num
  have hval : (∫ x in (0:ℝ)..y, (-x) * w (-x)) = (∫ x in (0:ℝ)..y, x * w x) - y ^ 2 / 2 := by
    have h1 : (∫ x in (0:ℝ)..y, (-x) * w (-x)) = ∫ x in (0:ℝ)..y, (x * w x - x) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      rw [w_neg]
      ring
    rw [h1, intervalIntegral.integral_sub (intervalIntegrable_id_mul_w _ _)
      (intervalIntegral.intervalIntegrable_id), integral_id]
    ring_nf
  rw [hneg, hval] at hadd
  linarith

lemma integral_Ioi_split {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : IntegrableOn f (Ioi a)) :
    (∫ u in Ioi a, f u) = (∫ u in Ioc a b, f u) + (∫ u in Ioi b, f u) := by
  rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hf.mono_set (fun x hx => hx.1)) (hf.mono_set (fun x hx => lt_of_le_of_lt hab hx)),
    Set.Ioc_union_Ioi_eq_Ioi hab]

lemma integral_id_mul_H_of_nonneg {y : ℝ} (hy : 0 ≤ y) :
    (∫ x in Ioi (0:ℝ), x * H x y) = y ^ 2 / 2 + 2 * π ^ 2 / 3 := by
  have hA : IntegrableOn (fun x : ℝ => x * w (x + y)) (Ioi 0) := by
    refine (integrableOn_affine_mul_w_shift (0:ℝ) 1 0 y).congr_fun ?_ measurableSet_Ioi
    intro x _; ring
  have hB : IntegrableOn (fun x : ℝ => x * w (x + -y)) (Ioi 0) := by
    refine (integrableOn_affine_mul_w_shift (0:ℝ) 1 0 (-y)).congr_fun ?_ measurableSet_Ioi
    intro x _; ring
  have hsplit : (∫ x in Ioi (0:ℝ), x * H x y)
      = (∫ x in Ioi (0:ℝ), x * w (x + y)) + (∫ x in Ioi (0:ℝ), x * w (x + -y)) := by
    rw [← integral_add hA hB]
    exact setIntegral_congr_fun measurableSet_Ioi
      (fun x _ => by simp only [H, sub_eq_add_neg]; ring)
  have hA2 : (∫ x in Ioi (0:ℝ), x * w (x + y)) = ∫ u in Ioi y, (u - y) * w u := by
    have h := integral_Ioi_comp_add_right (fun u => (u - y) * w u) 0 y
    simpa using h
  have hB2 : (∫ x in Ioi (0:ℝ), x * w (x + -y)) = ∫ u in Ioi (-y), (u + y) * w u := by
    have h := integral_Ioi_comp_add_right (fun u => (u + y) * w u) 0 (-y)
    simpa using h
  have hIy : IntegrableOn (fun u => (u + y) * w u) (Ioi (-y)) := by
    refine (integrableOn_affine_mul_w (-y) 1 y).congr_fun ?_ measurableSet_Ioi
    intro u _; ring
  have hsp1 : (∫ u in Ioi (-y), (u + y) * w u)
      = (∫ u in Ioc (-y) y, (u + y) * w u) + (∫ u in Ioi y, (u + y) * w u) :=
    integral_Ioi_split (by linarith) hIy
  have hI0 : IntegrableOn (fun u => u * w u) (Ioi (0:ℝ)) := by
    refine (integrableOn_affine_mul_w (0:ℝ) 1 0).congr_fun ?_ measurableSet_Ioi
    intro u _; ring
  have hsp2 : (∫ u in Ioi (0:ℝ), u * w u)
      = (∫ u in Ioc (0:ℝ) y, u * w u) + (∫ u in Ioi y, u * w u) := integral_Ioi_split hy hI0
  have hIy1 : IntegrableOn (fun u => (u - y) * w u) (Ioi y) := by
    refine (integrableOn_affine_mul_w y 1 (-y)).congr_fun ?_ measurableSet_Ioi
    intro u _; ring
  have hIy2 : IntegrableOn (fun u => (u + y) * w u) (Ioi y) := by
    refine (integrableOn_affine_mul_w y 1 y).congr_fun ?_ measurableSet_Ioi
    intro u _; ring
  have hcomb : (∫ u in Ioi y, (u - y) * w u) + (∫ u in Ioi y, (u + y) * w u)
      = 2 * ∫ u in Ioi y, u * w u := by
    rw [← integral_add hIy1 hIy2, ← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u _ => by ring)
  have hQ : (∫ u in Ioc (0:ℝ) y, u * w u) = ∫ u in (0:ℝ)..y, u * w u :=
    (intervalIntegral.integral_of_le hy).symm
  have hRc : (∫ u in Ioc (-y) y, (u + y) * w u) = ∫ u in (-y)..y, (u + y) * w u :=
    (intervalIntegral.integral_of_le (by linarith)).symm
  have hR : (∫ u in (-y)..y, (u + y) * w u) = 2 * (∫ u in (0:ℝ)..y, u * w u) + y ^ 2 / 2 := by
    have e1 : (∫ u in (-y)..y, (u + y) * w u)
        = (∫ u in (-y)..y, u * w u) + y * (∫ u in (-y)..y, w u) := by
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add (intervalIntegrable_id_mul_w _ _)
          ((intervalIntegrable_w _ _).const_mul y)]
      exact intervalIntegral.integral_congr (fun u _ => by ring)
    rw [e1, integral_symm_w, integral_symm_id_mul_w]; ring
  have hbase := integral_id_mul_w
  rw [hQ] at hsp2
  rw [hsplit, hA2, hB2, hsp1, hRc, hR]
  linarith

/-- **The basic Mirzakhani moment integral**: `∫_0^∞ x H(x,y) dx = y²/2 + 2π²/3`. -/
theorem integral_id_mul_H (y : ℝ) :
    (∫ x in Ioi (0:ℝ), x * H x y) = y ^ 2 / 2 + 2 * π ^ 2 / 3 := by
  rcases le_total 0 y with hy | hy
  · exact integral_id_mul_H_of_nonneg hy
  · have h := integral_id_mul_H_of_nonneg (y := -y) (by linarith)
    have hEq : (∫ x in Ioi (0:ℝ), x * H x (-y)) = ∫ x in Ioi (0:ℝ), x * H x y :=
      setIntegral_congr_fun measurableSet_Ioi (fun x _ => by rw [H_symm])
    rw [hEq] at h
    rw [h]; ring

/-- The two-kernel moment integral appearing in the `B` term of Mirzakhani's recursion. -/
theorem integral_id_mul_H_pair (p q : ℝ) :
    (∫ x in Ioi (0:ℝ), x * (H x p + H x q)) = p ^ 2 / 2 + q ^ 2 / 2 + 4 * π ^ 2 / 3 := by
  have h1 := integrableOn_id_mul_H p
  have h2 := integrableOn_id_mul_H q
  have hsum : (∫ x in Ioi (0:ℝ), x * (H x p + H x q))
      = (∫ x in Ioi (0:ℝ), x * H x p) + ∫ x in Ioi (0:ℝ), x * H x q := by
    rw [← integral_add h1 h2]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)
  rw [hsum, integral_id_mul_H, integral_id_mul_H]
  ring

end Mirzakhani

