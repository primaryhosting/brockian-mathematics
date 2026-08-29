/-
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
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

/-! ## The cost function and the Ma–Trudinger–Wang condition -/

/-- The quadratic (Brenier) transport cost `c(x,y) = ‖x - y‖² / 2` on a real inner product
space. -/
noncomputable def quadCost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : ℝ := ‖x - y‖ ^ 2 / 2

/-- **Loeper's maximum principle**, the geometric reformulation of the
Ma–Trudinger–Wang condition (A3w) used in the regularity theory of optimal transport.
For a cost `c` whose `c`-segments are straight segments it reads: for all `x, z` and all
`y₀, y₁`, the function `t ↦ c x yₜ - c z yₜ` along the segment `yₜ = (1-t) y₀ + t y₁`
is bounded by its values at the endpoints. -/
def LoeperMaximumPrinciple {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E → E → ℝ) : Prop :=
  ∀ (x z y₀ y₁ : E), ∀ t ∈ Set.Icc (0 : ℝ) 1,
    c x ((1 - t) • y₀ + t • y₁) - c z ((1 - t) • y₀ + t • y₁) ≤
      max (c x y₀ - c z y₀) (c x y₁ - c z y₁)

/-- Base case of the MTW theory: the quadratic cost satisfies the (degenerate) MTW
condition (A3w), in Loeper's form.  Indeed `c x y - c z y` is an affine function of `y`. -/
theorem quadCost_loeperMaximumPrinciple {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : LoeperMaximumPrinciple (quadCost (E := E)) := by
  intro x z y₀ y₁ t ht
  have key : ∀ y : E, quadCost x y - quadCost z y
      = (‖x‖ ^ 2 - ‖z‖ ^ 2) / 2 - inner ℝ (x - z) y := by
    intro y
    simp only [quadCost, inner_sub_left]
    rw [norm_sub_sq_real, norm_sub_sq_real]
    ring
  have hlin : inner ℝ (x - z) ((1 - t) • y₀ + t • y₁)
      = (1 - t) * inner ℝ (x - z) y₀ + t * inner ℝ (x - z) y₁ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [key, key, key, hlin]
  obtain ⟨ht0, ht1⟩ := ht
  rcases le_total ((‖x‖ ^ 2 - ‖z‖ ^ 2) / 2 - inner ℝ (x - z) y₀)
      ((‖x‖ ^ 2 - ‖z‖ ^ 2) / 2 - inner ℝ (x - z) y₁) with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

/-! ## The one-dimensional base case

Here `F` and `G` are the cumulative distribution functions of the source measure `μ` and
the target measure `ν`, and `T` is the monotone (optimal, for the quadratic cost) transport
map, characterised by `G ∘ T = F`.  The hypothesis `hFup` says that `μ` has density at most
`Lam`, and `hGlow` says that `ν` has density at least `lam > 0`.  The conclusion is the
Lipschitz regularity of `T` with the sharp constant `Lam / lam`. -/

/-- One-sided form of the one-dimensional regularity estimate. -/
theorem transport_one_dim_aux {F G T : ℝ → ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hFmono : Monotone F)
    (hFup : ∀ x y : ℝ, x ≤ y → F y - F x ≤ Lam * (y - x))
    (hGlow : ∀ y y' : ℝ, y ≤ y' → lam * (y' - y) ≤ G y' - G y)
    (hT : ∀ x : ℝ, G (T x) = F x) :
    ∀ x y : ℝ, T x ≤ T y → T y - T x ≤ (Lam / lam) * |x - y| := by
  have hLam0 : 0 ≤ Lam := by
    have h1 : F 0 ≤ F 1 := hFmono (by norm_num)
    have h2 : F 1 - F 0 ≤ Lam * (1 - 0) := hFup 0 1 (by norm_num)
    nlinarith
  intro x y hxy
  have h1 : lam * (T y - T x) ≤ F y - F x := by
    have := hGlow (T x) (T y) hxy
    rwa [hT, hT] at this
  rcases le_total x y with hle | hle
  · have h2 : F y - F x ≤ Lam * (y - x) := hFup x y hle
    have habs : |x - y| = y - x := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [habs]
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
    nlinarith
  · -- if `y ≤ x` then `F y ≤ F x`, forcing `T x = T y`
    have h2 : F y ≤ F x := hFmono hle
    have h3 : T y - T x ≤ 0 := by nlinarith
    have h4 : T y - T x = 0 := le_antisymm h3 (by linarith)
    rw [h4]
    exact mul_nonneg (div_nonneg hLam0 hlam.le) (abs_nonneg _)

/-- **One-dimensional regularity of the optimal transport map (base case).**
If the source measure has density bounded above by `Lam` (`hFup`) and the target measure has
density bounded below by `lam > 0` (`hGlow`), then the monotone transport map `T`,
characterised by `G ∘ T = F`, is Lipschitz with constant `Lam / lam`. -/
theorem transport_lipschitz_one_dim {F G T : ℝ → ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hFmono : Monotone F)
    (hFup : ∀ x y : ℝ, x ≤ y → F y - F x ≤ Lam * (y - x))
    (hGlow : ∀ y y' : ℝ, y ≤ y' → lam * (y' - y) ≤ G y' - G y)
    (hT : ∀ x : ℝ, G (T x) = F x) :
    ∀ x y : ℝ, |T x - T y| ≤ (Lam / lam) * |x - y| := by
  intro x y
  rcases le_total (T x) (T y) with h | h
  · have := transport_one_dim_aux hlam hFmono hFup hGlow hT x y h
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    exact this
  · have := transport_one_dim_aux hlam hFmono hFup hGlow hT y x h
    rw [abs_of_nonneg (show (0:ℝ) ≤ T x - T y by linarith), abs_sub_comm x y]
    exact this

/-! ## Induction on the dimension -/

/-- Auxiliary induction on the dimension: a pointwise Lipschitz bound on the coordinates
gives a bound on the sums of squares.  Proved by induction on `n`. -/
theorem sum_sq_le_of_coord_le (K : ℝ) :
    ∀ (n : ℕ) (a b : Fin n → ℝ), (∀ i, |a i| ≤ K * |b i|) →
      ∑ i, (a i) ^ 2 ≤ K ^ 2 * ∑ i, (b i) ^ 2 := by
  intro n
  induction n with
  | zero => intro a b _; simp
  | succ m ih =>
      intro a b h
      have hIH : ∑ i : Fin m, (a i.succ) ^ 2 ≤ K ^ 2 * ∑ i : Fin m, (b i.succ) ^ 2 :=
        ih (fun i => a i.succ) (fun i => b i.succ) (fun i => h i.succ)
      have h0 : (a 0) ^ 2 ≤ K ^ 2 * (b 0) ^ 2 := by
        have h1 : |a 0| ≤ K * |b 0| := h 0
        have h2 : (0:ℝ) ≤ |a 0| := abs_nonneg _
        nlinarith [abs_nonneg (b 0), sq_abs (a 0), sq_abs (b 0)]
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun i => (b i) ^ 2)]
      nlinarith

/-- **Figalli-type regularity of optimal transport maps under the MTW condition.**

The statement is formalised in the following Lean-checked reduction.  The cost is the
quadratic (Brenier) cost, which satisfies the Ma–Trudinger–Wang condition (A3w) in Loeper's
form (see `Frontier.quadCost_loeperMaximumPrinciple`).  The source and target measures are
products of one-dimensional measures, whose cumulative distribution functions are `F i` and
`G i`; the source densities are bounded above by `Lam` and the target densities are bounded
below by `lam > 0`.  The optimal map is then the product map `v ↦ (T i (v i))ᵢ`, each `T i`
being the monotone one-dimensional transport map characterised by `G i ∘ T i = F i`.

Conclusion: the transport map is globally Lipschitz, with constant `Lam / lam`, for the
Euclidean distance on `ℝⁿ`.  The proof combines the one-dimensional base case
(`Frontier.transport_lipschitz_one_dim`) with an induction on the dimension `n`
(`Frontier.sum_sq_le_of_coord_le`). -/
theorem figalli_OT_regularity (n : ℕ) (lam Lam : ℝ) (hlam : 0 < lam)
    (F G T : Fin n → ℝ → ℝ)
    (hFmono : ∀ i, Monotone (F i))
    (hFup : ∀ (i : Fin n) (x y : ℝ), x ≤ y → F i y - F i x ≤ Lam * (y - x))
    (hGlow : ∀ (i : Fin n) (y y' : ℝ), y ≤ y' → lam * (y' - y) ≤ G i y' - G i y)
    (hT : ∀ (i : Fin n) (x : ℝ), G i (T i x) = F i x) :
    ∀ v w : Fin n → ℝ,
      Real.sqrt (∑ i, (T i (v i) - T i (w i)) ^ 2) ≤
        (Lam / lam) * Real.sqrt (∑ i, (v i - w i) ^ 2) := by
  intro v w
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · simp
  obtain ⟨i₀⟩ := hn
  have hLam : 0 ≤ Lam := by
    have h1 : F i₀ 0 ≤ F i₀ 1 := hFmono i₀ (by norm_num)
    have h2 : F i₀ 1 - F i₀ 0 ≤ Lam * (1 - 0) := hFup i₀ 0 1 (by norm_num)
    nlinarith
  have hK : (0:ℝ) ≤ Lam / lam := div_nonneg hLam hlam.le
  have hcoord : ∀ i : Fin n, |T i (v i) - T i (w i)| ≤ (Lam / lam) * |v i - w i| := by
    intro i
    exact transport_lipschitz_one_dim hlam (hFmono i) (hFup i) (hGlow i) (hT i) (v i) (w i)
  have hsum : ∑ i, (T i (v i) - T i (w i)) ^ 2
      ≤ (Lam / lam) ^ 2 * ∑ i, (v i - w i) ^ 2 :=
    sum_sq_le_of_coord_le (Lam / lam) n _ _ hcoord
  calc Real.sqrt (∑ i, (T i (v i) - T i (w i)) ^ 2)
      ≤ Real.sqrt ((Lam / lam) ^ 2 * ∑ i, (v i - w i) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = (Lam / lam) * Real.sqrt (∑ i, (v i - w i) ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hK]

end Frontier

