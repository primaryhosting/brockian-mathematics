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

set_option grind.warning false

namespace Frontier

/-! ## Partial derivatives of a cost function in coordinates -/

section MTW

variable {n : ℕ}

/-- Partial derivative of a cost `c x y` in the `i`-th coordinate of the source variable `x`. -/
noncomputable def pdx (c : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (i : Fin n) :
    (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
  fun x y => deriv (fun t : ℝ => c (Function.update x i t) y) (x i)

/-- Partial derivative of a cost `c x y` in the `j`-th coordinate of the target variable `y`. -/
noncomputable def pdy (c : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (j : Fin n) :
    (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
  fun x y => deriv (fun t : ℝ => c x (Function.update y j t)) (y j)

/-- The mixed second derivative `c_{i,j} = ∂_{x_i} ∂_{y_j} c`. -/
noncomputable def costMixed (c : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (i j : Fin n) :
    (Fin n → ℝ) → (Fin n → ℝ) → ℝ := pdy (pdx c i) j

/-- The third derivative `c_{ij,r} = ∂_{x_i} ∂_{x_j} ∂_{y_r} c`. -/
noncomputable def costXXY (c : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (i j r : Fin n) :
    (Fin n → ℝ) → (Fin n → ℝ) → ℝ := pdy (pdx (pdx c i) j) r

/-- The third derivative `c_{s,kl} = ∂_{x_s} ∂_{y_k} ∂_{y_l} c`. -/
noncomputable def costXYY (c : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (s k l : Fin n) :
    (Fin n → ℝ) → (Fin n → ℝ) → ℝ := pdy (pdy (pdx c s) k) l

/-- The fourth derivative `c_{ij,kl} = ∂_{x_i} ∂_{x_j} ∂_{y_k} ∂_{y_l} c`. -/
noncomputable def costXXYY (c : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (i j k l : Fin n) :
    (Fin n → ℝ) → (Fin n → ℝ) → ℝ := pdy (pdy (pdx (pdx c i) j) k) l

/-- The Ma–Trudinger–Wang tensor of a cost `c`, computed with respect to a matrix field `A`
(which is meant to be the inverse of the mixed Hessian `c_{i,j}`):
`S_c(x,y)(ξ,η) = -(3/2) ∑ (c_{ij,r} A^{rs} c_{s,kl} - c_{ij,kl}) ξ^i ξ^j η^k η^l`. -/
noncomputable def MTWtensor (c : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (x y ξ η : Fin n → ℝ) : ℝ :=
  -(3 / 2) * ∑ i, ∑ j, ∑ k, ∑ l,
    ((∑ r, ∑ s, costXXY c i j r x y * A x y r s * costXYY c s k l x y)
      - costXXYY c i j k l x y) * ξ i * ξ j * η k * η l

/-- The Ma–Trudinger–Wang condition `MTW(0)`: for every inverse `A` of the mixed Hessian of `c`,
the MTW tensor is nonnegative on orthogonal pairs of vectors. -/
def SatisfiesMTW (c : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ A : (Fin n → ℝ) → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ,
    (∀ x y, (Matrix.of fun i j => costMixed c i j x y) * A x y = 1) →
      ∀ x y ξ η : Fin n → ℝ, (∑ i, ξ i * η i = 0) → 0 ≤ MTWtensor c A x y ξ η

/-- The quadratic cost `c(x,y) = |x - y|² / 2` in coordinates. -/
noncomputable def quadCost (n : ℕ) : (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
  fun x y => (∑ k, (x k - y k) ^ 2) / 2

lemma pdy_of_indep (f : (Fin n → ℝ) → ℝ) (j : Fin n) :
    pdy (fun x _ => f x) j = fun _ _ => (0 : ℝ) := by
  funext x y
  simp [pdy]

lemma pdx_quadCost (i : Fin n) : pdx (quadCost n) i = fun x y => x i - y i := by
  funext x y
  have h : ∀ k : Fin n, HasDerivAt (fun t : ℝ => (Function.update x i t k - y k) ^ 2)
      (if k = i then 2 * (x i - y i) else 0) (x i) := by
    intro k
    by_cases hk : k = i
    · subst hk
      have : HasDerivAt (fun t : ℝ => (t - y k) ^ 2) (2 * (x k - y k)) (x k) := by
        have h1 : HasDerivAt (fun t : ℝ => t - y k) 1 (x k) :=
          (hasDerivAt_id (x k)).sub_const _
        have := h1.pow 2
        simpa [mul_comm] using this
      simpa [Function.update_self] using this
    · have : (fun t : ℝ => (Function.update x i t k - y k) ^ 2)
          = fun _ : ℝ => (x k - y k) ^ 2 := by
        funext t; rw [Function.update_of_ne hk]
      rw [this, if_neg hk]
      exact hasDerivAt_const _ _
  have hsum : HasDerivAt (fun t : ℝ => ∑ k, (Function.update x i t k - y k) ^ 2)
      (∑ k, if k = i then 2 * (x i - y i) else 0) (x i) := HasDerivAt.fun_sum fun k _ => h k
  have hfin : HasDerivAt (fun t : ℝ => (∑ k, (Function.update x i t k - y k) ^ 2) / 2)
      (x i - y i) (x i) := by
    have := hsum.div_const 2
    simpa [Finset.sum_ite_eq' Finset.univ i (fun _ => 2 * (x i - y i))] using this
  show deriv (fun t : ℝ => quadCost n (Function.update x i t) y) (x i) = x i - y i
  exact hfin.deriv

lemma pdx_pdx_quadCost (i j : Fin n) :
    pdx (pdx (quadCost n) i) j = fun _ _ => (if i = j then (1 : ℝ) else 0) := by
  funext x y
  rw [pdx_quadCost]
  show deriv (fun t : ℝ => Function.update x j t i - y i) (x j) = _
  by_cases hij : i = j
  · subst hij
    have : HasDerivAt (fun t : ℝ => Function.update x i t i - y i) 1 (x i) := by
      have h1 : HasDerivAt (fun t : ℝ => t - y i) 1 (x i) := (hasDerivAt_id (x i)).sub_const _
      have heq : (fun t : ℝ => Function.update x i t i - y i) = fun t : ℝ => t - y i := by
        funext t; rw [Function.update_self]
      rwa [heq]
    rw [this.deriv, if_pos rfl]
  · have heq : (fun t : ℝ => Function.update x j t i - y i) = fun _ : ℝ => x i - y i := by
      funext t; rw [Function.update_of_ne hij]
    rw [heq, if_neg hij, deriv_const]

lemma pdy_pdx_quadCost (i k : Fin n) :
    pdy (pdx (quadCost n) i) k = fun _ _ => -(if i = k then (1 : ℝ) else 0) := by
  funext x y
  rw [pdx_quadCost]
  show deriv (fun t : ℝ => x i - Function.update y k t i) (y k) = _
  by_cases hik : i = k
  · subst hik
    have heq : (fun t : ℝ => x i - Function.update y i t i) = fun t : ℝ => x i - t := by
      funext t; rw [Function.update_self]
    rw [heq, if_pos rfl]
    have : HasDerivAt (fun t : ℝ => x i - t) (-1) (y i) := by
      simpa using (hasDerivAt_id (y i)).const_sub (x i)
    simp [this.deriv]
  · have heq : (fun t : ℝ => x i - Function.update y k t i) = fun _ : ℝ => x i - y i := by
      funext t; rw [Function.update_of_ne hik]
    rw [heq, if_neg hik, deriv_const]
    ring

lemma costXXY_quadCost (i j r : Fin n) : costXXY (quadCost n) i j r = fun _ _ => (0 : ℝ) := by
  rw [costXXY, pdx_pdx_quadCost]
  exact pdy_of_indep (fun _ => (if i = j then (1 : ℝ) else 0)) r

lemma costXYY_quadCost (s k l : Fin n) : costXYY (quadCost n) s k l = fun _ _ => (0 : ℝ) := by
  rw [costXYY, pdy_pdx_quadCost]
  exact pdy_of_indep (fun _ => -(if s = k then (1 : ℝ) else 0)) l

lemma costXXYY_quadCost (i j k l : Fin n) :
    costXXYY (quadCost n) i j k l = fun _ _ => (0 : ℝ) := by
  have h : pdy (pdx (pdx (quadCost n) i) j) k = fun _ _ => (0 : ℝ) := costXXY_quadCost i j k
  rw [costXXYY, h]
  exact pdy_of_indep (fun _ => (0 : ℝ)) l

/-- The mixed Hessian of the quadratic cost is `-1`; in particular the cost is nondegenerate. -/
lemma costMixed_quadCost (x y : Fin n → ℝ) :
    (Matrix.of fun i j => costMixed (quadCost n) i j x y) = -1 := by
  ext i j
  show pdy (pdx (quadCost n) i) j x y = _
  rw [pdy_pdx_quadCost]
  by_cases hij : i = j <;> simp [hij]

/-- The MTW tensor of the quadratic cost vanishes identically: the quadratic cost is the
model case `MTW(0)`. -/
theorem MTWtensor_quadCost (A : (Fin n → ℝ) → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (x y ξ η : Fin n → ℝ) : MTWtensor (quadCost n) A x y ξ η = 0 := by
  simp [MTWtensor, costXXY_quadCost, costXYY_quadCost, costXXYY_quadCost]

/-- The quadratic cost satisfies the Ma–Trudinger–Wang condition `MTW(0)`. -/
theorem quadCost_satisfiesMTW : SatisfiesMTW (quadCost n) := by
  intro A _ x y ξ η _
  rw [MTWtensor_quadCost]

/-- The MTW condition for the quadratic cost is not vacuous: the mixed Hessian `-1` really
has an inverse. -/
theorem quadCost_mixedHessian_invertible (x y : Fin n → ℝ) :
    (Matrix.of fun i j => costMixed (quadCost n) i j x y) * (-1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  rw [costMixed_quadCost]
  simp

end MTW

/-! ## Base case regularity: Brenier potentials for the quadratic cost -/

section Brenier

open InnerProductSpace

variable {n : ℕ} {ι : Type*}

/-- The quadratic transport cost `c(x,y) = |x - y|²/2` on Euclidean space. -/
noncomputable def sqCost (x y : EuclideanSpace ℝ (Fin n)) : ℝ := ‖x - y‖ ^ 2 / 2

/-- The `c`-convex Kantorovich potential associated with a family of target points `g i`
weighted by `b i`, for the quadratic cost:
`u(x) = ⨆ i, (-c(x, g i) - b i)`. -/
noncomputable def kPot (g : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := ⨆ i, (-sqCost x (g i) - b i)

/-- The associated Brenier (convex) potential
`φ(x) = ⨆ i, (⟪g i, x⟫ - |g i|²/2 - b i) = u(x) + |x|²/2`. -/
noncomputable def brenierPot (g : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨆ i, (inner ℝ (g i) x - (‖g i‖ ^ 2 / 2 + b i))

/-- The optimal transport map associated with the potential, `T = ∇φ`. -/
noncomputable def brenierMap (g : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := gradient (brenierPot g b) x

variable {g : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ} {R m : ℝ}

lemma bddAbove_brenier_family [Nonempty ι] (hR : ∀ i, ‖g i‖ ≤ R) (hb : ∀ i, m ≤ b i)
    (x : EuclideanSpace ℝ (Fin n)) :
    BddAbove (Set.range fun i => inner ℝ (g i) x - (‖g i‖ ^ 2 / 2 + b i)) := by
  refine ⟨R * ‖x‖ - m, ?_⟩
  rintro _ ⟨i, rfl⟩
  have h1 : (inner ℝ (g i) x : ℝ) ≤ ‖g i‖ * ‖x‖ := real_inner_le_norm _ _
  have h2 : ‖g i‖ * ‖x‖ ≤ R * ‖x‖ :=
    mul_le_mul_of_nonneg_right (hR i) (norm_nonneg x)
  have h3 : (0 : ℝ) ≤ ‖g i‖ ^ 2 / 2 := by positivity
  have h4 : m ≤ b i := hb i
  linarith

lemma zero_le_R [Nonempty ι] (hR : ∀ i, ‖g i‖ ≤ R) : 0 ≤ R :=
  le_trans (norm_nonneg (g (Classical.arbitrary ι))) (hR _)

/-- The Kantorovich potential for the quadratic cost differs from the convex Brenier
potential exactly by `|x|²/2`; in particular the Brenier potential is convex. -/
theorem kPot_add_sq_eq_brenierPot [Nonempty ι] (hR : ∀ i, ‖g i‖ ≤ R) (hb : ∀ i, m ≤ b i)
    (x : EuclideanSpace ℝ (Fin n)) :
    kPot g b x + ‖x‖ ^ 2 / 2 = brenierPot g b x := by
  have hbdd : BddAbove (Set.range fun i => -sqCost x (g i) - b i) := by
    obtain ⟨C, hC⟩ := bddAbove_brenier_family hR hb x
    refine ⟨C - ‖x‖ ^ 2 / 2, ?_⟩
    rintro _ ⟨i, rfl⟩
    have hc : -sqCost x (g i) - b i + ‖x‖ ^ 2 / 2
        = inner ℝ (g i) x - (‖g i‖ ^ 2 / 2 + b i) := by
      have := norm_sub_pow_two_real x (g i)
      simp only [sqCost]
      rw [this, real_inner_comm]
      ring
    linarith [hC (Set.mem_range_self (f := fun i => inner ℝ (g i) x - (‖g i‖ ^ 2 / 2 + b i)) i)]
  rw [kPot, ciSup_add hbdd]
  refine congrArg _ (funext fun i => ?_)
  have := norm_sub_pow_two_real x (g i)
  simp only [sqCost]
  rw [this, real_inner_comm]
  ring

/-- The Brenier potential is a convex function (a supremum of affine functions). -/
theorem brenierPot_convexOn [Nonempty ι] (hR : ∀ i, ‖g i‖ ≤ R) (hb : ∀ i, m ≤ b i) :
    ConvexOn ℝ Set.univ (brenierPot g b) := by
  refine ⟨convex_univ, ?_⟩
  rintro x - y - a c ha hc hac
  refine ciSup_le fun i => ?_
  have hx : inner ℝ (g i) x - (‖g i‖ ^ 2 / 2 + b i) ≤ brenierPot g b x :=
    le_ciSup (bddAbove_brenier_family hR hb x) i
  have hy : inner ℝ (g i) y - (‖g i‖ ^ 2 / 2 + b i) ≤ brenierPot g b y :=
    le_ciSup (bddAbove_brenier_family hR hb y) i
  have hlin : (inner ℝ (g i) (a • x + c • y) : ℝ)
      = a * inner ℝ (g i) x + c * inner ℝ (g i) y := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have h1 : a * (inner ℝ (g i) x - (‖g i‖ ^ 2 / 2 + b i)) ≤ a * brenierPot g b x :=
    mul_le_mul_of_nonneg_left hx ha
  have h2 : c * (inner ℝ (g i) y - (‖g i‖ ^ 2 / 2 + b i)) ≤ c * brenierPot g b y :=
    mul_le_mul_of_nonneg_left hy hc
  have hkey : inner ℝ (g i) (a • x + c • y) - (‖g i‖ ^ 2 / 2 + b i)
      = a * (inner ℝ (g i) x - (‖g i‖ ^ 2 / 2 + b i))
        + c * (inner ℝ (g i) y - (‖g i‖ ^ 2 / 2 + b i)) := by
    rw [hlin]
    have : a * (‖g i‖ ^ 2 / 2 + b i) + c * (‖g i‖ ^ 2 / 2 + b i) = ‖g i‖ ^ 2 / 2 + b i := by
      rw [← add_mul, hac, one_mul]
    linarith
  rw [hkey]
  simp only [smul_eq_mul]
  linarith

lemma brenierPot_le_add [Nonempty ι] (hR : ∀ i, ‖g i‖ ≤ R) (hb : ∀ i, m ≤ b i)
    (x y : EuclideanSpace ℝ (Fin n)) :
    brenierPot g b x ≤ brenierPot g b y + R * ‖x - y‖ := by
  refine ciSup_le fun i => ?_
  have hy : inner ℝ (g i) y - (‖g i‖ ^ 2 / 2 + b i) ≤ brenierPot g b y :=
    le_ciSup (bddAbove_brenier_family hR hb y) i
  have hsplit : (inner ℝ (g i) x : ℝ) = inner ℝ (g i) y + inner ℝ (g i) (x - y) := by
    rw [inner_sub_right]; ring
  have hle : (inner ℝ (g i) (x - y) : ℝ) ≤ R * ‖x - y‖ :=
    le_trans (real_inner_le_norm _ _) (mul_le_mul_of_nonneg_right (hR i) (norm_nonneg _))
  rw [hsplit]
  linarith

/-- The Brenier potential is globally `R`-Lipschitz when the targets have norm at most `R`. -/
theorem brenierPot_lipschitz [Nonempty ι] (hR : ∀ i, ‖g i‖ ≤ R) (hb : ∀ i, m ≤ b i) :
    LipschitzWith R.toNNReal (brenierPot g b) := by
  have hR0 : 0 ≤ R := zero_le_R hR
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h1 := brenierPot_le_add hR hb x y
  have h2 := brenierPot_le_add hR hb y x
  rw [norm_sub_rev] at h2
  have hd : dist (brenierPot g b x) (brenierPot g b y) ≤ R * ‖x - y‖ := by
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor <;> linarith
  have : (R.toNNReal : ℝ) = R := Real.coe_toNNReal R hR0
  rw [this, dist_eq_norm]
  exact hd

/-- Rademacher: the Brenier potential is differentiable almost everywhere, so the optimal
transport map `T = ∇φ` is well defined a.e. -/
theorem brenierPot_ae_differentiableAt [Nonempty ι] (hR : ∀ i, ‖g i‖ ≤ R) (hb : ∀ i, m ≤ b i) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin n), DifferentiableAt ℝ (brenierPot g b) x :=
  (brenierPot_lipschitz hR hb).ae_differentiableAt

/-- The optimal transport map is bounded by `R`, the radius of the target set. -/
theorem norm_brenierMap_le [Nonempty ι] (hR : ∀ i, ‖g i‖ ≤ R) (hb : ∀ i, m ≤ b i)
    (x : EuclideanSpace ℝ (Fin n)) : ‖brenierMap g b x‖ ≤ R := by
  have hR0 : 0 ≤ R := zero_le_R hR
  have h : ‖fderiv ℝ (brenierPot g b) x‖ ≤ (R.toNNReal : ℝ) :=
    norm_fderiv_le_of_lipschitz ℝ (brenierPot_lipschitz hR hb)
  rw [Real.coe_toNNReal R hR0] at h
  have hgrad : ‖brenierMap g b x‖ = ‖fderiv ℝ (brenierPot g b) x‖ := by
    rw [brenierMap, gradient]
    exact (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.norm_map _
  rw [hgrad]
  exact h

end Brenier

/-! ## Main statement -/

/-- **Regularity of optimal transport maps under the Ma–Trudinger–Wang condition (Figalli).**

This formalizes the statement together with its model (base) case, the quadratic cost
`c(x,y) = |x-y|²/2`:

* the mixed Hessian `c_{i,j}` of the quadratic cost equals `-1`, so the cost is nondegenerate,
  and its inverse `A = -1` is exhibited;
* the Ma–Trudinger–Wang tensor of the quadratic cost vanishes identically, hence the quadratic
  cost satisfies `MTW(0)`;
* for this cost, every `c`-convex Kantorovich potential `u` generated by a family of target
  points of norm at most `R` (the standard bounded-target hypothesis) satisfies
  `u(x) + |x|²/2 = φ(x)` with `φ` convex and globally `R`-Lipschitz;
* consequently (Rademacher) `φ` is differentiable almost everywhere, so the optimal transport
  map `T = ∇φ` is defined almost everywhere and is bounded by `R`.
-/
theorem figalli_OT_regularity (n : ℕ) {ι : Type*} [Nonempty ι]
    (g : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (R m : ℝ)
    (hR : ∀ i, ‖g i‖ ≤ R) (hb : ∀ i, m ≤ b i) :
    -- (i) the quadratic cost is nondegenerate and satisfies MTW(0)
    ((∀ x y : Fin n → ℝ, (Matrix.of fun i j => costMixed (quadCost n) i j x y) = -1) ∧
      (∀ A x y ξ η, MTWtensor (quadCost n) A x y ξ η = 0) ∧
      SatisfiesMTW (quadCost n)) ∧
    -- (ii) base case regularity of the optimal transport map for the quadratic cost
    ((∀ x, kPot g b x + ‖x‖ ^ 2 / 2 = brenierPot g b x) ∧
      ConvexOn ℝ Set.univ (brenierPot g b) ∧
      LipschitzWith R.toNNReal (brenierPot g b) ∧
      (∀ᵐ x : EuclideanSpace ℝ (Fin n), DifferentiableAt ℝ (brenierPot g b) x) ∧
      (∀ x, ‖brenierMap g b x‖ ≤ R)) := by
  refine ⟨⟨fun x y => costMixed_quadCost x y, fun A x y ξ η => MTWtensor_quadCost A x y ξ η,
    quadCost_satisfiesMTW⟩,
    fun x => kPot_add_sq_eq_brenierPot hR hb x, brenierPot_convexOn hR hb,
    brenierPot_lipschitz hR hb, brenierPot_ae_differentiableAt hR hb,
    fun x => norm_brenierMap_le hR hb x⟩

end Frontier

#print axioms Frontier.figalli_OT_regularity

