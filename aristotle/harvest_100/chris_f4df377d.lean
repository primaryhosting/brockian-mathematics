import Mathlib
import RequestProject.Kernel
import RequestProject.TwoDim

/-!
# Weil–Petersson volume polynomials in low complexity

We record the Weil–Petersson volume polynomials `V_{0,3}`, `V_{0,4}` and `V_{0,5}`, the
right-hand sides of Mirzakhani's recursion in the cases `(g,n) = (0,4)` and `(0,5)`, and
verify the recursion in both cases, together with the fact that the recursion determines
the volume polynomial.
-/

open scoped BigOperators Real
open MeasureTheory Set Real

namespace Frontier

set_option maxHeartbeats 1000000

/-! ## The volume polynomials -/

/-- `V_{0,3} ≡ 1`: the moduli space of pairs of pants is a point. -/
def V03 : (Fin 3 → ℝ) → ℝ := fun _ => 1

/-- `V_{0,4}(L) = 2π² + (L₁²+L₂²+L₃²+L₄²)/2`. -/
noncomputable def V04 (L : Fin 4 → ℝ) : ℝ := 2 * π ^ 2 + (∑ i, (L i) ^ 2) / 2

/-- `V_{0,5}(L) = (Σ Lᵢ²)²/4 − (Σ Lᵢ⁴)/8 + 3π² Σ Lᵢ² + 10π⁴`. -/
noncomputable def V05 (L : Fin 5 → ℝ) : ℝ :=
  (∑ i, (L i) ^ 2) ^ 2 / 4 - (∑ i, (L i) ^ 4) / 8 + 3 * π ^ 2 * (∑ i, (L i) ^ 2) + 10 * π ^ 4

/-! ## One-dimensional (`B`-type) terms -/

lemma integral_x_mirzKernel_add (a b : ℝ) :
    (∫ x in Ioi (0:ℝ), x * (mirzKernel x a + mirzKernel x b)) = F1 a + F1 b := by
  have ha := intOn_pow_mirzKernel 1 a
  have hb := intOn_pow_mirzKernel 1 b
  simp only [pow_one] at ha hb
  rw [F1, F1, ← integral_add ha hb]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x _
  show x * (mirzKernel x a + mirzKernel x b) = x * mirzKernel x a + x * mirzKernel x b
  ring

/-- The `B`-term integral against an affine-in-`x²` volume factor. -/
lemma integral_B_term (a b c : ℝ) :
    (∫ x in Ioi (0:ℝ), x * (mirzKernel x a + mirzKernel x b) * (c + x ^ 2 / 2))
      = c * (F1 a + F1 b) + (F3 a + F3 b) / 2 := by
  have h1a : IntegrableOn (fun x : ℝ => c * (x * mirzKernel x a)) (Ioi 0) := by
    have := (intOn_pow_mirzKernel 1 a).const_mul c
    simpa [pow_one] using this
  have h1b : IntegrableOn (fun x : ℝ => c * (x * mirzKernel x b)) (Ioi 0) := by
    have := (intOn_pow_mirzKernel 1 b).const_mul c
    simpa [pow_one] using this
  have h3a : IntegrableOn (fun x : ℝ => (1/2) * (x ^ 3 * mirzKernel x a)) (Ioi 0) :=
    (intOn_pow_mirzKernel 3 a).const_mul _
  have h3b : IntegrableOn (fun x : ℝ => (1/2) * (x ^ 3 * mirzKernel x b)) (Ioi 0) :=
    (intOn_pow_mirzKernel 3 b).const_mul _
  have h12 : IntegrableOn
      (fun x : ℝ => c * (x * mirzKernel x a) + c * (x * mirzKernel x b)) (Ioi 0) := h1a.add h1b
  have h34 : IntegrableOn
      (fun x : ℝ => (1/2) * (x ^ 3 * mirzKernel x a)
        + (1/2) * (x ^ 3 * mirzKernel x b)) (Ioi 0) := h3a.add h3b
  have hcongr : (∫ x in Ioi (0:ℝ), x * (mirzKernel x a + mirzKernel x b) * (c + x ^ 2 / 2))
      = ∫ x in Ioi (0:ℝ), ((c * (x * mirzKernel x a) + c * (x * mirzKernel x b))
          + ((1/2) * (x ^ 3 * mirzKernel x a) + (1/2) * (x ^ 3 * mirzKernel x b))) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _
    show x * (mirzKernel x a + mirzKernel x b) * (c + x ^ 2 / 2)
      = (c * (x * mirzKernel x a) + c * (x * mirzKernel x b))
        + ((1/2) * (x ^ 3 * mirzKernel x a) + (1/2) * (x ^ 3 * mirzKernel x b))
    ring
  rw [hcongr, integral_add h12 h34, integral_add h1a h1b, integral_add h3a h3b,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  have hF1a : (∫ x in Ioi (0:ℝ), x * mirzKernel x a) = F1 a := rfl
  have hF1b : (∫ x in Ioi (0:ℝ), x * mirzKernel x b) = F1 b := rfl
  have hF3a : (∫ x in Ioi (0:ℝ), x ^ 3 * mirzKernel x a) = F3 a := rfl
  have hF3b : (∫ x in Ioi (0:ℝ), x ^ 3 * mirzKernel x b) = F3 b := rfl
  rw [hF1a, hF1b, hF3a, hF3b]
  ring

/-! ## Mirzakhani's recursion for `(g,n) = (0,4)` -/

/-- For `j ∈ {1,2,3}`, `rest04 j` lists the two indices of `{1,2,3}` other than `j`. -/
def rest04 : Fin 4 → Fin 2 → Fin 4 := ![![1, 2], ![2, 3], ![1, 3], ![1, 2]]

/-- The right-hand side of Mirzakhani's recursion for `(g,n) = (0,4)`.  The
non-separating and separating terms are absent (no stable splittings in this
complexity), so only the `B`-term survives. -/
noncomputable def mirzRHS04 (L : Fin 4 → ℝ) : ℝ :=
  (1 / 2) * ∑ j ∈ ({1, 2, 3} : Finset (Fin 4)),
    ∫ x in Ioi (0:ℝ),
      x * (mirzKernel x (L 0 + L j) + mirzKernel x (L 0 - L j)) *
        V03 (Fin.cons x (fun k => L (rest04 j k)))

lemma mirzRHS04_eq (L : Fin 4 → ℝ) :
    mirzRHS04 L = 2 * π ^ 2 + (3 * (L 0) ^ 2 + (L 1) ^ 2 + (L 2) ^ 2 + (L 3) ^ 2) / 2 := by
  have hterm : ∀ j : Fin 4,
      (∫ x in Ioi (0:ℝ), x * (mirzKernel x (L 0 + L j) + mirzKernel x (L 0 - L j)) *
        V03 (Fin.cons x (fun k => L (rest04 j k))))
      = F1 (L 0 + L j) + F1 (L 0 - L j) := by
    intro j
    rw [← integral_x_mirzKernel_add]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _
    show x * (mirzKernel x (L 0 + L j) + mirzKernel x (L 0 - L j)) *
        V03 (Fin.cons x (fun k => L (rest04 j k)))
      = x * (mirzKernel x (L 0 + L j) + mirzKernel x (L 0 - L j))
    rw [show V03 (Fin.cons x (fun k => L (rest04 j k))) = 1 from rfl]
    ring
  have hsum : ∀ f : Fin 4 → ℝ, ∑ j ∈ ({1,2,3} : Finset (Fin 4)), f j = f 1 + f 2 + f 3 := by
    intro f; simp [Finset.sum_insert, Finset.mem_insert]; ring
  rw [mirzRHS04, Finset.sum_congr rfl (fun j _ => hterm j), hsum]
  rw [F1_eq, F1_eq, F1_eq, F1_eq, F1_eq, F1_eq]
  ring

lemma hasDerivAt_V04 (L : Fin 4 → ℝ) :
    HasDerivAt (fun x : ℝ => x * V04 (Function.update L 0 x)) (mirzRHS04 L) (L 0) := by
  set S : ℝ := (L 1)^2 + (L 2)^2 + (L 3)^2 with hS
  have hfun : (fun x : ℝ => x * V04 (Function.update L 0 x))
      = fun x : ℝ => 2*π^2*x + x^3/2 + (S/2)*x := by
    funext x
    have hupd : ∑ i, (Function.update L 0 x i)^2 = x^2 + S := by
      rw [Fin.sum_univ_four]
      simp [hS]
      ring
    rw [V04, hupd]
    ring
  rw [hfun, mirzRHS04_eq]
  have h : HasDerivAt (fun x : ℝ => 2*π^2*x + x^3/2 + (S/2)*x)
      (2*π^2 + 3*(L 0)^2/2 + S/2) (L 0) := by
    have h1 : HasDerivAt (fun x : ℝ => 2*π^2*x) (2*π^2) (L 0) := by
      simpa using (hasDerivAt_id (L 0)).const_mul (2*π^2)
    have h2 : HasDerivAt (fun x : ℝ => x^3/2) (3*(L 0)^2/2) (L 0) := by
      simpa using (hasDerivAt_pow 3 (L 0)).div_const 2
    have h3 : HasDerivAt (fun x : ℝ => (S/2)*x) (S/2) (L 0) := by
      simpa using (hasDerivAt_id (L 0)).const_mul (S/2)
    exact (h1.add h2).add h3
  convert h using 1
  rw [hS]; ring

/-- The recursion determines `V_{0,4}` away from `L₁ = 0`. -/
lemma uniqueness_V04 (W : (Fin 4 → ℝ) → ℝ)
    (hW : ∀ L : Fin 4 → ℝ,
      HasDerivAt (fun x : ℝ => x * W (Function.update L 0 x)) (mirzRHS04 L) (L 0)) :
    ∀ L : Fin 4 → ℝ, L 0 ≠ 0 → W L = V04 L := by
  intro L hL0
  have hg : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y * W (Function.update L 0 y))
      (mirzRHS04 (Function.update L 0 x)) x := by
    intro x
    have h := hW (Function.update L 0 x)
    rw [Function.update_self] at h
    simpa [Function.update_idem] using h
  have hh : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y * V04 (Function.update L 0 y))
      (mirzRHS04 (Function.update L 0 x)) x := by
    intro x
    have h := hasDerivAt_V04 (Function.update L 0 x)
    rw [Function.update_self] at h
    simpa [Function.update_idem] using h
  have hd : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => y * W (Function.update L 0 y) - y * V04 (Function.update L 0 y)) 0 x := by
    intro x
    simpa using (hg x).sub (hh x)
  have hconst := is_const_of_deriv_eq_zero
    (f := fun y : ℝ => y * W (Function.update L 0 y) - y * V04 (Function.update L 0 y))
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv)
  have h0 := hconst (L 0) 0
  simp only [zero_mul, sub_self] at h0
  rw [Function.update_eq_self] at h0
  have hcancel : L 0 * W L = L 0 * V04 L := by linarith [h0]
  exact mul_left_cancel₀ hL0 hcancel

/-! ## Mirzakhani's recursion for `(g,n) = (0,5)` -/

/-- The six ordered stable splittings of `{2,3,4,5}` into two pairs. -/
def split05 : Fin 6 → (Fin 2 → Fin 5) × (Fin 2 → Fin 5) :=
  ![(![1, 2], ![3, 4]), (![1, 3], ![2, 4]), (![1, 4], ![2, 3]),
    (![3, 4], ![1, 2]), (![2, 4], ![1, 3]), (![2, 3], ![1, 4])]

/-- For `j ∈ {1,2,3,4}`, `rest05 j` lists the three indices of `{1,2,3,4}` other than `j`. -/
def rest05 : Fin 5 → Fin 3 → Fin 5 :=
  ![![2, 3, 4], ![2, 3, 4], ![1, 3, 4], ![1, 2, 4], ![1, 2, 3]]

/-- The right-hand side of Mirzakhani's recursion for `(g,n) = (0,5)`: the separating
term (a sum over the six ordered splittings of the remaining boundary components into
two pairs, each contributing a product `V_{0,3} · V_{0,3}`) plus the `B`-term (a sum
over the four remaining boundary components, each contributing a `V_{0,4}`).  The
non-separating term is absent in genus `0`. -/
noncomputable def mirzRHS05 (L : Fin 5 → ℝ) : ℝ :=
  (1 / 2) * ∑ k : Fin 6, (∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ),
      x * y * mirzKernel (x + y) (L 0) *
        V03 (Fin.cons x (fun m => L ((split05 k).1 m))) *
        V03 (Fin.cons y (fun m => L ((split05 k).2 m))))
  + (1 / 2) * ∑ j ∈ ({1, 2, 3, 4} : Finset (Fin 5)),
      ∫ x in Ioi (0:ℝ), x * (mirzKernel x (L 0 + L j) + mirzKernel x (L 0 - L j)) *
        V04 (Fin.cons x (fun m => L (rest05 j m)))

lemma V04_cons (x : ℝ) (r : Fin 3 → ℝ) :
    V04 (Fin.cons x r) = (2 * π ^ 2 + (∑ m, (r m) ^ 2) / 2) + x ^ 2 / 2 := by
  have e0 : (Fin.cons x r : Fin 4 → ℝ) 0 = x := rfl
  have e1 : (Fin.cons x r : Fin 4 → ℝ) 1 = r 0 := rfl
  have e2 : (Fin.cons x r : Fin 4 → ℝ) 2 = r 1 := rfl
  have e3 : (Fin.cons x r : Fin 4 → ℝ) 3 = r 2 := rfl
  rw [V04, Fin.sum_univ_four, Fin.sum_univ_three, e0, e1, e2, e3]
  ring

lemma mirzRHS05_sep (L : Fin 5 → ℝ) (k : Fin 6) :
    (∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ),
      x * y * mirzKernel (x + y) (L 0) *
        V03 (Fin.cons x (fun m => L ((split05 k).1 m))) *
        V03 (Fin.cons y (fun m => L ((split05 k).2 m)))) = F3 (L 0) / 6 := by
  rw [← integral_quadrant_mirzKernel (L 0)]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x _
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro y _
  show x * y * mirzKernel (x + y) (L 0) *
      V03 (Fin.cons x (fun m => L ((split05 k).1 m))) *
      V03 (Fin.cons y (fun m => L ((split05 k).2 m)))
    = x * y * mirzKernel (x + y) (L 0)
  rw [show V03 (Fin.cons x (fun m => L ((split05 k).1 m))) = 1 from rfl,
    show V03 (Fin.cons y (fun m => L ((split05 k).2 m))) = 1 from rfl]
  ring

lemma mirzRHS05_eq (L : Fin 5 → ℝ) :
    mirzRHS05 L
      = 5 * (L 0) ^ 4 / 8
        + (3 * ((L 1)^2 + (L 2)^2 + (L 3)^2 + (L 4)^2) / 2 + 9 * π ^ 2) * (L 0) ^ 2
        + (3 * π ^ 2 * ((L 1)^2 + (L 2)^2 + (L 3)^2 + (L 4)^2)
            + ((L 1)^2 + (L 2)^2 + (L 3)^2 + (L 4)^2) ^ 2 / 4
            - ((L 1)^4 + (L 2)^4 + (L 3)^4 + (L 4)^4) / 8 + 10 * π ^ 4) := by
  have hB : ∀ j : Fin 5,
      (∫ x in Ioi (0:ℝ), x * (mirzKernel x (L 0 + L j) + mirzKernel x (L 0 - L j)) *
        V04 (Fin.cons x (fun m => L (rest05 j m))))
      = (2 * π ^ 2 + (∑ m, (L (rest05 j m)) ^ 2) / 2)
          * (F1 (L 0 + L j) + F1 (L 0 - L j)) + (F3 (L 0 + L j) + F3 (L 0 - L j)) / 2 := by
    intro j
    rw [← integral_B_term (L 0 + L j) (L 0 - L j)
      (2 * π ^ 2 + (∑ m, (L (rest05 j m)) ^ 2) / 2)]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _
    show x * (mirzKernel x (L 0 + L j) + mirzKernel x (L 0 - L j)) *
        V04 (Fin.cons x (fun m => L (rest05 j m)))
      = x * (mirzKernel x (L 0 + L j) + mirzKernel x (L 0 - L j)) *
        ((2 * π ^ 2 + (∑ m, (L (rest05 j m)) ^ 2) / 2) + x ^ 2 / 2)
    rw [V04_cons]
  have hsumB : ∀ f : Fin 5 → ℝ,
      ∑ j ∈ ({1,2,3,4} : Finset (Fin 5)), f j = f 1 + f 2 + f 3 + f 4 := by
    intro f; simp [Finset.sum_insert, Finset.mem_insert]; ring
  have s1 : ∑ m, (L (rest05 1 m)) ^ 2 = (L 2)^2 + (L 3)^2 + (L 4)^2 := by
    rw [Fin.sum_univ_three, show rest05 1 0 = 2 from rfl, show rest05 1 1 = 3 from rfl,
      show rest05 1 2 = 4 from rfl]
  have s2 : ∑ m, (L (rest05 2 m)) ^ 2 = (L 1)^2 + (L 3)^2 + (L 4)^2 := by
    rw [Fin.sum_univ_three, show rest05 2 0 = 1 from rfl, show rest05 2 1 = 3 from rfl,
      show rest05 2 2 = 4 from rfl]
  have s3 : ∑ m, (L (rest05 3 m)) ^ 2 = (L 1)^2 + (L 2)^2 + (L 4)^2 := by
    rw [Fin.sum_univ_three, show rest05 3 0 = 1 from rfl, show rest05 3 1 = 2 from rfl,
      show rest05 3 2 = 4 from rfl]
  have s4 : ∑ m, (L (rest05 4 m)) ^ 2 = (L 1)^2 + (L 2)^2 + (L 3)^2 := by
    rw [Fin.sum_univ_three, show rest05 4 0 = 1 from rfl, show rest05 4 1 = 2 from rfl,
      show rest05 4 2 = 3 from rfl]
  rw [mirzRHS05, Finset.sum_congr rfl (fun k _ => mirzRHS05_sep L k),
    Finset.sum_congr rfl (fun j _ => hB j), hsumB, Finset.sum_const, s1, s2, s3, s4]
  rw [F1_eq, F1_eq, F1_eq, F1_eq, F1_eq, F1_eq, F1_eq, F1_eq,
    F3_eq, F3_eq, F3_eq, F3_eq, F3_eq, F3_eq, F3_eq, F3_eq, F3_eq]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma hasDerivAt_V05 (L : Fin 5 → ℝ) :
    HasDerivAt (fun x : ℝ => x * V05 (Function.update L 0 x)) (mirzRHS05 L) (L 0) := by
  set Q : ℝ := (L 1)^2 + (L 2)^2 + (L 3)^2 + (L 4)^2 with hQ
  set R : ℝ := (L 1)^4 + (L 2)^4 + (L 3)^4 + (L 4)^4 with hR
  have hfun : (fun x : ℝ => x * V05 (Function.update L 0 x))
      = fun x : ℝ => x^5/8 + (Q/2 + 3*π^2) * x^3
          + (3*π^2*Q + Q^2/4 - R/8 + 10*π^4) * x := by
    funext x
    have h2 : ∑ i, (Function.update L 0 x i)^2 = x^2 + Q := by
      rw [Fin.sum_univ_five]; simp [hQ]; ring
    have h4 : ∑ i, (Function.update L 0 x i)^4 = x^4 + R := by
      rw [Fin.sum_univ_five]; simp [hR]; ring
    rw [V05, h2, h4]
    ring
  rw [hfun, mirzRHS05_eq]
  have h : HasDerivAt (fun x : ℝ => x^5/8 + (Q/2 + 3*π^2) * x^3
      + (3*π^2*Q + Q^2/4 - R/8 + 10*π^4) * x)
      (5*(L 0)^4/8 + (Q/2 + 3*π^2) * (3*(L 0)^2) + (3*π^2*Q + Q^2/4 - R/8 + 10*π^4)) (L 0) := by
    have h1 : HasDerivAt (fun x : ℝ => x^5/8) (5*(L 0)^4/8) (L 0) := by
      simpa using (hasDerivAt_pow 5 (L 0)).div_const 8
    have h2 : HasDerivAt (fun x : ℝ => (Q/2 + 3*π^2) * x^3) ((Q/2 + 3*π^2) * (3*(L 0)^2)) (L 0) := by
      simpa using (hasDerivAt_pow 3 (L 0)).const_mul (Q/2 + 3*π^2)
    have h3 : HasDerivAt (fun x : ℝ => (3*π^2*Q + Q^2/4 - R/8 + 10*π^4) * x)
        (3*π^2*Q + Q^2/4 - R/8 + 10*π^4) (L 0) := by
      simpa using (hasDerivAt_id (L 0)).const_mul (3*π^2*Q + Q^2/4 - R/8 + 10*π^4)
    exact (h1.add h2).add h3
  convert h using 1
  rw [hQ, hR]; ring

/-- The recursion determines `V_{0,5}` away from `L₁ = 0`. -/
lemma uniqueness_V05 (W : (Fin 5 → ℝ) → ℝ)
    (hW : ∀ L : Fin 5 → ℝ,
      HasDerivAt (fun x : ℝ => x * W (Function.update L 0 x)) (mirzRHS05 L) (L 0)) :
    ∀ L : Fin 5 → ℝ, L 0 ≠ 0 → W L = V05 L := by
  intro L hL0
  have hg : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y * W (Function.update L 0 y))
      (mirzRHS05 (Function.update L 0 x)) x := by
    intro x
    have h := hW (Function.update L 0 x)
    rw [Function.update_self] at h
    simpa [Function.update_idem] using h
  have hh : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y * V05 (Function.update L 0 y))
      (mirzRHS05 (Function.update L 0 x)) x := by
    intro x
    have h := hasDerivAt_V05 (Function.update L 0 x)
    rw [Function.update_self] at h
    simpa [Function.update_idem] using h
  have hd : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => y * W (Function.update L 0 y) - y * V05 (Function.update L 0 y)) 0 x := by
    intro x
    simpa using (hg x).sub (hh x)
  have hconst := is_const_of_deriv_eq_zero
    (f := fun y : ℝ => y * W (Function.update L 0 y) - y * V05 (Function.update L 0 y))
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv)
  have h0 := hconst (L 0) 0
  simp only [zero_mul, sub_self] at h0
  rw [Function.update_eq_self] at h0
  have hcancel : L 0 * W L = L 0 * V05 L := by linarith [h0]
  exact mul_left_cancel₀ hL0 hcancel

end Frontier

import Mathlib
import RequestProject.Kernel

/-!
# The two-dimensional moment identity

Mirzakhani's recursion contains, besides the one-dimensional `B`-terms, two-dimensional
integrals of the shape

`∫₀^∞ ∫₀^∞ x y H(x+y, t) V(x, …) V(y, …) dx dy`.

In the lowest complexity where such a term occurs, `(g,n) = (0,5)`, the volume factors are
the constant `V_{0,3} = 1`, so what is needed is the identity

`∫₀^∞ ∫₀^∞ x y H(x+y, t) dx dy = F₃(t)/6`.

We prove the general statement `∫₀^∞ ∫₀^∞ x y φ(x+y) dx dy = (1/6) ∫₀^∞ u³ φ(u) du`
for any measurable `φ` with an exponential majorant, using Fubini's theorem for the shear
`(x,y) ↦ (x, x+y)` of the plane together with the elementary convolution
`∫₀^u x (u-x) dx = u³/6`, and then specialise to `φ = H(·, t)`.
-/

open scoped Real
open MeasureTheory Set Real

namespace Frontier

set_option maxHeartbeats 1000000

/-! ## The weight `wt x = x · 1_{x>0}` -/

/-- `wt x = x` for `x > 0` and `wt x = 0` otherwise. -/
noncomputable def wt (x : ℝ) : ℝ := Set.indicator (Ioi (0:ℝ)) (fun x => x) x

lemma wt_of_pos {x : ℝ} (hx : 0 < x) : wt x = x := indicator_of_mem (mem_Ioi.mpr hx) _

lemma wt_of_nonpos {x : ℝ} (hx : x ≤ 0) : wt x = 0 :=
  indicator_of_notMem (by simpa using hx) _

lemma wt_nonneg (x : ℝ) : 0 ≤ wt x := by
  rcases lt_or_ge 0 x with h | h
  · rw [wt_of_pos h]; exact h.le
  · rw [wt_of_nonpos h]

lemma measurable_wt : Measurable wt := measurable_id.indicator measurableSet_Ioi

/-- `wt3 u = u³/6` for `u > 0` and `0` otherwise: the convolution `wt ⋆ wt`. -/
noncomputable def wt3 (u : ℝ) : ℝ := Set.indicator (Ioi (0:ℝ)) (fun u => u ^ 3 / 6) u

lemma wt3_of_pos {u : ℝ} (hu : 0 < u) : wt3 u = u ^ 3 / 6 :=
  indicator_of_mem (mem_Ioi.mpr hu) _

lemma wt3_of_nonpos {u : ℝ} (hu : u ≤ 0) : wt3 u = 0 :=
  indicator_of_notMem (by simpa using hu) _

/-! ## An integrable majorant -/

lemma exp_le_two_fd {x : ℝ} (hx : 0 ≤ x) : Real.exp (-(x/2)) ≤ 2 * fd x := by
  have hpos : (0:ℝ) < 1 + Real.exp (x/2) := by positivity
  have he : (1:ℝ) ≤ Real.exp (x/2) := Real.one_le_exp (by linarith)
  have key : 1 / Real.exp (x/2) ≤ 2 / (1 + Real.exp (x/2)) := by
    rw [div_le_div_iff₀ (Real.exp_pos _) hpos]; nlinarith
  rw [Real.exp_neg, fd]
  calc (Real.exp (x/2))⁻¹ = 1 / Real.exp (x/2) := (one_div _).symm
    _ ≤ 2 / (1 + Real.exp (x/2)) := key
    _ = 2 * (1 / (1 + Real.exp (x/2))) := by ring

lemma intOn_x_exp : IntegrableOn (fun x : ℝ => x * Real.exp (-(x/2))) (Ioi 0) := by
  have h := (intOn_pow_fd 1 0).const_mul 2
  refine Integrable.mono' h ?_ ?_
  · exact (measurable_id.mul (Real.measurable_exp.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0:ℝ) < x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc x * Real.exp (-(x/2)) ≤ x * (2 * fd x) := by
          nlinarith [exp_le_two_fd hx0.le, fd_pos x]
      _ = 2 * (x ^ 1 * fd x) := by ring

lemma integrable_wt_exp : Integrable (fun x : ℝ => wt x * Real.exp (-(x/2))) := by
  have hrw : (fun x : ℝ => wt x * Real.exp (-(x/2)))
      = Set.indicator (Ioi (0:ℝ)) (fun x => x * Real.exp (-(x/2))) := by
    funext x
    rcases lt_or_ge 0 x with h | h
    · rw [wt_of_pos h, indicator_of_mem (mem_Ioi.mpr h)]
    · rw [wt_of_nonpos h, indicator_of_notMem (by simpa using h), zero_mul]
  rw [hrw, integrable_indicator_iff measurableSet_Ioi]
  exact intOn_x_exp

/-! ## Integrability on the plane -/

variable {φ : ℝ → ℝ} {C : ℝ}

lemma integrable_prodKernel (hmeas : Measurable φ)
    (hb : ∀ s, |φ s| ≤ C * Real.exp (-(s/2))) :
    Integrable (fun p : ℝ × ℝ => wt p.1 * wt p.2 * φ (p.1 + p.2)) (volume.prod volume) := by
  have hmaj : Integrable
      (fun p : ℝ × ℝ => C *
        ((wt p.1 * Real.exp (-(p.1/2))) * (wt p.2 * Real.exp (-(p.2/2)))))
      (volume.prod volume) :=
    (integrable_wt_exp.mul_prod integrable_wt_exp).const_mul _
  refine Integrable.mono' hmaj ?_ ?_
  · exact ((measurable_wt.comp measurable_fst).mul (measurable_wt.comp measurable_snd) |>.mul
      (hmeas.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards with p
    have hsplit : Real.exp (-((p.1 + p.2)/2))
        = Real.exp (-(p.1/2)) * Real.exp (-(p.2/2)) := by
      rw [← Real.exp_add]; ring_nf
    have hw : 0 ≤ wt p.1 * wt p.2 := mul_nonneg (wt_nonneg _) (wt_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    calc wt p.1 * wt p.2 * |φ (p.1 + p.2)|
        ≤ wt p.1 * wt p.2 * (C * Real.exp (-((p.1 + p.2)/2))) :=
          mul_le_mul_of_nonneg_left (hb _) hw
      _ = C * ((wt p.1 * Real.exp (-(p.1/2))) * (wt p.2 * Real.exp (-(p.2/2)))) := by
          rw [hsplit]; ring

lemma integrable_shearKernel (hmeas : Measurable φ)
    (hb : ∀ s, |φ s| ≤ C * Real.exp (-(s/2))) :
    Integrable (fun p : ℝ × ℝ => wt p.1 * wt (p.2 - p.1) * φ p.2) (volume.prod volume) := by
  refine ((measurePreserving_prod_add (volume : Measure ℝ) volume).integrable_comp_emb
    (MeasurableEquiv.shearAddRight ℝ).measurableEmbedding).mp ?_
  have hcongr : ((fun p : ℝ × ℝ => wt p.1 * wt (p.2 - p.1) * φ p.2) ∘
      fun z : ℝ × ℝ => (z.1, z.1 + z.2))
      = fun p : ℝ × ℝ => wt p.1 * wt p.2 * φ (p.1 + p.2) := by
    funext p
    simp [Function.comp]
  rw [hcongr]
  exact integrable_prodKernel hmeas hb

/-! ## The two Fubini evaluations -/

lemma prodKernel_integral_eq (hmeas : Measurable φ)
    (hb : ∀ s, |φ s| ≤ C * Real.exp (-(s/2))) :
    (∫ p : ℝ × ℝ, wt p.1 * wt p.2 * φ (p.1 + p.2) ∂(volume.prod volume))
      = ∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ), x * y * φ (x + y) := by
  have hfub : (∫ x : ℝ, ∫ y : ℝ, wt x * wt y * φ (x + y))
      = ∫ p : ℝ × ℝ, wt p.1 * wt p.2 * φ (p.1 + p.2) ∂(volume.prod volume) :=
    integral_integral (integrable_prodKernel hmeas hb)
  rw [← hfub]
  have hinner : ∀ x : ℝ, (∫ y : ℝ, wt x * wt y * φ (x + y))
      = wt x * ∫ y in Ioi (0:ℝ), y * φ (x + y) := by
    intro x
    have hrw : (fun y : ℝ => wt x * wt y * φ (x + y))
        = Set.indicator (Ioi (0:ℝ)) (fun y => wt x * (y * φ (x + y))) := by
      funext y
      rcases lt_or_ge 0 y with h | h
      · rw [wt_of_pos h, indicator_of_mem (mem_Ioi.mpr h)]; ring
      · rw [wt_of_nonpos h, indicator_of_notMem (by simpa using h)]; ring
    rw [hrw, integral_indicator measurableSet_Ioi, integral_const_mul]
  simp_rw [hinner]
  have hrw2 : (fun x : ℝ => wt x * ∫ y in Ioi (0:ℝ), y * φ (x + y))
      = Set.indicator (Ioi (0:ℝ)) (fun x => ∫ y in Ioi (0:ℝ), x * y * φ (x + y)) := by
    funext x
    rcases lt_or_ge 0 x with h | h
    · rw [wt_of_pos h, indicator_of_mem (mem_Ioi.mpr h), ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
      ring
    · rw [wt_of_nonpos h, indicator_of_notMem (by simpa using h), zero_mul]
  rw [hrw2, integral_indicator measurableSet_Ioi]

lemma integral_wt_conv (u : ℝ) : (∫ x : ℝ, wt x * wt (u - x)) = wt3 u := by
  rcases lt_or_ge 0 u with hu | hu
  · have hrw : (fun x : ℝ => wt x * wt (u - x))
        = Set.indicator (Ioo (0:ℝ) u) (fun x => x * (u - x)) := by
      funext x
      by_cases hx : 0 < x
      · by_cases hx2 : x < u
        · rw [wt_of_pos hx, wt_of_pos (by linarith), indicator_of_mem (mem_Ioo.mpr ⟨hx, hx2⟩)]
        · rw [wt_of_nonpos (by linarith : u - x ≤ 0), indicator_of_notMem, mul_zero]
          simp only [mem_Ioo, not_and, not_lt]
          intro _; linarith
      · rw [wt_of_nonpos (by linarith : x ≤ 0), indicator_of_notMem, zero_mul]
        simp only [mem_Ioo, not_and, not_lt]
        intro h; exact absurd h hx
    rw [hrw, integral_indicator measurableSet_Ioo, wt3_of_pos hu,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hu.le]
    have hcalc : ∫ x in (0:ℝ)..u, x * (u - x) = u ^ 3 / 6 := by
      have h1 : ∫ x in (0:ℝ)..u, x * (u - x) = ∫ x in (0:ℝ)..u, (u * x - x ^ 2) := by
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        ring
      rw [h1, intervalIntegral.integral_sub
        ((intervalIntegral.intervalIntegrable_id).const_mul u)
        (intervalIntegral.intervalIntegrable_pow 2)]
      rw [intervalIntegral.integral_const_mul, integral_id, integral_pow]
      norm_num
      ring
    rw [hcalc]
  · have hrw : (fun x : ℝ => wt x * wt (u - x)) = fun _ => 0 := by
      funext x
      by_cases hx : 0 < x
      · rw [wt_of_nonpos (by linarith : u - x ≤ 0), mul_zero]
      · rw [wt_of_nonpos (by linarith : x ≤ 0), zero_mul]
    rw [hrw, integral_zero, wt3_of_nonpos hu]

lemma shearKernel_integral_eq (hmeas : Measurable φ)
    (hb : ∀ s, |φ s| ≤ C * Real.exp (-(s/2))) :
    (∫ p : ℝ × ℝ, wt p.1 * wt (p.2 - p.1) * φ p.2 ∂(volume.prod volume))
      = (1/6) * ∫ u in Ioi (0:ℝ), u ^ 3 * φ u := by
  have hfub : (∫ x : ℝ, ∫ u : ℝ, wt x * wt (u - x) * φ u)
      = ∫ p : ℝ × ℝ, wt p.1 * wt (p.2 - p.1) * φ p.2 ∂(volume.prod volume) :=
    integral_integral (integrable_shearKernel hmeas hb)
  rw [← hfub, integral_integral_swap (integrable_shearKernel hmeas hb)]
  have hinner : ∀ u : ℝ, (∫ x : ℝ, wt x * wt (u - x) * φ u) = wt3 u * φ u := by
    intro u
    rw [← integral_wt_conv u, ← integral_mul_const]
  simp_rw [hinner]
  have hrw : (fun u : ℝ => wt3 u * φ u)
      = Set.indicator (Ioi (0:ℝ)) (fun u => (1/6) * (u ^ 3 * φ u)) := by
    funext u
    rcases lt_or_ge 0 u with h | h
    · rw [wt3_of_pos h, indicator_of_mem (mem_Ioi.mpr h)]; ring
    · rw [wt3_of_nonpos h, indicator_of_notMem (by simpa using h), zero_mul]
  rw [hrw, integral_indicator measurableSet_Ioi, integral_const_mul]

/-- **The two-dimensional moment identity.**  For a measurable `φ` with an exponentially
decaying majorant, `∫₀^∞ ∫₀^∞ x y φ(x+y) dy dx = (1/6) ∫₀^∞ u³ φ(u) du`. -/
theorem integral_quadrant (hmeas : Measurable φ)
    (hb : ∀ s, |φ s| ≤ C * Real.exp (-(s/2))) :
    (∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ), x * y * φ (x + y))
      = (1/6) * ∫ u in Ioi (0:ℝ), u ^ 3 * φ u := by
  rw [← prodKernel_integral_eq hmeas hb, ← shearKernel_integral_eq hmeas hb]
  have h := (measurePreserving_prod_add (volume : Measure ℝ) volume).integral_comp
    (MeasurableEquiv.shearAddRight ℝ).measurableEmbedding
    (fun p : ℝ × ℝ => wt p.1 * wt (p.2 - p.1) * φ p.2)
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards with p
  simp

/-! ## Specialisation to Mirzakhani's kernel -/

lemma abs_mirzKernel_le (t s : ℝ) :
    |mirzKernel s t| ≤ (Real.exp (-(t/2)) + Real.exp (t/2)) * Real.exp (-(s/2)) := by
  have h1 : fd (s + t) ≤ Real.exp (-((s + t)/2)) := fd_le_exp _
  have h2 : fd (s - t) ≤ Real.exp (-((s - t)/2)) := fd_le_exp _
  have e1 : Real.exp (-((s + t)/2)) = Real.exp (-(t/2)) * Real.exp (-(s/2)) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-((s - t)/2)) = Real.exp (t/2) * Real.exp (-(s/2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [mirzKernel, abs_of_pos (add_pos (fd_pos _) (fd_pos _))]
  rw [e1] at h1
  rw [e2] at h2
  nlinarith

/-- **The two-dimensional term of Mirzakhani's recursion in the lowest complexity.**
`∫₀^∞ ∫₀^∞ x y H(x+y, t) dy dx = F₃(t)/6 = t⁴/24 + π² t²/3 + 14 π⁴/45`. -/
theorem integral_quadrant_mirzKernel (t : ℝ) :
    (∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ), x * y * mirzKernel (x + y) t) = F3 t / 6 := by
  have hmeas : Measurable (fun s => mirzKernel s t) := by
    have : Continuous (fun s => mirzKernel s t) := by
      unfold mirzKernel
      exact (continuous_fd.comp (continuous_id.add continuous_const)).add
        (continuous_fd.comp (continuous_id.sub continuous_const))
    exact this.measurable
  rw [integral_quadrant hmeas (C := Real.exp (-(t/2)) + Real.exp (t/2))
    (fun s => abs_mirzKernel_le t s), F3]
  ring

end Frontier

/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the
-- header above is written as an ordinary block comment.)

import Mathlib
import RequestProject.Kernel
import RequestProject.TwoDim
import RequestProject.Volumes

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open MeasureTheory Set Real

/-!
## Overview

Mirzakhani's recursion expresses the Weil–Petersson volume `V_{g,n}(L₁,…,L_n)` of the
moduli space of genus `g` hyperbolic surfaces with `n` geodesic boundary components of
lengths `L₁,…,L_n` through volumes of smaller complexity:

```
∂/∂L₁ (L₁ · V_{g,n}(L))
  = ½ ∫₀^∞ ∫₀^∞ x y H(x+y, L₁) V_{g-1,n+1}(x, y, L̂) dx dy          (non-separating)
  + ½ Σ_{stable splittings} ∫₀^∞ ∫₀^∞ x y H(x+y, L₁) V₁(x,·) V₂(y,·) dx dy  (separating)
  + ½ Σ_{j=2}^{n} ∫₀^∞ x (H(x, L₁+L_j) + H(x, L₁-L_j)) V_{g,n-1}(x, L̂_j) dx  (`B`-term)
```

where the kernel is `H(x,t) = 1/(1+e^{(x+t)/2}) + 1/(1+e^{(x-t)/2})`.

The analytic input is developed in `RequestProject.Kernel` and `RequestProject.TwoDim`:

* the moment transforms `F₁(t) = ∫₀^∞ x H(x,t) dx = t²/2 + 2π²/3` and
  `F₃(t) = ∫₀^∞ x³ H(x,t) dx = t⁴/4 + 2π²t² + 28π⁴/15`;
* the two-dimensional identity `∫₀^∞ ∫₀^∞ x y H(x+y,t) dx dy = F₃(t)/6`.

`RequestProject.Volumes` then records the volume polynomials in low complexity and
verifies Mirzakhani's recursion in the first two nontrivial cases:

* the base case `V_{0,3} = 1`;
* the recursion for `(g,n) = (0,4)`, where the separating and non-separating terms are
  vacuous since no stable splitting exists, with
  `V_{0,4}(L) = 2π² + ½ Σ L_i²`;
* the recursion for `(g,n) = (0,5)`, where the separating term is present — a sum over the
  six ordered splittings of the remaining four boundary components into two pairs, each
  contributing a product `V_{0,3}·V_{0,3}` — and the `B`-term involves `V_{0,4}`, with
  `V_{0,5}(L) = ¼(Σ L_i²)² − ⅛ Σ L_i⁴ + 3π² Σ L_i² + 10π⁴`;
* the converse in each case: the recursion *determines* the volume polynomial (for
  `L₁ ≠ 0`; the value at `L₁ = 0` is not pinned down pointwise by the recursion, though
  it is by continuity).

Mathlib contains no Weil–Petersson theory, so no existing lemma closes the statement; the
Mathlib results carrying the analytic work here are `integrable_of_isBigO_exp_neg` and
`Real.pow_div_factorial_le_exp` (convergence of the moment integrals),
`hasSum_zeta_two` / `hasSum_zeta_four` (the values `η(2) = π²/12` and
`η(4) = 7π⁴/720` of the alternating zeta values produced by the Fermi–Dirac expansion of
the kernel), `measurePreserving_prod_add` together with
`MeasureTheory.integral_integral_swap` (Fubini for the shear `(x,y) ↦ (x, x+y)`, giving the
two-dimensional term), and `is_const_of_deriv_eq_zero` (the uniqueness statements).
-/

/-- **Mirzakhani's recursion for Weil–Petersson volumes, verified in the first two
nontrivial complexities.**

* The base case: the volume of the moduli space of pairs of pants is `V_{0,3} = 1`.
* Mirzakhani's recursion
  `∂/∂L₁ (L₁ V_{g,n}(L)) = ½ Σ_{stable splittings} ∫∫ x y H(x+y,L₁) V₁(x,·) V₂(y,·) dx dy
     + ½ Σ_{j≥2} ∫₀^∞ x (H(x,L₁+L_j)+H(x,L₁-L_j)) V_{g,n-1}(x, L̂) dx`
  holds for `(g,n) = (0,4)` with `V_{0,4}(L) = 2π² + ½ Σ L_i²` (where the separating and
  non-separating terms are vacuous), and for `(g,n) = (0,5)` with
  `V_{0,5}(L) = ¼(Σ L_i²)² − ⅛ Σ L_i⁴ + 3π² Σ L_i² + 10π⁴` (where the separating term
  contributes through the two-dimensional integral `∫∫ x y H(x+y,L₁) dx dy = F₃(L₁)/6`).
* Conversely, the recursion together with the base case *determines* these volumes:
  any function satisfying it agrees with `V_{0,4}` resp. `V_{0,5}` whenever `L₁ ≠ 0`.
-/
theorem mirzakhani_WP_volume :
    (∀ L : Fin 3 → ℝ, V03 L = 1) ∧
    (∀ L : Fin 4 → ℝ,
      HasDerivAt (fun x : ℝ => x * V04 (Function.update L 0 x)) (mirzRHS04 L) (L 0)) ∧
    (∀ W : (Fin 4 → ℝ) → ℝ,
      (∀ L : Fin 4 → ℝ,
        HasDerivAt (fun x : ℝ => x * W (Function.update L 0 x)) (mirzRHS04 L) (L 0)) →
      ∀ L : Fin 4 → ℝ, L 0 ≠ 0 → W L = V04 L) ∧
    (∀ L : Fin 5 → ℝ,
      HasDerivAt (fun x : ℝ => x * V05 (Function.update L 0 x)) (mirzRHS05 L) (L 0)) ∧
    (∀ W : (Fin 5 → ℝ) → ℝ,
      (∀ L : Fin 5 → ℝ,
        HasDerivAt (fun x : ℝ => x * W (Function.update L 0 x)) (mirzRHS05 L) (L 0)) →
      ∀ L : Fin 5 → ℝ, L 0 ≠ 0 → W L = V05 L) :=
  ⟨fun _ => rfl, hasDerivAt_V04, uniqueness_V04, hasDerivAt_V05, uniqueness_V05⟩

end Frontier

import Mathlib

/-!
# Mirzakhani's integration kernel and its moment transforms

This file develops the analytic input to Mirzakhani's recursion for Weil–Petersson
volumes: the kernel

`H(x,t) = 1/(1+e^{(x+t)/2}) + 1/(1+e^{(x-t)/2})`

and the moment transforms `F_{2k+1}(t) = ∫₀^∞ x^{2k+1} H(x,t) dx` for `k = 0, 1`:

* `Frontier.F1_eq` : `∫₀^∞ x H(x,t) dx = t²/2 + 2π²/3`;
* `Frontier.F3_eq` : `∫₀^∞ x³ H(x,t) dx = t⁴/4 + 2π²t² + 28π⁴/15`.

These rest on the Fermi–Dirac integrals `∫₀^∞ xᵐ/(1+eˣ) dx = m! · η(m+1)`, where `η` is
the Dirichlet eta function, evaluated here at `η(2) = π²/12` and `η(4) = 7π⁴/720`.
-/

open scoped BigOperators
open scoped Real
open scoped Nat

set_option maxHeartbeats 1000000

namespace Frontier

open MeasureTheory Set Real

/-- The "Fermi–Dirac" building block `fd s = 1/(1+e^{s/2})` of Mirzakhani's kernel. -/
noncomputable def fd (s : ℝ) : ℝ := 1 / (1 + Real.exp (s / 2))

/-- Mirzakhani's kernel `H(x,t) = 1/(1+e^{(x+t)/2}) + 1/(1+e^{(x-t)/2})`. -/
noncomputable def mirzKernel (x t : ℝ) : ℝ := fd (x + t) + fd (x - t)

/-- The first Mirzakhani transform `F₁(t) = ∫₀^∞ x H(x,t) dx`. -/
noncomputable def F1 (t : ℝ) : ℝ := ∫ x in Ioi (0:ℝ), x * mirzKernel x t

/-- The second Mirzakhani transform `F₃(t) = ∫₀^∞ x³ H(x,t) dx`. -/
noncomputable def F3 (t : ℝ) : ℝ := ∫ x in Ioi (0:ℝ), x ^ 3 * mirzKernel x t

/-! ## Basic properties of `fd` -/

lemma fd_pos (s : ℝ) : 0 < fd s := by
  have h : 0 < 1 + Real.exp (s / 2) := by positivity
  simpa [fd] using (one_div_pos.mpr h)

lemma fd_add_neg (s : ℝ) : fd s + fd (-s) = 1 := by
  have hE : (0:ℝ) < Real.exp (s / 2) := Real.exp_pos _
  have h : Real.exp (-s / 2) = (Real.exp (s / 2))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [fd, fd, h]
  field_simp
  ring

lemma continuous_fd : Continuous fd := by
  unfold fd
  fun_prop (disch := intro s; positivity)

lemma fd_le_exp (s : ℝ) : fd s ≤ Real.exp (-(s/2)) := by
  have h1 : (0:ℝ) < 1 + Real.exp (s / 2) := by positivity
  rw [fd, div_le_iff₀ h1, Real.exp_neg]
  have hx : (0:ℝ) < Real.exp (s/2) := Real.exp_pos _
  rw [inv_mul_eq_div, le_div_iff₀ hx]
  nlinarith [hx]

/-! ## Integrability -/

/-- All moments of the shifted kernel converge on any half-line. -/
lemma intOn_pow_fd_shift (k : ℕ) (t c : ℝ) :
    IntegrableOn (fun x => x ^ k * fd (x + t)) (Ioi c) := by
  refine integrable_of_isBigO_exp_neg (b := 1/4) (by norm_num)
    (((continuous_pow k).mul
      (continuous_fd.comp (continuous_id.add continuous_const))).continuousOn) ?_
  refine Asymptotics.IsBigO.of_bound (4^k * k.factorial * Real.exp (-(t/2))) ?_
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with x hx
  have h1 : fd (x + t) ≤ Real.exp (-((x+t)/2)) := fd_le_exp _
  have h2 : ‖x ^ k * fd (x+t)‖ = x ^ k * fd (x+t) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx k) (fd_pos _).le)]
  have h3 : x ^ k ≤ 4^k * k.factorial * Real.exp (x/4) := by
    have hb := Real.pow_div_factorial_le_exp (x/4) (by linarith) k
    have hk : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [div_le_iff₀ hk, div_pow, div_le_iff₀ (by positivity : (0:ℝ) < 4^k)] at hb
    calc x ^ k ≤ Real.exp (x/4) * k.factorial * 4^k := hb
    _ = 4^k * k.factorial * Real.exp (x/4) := by ring
  have hkey : x ^ k * fd (x+t)
      ≤ (4^k * k.factorial) * (Real.exp (x/4) * Real.exp (-((x+t)/2))) := by
    have hmul := mul_le_mul h3 h1 (fd_pos _).le (by positivity)
    calc x ^ k * fd (x+t) ≤ (4^k * k.factorial * Real.exp (x/4)) * Real.exp (-((x+t)/2)) := hmul
    _ = (4^k * k.factorial) * (Real.exp (x/4) * Real.exp (-((x+t)/2))) := by ring
  have hcalc : Real.exp (x/4) * Real.exp (-((x+t)/2))
      = Real.exp (-(t/2)) * Real.exp (-(1/4) * x) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hnorm : ‖Real.exp (-(1/4) * x)‖ = Real.exp (-(1/4) * x) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hcalc] at hkey
  rw [h2, hnorm]
  exact le_trans hkey (le_of_eq (by ring))

lemma intOn_pow_fd (k : ℕ) (c : ℝ) : IntegrableOn (fun x => x ^ k * fd x) (Ioi c) := by
  have h := intOn_pow_fd_shift k 0 c
  simpa using h

lemma intOn_x_fd_shift (t c : ℝ) : IntegrableOn (fun x => x * fd (x + t)) (Ioi c) := by
  have h := intOn_pow_fd_shift 1 t c
  simpa using h

lemma intOn_fd_shift (t c : ℝ) : IntegrableOn (fun x => fd (x + t)) (Ioi c) := by
  have h := intOn_pow_fd_shift 0 t c
  simpa using h

/-- All moments of Mirzakhani's kernel converge on the positive half-line. -/
lemma intOn_pow_mirzKernel (k : ℕ) (t : ℝ) :
    IntegrableOn (fun x => x ^ k * mirzKernel x t) (Ioi 0) := by
  have h1 := intOn_pow_fd_shift k t 0
  have h2 := intOn_pow_fd_shift k (-t) 0
  refine (h1.add h2).congr (Filter.Eventually.of_forall (fun x => ?_))
  show x ^ k * fd (x + t) + x ^ k * fd (x + -t) = x ^ k * mirzKernel x t
  simp only [mirzKernel, sub_eq_add_neg]
  ring

lemma intOn_pow_exp_neg (m n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ m * Real.exp (-(((n:ℝ)+1) * x))) (Ioi 0) := by
  refine integrable_of_isBigO_exp_neg (b := 1/2) (by norm_num)
    (((continuous_pow m).mul ((Real.continuous_exp).comp (by fun_prop))).continuousOn) ?_
  refine Asymptotics.IsBigO.of_bound (2^m * m.factorial) ?_
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with x hx
  have hn1 : (1:ℝ) ≤ (n:ℝ)+1 := by
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have he : Real.exp (-(((n:ℝ)+1) * x)) ≤ Real.exp (-x) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have h3 : x ^ m ≤ 2^m * m.factorial * Real.exp (x/2) := by
    have hb := Real.pow_div_factorial_le_exp (x/2) (by linarith) m
    have hk : (0:ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    rw [div_le_iff₀ hk, div_pow, div_le_iff₀ (by positivity : (0:ℝ) < 2^m)] at hb
    calc x ^ m ≤ Real.exp (x/2) * m.factorial * 2^m := hb
    _ = 2^m * m.factorial * Real.exp (x/2) := by ring
  have hnn : ‖x ^ m * Real.exp (-(((n:ℝ)+1) * x))‖ = x ^ m * Real.exp (-(((n:ℝ)+1) * x)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx m) (Real.exp_pos _).le)]
  have hb2 : ‖Real.exp (-(1/2) * x)‖ = Real.exp (-(1/2) * x) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hkey : x ^ m * Real.exp (-(((n:ℝ)+1) * x))
      ≤ (2^m * m.factorial) * (Real.exp (x/2) * Real.exp (-x)) := by
    have hmul := mul_le_mul h3 he (Real.exp_pos _).le (by positivity)
    calc x ^ m * Real.exp (-(((n:ℝ)+1) * x))
        ≤ (2^m * m.factorial * Real.exp (x/2)) * Real.exp (-x) := hmul
    _ = (2^m * m.factorial) * (Real.exp (x/2) * Real.exp (-x)) := by ring
  have hcalc : Real.exp (x/2) * Real.exp (-x) = Real.exp (-(1/2)*x) := by
    rw [← Real.exp_add]; ring_nf
  rw [hcalc] at hkey
  rw [hnn, hb2]
  exact hkey

/-! ## Fermi–Dirac integrals -/

lemma integral_pow_exp_neg (m n : ℕ) :
    (∫ x in Ioi (0:ℝ), x ^ m * Real.exp (-(((n:ℝ)+1) * x)))
      = (m.factorial : ℝ)/((n:ℝ)+1)^(m+1) := by
  have hr : (0:ℝ) < (n:ℝ)+1 := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (m:ℝ)+1) (r := (n:ℝ)+1)
    (by positivity) hr
  rw [show ((m:ℝ)+1-1) = (m:ℝ) by ring] at h
  rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun t : ℝ => t ^ (m:ℝ) * Real.exp (-(((n:ℝ)+1) * t))) ?_]
  · rw [h, Real.Gamma_nat_eq_factorial,
      show ((m:ℝ)+1) = ((m+1 : ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [div_pow, one_pow]
    field_simp
  · intro t ht
    show t ^ m * Real.exp (-(((n:ℝ)+1) * t)) = t ^ (m:ℝ) * Real.exp (-(((n:ℝ)+1) * t))
    rw [Real.rpow_natCast]

/-- Expansion of the Fermi–Dirac weight into a geometric series. -/
lemma hasSum_fermi_pow (m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => (-1:ℝ)^n * (x^m * Real.exp (-(((n:ℝ)+1) * x))))
      (x^m / (1 + Real.exp x)) := by
  have hr : ‖(-Real.exp (-x))‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-x) < Real.exp 0 := by apply Real.exp_lt_exp.mpr; linarith
    _ = 1 := Real.exp_zero
  have hg := hasSum_geometric_of_norm_lt_one hr
  have h := hg.mul_left (x^m * Real.exp (-x))
  have hex : (0:ℝ) < Real.exp x := Real.exp_pos x
  have key : Real.exp (-x) * (1 + Real.exp (-x))⁻¹ = (1 + Real.exp x)⁻¹ := by
    rw [Real.exp_neg]
    have h2 : (0:ℝ) < 1 + Real.exp x := by positivity
    field_simp
    ring
  have hval : x^m * Real.exp (-x) * (1 - -Real.exp (-x))⁻¹ = x^m / (1 + Real.exp x) := by
    rw [show (1 - -Real.exp (-x)) = 1 + Real.exp (-x) by ring, mul_assoc, key, div_eq_mul_inv]
  rw [hval] at h
  refine h.congr_fun ?_
  intro n
  have hexp : Real.exp (-(((n:ℝ)+1) * x)) = Real.exp (-x) * (Real.exp (-x))^n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf
  rw [hexp, neg_pow]
  ring

/-- The Dirichlet eta value from the corresponding zeta value:
`∑ (-1)ⁿ/(n+1)^p = (1 - 2^{1-p}) ζ(p)`. -/
lemma hasSum_alt_of_hasSum (p : ℕ) {Z : ℝ}
    (hZ : HasSum (fun n : ℕ => 1/((n:ℝ)+1)^p) Z) :
    HasSum (fun n : ℕ => (-1:ℝ)^n/((n:ℝ)+1)^p) ((1 - 2/2^p) * Z) := by
  set c : ℕ → ℝ := fun n => 1 / ((n:ℝ)+1)^p - (-1:ℝ)^n / ((n:ℝ)+1)^p with hc
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h; simp only [] at h; omega
  have hzero : ∀ n ∉ Set.range (fun k : ℕ => 2 * k + 1), c n = 0 := by
    intro n hn
    have hne : ¬ Odd n := by
      intro ho
      obtain ⟨k, hk⟩ := ho
      exact hn ⟨k, by simp only []; omega⟩
    have : Even n := Nat.not_odd_iff_even.mp hne
    simp [hc, this.neg_one_pow]
  have hcomp : HasSum (c ∘ (fun k : ℕ => 2 * k + 1)) ((2/2^p) * Z) := by
    have h := hZ.mul_left (2/2^p)
    refine h.congr_fun ?_
    intro k
    have h1 : ((2 * k + 1 : ℕ) : ℝ) + 1 = 2 * ((k:ℝ) + 1) := by push_cast; ring
    have h2 : (-1:ℝ)^(2*k+1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    show c (2*k+1) = 2/2^p * (1/((k:ℝ)+1)^p)
    rw [hc]
    simp only [h1, h2]
    have hk : ((k:ℝ)+1) ≠ 0 := by positivity
    rw [mul_pow]
    field_simp
    ring
  have hcsum : HasSum c ((2/2^p) * Z) := (hinj.hasSum_iff hzero).mp hcomp
  have h := hZ.sub hcsum
  have heq : (fun n : ℕ => 1/((n:ℝ)+1)^p - c n) = fun n : ℕ => (-1:ℝ)^n/((n:ℝ)+1)^p := by
    funext n; simp [hc]
  rw [heq] at h
  convert h using 1
  ring

/-- `∫₀^∞ xᵐ/(1+eˣ) dx = m! · η(m+1)`. -/
lemma integral_pow_div_one_add_exp (m : ℕ) {S : ℝ}
    (hS : HasSum (fun n : ℕ => (-1:ℝ)^n / ((n:ℝ)+1)^(m+1)) S) :
    (∫ x in Ioi (0:ℝ), x^m / (1 + Real.exp x)) = (m.factorial : ℝ) * S := by
  set F : ℕ → ℝ → ℝ := fun n x => (-1:ℝ)^n * (x^m * Real.exp (-(((n:ℝ)+1) * x))) with hF
  have hF_int : ∀ n, Integrable (F n) (volume.restrict (Ioi (0:ℝ))) := fun n =>
    (intOn_pow_exp_neg m n).const_mul _
  have hnorm : ∀ n, (∫ x in Ioi (0:ℝ), ‖F n x‖) = (m.factorial : ℝ)/((n:ℝ)+1)^(m+1) := by
    intro n
    rw [← integral_pow_exp_neg m n]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    show ‖(-1:ℝ)^n * (x^m * Real.exp (-(((n:ℝ)+1) * x)))‖
        = x^m * Real.exp (-(((n:ℝ)+1) * x))
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [abs_of_pos hx0, abs_of_pos (Real.exp_pos _)]
  have habs : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^(m+1)) := by
    have h := hS.summable.abs
    refine h.congr (fun n => ?_)
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_pos (by positivity : (0:ℝ) < ((n:ℝ)+1)^(m+1))]
  have hsummable : Summable (fun n : ℕ => ∫ x in Ioi (0:ℝ), ‖F n x‖) := by
    refine Summable.congr (habs.mul_left (m.factorial : ℝ)) (fun n => ?_)
    rw [hnorm n]; ring
  have hmain := integral_tsum_of_summable_integral_norm hF_int hsummable
  have hlhs : ∑' n, (∫ x in Ioi (0:ℝ), F n x) = (m.factorial : ℝ) * S := by
    have hterm : ∀ n : ℕ, (∫ x in Ioi (0:ℝ), F n x)
        = (m.factorial : ℝ) * ((-1:ℝ)^n / ((n:ℝ)+1)^(m+1)) := by
      intro n
      rw [hF]
      simp only
      rw [integral_const_mul, integral_pow_exp_neg m n]
      ring
    rw [tsum_congr hterm]
    exact (hS.mul_left (m.factorial : ℝ)).tsum_eq
  rw [hlhs] at hmain
  rw [hmain]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  exact ((hasSum_fermi_pow m hx).tsum_eq).symm

lemma hasSum_inv_pow_two : HasSum (fun n : ℕ => 1 / ((n:ℝ)+1) ^ 2) (π^2/6) := by
  have h := hasSum_zeta_two
  rw [← hasSum_nat_add_iff' 1] at h
  simpa using h

lemma hasSum_inv_pow_four : HasSum (fun n : ℕ => 1 / ((n:ℝ)+1) ^ 4) (π^4/90) := by
  have h := hasSum_zeta_four
  rw [← hasSum_nat_add_iff' 1] at h
  simpa using h

/-- The alternating Euler sum `η(2) = π²/12`. -/
theorem hasSum_alt_zeta_two : HasSum (fun n : ℕ => (-1:ℝ)^n / ((n:ℝ)+1)^2) (π^2/12) := by
  have h := hasSum_alt_of_hasSum 2 hasSum_inv_pow_two
  convert h using 1
  norm_num
  ring

/-- The alternating Euler sum `η(4) = 7π⁴/720`. -/
theorem hasSum_alt_zeta_four : HasSum (fun n : ℕ => (-1:ℝ)^n / ((n:ℝ)+1)^4) (7*π^4/720) := by
  have h := hasSum_alt_of_hasSum 4 hasSum_inv_pow_four
  convert h using 1
  norm_num
  ring

/-- The Fermi–Dirac integral `∫₀^∞ x/(1+eˣ) dx = π²/12`. -/
theorem integral_id_div_one_add_exp :
    (∫ x in Ioi (0:ℝ), x / (1 + Real.exp x)) = π ^ 2 / 12 := by
  have h := integral_pow_div_one_add_exp 1 hasSum_alt_zeta_two
  rw [show ((1:ℕ).factorial : ℝ) = 1 from by norm_num, one_mul] at h
  simpa using h

/-- The Fermi–Dirac integral `∫₀^∞ x³/(1+eˣ) dx = 7π⁴/120`. -/
theorem integral_pow_three_div_one_add_exp :
    (∫ x in Ioi (0:ℝ), x ^ 3 / (1 + Real.exp x)) = 7 * π ^ 4 / 120 := by
  have h := integral_pow_div_one_add_exp 3 hasSum_alt_zeta_four
  rw [show ((3:ℕ).factorial : ℝ) = 6 from by norm_num] at h
  rw [h]
  ring

/-! ## Moments of `fd` -/

lemma integral_pow_mul_fd (m : ℕ) :
    (∫ x in Ioi (0:ℝ), x^m * fd x) = 2^(m+1) * ∫ x in Ioi (0:ℝ), x^m / (1 + Real.exp x) := by
  have h := MeasureTheory.integral_comp_mul_left_Ioi
    (fun y : ℝ => y^m / (1 + Real.exp y)) 0 (b := 1/2) (by norm_num)
  simp only [mul_zero, smul_eq_mul] at h
  have hlhs : (∫ x in Ioi (0:ℝ), (1/2 * x)^m / (1 + Real.exp (1/2 * x)))
      = (1/2)^m * ∫ x in Ioi (0:ℝ), x^m * fd x := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    show (1/2 * x)^m / (1 + Real.exp (1/2 * x)) = (1/2)^m * (x^m * fd x)
    have hp : (0:ℝ) < 1 + Real.exp (1/2 * x) := by positivity
    have hfdx : fd x = 1 / (1 + Real.exp (1/2 * x)) := by
      unfold fd; rw [show x / 2 = 1/2 * x by ring]
    rw [hfdx, mul_pow]
    field_simp
  rw [hlhs] at h
  have hpow : (2:ℝ)^m * (1/2)^m = 1 := by rw [← mul_pow]; norm_num
  calc (∫ x in Ioi (0:ℝ), x^m * fd x)
      = 2^m * ((1/2)^m * ∫ x in Ioi (0:ℝ), x^m * fd x) := by rw [← mul_assoc, hpow, one_mul]
    _ = 2^m * (2 * ∫ x in Ioi (0:ℝ), x^m / (1 + Real.exp x)) := by rw [h]; norm_num
    _ = 2^(m+1) * ∫ x in Ioi (0:ℝ), x^m / (1 + Real.exp x) := by rw [pow_succ]; ring

/-- The first moment `∫₀^∞ x · fd x dx = π²/3`. -/
theorem integral_id_mul_fd : (∫ x in Ioi (0:ℝ), x * fd x) = π ^ 2 / 3 := by
  have h := integral_pow_mul_fd 1
  simp only [pow_one] at h
  rw [integral_id_div_one_add_exp] at h
  rw [h]
  norm_num
  ring

/-- The third moment `∫₀^∞ x³ · fd x dx = 14π⁴/15`. -/
theorem integral_pow_three_mul_fd : (∫ x in Ioi (0:ℝ), x ^ 3 * fd x) = 14 * π ^ 4 / 15 := by
  have h := integral_pow_mul_fd 3
  rw [integral_pow_three_div_one_add_exp] at h
  rw [h]
  norm_num
  ring


lemma moment_one : (∫ y in Ioi (0:ℝ), y ^ 1 * fd y) = π ^ 2 / 3 := by
  simpa using integral_id_mul_fd

lemma moment_three : (∫ y in Ioi (0:ℝ), y ^ 3 * fd y) = 14 * π ^ 4 / 15 :=
  integral_pow_three_mul_fd

/-! ## Translations, splittings and reflections -/

/-- Translation invariance of the integral over a half-line. -/
lemma integral_Ioi_comp_add_right (f : ℝ → ℝ) (c d : ℝ) :
    (∫ x in Ioi c, f (x + d)) = ∫ y in Ioi (c + d), f y := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  rw [← integral_add_right_eq_self (fun y => (Ioi (c+d)).indicator f y) d]
  congr 1
  funext x
  by_cases hx : x ∈ Ioi c
  · have : x + d ∈ Ioi (c + d) := by simp only [mem_Ioi] at *; linarith
    simp [indicator_of_mem, hx, this]
  · have : x + d ∉ Ioi (c + d) := by
      simp only [mem_Ioi] at *; intro h; exact hx (by linarith)
    simp [indicator_of_notMem, hx, this]

/-- Splitting a half-line integral at an intermediate point. -/
lemma integral_Ioi_split (f : ℝ → ℝ) {c d : ℝ} (h : c ≤ d) (hint : IntegrableOn f (Ioi c)) :
    (∫ x in Ioi c, f x) = (∫ x in c..d, f x) + ∫ x in Ioi d, f x := by
  rw [intervalIntegral.integral_of_le h]
  rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set (fun x hx => hx.1))
    (hint.mono_set (fun x hx => lt_of_le_of_lt h hx))]
  rw [Set.Ioc_union_Ioi_eq_Ioi h]

/-- Shifting the argument of the kernel turns the half-line `(0,∞)` into `(d,∞)`. -/
lemma integral_shift_pow (m : ℕ) (d : ℝ) :
    (∫ x in Ioi (0:ℝ), x^m * fd (x + d)) = ∫ y in Ioi d, (y - d)^m * fd y := by
  have h := integral_Ioi_comp_add_right (fun y => (y - d)^m * fd y) 0 d
  simp only [zero_add] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  show x^m * fd (x + d) = (x + d - d)^m * fd (x + d)
  rw [add_sub_cancel_right]

lemma moment_split_pos (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ y in Ioi t, y^k * fd y)
      = (∫ y in Ioi (0:ℝ), y^k * fd y) - ∫ y in (0:ℝ)..t, y^k * fd y := by
  have h := integral_Ioi_split (fun y => y^k * fd y) ht (intOn_pow_fd k 0)
  linarith [h]

lemma moment_split_neg (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ y in Ioi (-t), y^k * fd y)
      = (∫ y in (-t)..(0:ℝ), y^k * fd y) + ∫ y in Ioi (0:ℝ), y^k * fd y :=
  integral_Ioi_split (fun y => y^k * fd y) (by linarith) (intOn_pow_fd k (-t))

/-- Reflection of a moment across the origin, using `fd s + fd (-s) = 1`. -/
lemma interval_refl (k : ℕ) (t : ℝ) :
    (∫ y in (-t)..(0:ℝ), y^k * fd y)
      = (-1)^k * (t^(k+1)/(k+1) - ∫ u in (0:ℝ)..t, u^k * fd u) := by
  have hneg := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := t) (fun y => y^k * fd y)
  rw [neg_zero] at hneg
  rw [← hneg]
  have heq : (∫ u in (0:ℝ)..t, (-u)^k * fd (-u))
      = ∫ u in (0:ℝ)..t, ((-1)^k * u^k - (-1)^k * (u^k * fd u)) := by
    refine intervalIntegral.integral_congr ?_
    intro u hu
    have h : fd (-u) = 1 - fd u := by linarith [fd_add_neg u]
    show (-u)^k * fd (-u) = (-1)^k * u^k - (-1)^k * (u^k * fd u)
    rw [h, neg_pow]
    ring
  rw [heq]
  rw [intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable
        exact continuous_const.mul ((continuous_pow k).mul continuous_fd))]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow]
  simp
  ring

/-- Linearity of the shifted first moment. -/
lemma integral_Ioi_linear_shift (c s : ℝ) :
    (∫ y in Ioi c, (y - s)^1 * fd y)
      = (∫ y in Ioi c, y^1 * fd y) - s*(∫ y in Ioi c, y^0 * fd y) := by
  have h0 := intOn_pow_fd 0 c
  have h1 := intOn_pow_fd 1 c
  have hsub : ∀ (f g : ℝ → ℝ), IntegrableOn f (Ioi c) → IntegrableOn g (Ioi c) →
      (∫ y in Ioi c, (f y - g y)) = (∫ y in Ioi c, f y) - ∫ y in Ioi c, g y :=
    fun f g hf hg => integral_sub hf hg
  have hcm : ∀ (a : ℝ) (f : ℝ → ℝ), (∫ y in Ioi c, a * f y) = a * ∫ y in Ioi c, f y :=
    fun a f => integral_const_mul a f
  calc (∫ y in Ioi c, (y - s)^1 * fd y)
      = ∫ y in Ioi c, (y^1 * fd y - s*(y^0 * fd y)) := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro y hy
        show (y - s)^1 * fd y = y^1 * fd y - s*(y^0 * fd y)
        ring
    _ = (∫ y in Ioi c, y^1 * fd y) - ∫ y in Ioi c, s*(y^0 * fd y) :=
        hsub _ _ h1 (h0.const_mul s)
    _ = (∫ y in Ioi c, y^1 * fd y) - s*(∫ y in Ioi c, y^0 * fd y) := by rw [hcm]

/-- Linearity of the shifted third moment. -/
lemma integral_Ioi_cubic_shift (c s : ℝ) :
    (∫ y in Ioi c, (y - s)^3 * fd y)
      = (∫ y in Ioi c, y^3 * fd y) - 3*s*(∫ y in Ioi c, y^2 * fd y)
        + 3*s^2*(∫ y in Ioi c, y^1 * fd y) - s^3*(∫ y in Ioi c, y^0 * fd y) := by
  have h0 := intOn_pow_fd 0 c
  have h1 := intOn_pow_fd 1 c
  have h2 := intOn_pow_fd 2 c
  have h3 := intOn_pow_fd 3 c
  have hA : IntegrableOn (fun y : ℝ => y^3*fd y - 3*s*(y^2 * fd y)) (Ioi c) :=
    h3.sub (h2.const_mul (3*s))
  have hB : IntegrableOn
      (fun y : ℝ => y^3*fd y - 3*s*(y^2 * fd y) + 3*s^2*(y^1 * fd y)) (Ioi c) :=
    hA.add (h1.const_mul (3*s^2))
  have hsub : ∀ (f g : ℝ → ℝ), IntegrableOn f (Ioi c) → IntegrableOn g (Ioi c) →
      (∫ y in Ioi c, (f y - g y)) = (∫ y in Ioi c, f y) - ∫ y in Ioi c, g y :=
    fun f g hf hg => integral_sub hf hg
  have hadd : ∀ (f g : ℝ → ℝ), IntegrableOn f (Ioi c) → IntegrableOn g (Ioi c) →
      (∫ y in Ioi c, (f y + g y)) = (∫ y in Ioi c, f y) + ∫ y in Ioi c, g y :=
    fun f g hf hg => integral_add hf hg
  have hcm : ∀ (a : ℝ) (f : ℝ → ℝ), (∫ y in Ioi c, a * f y) = a * ∫ y in Ioi c, f y :=
    fun a f => integral_const_mul a f
  calc (∫ y in Ioi c, (y - s)^3 * fd y)
      = ∫ y in Ioi c, ((y^3*fd y - 3*s*(y^2 * fd y) + 3*s^2*(y^1 * fd y))
          - s^3*(y^0 * fd y)) := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro y hy
        show (y - s)^3 * fd y
            = (y^3*fd y - 3*s*(y^2 * fd y) + 3*s^2*(y^1 * fd y)) - s^3*(y^0 * fd y)
        ring
    _ = (∫ y in Ioi c, (y^3*fd y - 3*s*(y^2 * fd y) + 3*s^2*(y^1 * fd y)))
          - ∫ y in Ioi c, s^3*(y^0 * fd y) := hsub _ _ hB (h0.const_mul (s^3))
    _ = ((∫ y in Ioi c, (y^3*fd y - 3*s*(y^2 * fd y))) + ∫ y in Ioi c, 3*s^2*(y^1 * fd y))
          - ∫ y in Ioi c, s^3*(y^0 * fd y) := by
        rw [hadd _ _ hA (h1.const_mul (3*s^2))]
    _ = (((∫ y in Ioi c, y^3*fd y) - ∫ y in Ioi c, 3*s*(y^2 * fd y))
          + ∫ y in Ioi c, 3*s^2*(y^1 * fd y)) - ∫ y in Ioi c, s^3*(y^0 * fd y) := by
        rw [hsub _ _ h3 (h2.const_mul (3*s))]
    _ = (∫ y in Ioi c, y^3 * fd y) - 3*s*(∫ y in Ioi c, y^2 * fd y)
        + 3*s^2*(∫ y in Ioi c, y^1 * fd y) - s^3*(∫ y in Ioi c, y^0 * fd y) := by
        rw [hcm, hcm, hcm]

/-! ## The Mirzakhani transforms `F₁` and `F₃` -/

lemma mirz_split_pow (m : ℕ) (t : ℝ) :
    (∫ x in Ioi (0:ℝ), x^m * mirzKernel x t)
      = (∫ x in Ioi (0:ℝ), x^m * fd (x + t)) + ∫ x in Ioi (0:ℝ), x^m * fd (x + -t) := by
  rw [← integral_add (intOn_pow_fd_shift m t 0) (intOn_pow_fd_shift m (-t) 0)]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  show x^m * mirzKernel x t = x^m * fd (x + t) + x^m * fd (x + -t)
  simp only [mirzKernel, sub_eq_add_neg]
  ring

lemma F1_eq_of_nonneg {t : ℝ} (ht : 0 ≤ t) : F1 t = t ^ 2 / 2 + 2 * π ^ 2 / 3 := by
  have hF : F1 t = ∫ x in Ioi (0:ℝ), x^1 * mirzKernel x t := by
    rw [F1]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    show x * mirzKernel x t = x^1 * mirzKernel x t
    rw [pow_one]
  rw [hF, mirz_split_pow 1 t, integral_shift_pow 1 t, integral_shift_pow 1 (-t),
    integral_Ioi_linear_shift t t, integral_Ioi_linear_shift (-t) (-t),
    moment_split_pos 0 ht, moment_split_pos 1 ht, moment_split_neg 0 ht, moment_split_neg 1 ht,
    interval_refl 0 t, interval_refl 1 t, moment_one]
  norm_num
  ring

lemma F3_eq_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    F3 t = t ^ 4 / 4 + 2 * π ^ 2 * t ^ 2 + 28 * π ^ 4 / 15 := by
  rw [F3, mirz_split_pow 3 t, integral_shift_pow 3 t, integral_shift_pow 3 (-t),
    integral_Ioi_cubic_shift t t, integral_Ioi_cubic_shift (-t) (-t),
    moment_split_pos 0 ht, moment_split_pos 1 ht, moment_split_pos 2 ht, moment_split_pos 3 ht,
    moment_split_neg 0 ht, moment_split_neg 1 ht, moment_split_neg 2 ht, moment_split_neg 3 ht,
    interval_refl 0 t, interval_refl 1 t, interval_refl 2 t, interval_refl 3 t,
    moment_one, moment_three]
  norm_num
  ring

lemma F1_neg (t : ℝ) : F1 (-t) = F1 t := by
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  simp only [mirzKernel, sub_neg_eq_add, ← sub_eq_add_neg]
  ring

lemma F3_neg (t : ℝ) : F3 (-t) = F3 t := by
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  simp only [mirzKernel, sub_neg_eq_add, ← sub_eq_add_neg]
  ring

/-- **Mirzakhani's first integral transform.**  `∫₀^∞ x H(x,t) dx = t²/2 + 2π²/3`. -/
theorem F1_eq (t : ℝ) : F1 t = t ^ 2 / 2 + 2 * π ^ 2 / 3 := by
  rcases le_total 0 t with h | h
  · exact F1_eq_of_nonneg h
  · have h' : (0:ℝ) ≤ -t := by linarith
    have hval := F1_eq_of_nonneg h'
    rw [F1_neg] at hval
    rw [hval]; ring

/-- **Mirzakhani's second integral transform.**
`∫₀^∞ x³ H(x,t) dx = t⁴/4 + 2π²t² + 28π⁴/15`. -/
theorem F3_eq (t : ℝ) : F3 t = t ^ 4 / 4 + 2 * π ^ 2 * t ^ 2 + 28 * π ^ 4 / 15 := by
  rcases le_total 0 t with h | h
  · exact F3_eq_of_nonneg h
  · have h' : (0:ℝ) ≤ -t := by linarith
    have hval := F3_eq_of_nonneg h'
    rw [F3_neg] at hval
    rw [hval]; ring

end Frontier

