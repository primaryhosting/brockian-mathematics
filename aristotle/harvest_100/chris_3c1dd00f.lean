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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

section Mixing

variable {V : Type*} [Fintype V]

/-- The bilinear form associated with a weight matrix `A : V → V → ℝ`. -/
noncomputable def bil (A : V → V → ℝ) (f g : V → ℝ) : ℝ := ∑ u, ∑ v, f u * A u v * g v

lemma bil_symm (A : V → V → ℝ) (hsymm : ∀ u v, A u v = A v u) (f g : V → ℝ) :
    bil A f g = bil A g f := by
  unfold bil
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
  rw [hsymm v u]; ring

lemma bil_add_left (A : V → V → ℝ) (f g h : V → ℝ) :
    bil A (fun x => f x + g x) h = bil A f h + bil A g h := by
  unfold bil
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  ring

lemma bil_add_right (A : V → V → ℝ) (f g h : V → ℝ) :
    bil A f (fun x => g x + h x) = bil A f g + bil A f h := by
  unfold bil
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  ring

lemma bil_smul_left (A : V → V → ℝ) (c : ℝ) (f g : V → ℝ) :
    bil A (fun x => c * f x) g = c * bil A f g := by
  unfold bil
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  ring

lemma bil_smul_right (A : V → V → ℝ) (c : ℝ) (f g : V → ℝ) :
    bil A f (fun x => c * g x) = c * bil A f g := by
  unfold bil
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  ring

/-- Polarization bound: on the space orthogonal to the constants, `|bil A f g|` is bounded
by `lam * (‖f‖² + ‖g‖²) / 2`. -/
lemma bil_le_half (A : V → V → ℝ) (lam : ℝ) (hsymm : ∀ u v, A u v = A v u)
    (hlam : ∀ f : V → ℝ, ∑ v, f v = 0 → |bil A f f| ≤ lam * ∑ v, (f v) ^ 2)
    (f g : V → ℝ) (hf : ∑ v, f v = 0) (hg : ∑ v, g v = 0) :
    |bil A f g| ≤ lam * ((∑ v, (f v) ^ 2) + (∑ v, (g v) ^ 2)) / 2 := by
  have hsum : ∑ v, (f v + g v) = 0 := by
    rw [Finset.sum_add_distrib, hf, hg]; ring
  have hdiff : ∑ v, (f v - g v) = 0 := by
    rw [Finset.sum_sub_distrib, hf, hg]; ring
  have h1 := hlam (fun x => f x + g x) hsum
  have h2 := hlam (fun x => f x - g x) hdiff
  -- expand the two quadratic forms
  have e1 : bil A (fun x => f x + g x) (fun x => f x + g x)
      = bil A f f + bil A f g + (bil A g f + bil A g g) := by
    rw [bil_add_left, bil_add_right, bil_add_right]
  have e2 : bil A (fun x => f x - g x) (fun x => f x - g x)
      = bil A f f - bil A f g - (bil A g f - bil A g g) := by
    have hneg : (fun x => f x - g x) = (fun x => f x + (-1 : ℝ) * g x) := by
      funext x; ring
    rw [hneg, bil_add_left, bil_add_right, bil_add_right, bil_smul_left, bil_smul_right,
      bil_smul_right, bil_smul_left]
    ring
  have hfg : bil A g f = bil A f g := (bil_symm A hsymm g f)
  rw [e1, hfg] at h1
  rw [e2, hfg] at h2
  have q1 : ∑ v, ((fun x => f x + g x) v) ^ 2
      = (∑ v, (f v) ^ 2) + 2 * (∑ v, f v * g v) + (∑ v, (g v) ^ 2) := by
    simp only []
    rw [show (∑ v, (f v + g v) ^ 2)
        = ∑ v, ((f v) ^ 2 + 2 * (f v * g v) + (g v) ^ 2) from
      Finset.sum_congr rfl (fun v _ => by ring)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have q2 : ∑ v, ((fun x => f x - g x) v) ^ 2
      = (∑ v, (f v) ^ 2) - 2 * (∑ v, f v * g v) + (∑ v, (g v) ^ 2) := by
    simp only []
    rw [show (∑ v, (f v - g v) ^ 2)
        = ∑ v, ((f v) ^ 2 - 2 * (f v * g v) + (g v) ^ 2) from
      Finset.sum_congr rfl (fun v _ => by ring)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [q1] at h1
  rw [q2] at h2
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- The key spectral bound: `|bil A f g| ≤ lam * ‖f‖ * ‖g‖` for `f, g` orthogonal to constants. -/
lemma bil_le_mul_sqrt (A : V → V → ℝ) (lam : ℝ) (hsymm : ∀ u v, A u v = A v u)
    (hlam : ∀ f : V → ℝ, ∑ v, f v = 0 → |bil A f f| ≤ lam * ∑ v, (f v) ^ 2)
    (f g : V → ℝ) (hf : ∑ v, f v = 0) (hg : ∑ v, g v = 0) :
    |bil A f g| ≤ lam * Real.sqrt (∑ v, (f v) ^ 2) * Real.sqrt (∑ v, (g v) ^ 2) := by
  set a : ℝ := ∑ v, (f v) ^ 2 with ha
  set b : ℝ := ∑ v, (g v) ^ 2 with hb
  have ha0 : 0 ≤ a := Finset.sum_nonneg (fun v _ => sq_nonneg _)
  have hb0 : 0 ≤ b := Finset.sum_nonneg (fun v _ => sq_nonneg _)
  rcases eq_or_lt_of_le ha0 with ha' | ha'
  · -- a = 0 forces f = 0
    have hf0 : ∀ v, f v = 0 := by
      intro v
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun v (_ : v ∈ (Finset.univ : Finset V)) =>
        sq_nonneg (f v))).1 (ha.symm.trans ha'.symm) v (Finset.mem_univ v)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have : bil A f g = 0 := by
      unfold bil
      refine Finset.sum_eq_zero (fun u _ => Finset.sum_eq_zero (fun v _ => ?_))
      rw [hf0 u]; ring
    rw [this, ← ha']
    simp
  rcases eq_or_lt_of_le hb0 with hb' | hb'
  · have hg0 : ∀ v, g v = 0 := by
      intro v
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun v (_ : v ∈ (Finset.univ : Finset V)) =>
        sq_nonneg (g v))).1 (hb.symm.trans hb'.symm) v (Finset.mem_univ v)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have : bil A f g = 0 := by
      unfold bil
      refine Finset.sum_eq_zero (fun u _ => Finset.sum_eq_zero (fun v _ => ?_))
      rw [hg0 v]; ring
    rw [this, ← hb']
    simp
  · have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha'
    have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb'
    set c : ℝ := Real.sqrt (Real.sqrt b / Real.sqrt a) with hc
    have hc0 : 0 < c := Real.sqrt_pos.2 (div_pos hsb hsa)
    have hc2 : c ^ 2 = Real.sqrt b / Real.sqrt a := by
      rw [hc, Real.sq_sqrt (le_of_lt (div_pos hsb hsa))]
    have key := bil_le_half A lam hsymm hlam (fun x => c * f x) (fun x => c⁻¹ * g x)
      (by rw [← Finset.mul_sum, hf]; ring) (by rw [← Finset.mul_sum, hg]; ring)
    rw [bil_smul_left, bil_smul_right] at key
    have hnorm1 : ∑ v, ((fun x => c * f x) v) ^ 2 = c ^ 2 * a := by
      rw [ha, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    have hnorm2 : ∑ v, ((fun x => c⁻¹ * g x) v) ^ 2 = (c⁻¹) ^ 2 * b := by
      rw [hb, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    rw [hnorm1, hnorm2] at key
    have hcc : c * (c⁻¹ * bil A f g) = bil A f g := by
      field_simp
    rw [hcc] at key
    have hsa2 : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0
    have hsb2 : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb0
    have hcinv : (c⁻¹) ^ 2 = Real.sqrt a / Real.sqrt b := by
      rw [inv_pow, hc2, inv_div]
    have hval : (c ^ 2 * a + (c⁻¹) ^ 2 * b) / 2 = Real.sqrt a * Real.sqrt b := by
      rw [hc2, hcinv]
      field_simp
      nlinarith [hsa2, hsb2]
    calc |bil A f g| ≤ lam * (c ^ 2 * a + (c⁻¹) ^ 2 * b) / 2 := key
      _ = lam * ((c ^ 2 * a + (c⁻¹) ^ 2 * b) / 2) := by ring
      _ = lam * Real.sqrt a * Real.sqrt b := by rw [hval]; ring

lemma bil_one_right (A : V → V → ℝ) (d : ℝ) (hreg : ∀ u, ∑ v, A u v = d) (f : V → ℝ) :
    bil A f (fun _ => 1) = d * ∑ u, f u := by
  unfold bil
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have : ∑ v, f u * A u v * (1 : ℝ) = f u * ∑ v, A u v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  rw [this, hreg u]; ring

lemma bil_indicator (A : V → V → ℝ) (S T : Finset V) :
    bil A (fun v => if v ∈ S then (1 : ℝ) else 0) (fun v => if v ∈ T then (1 : ℝ) else 0)
      = ∑ u ∈ S, ∑ v ∈ T, A u v := by
  unfold bil
  have inner : ∀ u : V, ∑ v, (if u ∈ S then (1 : ℝ) else 0) * A u v *
      (if v ∈ T then (1 : ℝ) else 0)
      = (if u ∈ S then (1 : ℝ) else 0) * ∑ v ∈ T, A u v := by
    intro u
    rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ T)]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have h2 : ∑ v ∈ Finset.univ.filter (fun v => ¬ v ∈ T),
        (if u ∈ S then (1 : ℝ) else 0) * A u v * (if v ∈ T then (1 : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun v hv => ?_)
      rw [if_neg (Finset.mem_filter.1 hv).2]; ring
    rw [h2, add_zero]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [if_pos hv]; ring
  rw [Finset.sum_congr rfl (fun u _ => inner u)]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h3 : ∑ u ∈ Finset.univ.filter (fun u => ¬ u ∈ S),
      (if u ∈ S then (1 : ℝ) else 0) * ∑ v ∈ T, A u v = 0 := by
    refine Finset.sum_eq_zero (fun u hu => ?_)
    rw [if_neg (Finset.mem_filter.1 hu).2]; ring
  rw [h3, add_zero]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  rw [if_pos hu]; ring

lemma bil_shift_zero (A : V → V → ℝ) (d : ℝ) (hsymm : ∀ u v, A u v = A v u)
    (hreg : ∀ u, ∑ v, A u v = d) (p q : V → ℝ) (hp : ∑ v, p v = 0) (hq : ∑ v, q v = 0)
    (al be : ℝ) :
    bil A (fun x => p x + al) (fun x => q x + be)
      = bil A p q + al * be * d * (Fintype.card V : ℝ) := by
  have hone : ∀ (r : V → ℝ) (c : ℝ), (fun x => r x + c) = (fun x => r x + c * (1 : ℝ)) := by
    intro r c; funext x; ring
  rw [hone p al, hone q be]
  rw [bil_add_left, bil_add_right, bil_add_right]
  have h1 : bil A p (fun x => be * (1 : ℝ)) = 0 := by
    rw [show (fun x : V => be * (1 : ℝ)) = (fun x : V => be * (fun _ : V => (1:ℝ)) x) from rfl,
      bil_smul_right, bil_one_right A d hreg, hp]
    ring
  have hq1 : bil A (fun x : V => al * (1 : ℝ)) q = 0 := by
    rw [show (fun x : V => al * (1 : ℝ)) = (fun x : V => al * (fun _ : V => (1:ℝ)) x) from rfl,
      bil_smul_left, bil_symm A hsymm, bil_one_right A d hreg, hq]
    ring
  have h11 : bil A (fun x : V => al * (1 : ℝ)) (fun x : V => be * (1 : ℝ))
      = al * be * d * (Fintype.card V : ℝ) := by
    rw [show (fun x : V => al * (1 : ℝ)) = (fun x : V => al * (fun _ : V => (1:ℝ)) x) from rfl,
      show (fun x : V => be * (1 : ℝ)) = (fun x : V => be * (fun _ : V => (1:ℝ)) x) from rfl,
      bil_smul_left, bil_smul_right, bil_one_right A d hreg]
    simp [Finset.card_univ]
    ring
  rw [h1, hq1, h11]
  ring

lemma sum_indicator_eq_card (S : Finset V) :
    ∑ v, (if v ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp

/-- **Expander mixing lemma** (base case, weighted/matrix form).

Let `A` be a symmetric real matrix indexed by a finite nonempty vertex set `V`, all of whose
row sums equal `d` (a `d`-regular weighted graph, e.g. the adjacency matrix of a `d`-regular
graph), and suppose that the quadratic form of `A` restricted to the space orthogonal to the
all-ones vector is bounded in absolute value by `lam` (i.e. `lam` bounds the second largest
eigenvalue in absolute value). Then for any two sets of vertices `S`, `T`, the number of edges
between them (counted with weights) differs from its "expected" value `d |S| |T| / n` by at
most `lam * √(|S| |T|)`. -/
theorem wigderson_expander_mixing
    {V : Type*} [Fintype V] [Nonempty V]
    (A : V → V → ℝ) (d lam : ℝ)
    (hsymm : ∀ u v, A u v = A v u)
    (hreg : ∀ u, ∑ v, A u v = d)
    (hlam0 : 0 ≤ lam)
    (hlam : ∀ f : V → ℝ, ∑ v, f v = 0 → |∑ u, ∑ v, f u * A u v * f v| ≤ lam * ∑ v, (f v) ^ 2)
    (S T : Finset V) :
    |(∑ u ∈ S, ∑ v ∈ T, A u v) - d * S.card * T.card / (Fintype.card V)|
      ≤ lam * Real.sqrt (S.card * T.card) := by
  have hn0 : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set s : ℝ := (S.card : ℝ) with hs
  set t : ℝ := (T.card : ℝ) with ht
  have hs0 : 0 ≤ s := by positivity
  have ht0 : 0 ≤ t := by positivity
  have hlam' : ∀ f : V → ℝ, ∑ v, f v = 0 → |bil A f f| ≤ lam * ∑ v, (f v) ^ 2 := hlam
  -- the centered indicator vectors
  have hsum_ind : ∀ (R : Finset V), ∑ v, ((if v ∈ R then (1 : ℝ) else 0) - (R.card : ℝ) / n) = 0 := by
    intro R
    rw [Finset.sum_sub_distrib, sum_indicator_eq_card R, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, ← hn]
    field_simp
    ring
  have hsq_ind : ∀ (R : Finset V),
      ∑ v, ((if v ∈ R then (1 : ℝ) else 0) - (R.card : ℝ) / n) ^ 2
        = (R.card : ℝ) - (R.card : ℝ) ^ 2 / n := by
    intro R
    have hpt : ∀ v : V, ((if v ∈ R then (1 : ℝ) else 0) - (R.card : ℝ) / n) ^ 2
        = (if v ∈ R then (1 : ℝ) else 0) * (1 - 2 * ((R.card : ℝ) / n))
          + ((R.card : ℝ) / n) ^ 2 := by
      intro v
      by_cases hv : v ∈ R
      · simp [hv]; ring
      · simp [hv]
    rw [Finset.sum_congr rfl (fun v _ => hpt v), Finset.sum_add_distrib, ← Finset.sum_mul,
      sum_indicator_eq_card R, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← hn]
    field_simp
    ring
  set f : V → ℝ := fun v => (if v ∈ S then (1 : ℝ) else 0) - s / n with hf
  set g : V → ℝ := fun v => (if v ∈ T then (1 : ℝ) else 0) - t / n with hg
  have hfz : ∑ v, f v = 0 := hsum_ind S
  have hgz : ∑ v, g v = 0 := hsum_ind T
  -- decomposition of the edge count
  have hdec : (∑ u ∈ S, ∑ v ∈ T, A u v) = bil A f g + d * s * t / n := by
    have e1 : (fun x => f x + s / n) = (fun v => if v ∈ S then (1 : ℝ) else 0) := by
      funext x; simp [hf]
    have e2 : (fun x => g x + t / n) = (fun v => if v ∈ T then (1 : ℝ) else 0) := by
      funext x; simp [hg]
    have := bil_shift_zero A d hsymm hreg f g hfz hgz (s / n) (t / n)
    rw [e1, e2, bil_indicator] at this
    rw [this, ← hn]
    field_simp
  -- the spectral bound
  have hspec : |bil A f g| ≤ lam * Real.sqrt (∑ v, (f v) ^ 2) * Real.sqrt (∑ v, (g v) ^ 2) :=
    bil_le_mul_sqrt A lam hsymm hlam' f g hfz hgz
  have hnf : ∑ v, (f v) ^ 2 = s - s ^ 2 / n := hsq_ind S
  have hng : ∑ v, (g v) ^ 2 = t - t ^ 2 / n := hsq_ind T
  have hfle : Real.sqrt (∑ v, (f v) ^ 2) ≤ Real.sqrt s := by
    rw [hnf]
    have : 0 ≤ s ^ 2 / n := by positivity
    exact Real.sqrt_le_sqrt (by linarith)
  have hgle : Real.sqrt (∑ v, (g v) ^ 2) ≤ Real.sqrt t := by
    rw [hng]
    have : 0 ≤ t ^ 2 / n := by positivity
    exact Real.sqrt_le_sqrt (by linarith)
  have hfnn : 0 ≤ Real.sqrt (∑ v, (f v) ^ 2) := Real.sqrt_nonneg _
  have hgnn : 0 ≤ Real.sqrt (∑ v, (g v) ^ 2) := Real.sqrt_nonneg _
  have hfinal : lam * Real.sqrt (∑ v, (f v) ^ 2) * Real.sqrt (∑ v, (g v) ^ 2)
      ≤ lam * Real.sqrt (s * t) := by
    rw [Real.sqrt_mul hs0]
    have h1 : lam * Real.sqrt (∑ v, (f v) ^ 2) ≤ lam * Real.sqrt s :=
      mul_le_mul_of_nonneg_left hfle hlam0
    calc lam * Real.sqrt (∑ v, (f v) ^ 2) * Real.sqrt (∑ v, (g v) ^ 2)
        ≤ lam * Real.sqrt s * Real.sqrt (∑ v, (g v) ^ 2) :=
          mul_le_mul_of_nonneg_right h1 hgnn
      _ ≤ lam * Real.sqrt s * Real.sqrt t :=
          mul_le_mul_of_nonneg_left hgle (by positivity)
      _ = lam * (Real.sqrt s * Real.sqrt t) := by ring
  rw [hdec]
  have : bil A f g + d * s * t / n - d * s * t / n = bil A f g := by ring
  calc |bil A f g + d * s * t / n - d * (S.card : ℝ) * (T.card : ℝ) / n|
      = |bil A f g| := by rw [← hs, ← ht, this]
    _ ≤ lam * Real.sqrt (∑ v, (f v) ^ 2) * Real.sqrt (∑ v, (g v) ^ 2) := hspec
    _ ≤ lam * Real.sqrt (s * t) := hfinal

end Mixing

end Frontier

#print axioms Frontier.wigderson_expander_mixing

