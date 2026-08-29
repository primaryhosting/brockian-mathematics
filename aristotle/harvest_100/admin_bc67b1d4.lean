import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

section

variable {V : Type*} [Fintype V]

/-- The bilinear form `xᵀ A y` associated to a weight matrix `A`. -/
noncomputable def bil (A : V → V → ℝ) (x y : V → ℝ) : ℝ := ∑ i, ∑ j, x i * A i j * y j

/-- The squared Euclidean norm of a vector. -/
noncomputable def qf (x : V → ℝ) : ℝ := ∑ i, (x i) ^ 2

/-- The `0/1` indicator vector of a finite set of vertices. -/
noncomputable def indf (S : Finset V) : V → ℝ := fun i => if i ∈ S then 1 else 0

/-- The all-ones vector. -/
def onev : V → ℝ := fun _ => 1

/-! ### Basic properties of `qf` -/

lemma qf_nonneg (x : V → ℝ) : 0 ≤ qf x :=
  Finset.sum_nonneg fun i _ => sq_nonneg (x i)

lemma qf_eq_zero_iff (x : V → ℝ) : qf x = 0 ↔ ∀ i, x i = 0 := by
  constructor
  · intro h i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).1 h i
      (Finset.mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  · intro h
    simp [qf, h]

lemma qf_smul (c : ℝ) (x : V → ℝ) : qf (fun i => c * x i) = c ^ 2 * qf x := by
  simp only [qf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma qf_add_sub (x y : V → ℝ) :
    qf (fun i => x i + y i) + qf (fun i => x i - y i) = 2 * qf x + 2 * qf y := by
  simp only [qf, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Bilinearity of `bil` -/

lemma bil_smul_left (A : V → V → ℝ) (c : ℝ) (x y : V → ℝ) :
    bil A (fun i => c * x i) y = c * bil A x y := by
  simp only [bil, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma bil_smul_right (A : V → V → ℝ) (c : ℝ) (x y : V → ℝ) :
    bil A x (fun j => c * y j) = c * bil A x y := by
  simp only [bil, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma bil_add_left (A : V → V → ℝ) (x z y : V → ℝ) :
    bil A (fun i => x i + z i) y = bil A x y + bil A z y := by
  simp only [bil, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma bil_add_right (A : V → V → ℝ) (x y z : V → ℝ) :
    bil A x (fun j => y j + z j) = bil A x y + bil A x z := by
  simp only [bil, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma bil_sub_left (A : V → V → ℝ) (x z y : V → ℝ) :
    bil A (fun i => x i - z i) y = bil A x y - bil A z y := by
  simp only [bil, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma bil_sub_right (A : V → V → ℝ) (x y z : V → ℝ) :
    bil A x (fun j => y j - z j) = bil A x y - bil A x z := by
  simp only [bil, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma bil_symm {A : V → V → ℝ} (hsymm : ∀ i j, A i j = A j i) (x y : V → ℝ) :
    bil A x y = bil A y x := by
  simp only [bil]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [hsymm j i]; ring

/-- Polarization: the bilinear form recovered from the quadratic form. -/
lemma bil_polarization {A : V → V → ℝ} (hsymm : ∀ i j, A i j = A j i) (x y : V → ℝ) :
    bil A (fun i => x i + y i) (fun i => x i + y i)
      - bil A (fun i => x i - y i) (fun i => x i - y i) = 4 * bil A x y := by
  have h1 : bil A (fun i => x i + y i) (fun i => x i + y i)
      = bil A x x + bil A x y + (bil A y x + bil A y y) := by
    rw [bil_add_left, bil_add_right, bil_add_right]
  have h2 : bil A (fun i => x i - y i) (fun i => x i - y i)
      = bil A x x - bil A x y - (bil A y x - bil A y y) := by
    rw [bil_sub_left, bil_sub_right, bil_sub_right]
  rw [h1, h2, bil_symm hsymm y x]
  ring

/-! ### From the Rayleigh bound to the bilinear bound -/

/-- Half-and-half bound obtained from the Rayleigh quotient bound by polarization. -/
lemma bil_le_half {A : V → V → ℝ} {lam : ℝ} (hsymm : ∀ i j, A i j = A j i)
    (hlam : ∀ z : V → ℝ, ∑ i, z i = 0 → |bil A z z| ≤ lam * qf z)
    (x y : V → ℝ) (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) :
    |bil A x y| ≤ lam / 2 * (qf x + qf y) := by
  have hsum1 : ∑ i, (x i + y i) = 0 := by rw [Finset.sum_add_distrib, hx, hy]; ring
  have hsum2 : ∑ i, (x i - y i) = 0 := by rw [Finset.sum_sub_distrib, hx, hy]; ring
  have h1 := hlam _ hsum1
  have h2 := hlam _ hsum2
  have hpol := bil_polarization hsymm x y
  have hq := qf_add_sub x y
  have hkey : |4 * bil A x y| ≤ lam * qf (fun i => x i + y i) + lam * qf (fun i => x i - y i) := by
    rw [← hpol]
    calc |bil A (fun i => x i + y i) (fun i => x i + y i)
            - bil A (fun i => x i - y i) (fun i => x i - y i)|
        ≤ |bil A (fun i => x i + y i) (fun i => x i + y i)|
            + |bil A (fun i => x i - y i) (fun i => x i - y i)| := abs_sub _ _
      _ ≤ lam * qf (fun i => x i + y i) + lam * qf (fun i => x i - y i) := add_le_add h1 h2
  rw [abs_mul, show |(4 : ℝ)| = 4 by norm_num] at hkey
  have hrhs : lam * qf (fun i => x i + y i) + lam * qf (fun i => x i - y i)
      = lam * (2 * qf x + 2 * qf y) := by
    rw [← mul_add, hq]
  rw [hrhs] at hkey
  linarith

/-- Bilinear version of the spectral bound: if the Rayleigh quotient of `A` is bounded by
`lam` on the space of vectors summing to zero, then so is the bilinear form. -/
lemma bil_le_sqrt {A : V → V → ℝ} {lam : ℝ} (hsymm : ∀ i j, A i j = A j i) (hlam0 : 0 ≤ lam)
    (hlam : ∀ z : V → ℝ, ∑ i, z i = 0 → |bil A z z| ≤ lam * qf z)
    (x y : V → ℝ) (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) :
    |bil A x y| ≤ lam * Real.sqrt (qf x) * Real.sqrt (qf y) := by
  rcases eq_or_lt_of_le (qf_nonneg x) with hx0 | hx0
  · have hxz : ∀ i, x i = 0 := (qf_eq_zero_iff x).1 hx0.symm
    have hb0 : bil A x y = 0 := by
      simp only [bil, hxz, zero_mul, Finset.sum_const_zero]
    rw [hb0, ← hx0]
    simp
  rcases eq_or_lt_of_le (qf_nonneg y) with hy0 | hy0
  · have hyz : ∀ i, y i = 0 := (qf_eq_zero_iff y).1 hy0.symm
    have hb0 : bil A x y = 0 := by
      simp only [bil, hyz, mul_zero, Finset.sum_const_zero]
    rw [hb0, ← hy0]
    simp
  have hapos : 0 < Real.sqrt (qf x) := Real.sqrt_pos.2 hx0
  have hbpos : 0 < Real.sqrt (qf y) := Real.sqrt_pos.2 hy0
  have ha2 : Real.sqrt (qf x) ^ 2 = qf x := Real.sq_sqrt hx0.le
  have hb2 : Real.sqrt (qf y) ^ 2 = qf y := Real.sq_sqrt hy0.le
  have htpos : 0 < Real.sqrt (qf y) / Real.sqrt (qf x) := div_pos hbpos hapos
  have hsx : ∑ i, (Real.sqrt (qf y) / Real.sqrt (qf x)) * x i = 0 := by
    rw [← Finset.mul_sum, hx, mul_zero]
  have key := bil_le_half hsymm hlam
    (fun i => (Real.sqrt (qf y) / Real.sqrt (qf x)) * x i) y hsx hy
  rw [bil_smul_left, qf_smul, abs_mul, abs_of_pos htpos] at key
  have ht2 : (Real.sqrt (qf y) / Real.sqrt (qf x)) ^ 2 * qf x = qf y := by
    rw [div_pow, ha2, hb2]
    field_simp
  rw [ht2] at key
  have hstep : Real.sqrt (qf y) / Real.sqrt (qf x) * |bil A x y| ≤ lam * qf y := by
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hapos] at hstep
  have hfinal : |bil A x y| ≤ lam * Real.sqrt (qf x) * Real.sqrt (qf y) := by
    have hmul : Real.sqrt (qf y) * Real.sqrt (qf y) = qf y := Real.mul_self_sqrt hy0.le
    have h' : Real.sqrt (qf y) * |bil A x y|
        ≤ Real.sqrt (qf y) * (lam * Real.sqrt (qf x) * Real.sqrt (qf y)) := by
      calc Real.sqrt (qf y) * |bil A x y| ≤ lam * qf y * Real.sqrt (qf x) := hstep
        _ = Real.sqrt (qf y) * (lam * Real.sqrt (qf x) * Real.sqrt (qf y)) := by
            rw [← hmul]; ring
    exact le_of_mul_le_mul_left h' hbpos
  exact hfinal

/-! ### Indicator vectors -/

lemma sum_indicator_mul (S : Finset V) (h : V → ℝ) :
    ∑ j, h j * indf S j = ∑ j ∈ S, h j := by
  have hpt : ∀ j : V, h j * indf S j = if j ∈ S then h j else 0 := by
    intro j
    simp only [indf]
    split <;> simp
  simp only [hpt]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma sum_indf (S : Finset V) : ∑ i, indf S i = (S.card : ℝ) := by
  have := sum_indicator_mul S (fun _ => (1 : ℝ))
  simpa using this

lemma sum_onev : ∑ _i : V, (onev : V → ℝ) _i = (Fintype.card V : ℝ) := by
  simp [onev, Finset.card_univ]

lemma bil_ind_ind (A : V → V → ℝ) (S T : Finset V) :
    bil A (indf S) (indf T) = ∑ i ∈ S, ∑ j ∈ T, A i j := by
  have inner : ∀ i : V, ∑ j, indf S i * A i j * indf T j = (∑ j ∈ T, A i j) * indf S i := by
    intro i
    calc ∑ j, indf S i * A i j * indf T j
        = ∑ j ∈ T, indf S i * A i j := sum_indicator_mul T (fun j => indf S i * A i j)
      _ = (∑ j ∈ T, A i j) * indf S i := by rw [← Finset.mul_sum]; ring
  simp only [bil, inner]
  exact sum_indicator_mul S (fun i => ∑ j ∈ T, A i j)

lemma bil_ind_one {A : V → V → ℝ} {d : ℝ} (hreg : ∀ i, ∑ j, A i j = d) (S : Finset V) :
    bil A (indf S) onev = d * (S.card : ℝ) := by
  have inner : ∀ i : V, ∑ j, indf S i * A i j * onev j = d * indf S i := by
    intro i
    simp only [onev, mul_one, ← Finset.mul_sum, hreg i]
    ring
  simp only [bil, inner, ← Finset.mul_sum, sum_indf]

lemma bil_one_ind {A : V → V → ℝ} {d : ℝ} (hcol : ∀ j, ∑ i, A i j = d) (T : Finset V) :
    bil A onev (indf T) = d * (T.card : ℝ) := by
  have inner : ∀ i : V, ∑ j, onev i * A i j * indf T j = ∑ j ∈ T, A i j := by
    intro i
    have : ∀ j : V, onev i * A i j = A i j := by intro j; simp [onev]
    simp only [this]
    exact sum_indicator_mul T (fun j => A i j)
  simp only [bil, inner]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun j _ => hcol j)]
  simp [mul_comm]

lemma bil_one_one {A : V → V → ℝ} {d : ℝ} (hreg : ∀ i, ∑ j, A i j = d) :
    bil A (onev : V → ℝ) onev = d * (Fintype.card V : ℝ) := by
  have inner : ∀ i : V, ∑ j, onev i * A i j * onev j = d := by
    intro i
    have : ∀ j : V, (onev : V → ℝ) i * A i j * onev j = A i j := by
      intro j; simp [onev]
    simp only [this]
    exact hreg i
  simp only [bil, inner]
  simp [Finset.card_univ, mul_comm]

/-! ### Centred indicator vectors -/

/-- The indicator vector of `S`, centred so as to be orthogonal to the all-ones vector. -/
noncomputable def cind (S : Finset V) : V → ℝ :=
  fun i => indf S i - ((S.card : ℝ) / (Fintype.card V : ℝ)) * onev i

lemma cind_sum (S : Finset V) (hn : (Fintype.card V : ℝ) ≠ 0) : ∑ i, cind S i = 0 := by
  have h : ∑ i, cind S i
      = (∑ i, indf S i) - ((S.card : ℝ) / (Fintype.card V : ℝ)) * ∑ _i : V, (onev : V → ℝ) _i := by
    simp only [cind, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [h, sum_indf, sum_onev]
  field_simp
  ring

lemma cind_qf (S : Finset V) (hn : (Fintype.card V : ℝ) ≠ 0) :
    qf (cind S) = (S.card : ℝ) - (S.card : ℝ) ^ 2 / (Fintype.card V : ℝ) := by
  have key : ∀ i : V, (cind S i) ^ 2
      = indf S i * (1 - 2 * ((S.card : ℝ) / (Fintype.card V : ℝ)))
        + ((S.card : ℝ) / (Fintype.card V : ℝ)) ^ 2 := by
    intro i
    simp only [cind, indf, onev, mul_one]
    split <;> ring
  simp only [qf, key]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_indf, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp
  ring

lemma bil_cind {A : V → V → ℝ} {d : ℝ} (hsymm : ∀ i j, A i j = A j i)
    (hreg : ∀ i, ∑ j, A i j = d) (hn : (Fintype.card V : ℝ) ≠ 0) (S T : Finset V) :
    bil A (cind S) (cind T)
      = (∑ i ∈ S, ∑ j ∈ T, A i j) - d * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ) := by
  have hcol : ∀ j, ∑ i, A i j = d := by
    intro j
    rw [show ∑ i, A i j = ∑ i, A j i from Finset.sum_congr rfl fun i _ => hsymm i j]
    exact hreg j
  have expand : bil A (cind S) (cind T)
      = bil A (indf S) (indf T)
        - ((T.card : ℝ) / (Fintype.card V : ℝ)) * bil A (indf S) onev
        - (((S.card : ℝ) / (Fintype.card V : ℝ)) * bil A onev (indf T)
          - ((S.card : ℝ) / (Fintype.card V : ℝ))
            * (((T.card : ℝ) / (Fintype.card V : ℝ)) * bil A onev onev)) := by
    have hc : ∀ U : Finset V,
        cind U = fun i => indf U i - ((U.card : ℝ) / (Fintype.card V : ℝ)) * onev i :=
      fun U => rfl
    rw [hc S, hc T, bil_sub_left, bil_sub_right, bil_sub_right, bil_smul_left, bil_smul_right,
      bil_smul_right, bil_smul_left]
    ring
  rw [expand, bil_ind_ind, bil_ind_one hreg, bil_one_ind hcol, bil_one_one hreg]
  field_simp
  ring

end

/-- **Expander mixing lemma** (Alon–Chung / Wigderson form).

Let `A` be a symmetric real weight matrix on a finite vertex set `V` which is `d`-regular
(all row sums equal `d`), and suppose that the Rayleigh quotient of `A` is bounded in absolute
value by `lam ≥ 0` on the space of vectors orthogonal to the all-ones vector (i.e. `lam` bounds
the second eigenvalue of `A` in absolute value).  Then for all sets of vertices `S`, `T`, the
number of edges between `S` and `T` deviates from its "expected" value `d |S| |T| / |V|` by at
most `lam * sqrt (|S| |T|)`. -/
theorem wigderson_expander_mixing
    {V : Type*} [Fintype V] (A : V → V → ℝ) (d lam : ℝ)
    (hsymm : ∀ i j, A i j = A j i)
    (hreg : ∀ i, ∑ j, A i j = d)
    (hlam0 : 0 ≤ lam)
    (hlam : ∀ z : V → ℝ, ∑ i, z i = 0 →
      |∑ i, ∑ j, z i * A i j * z j| ≤ lam * ∑ i, (z i) ^ 2)
    (S T : Finset V) :
    |(∑ i ∈ S, ∑ j ∈ T, A i j) - d * S.card * T.card / (Fintype.card V : ℝ)|
      ≤ lam * Real.sqrt (S.card * T.card) := by
  have hlam' : ∀ z : V → ℝ, ∑ i, z i = 0 → |bil A z z| ≤ lam * qf z := hlam
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hcard | hcard
  · have hempty : IsEmpty V := Fintype.card_eq_zero_iff.1 hcard
    have hS : S = ∅ := Finset.eq_empty_of_isEmpty S
    have hT : T = ∅ := Finset.eq_empty_of_isEmpty T
    subst hS; subst hT
    simp
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hcard
  have hn : (Fintype.card V : ℝ) ≠ 0 := ne_of_gt hnpos
  have hmain := bil_le_sqrt hsymm hlam0 hlam' (cind S) (cind T)
    (cind_sum S hn) (cind_sum T hn)
  rw [bil_cind hsymm hreg hn S T] at hmain
  have hqxle : qf (cind S) ≤ (S.card : ℝ) := by
    rw [cind_qf S hn]
    have : 0 ≤ (S.card : ℝ) ^ 2 / (Fintype.card V : ℝ) :=
      div_nonneg (sq_nonneg _) hnpos.le
    linarith
  have hqyle : qf (cind T) ≤ (T.card : ℝ) := by
    rw [cind_qf T hn]
    have : 0 ≤ (T.card : ℝ) ^ 2 / (Fintype.card V : ℝ) :=
      div_nonneg (sq_nonneg _) hnpos.le
    linarith
  have hsx : Real.sqrt (qf (cind S)) ≤ Real.sqrt (S.card : ℝ) := Real.sqrt_le_sqrt hqxle
  have hsy : Real.sqrt (qf (cind T)) ≤ Real.sqrt (T.card : ℝ) := Real.sqrt_le_sqrt hqyle
  have hstep : lam * Real.sqrt (qf (cind S)) * Real.sqrt (qf (cind T))
      ≤ lam * Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ) := by
    have h2' : 0 ≤ lam * Real.sqrt (qf (cind S)) := mul_nonneg hlam0 (Real.sqrt_nonneg _)
    have h1' : lam * Real.sqrt (qf (cind S)) ≤ lam * Real.sqrt (S.card : ℝ) :=
      mul_le_mul_of_nonneg_left hsx hlam0
    calc lam * Real.sqrt (qf (cind S)) * Real.sqrt (qf (cind T))
        ≤ lam * Real.sqrt (qf (cind S)) * Real.sqrt (T.card : ℝ) :=
          mul_le_mul_of_nonneg_left hsy h2'
      _ ≤ lam * Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ) :=
          mul_le_mul_of_nonneg_right h1' (Real.sqrt_nonneg _)
  have hsqrt : Real.sqrt ((S.card : ℝ) * (T.card : ℝ))
      = Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ) :=
    Real.sqrt_mul (by positivity) _
  rw [hsqrt]
  calc |(∑ i ∈ S, ∑ j ∈ T, A i j) - d * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ)|
      ≤ lam * Real.sqrt (qf (cind S)) * Real.sqrt (qf (cind T)) := hmain
    _ ≤ lam * Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ) := hstep
    _ = lam * (Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ)) := by ring

end Frontier

