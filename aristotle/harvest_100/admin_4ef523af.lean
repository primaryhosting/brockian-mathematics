/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

We generalize the `D₅` (regular pentagon) representation picture to arbitrary regular
`n`-gons.  Concretely, for `n ≠ 0` we build

* `Brockian.zpowRoot n m = exp (2πi·m/n)`, the `n`-th roots of unity indexed by `ℤ`;
* `Brockian.vertex n k`, the vertices of the regular `n`-gon, indexed by `ZMod n`;
* `Brockian.rho n`, the standard two dimensional real representation of
  `DihedralGroup n` realized on `ℂ` (rotations act by multiplication by a root of unity,
  reflections by a root of unity times complex conjugation);
* `Brockian.act n`, the combinatorial action of `DihedralGroup n` on the vertex labels
  `ZMod n`.

The main theorem `Brockian.PentagonPentagonEquivarianceGeneral` states that `rho` is a
representation, that `act` is an action, and that the vertex map
`vertex n : ZMod n → ℂ` is an injective equivariant map between them.  Specializing to
`n = 5` recovers the pentagon statement (`Brockian.pentagon_equivariance`).
-/

namespace Brockian

open Complex

section Aux

/-- `((a.val : ℕ) : ZMod n) = a`. -/
private lemma natCast_val_self {n : ℕ} [NeZero n] (a : ZMod n) :
    ((a.val : ℕ) : ZMod n) = a := by
  simp [ZMod.natCast_val, ZMod.cast_id]

end Aux

/-- `zpowRoot n m = exp (2πi·m/n)`: the `m`-th power of the primitive `n`-th root of
unity `exp (2πi/n)`, indexed by an integer `m`. -/
noncomputable def zpowRoot (n : ℕ) (m : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / (n : ℂ))

lemma zpowRoot_add (n : ℕ) (a b : ℤ) :
    zpowRoot n (a + b) = zpowRoot n a * zpowRoot n b := by
  unfold zpowRoot
  rw [← Complex.exp_add]
  push_cast
  ring_nf

lemma zpowRoot_zero (n : ℕ) : zpowRoot n 0 = 1 := by
  simp [zpowRoot]

/-- The roots of unity only depend on the exponent modulo `n`. -/
lemma zpowRoot_congr {n : ℕ} (hn : n ≠ 0) {a b : ℤ} (h : (a : ZMod n) = (b : ZMod n)) :
    zpowRoot n a = zpowRoot n b := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  obtain ⟨q, hq⟩ : (n : ℤ) ∣ a - b := by
    have h2 : ((a - b : ℤ) : ZMod n) = 0 := by push_cast [h]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
  have ha : a = b + n * q := by omega
  have hone : zpowRoot n ((n : ℤ) * q) = 1 := by
    unfold zpowRoot
    have hrw : (2 * Real.pi * Complex.I * (((n : ℤ) * q : ℤ) : ℂ) / (n : ℂ))
        = (q : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp
    rw [hrw, Complex.exp_int_mul_two_pi_mul_I]
  rw [ha, zpowRoot_add, hone, mul_one]

lemma conj_zpowRoot (n : ℕ) (m : ℤ) :
    (starRingEnd ℂ) (zpowRoot n m) = zpowRoot n (-m) := by
  unfold zpowRoot
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.ext_iff]

/-- The vertices of the regular `n`-gon, labelled by `ZMod n`. -/
noncomputable def vertex (n : ℕ) (k : ZMod n) : ℂ := zpowRoot n (k.val : ℤ)

lemma vertex_eq_zpowRoot {n : ℕ} (hn : n ≠ 0) (m : ℤ) :
    vertex n ((m : ZMod n)) = zpowRoot n m := by
  haveI : NeZero n := ⟨hn⟩
  exact zpowRoot_congr hn (by push_cast [natCast_val_self]; ring)

/-- The standard representation of `DihedralGroup n` on `ℂ ≅ ℝ²`: the rotation `r i` acts
by multiplication by `exp (2πi·i/n)`, and the reflection `sr i` acts by conjugation
followed by multiplication by `exp (-2πi·i/n)`. -/
noncomputable def rho (n : ℕ) : DihedralGroup n → (ℂ → ℂ)
  | .r i => fun z => zpowRoot n (i.val : ℤ) * z
  | .sr i => fun z => zpowRoot n (-(i.val : ℤ)) * (starRingEnd ℂ) z

/-- The combinatorial action of `DihedralGroup n` on the vertex labels `ZMod n`. -/
def act (n : ℕ) : DihedralGroup n → ZMod n → ZMod n
  | .r i => fun k => i + k
  | .sr i => fun k => -i - k

lemma rho_mul {n : ℕ} (hn : n ≠ 0) (g h : DihedralGroup n) :
    rho n (g * h) = rho n g ∘ rho n h := by
  haveI : NeZero n := ⟨hn⟩
  cases g with
  | r i =>
    cases h with
    | r j =>
      funext z
      simp only [rho, DihedralGroup.r_mul_r, Function.comp_apply]
      have key : zpowRoot n (((i + j).val : ℤ))
          = zpowRoot n (i.val : ℤ) * zpowRoot n (j.val : ℤ) := by
        rw [← zpowRoot_add]
        exact zpowRoot_congr hn (by push_cast [natCast_val_self]; ring)
      rw [key, mul_assoc]
    | sr j =>
      funext z
      simp only [rho, DihedralGroup.r_mul_sr, Function.comp_apply]
      have key : zpowRoot n (-((j - i).val : ℤ))
          = zpowRoot n (i.val : ℤ) * zpowRoot n (-(j.val : ℤ)) := by
        rw [← zpowRoot_add]
        exact zpowRoot_congr hn (by push_cast [natCast_val_self]; ring)
      rw [key, mul_assoc]
  | sr i =>
    cases h with
    | r j =>
      funext z
      simp only [rho, DihedralGroup.sr_mul_r, Function.comp_apply]
      rw [map_mul, conj_zpowRoot]
      have key : zpowRoot n (-((i + j).val : ℤ))
          = zpowRoot n (-(i.val : ℤ)) * zpowRoot n (-(j.val : ℤ)) := by
        rw [← zpowRoot_add]
        exact zpowRoot_congr hn (by push_cast [natCast_val_self]; ring)
      rw [key, mul_assoc]
    | sr j =>
      funext z
      simp only [rho, DihedralGroup.sr_mul_sr, Function.comp_apply]
      rw [map_mul, conj_zpowRoot, neg_neg, Complex.conj_conj]
      have key : zpowRoot n ((j - i).val : ℤ)
          = zpowRoot n (-(i.val : ℤ)) * zpowRoot n (j.val : ℤ) := by
        rw [← zpowRoot_add]
        exact zpowRoot_congr hn (by push_cast [natCast_val_self]; ring)
      rw [key, mul_assoc]

lemma act_mul {n : ℕ} (g h : DihedralGroup n) : act n (g * h) = act n g ∘ act n h := by
  cases g with
  | r i => cases h with
    | r j => funext k; simp only [act, DihedralGroup.r_mul_r, Function.comp_apply]; ring
    | sr j => funext k; simp only [act, DihedralGroup.r_mul_sr, Function.comp_apply]; ring
  | sr i => cases h with
    | r j => funext k; simp only [act, DihedralGroup.sr_mul_r, Function.comp_apply]; ring
    | sr j => funext k; simp only [act, DihedralGroup.sr_mul_sr, Function.comp_apply]; ring

lemma rho_one {n : ℕ} : rho n 1 = id := by
  funext z
  show rho n (DihedralGroup.r 0) z = z
  simp [rho, zpowRoot_zero]

lemma act_one {n : ℕ} : act n 1 = id := by
  funext k
  show act n (DihedralGroup.r 0) k = k
  simp [act]

/-- Equivariance: the representation `rho` permutes the vertices of the regular `n`-gon
according to the combinatorial action `act`. -/
lemma rho_vertex {n : ℕ} (hn : n ≠ 0) (g : DihedralGroup n) (k : ZMod n) :
    rho n g (vertex n k) = vertex n (act n g k) := by
  haveI : NeZero n := ⟨hn⟩
  cases g with
  | r i =>
    show zpowRoot n (i.val : ℤ) * zpowRoot n (k.val : ℤ) = zpowRoot n (((i + k).val : ℤ))
    rw [← zpowRoot_add]
    exact zpowRoot_congr hn (by push_cast [natCast_val_self]; ring)
  | sr i =>
    show zpowRoot n (-(i.val : ℤ)) * (starRingEnd ℂ) (zpowRoot n (k.val : ℤ))
        = zpowRoot n (((-i - k).val : ℤ))
    rw [conj_zpowRoot, ← zpowRoot_add]
    exact zpowRoot_congr hn (by push_cast [natCast_val_self]; ring)

/-- The `n` vertices of the regular `n`-gon are pairwise distinct. -/
lemma vertex_injective {n : ℕ} (hn : n ≠ 0) : Function.Injective (vertex n) := by
  haveI : NeZero n := ⟨hn⟩
  intro a b h
  rw [vertex, vertex, zpowRoot, zpowRoot] at h
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨k, hk⟩ := h
  field_simp at hk
  have h2 : ((a.val : ℤ) : ℂ) = ((b.val : ℤ) : ℂ) + (n : ℂ) * (k : ℂ) := by
    push_cast
    push_cast at hk
    linear_combination hk
  have h4 : (a.val : ℤ) = (b.val : ℤ) + n * k := by exact_mod_cast h2
  have hva := ZMod.val_lt a
  have hvb := ZMod.val_lt b
  have hd : (n : ℤ) ∣ ((n : ℤ) * k) := ⟨k, rfl⟩
  have habs : |(n : ℤ) * k| < (n : ℤ) := by rw [abs_lt]; omega
  have hz := Int.eq_zero_of_abs_lt_dvd hd habs
  exact ZMod.val_injective n (by omega)

/-- **Pentagon equivariance, generalized to arbitrary `n`-gons.**

For every `n ≠ 0`:
* `rho n` is a representation of `DihedralGroup n` on `ℂ` (`≅ ℝ²`);
* `act n` is an action of `DihedralGroup n` on the vertex labels `ZMod n`;
* the vertex map `vertex n : ZMod n → ℂ` of the regular `n`-gon is injective and
  equivariant for these two actions.

For `n = 5` this is exactly the `D₅` pentagon statement. -/
theorem PentagonPentagonEquivarianceGeneral (n : ℕ) (hn : n ≠ 0) :
    (rho n 1 = id ∧ ∀ g h : DihedralGroup n, rho n (g * h) = rho n g ∘ rho n h) ∧
    (act n 1 = id ∧ ∀ g h : DihedralGroup n, act n (g * h) = act n g ∘ act n h) ∧
    Function.Injective (vertex n) ∧
    (∀ (g : DihedralGroup n) (k : ZMod n), rho n g (vertex n k) = vertex n (act n g k)) :=
  ⟨⟨rho_one, rho_mul hn⟩, ⟨act_one, act_mul⟩, vertex_injective hn, rho_vertex hn⟩

/-- The pentagon (`n = 5`) case of `PentagonPentagonEquivarianceGeneral`. -/
theorem pentagon_equivariance :
    (rho 5 1 = id ∧ ∀ g h : DihedralGroup 5, rho 5 (g * h) = rho 5 g ∘ rho 5 h) ∧
    (act 5 1 = id ∧ ∀ g h : DihedralGroup 5, act 5 (g * h) = act 5 g ∘ act 5 h) ∧
    Function.Injective (vertex 5) ∧
    (∀ (g : DihedralGroup 5) (k : ZMod 5), rho 5 g (vertex 5 k) = vertex 5 (act 5 g k)) :=
  PentagonPentagonEquivarianceGeneral 5 (by norm_num)

end Brockian

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

