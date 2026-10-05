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

namespace Brockian

open Complex

/-! ## The regular `n`-gon and its dihedral symmetries

We realize the regular `n`-gon in the complex plane as the set of `n`-th roots of unity,
indexed by `ZMod n`.  The dihedral group `DihedralGroup n` acts on the index set `ZMod n`
combinatorially (`r i` rotates the labels by `i`, `sr i` reflects them) and on the plane `ℂ`
geometrically (`r i` is multiplication by `ζ ^ i`, `sr i` is that rotation followed by complex
conjugation).  The main theorem states that the vertex map is equivariant for these two actions,
for every `n ≥ 1`; the classical pentagon (`D₅`) statement is the special case `n = 5`.
-/

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

lemma zeta_isPrimitiveRoot (n : ℕ) [NeZero n] : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n (NeZero.ne n)

lemma zeta_pow_card (n : ℕ) [NeZero n] : zeta n ^ n = 1 := (zeta_isPrimitiveRoot n).pow_eq_one

lemma zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := Complex.exp_ne_zero _

lemma norm_zeta (n : ℕ) : ‖zeta n‖ = 1 := by
  rw [zeta, Complex.norm_exp]
  norm_num [Complex.div_re]

lemma zeta_pow_mod (n : ℕ) [NeZero n] (m : ℕ) : zeta n ^ (m % n) = zeta n ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, zeta_pow_card, one_pow, one_mul]

/-- The `k`-th vertex of the regular `n`-gon, for `k` an index modulo `n`. -/
noncomputable def ngonVertex (n : ℕ) (k : ZMod n) : ℂ := zeta n ^ k.val

lemma ngonVertex_add (n : ℕ) [NeZero n] (a b : ZMod n) :
    ngonVertex n (a + b) = ngonVertex n a * ngonVertex n b := by
  unfold ngonVertex
  rw [ZMod.val_add, zeta_pow_mod, pow_add]

lemma ngonVertex_zero (n : ℕ) [NeZero n] : ngonVertex n 0 = 1 := by
  simp [ngonVertex]

lemma ngonVertex_ne_zero (n : ℕ) (k : ZMod n) : ngonVertex n k ≠ 0 :=
  pow_ne_zero _ (zeta_ne_zero n)

lemma norm_ngonVertex (n : ℕ) (k : ZMod n) : ‖ngonVertex n k‖ = 1 := by
  rw [ngonVertex, norm_pow, norm_zeta, one_pow]

/-- Conjugating a vertex negates its index: the `n`-gon is stable under reflection. -/
lemma conj_ngonVertex (n : ℕ) [NeZero n] (k : ZMod n) :
    (starRingEnd ℂ) (ngonVertex n k) = ngonVertex n (-k) := by
  have h1 : ngonVertex n k * ngonVertex n (-k) = 1 := by
    rw [← ngonVertex_add, add_neg_cancel, ngonVertex_zero]
  have h2 : (ngonVertex n k)⁻¹ = (starRingEnd ℂ) (ngonVertex n k) :=
    Complex.inv_eq_conj (norm_ngonVertex n k)
  rw [← h2, inv_eq_of_mul_eq_one_right h1]

lemma ngonVertex_sub (n : ℕ) [NeZero n] (a b : ZMod n) :
    ngonVertex n (a - b) = ngonVertex n a * (starRingEnd ℂ) (ngonVertex n b) := by
  rw [conj_ngonVertex, ← ngonVertex_add, sub_eq_add_neg]

/-- The vertices of the regular `n`-gon are pairwise distinct. -/
lemma ngonVertex_injective (n : ℕ) [NeZero n] : Function.Injective (ngonVertex n) := by
  intro a b hab
  have hval : a.val = b.val :=
    (zeta_isPrimitiveRoot n).pow_inj (ZMod.val_lt a) (ZMod.val_lt b) hab
  have := congrArg (fun m : ℕ => (m : ZMod n)) hval
  simpa [ZMod.natCast_val, ZMod.cast_id] using this

/-! ### The two actions -/

/-- The combinatorial action of the dihedral group on the vertex labels `ZMod n`:
the rotation `r i` shifts labels by `i`, and the reflection `sr i = s * r ^ i`
sends `k` to `-i - k`. -/
def idxAction (n : ℕ) : DihedralGroup n → ZMod n → ZMod n
  | DihedralGroup.r i, k => k + i
  | DihedralGroup.sr i, k => -i - k

/-- The geometric action of the dihedral group on the plane `ℂ`:
the rotation `r i` is multiplication by `ζ ^ i`, and the reflection `sr i` is that
rotation followed by complex conjugation. -/
noncomputable def planeAction (n : ℕ) : DihedralGroup n → ℂ → ℂ
  | DihedralGroup.r i, z => ngonVertex n i * z
  | DihedralGroup.sr i, z => (starRingEnd ℂ) (ngonVertex n i * z)

lemma idxAction_one (n : ℕ) [NeZero n] (k : ZMod n) : idxAction n 1 k = k := by
  show k + 0 = k
  rw [add_zero]

lemma idxAction_mul (n : ℕ) [NeZero n] (g h : DihedralGroup n) (k : ZMod n) :
    idxAction n (g * h) k = idxAction n g (idxAction n h k) := by
  cases g with
  | r i => cases h with
    | r j => show k + (i + j) = k + j + i; ring
    | sr j => show -(j - i) - k = -j - k + i; ring
  | sr i => cases h with
    | r j => show -(i + j) - k = -i - (k + j); ring
    | sr j => show k + (j - i) = -i - (-j - k); ring

lemma planeAction_one (n : ℕ) [NeZero n] (z : ℂ) : planeAction n 1 z = z := by
  show ngonVertex n 0 * z = z
  rw [ngonVertex_zero, one_mul]

lemma planeAction_mul (n : ℕ) [NeZero n] (g h : DihedralGroup n) (z : ℂ) :
    planeAction n (g * h) z = planeAction n g (planeAction n h z) := by
  cases g with
  | r i => cases h with
    | r j =>
        show ngonVertex n (i + j) * z = ngonVertex n i * (ngonVertex n j * z)
        rw [ngonVertex_add, mul_assoc]
    | sr j =>
        show (starRingEnd ℂ) (ngonVertex n (j - i) * z)
            = ngonVertex n i * (starRingEnd ℂ) (ngonVertex n j * z)
        have hij : (-(j - i) : ZMod n) = i + -j := by ring
        rw [map_mul, map_mul, conj_ngonVertex, conj_ngonVertex, hij, ← mul_assoc,
          ← ngonVertex_add]
  | sr i => cases h with
    | r j =>
        show (starRingEnd ℂ) (ngonVertex n (i + j) * z)
            = (starRingEnd ℂ) (ngonVertex n i * (ngonVertex n j * z))
        rw [ngonVertex_add, mul_assoc]
    | sr j =>
        show ngonVertex n (j - i) * z
            = (starRingEnd ℂ) (ngonVertex n i * (starRingEnd ℂ) (ngonVertex n j * z))
        have hij : (j - i : ZMod n) = -i + j := by ring
        rw [map_mul, map_mul, map_mul, conj_ngonVertex, Complex.conj_conj, Complex.conj_conj,
          hij, ngonVertex_add, mul_assoc]

/-! ### Equivariance -/

/-- **Equivariance of the `n`-gon vertex map.**  For every `n ≥ 1`, every dihedral symmetry
`g` and every label `k`, moving the label and then taking the vertex agrees with taking the
vertex and then moving the point. -/
theorem ngonVertex_equivariant (n : ℕ) [NeZero n] (g : DihedralGroup n) (k : ZMod n) :
    ngonVertex n (idxAction n g k) = planeAction n g (ngonVertex n k) := by
  cases g with
  | r i =>
      show ngonVertex n (k + i) = ngonVertex n i * ngonVertex n k
      rw [ngonVertex_add, mul_comm]
  | sr i =>
      show ngonVertex n (-i - k) = (starRingEnd ℂ) (ngonVertex n i * ngonVertex n k)
      have hik : (-i - k : ZMod n) = -(i + k) := by ring
      rw [← ngonVertex_add, conj_ngonVertex, hik]

/-- **Pentagon pentagon equivariance, general form.**

For every `n ≥ 1`, the regular `n`-gon `k ↦ exp (2 π i k / n)` (indexed by `ZMod n`) carries
a compatible pair of dihedral actions:

* `idxAction n` is an action of `DihedralGroup n` on the labels `ZMod n`;
* `planeAction n` is an action of `DihedralGroup n` on the plane `ℂ` by rotations and
  reflections (each of which preserves the unit circle);
* the vertex map is injective, lands on the unit circle, and is equivariant for these actions.

For `n = 5` this is exactly the D₅ pentagon representation statement. -/
theorem PentagonPentagonEquivarianceGeneral (n : ℕ) [NeZero n] :
    (∀ k : ZMod n, idxAction n 1 k = k) ∧
    (∀ (g h : DihedralGroup n) (k : ZMod n),
        idxAction n (g * h) k = idxAction n g (idxAction n h k)) ∧
    (∀ z : ℂ, planeAction n 1 z = z) ∧
    (∀ (g h : DihedralGroup n) (z : ℂ),
        planeAction n (g * h) z = planeAction n g (planeAction n h z)) ∧
    (∀ (g : DihedralGroup n) (z : ℂ), ‖planeAction n g z‖ = ‖z‖) ∧
    Function.Injective (ngonVertex n) ∧
    (∀ k : ZMod n, ‖ngonVertex n k‖ = 1) ∧
    (∀ (g : DihedralGroup n) (k : ZMod n),
        ngonVertex n (idxAction n g k) = planeAction n g (ngonVertex n k)) := by
  refine ⟨idxAction_one n, idxAction_mul n, planeAction_one n, planeAction_mul n, ?_,
    ngonVertex_injective n, norm_ngonVertex n, ngonVertex_equivariant n⟩
  intro g z
  cases g with
  | r i => show ‖ngonVertex n i * z‖ = ‖z‖; rw [norm_mul, norm_ngonVertex, one_mul]
  | sr i =>
      show ‖(starRingEnd ℂ) (ngonVertex n i * z)‖ = ‖z‖
      rw [RCLike.norm_conj, norm_mul, norm_ngonVertex, one_mul]

/-- The classical pentagon case: `D₅` acting on the regular pentagon. -/
theorem pentagon_equivariance (g : DihedralGroup 5) (k : ZMod 5) :
    ngonVertex 5 (idxAction 5 g k) = planeAction 5 g (ngonVertex 5 k) :=
  ngonVertex_equivariant 5 g k

end Brockian

