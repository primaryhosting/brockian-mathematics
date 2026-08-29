/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`; the header above is
-- the required header text as a plain block comment, and is repeated as a module docstring below.)

import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

open Finset ZMod AddChar

variable {n : ℕ} [NeZero n]

/-- The rotation of the regular `n`-gon acting on complex functions on its vertex set
`ZMod n`: `(rotateVertices f) j = f (j + 1)`. -/
noncomputable def rotateVertices (f : ZMod n → ℂ) : ZMod n → ℂ := fun j => f (j + 1)

/-- The reflection of the regular `n`-gon acting on complex functions on its vertex set
`ZMod n`: `(reflectVertices f) j = f (-j)`. -/
noncomputable def reflectVertices (f : ZMod n → ℂ) : ZMod n → ℂ := fun j => f (-j)

/-- The `k`-th character of the vertex rotation group, `charFun k j = exp (2πi k j / n)`. -/
noncomputable def charFun (k : ZMod n) : ZMod n → ℂ := fun j => ZMod.stdAddChar (k * j)

/-- The projection of a function on the vertices of the regular `n`-gon onto the
isotypic component of the rotation group for the character `charFun k`. -/
noncomputable def isoProj (k : ZMod n) (f : ZMod n → ℂ) : ZMod n → ℂ :=
  fun j => (n : ℂ)⁻¹ * ∑ m : ZMod n, ZMod.stdAddChar (k * (j - m)) * f m

/-- The `k`-th Fourier coefficient of `f`. -/
noncomputable def isoCoeff (k : ZMod n) (f : ZMod n → ℂ) : ℂ :=
  (n : ℂ)⁻¹ * ∑ m : ZMod n, ZMod.stdAddChar (-(k * m)) * f m

lemma cast_card_ne_zero : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)

/-- Orthogonality of the additive characters of `ZMod n`. -/
lemma sum_stdAddChar (t : ZMod n) :
    ∑ i : ZMod n, ZMod.stdAddChar (t * i) = if t = 0 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n h)

/-- The isotypic projection of `f` is the multiple of the character `charFun k` with
coefficient the `k`-th Fourier coefficient of `f`. -/
lemma isoProj_eq_coeff_smul_charFun (k : ZMod n) (f : ZMod n → ℂ) :
    isoProj k f = fun j => isoCoeff k f * charFun k j := by
  funext j
  have h : ∀ m : ZMod n, ZMod.stdAddChar (k * (j - m)) * f m
      = ZMod.stdAddChar (k * j) * (ZMod.stdAddChar (-(k * m)) * f m) := by
    intro m
    have hm : k * (j - m) = k * j + -(k * m) := by ring
    rw [hm, AddChar.map_add_eq_mul, mul_assoc]
  simp only [isoProj, isoCoeff, charFun, h, ← Finset.mul_sum]
  ring

lemma isoProj_smul (c : ℂ) (k : ZMod n) (f : ZMod n → ℂ) :
    isoProj k (fun j => c * f j) = fun j => c * isoProj k f j := by
  funext j
  have h : ∀ m : ZMod n, ZMod.stdAddChar (k * (j - m)) * (c * f m)
      = c * (ZMod.stdAddChar (k * (j - m)) * f m) := fun m => by ring
  simp only [isoProj, h, ← Finset.mul_sum]
  ring

/-- Projection of a character: `isoProj k (charFun l) = charFun k` if `k = l`, and `0`
otherwise. -/
lemma isoProj_charFun (k l : ZMod n) :
    isoProj k (charFun l) = if k = l then charFun k else 0 := by
  funext j
  have hkey : ∀ m : ZMod n, ZMod.stdAddChar (k * (j - m)) * charFun l m
      = ZMod.stdAddChar (k * j) * ZMod.stdAddChar ((l - k) * m) := by
    intro m
    have h1 : k * (j - m) = k * j + -(k * m) := by ring
    have h2 : (l - k) * m = l * m + -(k * m) := by ring
    rw [h1, h2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, charFun]
    ring
  simp only [isoProj, hkey, ← Finset.mul_sum, sum_stdAddChar]
  by_cases h : k = l
  · subst h
    rw [sub_self, if_pos rfl, if_pos rfl]
    simp only [charFun]
    field_simp
    rw [mul_comm, mul_div_assoc, div_self cast_card_ne_zero, mul_one]
  · have hlk : l - k ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    rw [if_neg hlk, if_neg h]
    simp

/-- Fourier inversion: the isotypic projections recover the original function. -/
lemma sum_isoProj (f : ZMod n → ℂ) : ∑ k : ZMod n, isoProj k f = f := by
  funext j
  simp only [Finset.sum_apply]
  have hswap : ∑ k : ZMod n, isoProj k f j
      = (n : ℂ)⁻¹ * ∑ m : ZMod n, (∑ k : ZMod n, ZMod.stdAddChar ((j - m) * k)) * f m := by
    simp only [isoProj, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_comm (j - m) k]
  rw [hswap]
  simp only [sum_stdAddChar]
  rw [Finset.sum_eq_single j]
  · rw [sub_self, if_pos rfl, ← mul_assoc, inv_mul_cancel₀ cast_card_ne_zero, one_mul]
  · intro m _ hm
    have : j - m ≠ 0 := fun hc => hm (sub_eq_zero.mp hc).symm
    rw [if_neg this, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Each isotypic projection is an eigenvector of the rotation, with eigenvalue
`charFun k 1`. -/
lemma rotate_isoProj (k : ZMod n) (f : ZMod n → ℂ) :
    rotateVertices (isoProj k f) = fun j => ZMod.stdAddChar k * isoProj k f j := by
  funext j
  have h : ∀ m : ZMod n, ZMod.stdAddChar (k * (j + 1 - m)) * f m
      = ZMod.stdAddChar k * (ZMod.stdAddChar (k * (j - m)) * f m) := by
    intro m
    have hm : k * (j + 1 - m) = k + k * (j - m) := by ring
    rw [hm, AddChar.map_add_eq_mul, mul_assoc]
  simp only [rotateVertices, isoProj, h, ← Finset.mul_sum]
  ring

/-- The reflection swaps the isotypic components `k` and `-k`. -/
lemma reflect_isoProj (k : ZMod n) (f : ZMod n → ℂ) :
    isoProj k (reflectVertices f) = reflectVertices (isoProj (-k) f) := by
  funext j
  simp only [isoProj, reflectVertices]
  refine congrArg _ ?_
  refine Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ fun m => ?_
  simp only [Equiv.neg_apply]
  congr 2
  ring

/-- Idempotence and orthogonality of the isotypic projections. -/
lemma isoProj_isoProj (k l : ZMod n) (f : ZMod n → ℂ) :
    isoProj k (isoProj l f) = if k = l then isoProj l f else 0 := by
  by_cases h : k = l
  · subst h
    conv_lhs => rw [isoProj_eq_coeff_smul_charFun k f]
    rw [isoProj_smul, isoProj_charFun, if_pos rfl, if_pos rfl]
    exact (isoProj_eq_coeff_smul_charFun k f).symm
  · conv_lhs => rw [isoProj_eq_coeff_smul_charFun l f]
    rw [isoProj_smul, isoProj_charFun, if_neg h, if_neg h]
    funext j
    simp

/--
**Pentagon Pentagon Isotypic Higher N.**

The pentagon (`D₅`) isotypic decomposition generalizes to every regular `n`-gon: for
complex functions on the vertex set `ZMod n` of the regular `n`-gon, the operators
`isoProj k` form a complete family of mutually orthogonal idempotents (Fourier
inversion; idempotence/orthogonality), the image of `isoProj k` is the line spanned by
the rotation character `charFun k` (so `isoProj k f` is a rotation eigenvector with
eigenvalue `charFun k 1`), and the reflection of the dihedral group interchanges the
isotypic components of `k` and `-k`.
-/
theorem PentagonPentagonIsotypicHigherN (n : ℕ) [NeZero n] :
    (∀ f : ZMod n → ℂ, ∑ k : ZMod n, isoProj k f = f) ∧
    (∀ (k : ZMod n) (f : ZMod n → ℂ),
      isoProj k f = fun j => isoCoeff k f * charFun k j) ∧
    (∀ (k : ZMod n) (f : ZMod n → ℂ),
      rotateVertices (isoProj k f) = fun j => ZMod.stdAddChar k * isoProj k f j) ∧
    (∀ (k l : ZMod n) (f : ZMod n → ℂ),
      isoProj k (isoProj l f) = if k = l then isoProj l f else 0) ∧
    (∀ (k : ZMod n) (f : ZMod n → ℂ),
      isoProj k (reflectVertices f) = reflectVertices (isoProj (-k) f)) :=
  ⟨sum_isoProj, isoProj_eq_coeff_smul_charFun, rotate_isoProj, isoProj_isoProj,
    reflect_isoProj⟩

/-- The pentagon (`n = 5`, dihedral group `D₅`) case of
`PentagonPentagonIsotypicHigherN`. -/
theorem PentagonIsotypic :
    (∀ f : ZMod 5 → ℂ, ∑ k : ZMod 5, isoProj k f = f) ∧
    (∀ (k : ZMod 5) (f : ZMod 5 → ℂ),
      isoProj k f = fun j => isoCoeff k f * charFun k j) ∧
    (∀ (k : ZMod 5) (f : ZMod 5 → ℂ),
      rotateVertices (isoProj k f) = fun j => ZMod.stdAddChar k * isoProj k f j) ∧
    (∀ (k l : ZMod 5) (f : ZMod 5 → ℂ),
      isoProj k (isoProj l f) = if k = l then isoProj l f else 0) ∧
    (∀ (k : ZMod 5) (f : ZMod 5 → ℂ),
      isoProj k (reflectVertices f) = reflectVertices (isoProj (-k) f)) :=
  PentagonPentagonIsotypicHigherN 5

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

