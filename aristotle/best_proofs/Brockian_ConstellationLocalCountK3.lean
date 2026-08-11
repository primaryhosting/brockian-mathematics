import Mathlib

open scoped BigOperators
open scoped Classical

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Local constellation counts

For a *constellation* (admissible tuple) `H = (h₁, …, h_k)` of integer shifts, the
*local count* at a modulus `p` is the number of residue classes `a mod p` for which none of
`a + h₁, …, a + h_k` is divisible by `p`; equivalently, the number of `a : ZMod p` with
`a + hᵢ ≠ 0` for all `i`.

This file gives the general closed formula (`Brockian.localCount_eq`) and specializes it to
tuples of length one, two and three; the `k = 3` case is
`Brockian.ConstellationLocalCountK3`, with an arithmetic (divisibility) restatement in
`Brockian.ConstellationLocalCountK3_dvd`.
-/

namespace Brockian

/-- The local constellation count of the shift set `H` at modulus `p`: the number of residues
`a : ZMod p` such that `a + h ≠ 0` for every shift `h ∈ H`. -/
noncomputable def localCount (p : ℕ) [NeZero p] (H : Finset ℤ) : ℕ :=
  (Finset.univ.filter (fun a : ZMod p => ∀ h ∈ H, a + (h : ZMod p) ≠ 0)).card

/-- Closed formula for the local count: the forbidden residues are exactly the classes `-h`
for `h ∈ H`, so the count is `p` minus the number of distinct such classes. -/
theorem localCount_eq (p : ℕ) [NeZero p] (H : Finset ℤ) :
    localCount p H = p - (H.image (fun h : ℤ => -(h : ZMod p))).card := by
  have key : (Finset.univ.filter (fun a : ZMod p => ∀ h ∈ H, a + (h : ZMod p) ≠ 0))
      = (H.image (fun h : ℤ => -(h : ZMod p)))ᶜ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
      Finset.mem_image, not_exists, not_and]
    exact ⟨fun h x hx hc => h x hx (by rw [← hc]; ring),
      fun h x hx hc => h x hx (by linear_combination -hc)⟩
  rw [localCount, key, Finset.card_compl, ZMod.card]

/-- The empty constellation: every residue is allowed. -/
theorem ConstellationLocalCountK0 (p : ℕ) [NeZero p] : localCount p (∅ : Finset ℤ) = p := by
  simp [localCount_eq]

/-- A one-element constellation forbids exactly one residue class. -/
theorem ConstellationLocalCountK1 (p : ℕ) [NeZero p] (h1 : ℤ) :
    localCount p {h1} = p - 1 := by
  simp [localCount_eq]

/-- A two-element constellation with distinct shifts mod `p` forbids exactly two classes. -/
theorem ConstellationLocalCountK2 (p : ℕ) [NeZero p] (h1 h2 : ℤ)
    (h12 : (h1 : ZMod p) ≠ (h2 : ZMod p)) :
    localCount p {h1, h2} = p - 2 := by
  rw [localCount_eq]
  congr 1
  rw [show ({h1, h2} : Finset ℤ).image (fun h : ℤ => -(h : ZMod p))
      = {-(h1 : ZMod p), -(h2 : ZMod p)} by simp]
  rw [Finset.card_insert_of_notMem (by simp [neg_inj, h12]), Finset.card_singleton]

/-- **Local constellation count for `k = 3`.** If the three shifts are pairwise distinct modulo
`p`, then exactly three residue classes are forbidden, so the local count is `p - 3`. -/
theorem ConstellationLocalCountK3 (p : ℕ) [NeZero p] (h1 h2 h3 : ℤ)
    (h12 : (h1 : ZMod p) ≠ (h2 : ZMod p)) (h13 : (h1 : ZMod p) ≠ (h3 : ZMod p))
    (h23 : (h2 : ZMod p) ≠ (h3 : ZMod p)) :
    localCount p {h1, h2, h3} = p - 3 := by
  rw [localCount_eq]
  congr 1
  rw [show ({h1, h2, h3} : Finset ℤ).image (fun h : ℤ => -(h : ZMod p))
      = {-(h1 : ZMod p), -(h2 : ZMod p), -(h3 : ZMod p)} by simp]
  rw [Finset.card_insert_of_notMem (by simp [neg_inj, h12, h13]),
    Finset.card_insert_of_notMem (by simp [neg_inj, h23]), Finset.card_singleton]

/-- Distinctness modulo `p` is the same as non-divisibility of the differences. -/
theorem intCast_ne_intCast_iff_not_dvd (p : ℕ) [NeZero p] (a b : ℤ) :
    (a : ZMod p) ≠ (b : ZMod p) ↔ ¬ ((p : ℤ) ∣ (a - b)) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]

/-- Arithmetic form of the `k = 3` local count: if `p` divides none of the pairwise
differences of the shifts, the local count is `p - 3`. -/
theorem ConstellationLocalCountK3_dvd (p : ℕ) [NeZero p] (h1 h2 h3 : ℤ)
    (h12 : ¬ ((p : ℤ) ∣ (h1 - h2))) (h13 : ¬ ((p : ℤ) ∣ (h1 - h3)))
    (h23 : ¬ ((p : ℤ) ∣ (h2 - h3))) :
    localCount p {h1, h2, h3} = p - 3 :=
  ConstellationLocalCountK3 p h1 h2 h3
    ((intCast_ne_intCast_iff_not_dvd p h1 h2).2 h12)
    ((intCast_ne_intCast_iff_not_dvd p h1 h3).2 h13)
    ((intCast_ne_intCast_iff_not_dvd p h2 h3).2 h23)

/-- For a prime `p > 3` a `3`-shift constellation with pairwise distinct shifts mod `p` still
admits a residue class, i.e. the local count is positive. -/
theorem ConstellationLocalCountK3_pos (p : ℕ) [NeZero p] (hp : 3 < p) (h1 h2 h3 : ℤ)
    (h12 : (h1 : ZMod p) ≠ (h2 : ZMod p)) (h13 : (h1 : ZMod p) ≠ (h3 : ZMod p))
    (h23 : (h2 : ZMod p) ≠ (h3 : ZMod p)) :
    0 < localCount p {h1, h2, h3} := by
  rw [ConstellationLocalCountK3 p h1 h2 h3 h12 h13 h23]
  omega

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

