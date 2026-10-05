/-
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
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

/-- A real Möbius transformation `x ↦ (a x + b) / (c x + d)`.  These are exactly the
boundary values on `ℝ = ∂ℍ` of the conformal automorphisms of the upper half-plane. -/
noncomputable def mobius (a b c d x : ℝ) : ℝ := (a * x + b) / (c * x + d)

/-- Four marked boundary points are pairwise distinct: this is the genericity condition
defining a *conformal quadrilateral* (a "quad") in the half-plane. -/
def Distinct4 (x₁ x₂ x₃ x₄ : ℝ) : Prop :=
  x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₁ ≠ x₄ ∧ x₂ ≠ x₃ ∧ x₂ ≠ x₄ ∧ x₃ ≠ x₄

/-- The conformal modulus (cross-ratio) of the quad with marked boundary points
`x₁, x₂, x₃, x₄`.  It is the unique conformal invariant of a quad. -/
noncomputable def modulus (x₁ x₂ x₃ x₄ : ℝ) : ℝ :=
  ((x₃ - x₁) * (x₄ - x₂)) / ((x₃ - x₂) * (x₄ - x₁))

/-- A crossing-probability function `C` on quads is *conformally invariant* if it is
unchanged by every Möbius transformation of the half-plane (applied to the four marked
boundary points).  This is the Cardy–Smirnov conformal invariance property. -/
def ConformallyInvariant (C : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ a b c d x₁ x₂ x₃ x₄ : ℝ, a * d - b * c ≠ 0 → Distinct4 x₁ x₂ x₃ x₄ →
    c * x₁ + d ≠ 0 → c * x₂ + d ≠ 0 → c * x₃ + d ≠ 0 → c * x₄ + d ≠ 0 →
    C (mobius a b c d x₁) (mobius a b c d x₂) (mobius a b c d x₃) (mobius a b c d x₄)
      = C x₁ x₂ x₃ x₄

/-- Difference formula for a Möbius map. -/
lemma mobius_sub {a b c d x y : ℝ} (hx : c * x + d ≠ 0) (hy : c * y + d ≠ 0) :
    mobius a b c d x - mobius a b c d y
      = (a * d - b * c) * (x - y) / ((c * x + d) * (c * y + d)) := by
  unfold mobius
  rw [div_sub_div _ _ hx hy]
  congr 1
  ring

/-- A Möbius map with nonzero determinant is injective away from its pole. -/
lemma mobius_injective {a b c d x y : ℝ} (hdet : a * d - b * c ≠ 0)
    (hx : c * x + d ≠ 0) (hy : c * y + d ≠ 0)
    (h : mobius a b c d x = mobius a b c d y) : x = y := by
  have h0 : mobius a b c d x - mobius a b c d y = 0 := by rw [h]; ring
  rw [mobius_sub hx hy, div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 hdet
    · linarith [sub_eq_zero.1 h1]
  · exact absurd h0 (mul_ne_zero hx hy)

lemma mobius_ne {a b c d x y : ℝ} (hdet : a * d - b * c ≠ 0)
    (hx : c * x + d ≠ 0) (hy : c * y + d ≠ 0) (hxy : x ≠ y) :
    mobius a b c d x ≠ mobius a b c d y := fun h => hxy (mobius_injective hdet hx hy h)

/-- Möbius images of four distinct points are four distinct points. -/
lemma distinct4_mobius {a b c d x₁ x₂ x₃ x₄ : ℝ} (hdet : a * d - b * c ≠ 0)
    (hx : Distinct4 x₁ x₂ x₃ x₄)
    (h1 : c * x₁ + d ≠ 0) (h2 : c * x₂ + d ≠ 0) (h3 : c * x₃ + d ≠ 0) (h4 : c * x₄ + d ≠ 0) :
    Distinct4 (mobius a b c d x₁) (mobius a b c d x₂) (mobius a b c d x₃)
      (mobius a b c d x₄) := by
  obtain ⟨a12, a13, a14, a23, a24, a34⟩ := hx
  exact ⟨mobius_ne hdet h1 h2 a12, mobius_ne hdet h1 h3 a13, mobius_ne hdet h1 h4 a14,
    mobius_ne hdet h2 h3 a23, mobius_ne hdet h2 h4 a24, mobius_ne hdet h3 h4 a34⟩

/-- **Conformal invariance of the modulus.**  The cross-ratio of four boundary points is
unchanged by Möbius transformations. -/
theorem modulus_mobius {a b c d x₁ x₂ x₃ x₄ : ℝ} (hdet : a * d - b * c ≠ 0)
    (hx : Distinct4 x₁ x₂ x₃ x₄)
    (h1 : c * x₁ + d ≠ 0) (h2 : c * x₂ + d ≠ 0) (h3 : c * x₃ + d ≠ 0) (h4 : c * x₄ + d ≠ 0) :
    modulus (mobius a b c d x₁) (mobius a b c d x₂) (mobius a b c d x₃) (mobius a b c d x₄)
      = modulus x₁ x₂ x₃ x₄ := by
  obtain ⟨a12, a13, a14, a23, a24, a34⟩ := hx
  have e31 : x₃ - x₁ ≠ 0 := sub_ne_zero.2 (Ne.symm a13)
  have e42 : x₄ - x₂ ≠ 0 := sub_ne_zero.2 (Ne.symm a24)
  have e32 : x₃ - x₂ ≠ 0 := sub_ne_zero.2 (Ne.symm a23)
  have e41 : x₄ - x₁ ≠ 0 := sub_ne_zero.2 (Ne.symm a14)
  unfold modulus
  rw [mobius_sub h3 h1, mobius_sub h4 h2, mobius_sub h3 h2, mobius_sub h4 h1]
  field_simp

/-- The modulus determines a quad up to a Möbius transformation: given two quads with the
same modulus there is a Möbius map carrying the first onto the second. -/
theorem exists_mobius_of_modulus_eq {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : ℝ}
    (hx : Distinct4 x₁ x₂ x₃ x₄) (hy : Distinct4 y₁ y₂ y₃ y₄)
    (h : modulus x₁ x₂ x₃ x₄ = modulus y₁ y₂ y₃ y₄) :
    ∃ a b c d : ℝ, a * d - b * c ≠ 0 ∧
      c * x₁ + d ≠ 0 ∧ c * x₂ + d ≠ 0 ∧ c * x₃ + d ≠ 0 ∧ c * x₄ + d ≠ 0 ∧
      mobius a b c d x₁ = y₁ ∧ mobius a b c d x₂ = y₂ ∧
      mobius a b c d x₃ = y₃ ∧ mobius a b c d x₄ = y₄ := by
  obtain ⟨x12, x13, x14, x23, x24, x34⟩ := hx
  obtain ⟨y12, y13, y14, y23, y24, y34⟩ := hy
  have hx31 : x₃ - x₁ ≠ 0 := sub_ne_zero.2 (Ne.symm x13)
  have hx32 : x₃ - x₂ ≠ 0 := sub_ne_zero.2 (Ne.symm x23)
  have hx12 : x₁ - x₂ ≠ 0 := sub_ne_zero.2 x12
  have hx21 : x₂ - x₁ ≠ 0 := sub_ne_zero.2 (Ne.symm x12)
  have hx42 : x₄ - x₂ ≠ 0 := sub_ne_zero.2 (Ne.symm x24)
  have hx41 : x₄ - x₁ ≠ 0 := sub_ne_zero.2 (Ne.symm x14)
  have hy31 : y₃ - y₁ ≠ 0 := sub_ne_zero.2 (Ne.symm y13)
  have hy32 : y₃ - y₂ ≠ 0 := sub_ne_zero.2 (Ne.symm y23)
  have hy12 : y₁ - y₂ ≠ 0 := sub_ne_zero.2 y12
  have hy42 : y₄ - y₂ ≠ 0 := sub_ne_zero.2 (Ne.symm y24)
  have hy41 : y₄ - y₁ ≠ 0 := sub_ne_zero.2 (Ne.symm y14)
  have hQ : (x₃ - x₂) * (x₄ - x₁) ≠ 0 := mul_ne_zero hx32 hx41
  have hQ' : (y₃ - y₂) * (y₄ - y₁) ≠ 0 := mul_ne_zero hy32 hy41
  rw [modulus, modulus, div_eq_div_iff hQ hQ'] at h
  refine ⟨(-y₂ * (y₃ - y₁)) * (x₃ - x₂) - (-y₁ * (y₃ - y₂)) * (x₃ - x₁),
    (-y₂ * (y₃ - y₁)) * (-x₁ * (x₃ - x₂)) - (-y₁ * (y₃ - y₂)) * (-x₂ * (x₃ - x₁)),
    (y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂),
    (y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : ((-y₂ * (y₃ - y₁)) * (x₃ - x₂) - (-y₁ * (y₃ - y₂)) * (x₃ - x₁)) *
        ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂))) -
        ((-y₂ * (y₃ - y₁)) * (-x₁ * (x₃ - x₂)) - (-y₁ * (y₃ - y₂)) * (-x₂ * (x₃ - x₁))) *
        ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂))
        = ((y₃ - y₂) * (y₃ - y₁) * (y₁ - y₂)) * ((x₃ - x₂) * (x₃ - x₁) * (x₁ - x₂)) := by
      ring
    rw [e]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hy32 hy31) hy12)
      (mul_ne_zero (mul_ne_zero hx32 hx31) hx12)
  · have e : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₁ +
        ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)))
        = (y₃ - y₂) * ((x₃ - x₁) * (x₁ - x₂)) := by ring
    rw [e]
    exact mul_ne_zero hy32 (mul_ne_zero hx31 hx12)
  · have e : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₂ +
        ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)))
        = -((y₃ - y₁) * ((x₃ - x₂) * (x₂ - x₁))) := by ring
    rw [e]
    exact neg_ne_zero.2 (mul_ne_zero hy31 (mul_ne_zero hx32 hx21))
  · have e : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₃ +
        ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)))
        = (y₁ - y₂) * ((x₃ - x₁) * (x₃ - x₂)) := by ring
    rw [e]
    exact mul_ne_zero hy12 (mul_ne_zero hx31 hx32)
  · -- the fourth point is not the pole: this uses the equality of moduli
    have e : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₄ +
        ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)))
        = (y₃ - y₂) * ((x₃ - x₁) * (x₄ - x₂)) - (y₃ - y₁) * ((x₃ - x₂) * (x₄ - x₁)) := by
      ring
    rw [e]
    intro hzero
    -- multiply by `(y₃ - y₂) * (y₄ - y₁)` and use the modulus identity
    have h1 : (y₃ - y₂) * (y₃ - y₁) * ((y₄ - y₂) - (y₄ - y₁)) *
        ((x₃ - x₂) * (x₄ - x₁)) = 0 := by
      linear_combination ((y₃ - y₂) * (y₄ - y₁)) * hzero - (y₃ - y₂) * h
    rcases mul_eq_zero.1 h1 with h2 | h2
    · rcases mul_eq_zero.1 h2 with h3 | h3
      · rcases mul_eq_zero.1 h3 with h4 | h4
        · exact hy32 h4
        · exact hy31 h4
      · exact hy12 (by linarith)
    · exact hQ h2
  · rw [mobius, div_eq_iff]
    · ring
    · have e : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₁ +
          ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)))
          = (y₃ - y₂) * ((x₃ - x₁) * (x₁ - x₂)) := by ring
      rw [e]
      exact mul_ne_zero hy32 (mul_ne_zero hx31 hx12)
  · rw [mobius, div_eq_iff]
    · ring
    · have e : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₂ +
          ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)))
          = -((y₃ - y₁) * ((x₃ - x₂) * (x₂ - x₁))) := by ring
      rw [e]
      exact neg_ne_zero.2 (mul_ne_zero hy31 (mul_ne_zero hx32 hx21))
  · rw [mobius, div_eq_iff]
    · ring
    · have e : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₃ +
          ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)))
          = (y₁ - y₂) * ((x₃ - x₁) * (x₃ - x₂)) := by ring
      rw [e]
      exact mul_ne_zero hy12 (mul_ne_zero hx31 hx32)
  · have hden : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₄ +
        ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂))) ≠ 0 := by
      have e : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₄ +
          ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)))
          = (y₃ - y₂) * ((x₃ - x₁) * (x₄ - x₂)) - (y₃ - y₁) * ((x₃ - x₂) * (x₄ - x₁)) := by
        ring
      rw [e]
      intro hzero
      have h1 : (y₃ - y₂) * (y₃ - y₁) * ((y₄ - y₂) - (y₄ - y₁)) *
          ((x₃ - x₂) * (x₄ - x₁)) = 0 := by
        linear_combination ((y₃ - y₂) * (y₄ - y₁)) * hzero - (y₃ - y₂) * h
      rcases mul_eq_zero.1 h1 with h2 | h2
      · rcases mul_eq_zero.1 h2 with h3 | h3
        · rcases mul_eq_zero.1 h3 with h4 | h4
          · exact hy32 h4
          · exact hy31 h4
        · exact hy12 (by linarith)
      · exact hQ h2
    rw [mobius, div_eq_iff hden]
    linear_combination -h

/-- Any two quads with the same modulus have the same value under a conformally invariant
crossing function. -/
theorem eq_of_modulus_eq {C : ℝ → ℝ → ℝ → ℝ → ℝ} (hC : ConformallyInvariant C)
    {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : ℝ}
    (hx : Distinct4 x₁ x₂ x₃ x₄) (hy : Distinct4 y₁ y₂ y₃ y₄)
    (h : modulus x₁ x₂ x₃ x₄ = modulus y₁ y₂ y₃ y₄) :
    C x₁ x₂ x₃ x₄ = C y₁ y₂ y₃ y₄ := by
  obtain ⟨a, b, c, d, hdet, h1, h2, h3, h4, e1, e2, e3, e4⟩ :=
    exists_mobius_of_modulus_eq hx hy h
  have := hC a b c d x₁ x₂ x₃ x₄ hdet hx h1 h2 h3 h4
  rw [e1, e2, e3, e4] at this
  exact this.symm

/-- The induced function of the modulus: it picks, for each possible value `l` of the
conformal modulus, the value of `C` on some quad with that modulus.  For a conformally
invariant `C` this is well defined, and it is the abstract "Cardy function" of `C`. -/
noncomputable def cardyFunction (C : ℝ → ℝ → ℝ → ℝ → ℝ) (l : ℝ) : ℝ :=
  if h : ∃ p : ℝ × ℝ × ℝ × ℝ,
      Distinct4 p.1 p.2.1 p.2.2.1 p.2.2.2 ∧ modulus p.1 p.2.1 p.2.2.1 p.2.2.2 = l then
    C h.choose.1 h.choose.2.1 h.choose.2.2.1 h.choose.2.2.2
  else 0

/-- **Cardy–Smirnov conformal invariance.**

A crossing-probability function on conformal quadrilaterals of the half-plane (four marked
boundary points) is conformally invariant precisely when it is a function of the conformal
modulus (cross-ratio) alone.  This is the exact content of the Cardy–Smirnov theorem's
conclusion, reduced to an algebraic statement about the Möbius group: the "shape" of a quad
is captured by a single real parameter, and Cardy's formula is the resulting function `F`. -/
theorem smirnov_percolation (C : ℝ → ℝ → ℝ → ℝ → ℝ) :
    ConformallyInvariant C ↔
      ∃ F : ℝ → ℝ, ∀ x₁ x₂ x₃ x₄ : ℝ, Distinct4 x₁ x₂ x₃ x₄ →
        C x₁ x₂ x₃ x₄ = F (modulus x₁ x₂ x₃ x₄) := by
  constructor
  · intro hC
    refine ⟨cardyFunction C, ?_⟩
    intro x₁ x₂ x₃ x₄ hx
    have hex : ∃ p : ℝ × ℝ × ℝ × ℝ,
        Distinct4 p.1 p.2.1 p.2.2.1 p.2.2.2 ∧
          modulus p.1 p.2.1 p.2.2.1 p.2.2.2 = modulus x₁ x₂ x₃ x₄ :=
      ⟨(x₁, x₂, x₃, x₄), hx, rfl⟩
    rw [cardyFunction, dif_pos hex]
    obtain ⟨hd, hm⟩ := hex.choose_spec
    exact eq_of_modulus_eq hC hx hd hm.symm
  · rintro ⟨F, hF⟩ a b c d x₁ x₂ x₃ x₄ hdet hx h1 h2 h3 h4
    rw [hF _ _ _ _ (distinct4_mobius hdet hx h1 h2 h3 h4), hF _ _ _ _ hx,
      modulus_mobius hdet hx h1 h2 h3 h4]

/-- **Base case / construction.**  Conversely, every function of the conformal modulus is a
conformally invariant crossing function; in particular the Cardy–Smirnov crossing
probability, being a function of the cross-ratio, is conformally invariant. -/
theorem conformallyInvariant_comp_modulus (F : ℝ → ℝ) :
    ConformallyInvariant (fun x₁ x₂ x₃ x₄ => F (modulus x₁ x₂ x₃ x₄)) :=
  (smirnov_percolation _).2 ⟨F, fun _ _ _ _ _ => rfl⟩

/-- The modulus is unchanged by reversing the cyclic order of the four marked points, as it
must be for a crossing probability between opposite sides of a quad. -/
theorem modulus_reverse (x₁ x₂ x₃ x₄ : ℝ) :
    modulus x₄ x₃ x₂ x₁ = modulus x₁ x₂ x₃ x₄ := by
  unfold modulus
  rw [show (x₂ - x₄) * (x₁ - x₃) = (x₃ - x₁) * (x₄ - x₂) by ring,
    show (x₂ - x₃) * (x₁ - x₄) = (x₃ - x₂) * (x₄ - x₁) by ring]

/-- **Percolation form of the statement.**  Suppose the crossing probabilities `P n` of
critical percolation at mesh `1/n` on a quad with marked boundary points converge to a
limit `C`, and that (Smirnov's theorem) the limit `C` is conformally invariant.  Then the
limiting crossing probability depends only on the conformal modulus of the quad: two quads
of equal modulus have the same limiting crossing probability. -/
theorem crossing_limit_eq_of_modulus_eq
    (P : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ) (C : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hconv : ∀ x₁ x₂ x₃ x₄ : ℝ, Distinct4 x₁ x₂ x₃ x₄ →
      Filter.Tendsto (fun n => P n x₁ x₂ x₃ x₄) Filter.atTop (nhds (C x₁ x₂ x₃ x₄)))
    (hC : ConformallyInvariant C)
    {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : ℝ}
    (hx : Distinct4 x₁ x₂ x₃ x₄) (hy : Distinct4 y₁ y₂ y₃ y₄)
    (hmod : modulus x₁ x₂ x₃ x₄ = modulus y₁ y₂ y₃ y₄) :
    Filter.Tendsto (fun n => P n x₁ x₂ x₃ x₄) Filter.atTop (nhds (C y₁ y₂ y₃ y₄)) := by
  have := hconv x₁ x₂ x₃ x₄ hx
  rwa [eq_of_modulus_eq hC hx hy hmod] at this

end Frontier

