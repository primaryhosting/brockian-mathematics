/-
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
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

namespace Chem

open MulAction

attribute [local instance] arrowAction

section

variable {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [Fintype P] [MulAction G P]
variable {C : Type*} [Fintype C]

/-- Burnside's lemma, phrased with `Nat.card`. -/
lemma burnside_natCard {α : Type*} [Fintype α] [MulAction G α] :
    Nat.card (orbitRel.Quotient G α) * Nat.card G
      = ∑ g : G, Nat.card (fixedBy α g) := by
  classical
  letI : ∀ g : G, Fintype (fixedBy α g) := fun g => Fintype.ofFinite _
  letI : Fintype (orbitRel.Quotient G α) := Fintype.ofFinite _
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (α := G) (β := α)
  simp only [← Nat.card_eq_fintype_card] at h
  simpa using h.symm

omit [Fintype G] [Fintype P] [Fintype C] in
/-- A coloring fixed by `g` is constant along the `⟨g⟩`-orbits. -/
lemma fixed_apply_zpow {g : G} {f : P → C} (hf : f ∈ fixedBy (P → C) g) (n : ℤ) (p : P) :
    f ((g ^ n) • p) = f p := by
  have h1 : ∀ q : P, f (g⁻¹ • q) = f q := fun q => congrFun hf q
  have hg : ∀ q : P, f (g • q) = f q := by
    intro q
    have h2 := h1 (g • q)
    rw [inv_smul_smul] at h2
    exact h2.symm
  have hginv : ∀ q : P, f (g⁻¹ • q) = f q := h1
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have : (g ^ ((k : ℤ) + 1)) • p = g • ((g ^ (k : ℤ)) • p) := by
        rw [show ((k : ℤ) + 1) = 1 + (k : ℤ) by ring, zpow_add, zpow_one, mul_smul]
      rw [this, hg, ih]
  | pred k ih =>
      have : (g ^ (-(k : ℤ) - 1)) • p = g⁻¹ • ((g ^ (-(k : ℤ))) • p) := by
        rw [show (-(k : ℤ) - 1) = -1 + -(k : ℤ) by ring, zpow_add, zpow_neg_one, mul_smul]
      rw [this, hginv, ih]

/-- Colorings fixed by `g` correspond to colorings of the set of cycles (orbits) of `g`. -/
noncomputable def fixedByEquivCycleColorings (g : G) :
    fixedBy (P → C) g ≃ (orbitRel.Quotient (Subgroup.zpowers g) P → C) where
  toFun f := Quotient.lift (f : P → C) (by
    rintro a b ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨n, rfl⟩ := hx
    exact fixed_apply_zpow f.2 n b)
  invFun F := ⟨fun p => F (Quotient.mk _ p), by
    funext p
    show F (Quotient.mk _ (g⁻¹ • p)) = F (Quotient.mk _ p)
    congr 1
    exact Quotient.sound ⟨⟨g⁻¹, inv_mem (Subgroup.mem_zpowers g)⟩, rfl⟩⟩
  left_inv f := by ext p; rfl
  right_inv F := by
    funext q
    induction q using Quotient.inductionOn with
    | h p => rfl

omit [Fintype G] [Fintype C] in
/-- The number of colorings fixed by `g` is `|C| ^ (number of cycles of g)`. -/
lemma card_fixedBy_eq (g : G) :
    Nat.card (fixedBy (P → C) g)
      = Nat.card C ^ Nat.card (orbitRel.Quotient (Subgroup.zpowers g) P) := by
  classical
  rw [Nat.card_congr (fixedByEquivCycleColorings (C := C) g)]
  haveI : Finite (orbitRel.Quotient (Subgroup.zpowers g) P) := Quotient.finite _
  exact Nat.card_fun

/-- **Pólya / Burnside isomer count.**  If a symmetry group `G` acts on the set `P` of
substitution positions of a molecular skeleton, and substituents are drawn from a set `C`
of types, then the number of distinct substitution isomers (i.e. orbits of colorings
`P → C` under the skeleton symmetry) times the order of `G` equals the sum over group
elements `g` of `|C|` raised to the number of cycles of `g` on the positions.  Equivalently,
the isomer count is the average `(1/|G|) ∑_g |C|^{c(g)}`: the Pólya cycle index evaluated
at `x_i = |C|`. -/
theorem polya_isomer_count :
    Nat.card (orbitRel.Quotient G (P → C)) * Nat.card G
      = ∑ g : G, Nat.card C ^ Nat.card (orbitRel.Quotient (Subgroup.zpowers g) P) := by
  rw [burnside_natCard (G := G) (α := (P → C))]
  exact Finset.sum_congr rfl fun g _ => card_fixedBy_eq g

/-- The Pólya average form: the number of substitution isomers is the average, over the
symmetry group, of `|C|` raised to the number of cycles of each symmetry. -/
theorem polya_isomer_count_average :
    (Nat.card (orbitRel.Quotient G (P → C)) : ℚ)
      = (∑ g : G, (Nat.card C : ℚ) ^ Nat.card (orbitRel.Quotient (Subgroup.zpowers g) P))
          / (Nat.card G : ℚ) := by
  have hG : (Nat.card G : ℚ) ≠ 0 := by
    have : 0 < Nat.card G := Nat.card_pos
    positivity
  rw [eq_div_iff hG]
  have h := polya_isomer_count (G := G) (P := P) (C := C)
  have := congrArg (fun n : ℕ => (n : ℚ)) h
  push_cast at this
  simpa using this

end

end Chem

