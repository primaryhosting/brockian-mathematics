/-
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
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

namespace Zeta23Obstruction

/-!
## Abstract finite-dimensional model

We model the "fixed-kernel pointwise-discard linear certificate" chain abstractly.

* A *configuration* is a finite collection of *species*, each carrying a nonnegative
  *weight* and sitting at a *deep point* of the real line.
* A *certificate* fixes once and for all a kernel `R : ℝ → ℝ`, together with a
  *shallow region* `shallow ⊆ ℝ` on which the kernel is known to be nonnegative
  (`h_pos`).  This is the only positivity input the certificate has.
* The certificate's chain evaluates the *linear charge functional*
  `charge R c = ∑ i, weight i * R (deep i)` and then performs a **pointwise discard**:
  each individual species contribution is thrown away as nonnegative.  This step is
  legitimate exactly when the *termwise bound* `0 ≤ weight i * R (deep i)` holds.
* *Validity* of the certificate is its ability to run this discard against every
  **deep-pair configuration**: two species with strictly positive weights placed at
  arbitrary (deep) points.

The content of the obstruction is purely about the quantifier structure: the kernel is
fixed *before* the configuration is chosen, and the discard is pointwise, so a single
deep point `z` with `R z < 0` — the repaired witness — already destroys validity, no
matter how large the shallow region on which `h_pos` holds.
-/

/-- Configuration data for `n` species: a nonnegative weight and a deep point for each. -/
structure Config (n : ℕ) where
  /-- The weight ("charge multiplicity") carried by each species. -/
  weight : Fin n → ℝ
  /-- The deep point at which each species is evaluated. -/
  deep : Fin n → ℝ
  /-- Weights are nonnegative. -/
  weight_nonneg : ∀ i, 0 ≤ weight i

/-- A fixed-kernel certificate: a kernel `R`, fixed in advance, known to be nonnegative
on some shallow region. -/
structure Certificate where
  /-- The fixed kernel. -/
  R : ℝ → ℝ
  /-- The region on which nonnegativity of the kernel is known. -/
  shallow : Set ℝ
  /-- Nonnegativity of the kernel on the shallow region. -/
  h_pos : ∀ x ∈ shallow, 0 ≤ R x

/-- The linear charge functional attached to a kernel: the total charge of a configuration. -/
noncomputable def charge (R : ℝ → ℝ) {n : ℕ} (c : Config n) : ℝ :=
  ∑ i, c.weight i * R (c.deep i)

/-- The termwise bound justifying the certificate's pointwise discard: every single species
contributes nonnegatively. -/
def TermwiseBound (R : ℝ → ℝ) {n : ℕ} (c : Config n) : Prop :=
  ∀ i, 0 ≤ c.weight i * R (c.deep i)

/-- The two-species ("deep-pair") configuration with weights `a, b` at deep points `z, w`. -/
noncomputable def deepPair (a b z w : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Config 2 where
  weight := ![a, b]
  deep := ![z, w]
  weight_nonneg i := by fin_cases i <;> simpa using ‹_›

/-- A certificate is *valid* when its pointwise discard is legitimate against every
deep-pair configuration (two species, strictly positive weights, arbitrary deep points). -/
def CertificateValid (C : Certificate) : Prop :=
  ∀ c : Config 2, (∀ i, 0 < c.weight i) → TermwiseBound C.R c

/-- The charge functional is linear in the weights: rescaling all weights rescales the charge. -/
theorem charge_smul_weight (R : ℝ → ℝ) {n : ℕ} (c : Config n) (t : ℝ) (ht : 0 ≤ t) :
    charge R { weight := fun i => t * c.weight i, deep := c.deep,
               weight_nonneg := fun i => mul_nonneg ht (c.weight_nonneg i) }
      = t * charge R c := by
  simp only [charge, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The charge functional is additive in the weights. -/
theorem charge_add_weight (R : ℝ → ℝ) {n : ℕ} (c₁ c₂ : Config n) (h : c₁.deep = c₂.deep) :
    charge R { weight := fun i => c₁.weight i + c₂.weight i, deep := c₁.deep,
               weight_nonneg := fun i => add_nonneg (c₁.weight_nonneg i) (c₂.weight_nonneg i) }
      = charge R c₁ + charge R c₂ := by
  simp only [charge, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h]
  ring

/-- The charge of a deep pair. -/
theorem charge_deepPair (R : ℝ → ℝ) (a b z w : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    charge R (deepPair a b z w ha hb) = a * R z + b * R w := by
  simp [charge, deepPair, Fin.sum_univ_two]

/-- Validity of a fixed-kernel pointwise-discard certificate is *exactly* global
nonnegativity of its kernel: the shallow-region hypothesis `h_pos` buys nothing. -/
theorem certificateValid_iff (C : Certificate) :
    CertificateValid C ↔ ∀ x : ℝ, 0 ≤ C.R x := by
  constructor
  · intro hV x
    have h := hV (deepPair 1 1 x x zero_le_one zero_le_one)
      (by intro i; fin_cases i <;> simp [deepPair]) 0
    simpa [deepPair] using h
  · intro hR c _ i
    exact mul_nonneg (c.weight_nonneg i) (hR _)

/--
**Abstract subclass obstruction.**

Let `C` be a fixed-kernel pointwise-discard linear certificate (kernel `C.R` fixed in
advance, nonnegative on its shallow region).  Suppose the repaired witness produces a
deep point `z` at which the analytically continued kernel is negative, `C.R z < 0`.

Then:

1. the certificate is invalid — its pointwise discard fails against deep-pair
   configurations; and
2. this is witnessed *explicitly* by the deep pair with unit weights placed at `z`:
   the termwise bound fails there, and the whole linear charge is negative,

and this holds regardless of how large the shallow region carrying `h_pos` is.
-/
theorem subclass_obstruction_statement (C : Certificate) (z : ℝ) (hz : C.R z < 0) :
    ¬ CertificateValid C ∧
      ∃ c : Config 2, (∀ i, 0 < c.weight i) ∧ ¬ TermwiseBound C.R c ∧ charge C.R c < 0 := by
  refine ⟨?_, deepPair 1 1 z z zero_le_one zero_le_one, ?_, ?_, ?_⟩
  · intro hV
    exact absurd ((certificateValid_iff C).1 hV z) (not_le.2 hz)
  · intro i; fin_cases i <;> simp [deepPair]
  · intro hT
    have := hT 0
    simp only [deepPair] at this
    norm_num at this
    linarith
  · rw [charge_deepPair]
    linarith

/-- A negative deep value can only occur outside the shallow region on which the certificate's
kernel positivity `h_pos` is known: the repaired witness is genuinely *deep*. -/
theorem bad_witness_not_shallow (C : Certificate) (z : ℝ) (hz : C.R z < 0) :
    z ∉ C.shallow := fun hmem => absurd (C.h_pos z hmem) (not_le.2 hz)

/-- Sharp form of the obstruction: a fixed-kernel pointwise-discard certificate is invalid
*precisely* when its kernel takes some negative value. -/
theorem not_certificateValid_iff_exists_bad_deep_value (C : Certificate) :
    ¬ CertificateValid C ↔ ∃ z : ℝ, C.R z < 0 := by
  rw [certificateValid_iff]
  push_neg
  exact ⟨fun ⟨z, hz⟩ => ⟨z, hz⟩, fun ⟨z, hz⟩ => ⟨z, hz⟩⟩

end Zeta23Obstruction

