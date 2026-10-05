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

/-- A **configuration** of deep points: finitely many species, each carrying a real
"deep point" `pt i` and a strictly positive weight `wt i`. -/
structure DeepConfig where
  /-- number of species -/
  n : ℕ
  /-- the deep point attached to each species -/
  pt : Fin n → ℝ
  /-- the (strictly positive) weight attached to each species -/
  wt : Fin n → ℝ
  /-- positivity of the weights -/
  wt_pos : ∀ i : Fin n, 0 < wt i

/-- The **linear charge** of a configuration relative to a fixed kernel `R`:
the linear functional `c ↦ ∑ᵢ wᵢ · R(zᵢ)` obtained by per-species linear charging. -/
noncomputable def charge (R : ℝ → ℝ) (c : DeepConfig) : ℝ :=
  ∑ i : Fin c.n, c.wt i * R (c.pt i)

/-- The **termwise bound** required by the pointwise-discard step: the chain only
concludes `0 ≤ charge R c` by discarding each summand separately, which is legitimate
exactly when every term `wᵢ · R(zᵢ)` is itself nonnegative. -/
def TermwiseNonneg (R : ℝ → ℝ) (c : DeepConfig) : Prop :=
  ∀ i : Fin c.n, 0 ≤ c.wt i * R (c.pt i)

/-- Pointwise discard is sound: if the termwise bound holds, the charge is nonnegative. -/
theorem charge_nonneg_of_termwiseNonneg (R : ℝ → ℝ) (c : DeepConfig)
    (h : TermwiseNonneg R c) : 0 ≤ charge R c :=
  Finset.sum_nonneg fun i _ => h i

/-- The **deep-pair configuration** at `z`: the two-species configuration supported on
the reflected pair `{z, σ z}`, with arbitrary positive weights `a`, `b`. -/
def deepPair (σ : ℝ → ℝ) (z a b : ℝ) (ha : 0 < a) (hb : 0 < b) : DeepConfig where
  n := 2
  pt := ![z, σ z]
  wt := ![a, b]
  wt_pos := by
    intro i
    fin_cases i <;> simpa using ‹_›

/-- **Validity of a fixed-kernel pointwise-discard certificate**: the certificate claims
that on *every* deep-pair configuration the termwise bound (and hence, by pointwise
discard, nonnegativity of the linear charge) holds. -/
def CertificateValid (R σ : ℝ → ℝ) : Prop :=
  ∀ (z a b : ℝ) (ha : 0 < a) (hb : 0 < b), TermwiseNonneg R (deepPair σ z a b ha hb)

/-- **Abstract subclass obstruction.**

A certificate in this subclass is determined by a *fixed* kernel `R : ℝ → ℝ`, symmetric
under the reflection `σ` pairing deep points, and it is used only through pointwise
discard plus per-species linear charging.  If the (analytically continued) kernel takes a
single negative value `R z < 0` at some deep point `z` — the repaired witness — then the
deep-pair configuration at `z` defeats the certificate: for *every* choice of positive
species weights the termwise bound fails and the linear charge is strictly negative.
Consequently no such certificate is valid. -/
theorem subclass_obstruction_statement
    (R σ : ℝ → ℝ) (hRσ : ∀ x : ℝ, R (σ x) = R x)
    (z : ℝ) (hz : R z < 0) :
    (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b),
        ¬ TermwiseNonneg R (deepPair σ z a b ha hb) ∧
          charge R (deepPair σ z a b ha hb) < 0) ∧
      ¬ CertificateValid R σ := by
  have key : ∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b),
      ¬ TermwiseNonneg R (deepPair σ z a b ha hb) ∧
        charge R (deepPair σ z a b ha hb) < 0 := by
    intro a b ha hb
    have hcharge : charge R (deepPair σ z a b ha hb) = a * R z + b * R z := by
      simp [charge, deepPair, Fin.sum_univ_two, hRσ]
    constructor
    · intro h
      have h0 := h ⟨0, by norm_num [deepPair]⟩
      simp [deepPair] at h0
      nlinarith
    · rw [hcharge]
      nlinarith
  refine ⟨key, ?_⟩
  intro hvalid
  exact (key 1 1 one_pos one_pos).1 (hvalid z 1 1 one_pos one_pos)

/-- Strengthening: the obstruction is not special to the two-species pair.  *Any*
configuration that charges some species at a point where the fixed kernel is negative
already breaks the termwise bound, whatever the (positive) weights are. -/
theorem termwiseNonneg_fails_of_negative_point (R : ℝ → ℝ) (c : DeepConfig) (i : Fin c.n)
    (hz : R (c.pt i) < 0) : ¬ TermwiseNonneg R c := by
  intro h
  have hw := c.wt_pos i
  have hi := h i
  nlinarith

/-- Validity of a fixed-kernel pointwise-discard certificate against *all* configurations,
not only deep pairs. -/
def CertificateValidAll (R : ℝ → ℝ) : Prop :=
  ∀ c : DeepConfig, TermwiseNonneg R c

/-- One bad deep value already invalidates the certificate against arbitrary
configurations: the single-species configuration at `z` is a counterexample. -/
theorem not_certificateValidAll (R : ℝ → ℝ) (z : ℝ) (hz : R z < 0) :
    ¬ CertificateValidAll R := by
  intro hvalid
  refine termwiseNonneg_fails_of_negative_point R
    ⟨1, fun _ => z, fun _ => 1, fun _ => one_pos⟩ ⟨0, one_pos⟩ ?_ (hvalid _)
  simpa using hz

/-- Corollary: a globally nonnegative kernel can never agree with the continued kernel,
so the "fixed kernel with `∀ x, 0 ≤ R x`" hypothesis of the certificate is unattainable
once a single bad deep value exists. -/
theorem no_globally_nonneg_kernel (R R' : ℝ → ℝ) (h_pos : ∀ x : ℝ, 0 ≤ R' x)
    (z : ℝ) (hz : R z < 0) : R' ≠ R := by
  intro h
  exact absurd (h ▸ h_pos z) (not_le.mpr hz)

end Zeta23Obstruction

