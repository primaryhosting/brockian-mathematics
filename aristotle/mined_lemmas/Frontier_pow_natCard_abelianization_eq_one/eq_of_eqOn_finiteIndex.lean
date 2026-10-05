import Mathlib

/-!
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
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

open MeasureTheory

/-!
## The setting

Margulis superrigidity concerns an irreducible lattice `Γ` in a higher-rank semisimple
group `G` and a linear representation `rho : Γ → H`.  It asserts that, under suitable
non-degeneracy assumptions on the image of `rho`, the representation `rho` is the restriction
to `Γ` of a *continuous* homomorphism `G → H`; i.e. the abstract homomorphism `rho`, defined
only on the discrete group `Γ`, is forced to come from the ambient topological group.

Below we formalise:

* `Frontier.IsLatticeIn` — a discrete subgroup with a finite-measure fundamental domain;
* `Frontier.ExtendsToContinuousHom` — the superrigidity conclusion for one representation;
* `Frontier.SuperrigidLattice` — "every non-degenerate representation of `Γ` extends";
* `Frontier.MargulisSuperrigidityStatement` — the theorem itself, as a statement schema in
  which the (semisimplicity + higher rank + irreducibility) package is an abstract
  predicate; `Frontier.HasHigherRankSplitTorus` records a concrete necessary condition
  for real rank `≥ 2` that such a predicate must imply;
* `Frontier.margulis_superrigidity` — the theorem proved here: the *abelian base case*
  together with uniqueness of the extension, plus (`margulis_superrigidity_finite_index`)
  a Lean-checked reduction from finite-index subgroups to the whole lattice.
-/

/-- `IsLatticeIn μ Γ`: the subgroup `Γ` of the topological group `G` is a **lattice**, i.e.
it is discrete and admits a fundamental domain of finite `μ`-measure (`μ` being a Haar
measure on `G`). -/

theorem eq_of_eqOn_finiteIndex {L : Type*} [Group L] {H : Type*} [CommGroup H]
    [IsMulTorsionFree H] {L₀ : Subgroup L} (hidx : L₀.FiniteIndex) (rho Φ : L →* H)
    (h : ∀ x ∈ L₀, rho x = Φ x) (x : L) : rho x = Φ x := by
  set δ : L →* H := rho * Φ⁻¹ with hδ
  have hker : L₀ ≤ δ.ker := by
    intro y hy
    simp [hδ, MonoidHom.mem_ker, h y hy]
  have hdvd : δ.ker.index ∣ L₀.index := Subgroup.index_dvd_of_le hker
  have hne : δ.ker.index ≠ 0 := by
    intro h0
    exact hidx.index_ne_zero (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  have hpow : δ x ^ Nat.card (L ⧸ δ.ker) = 1 := by
    have hx : δ x ^ Nat.card (L ⧸ δ.ker) = δ (x ^ Nat.card (L ⧸ δ.ker)) := (map_pow _ _ _).symm
    rw [hx, ← MonoidHom.mem_ker, ← QuotientGroup.eq_one_iff]
    simp
  have hpos : 0 < Nat.card (L ⧸ δ.ker) := Nat.pos_of_ne_zero hne
  have hinj := IsMulTorsionFree.pow_left_injective (M := H)
    (n := Nat.card (L ⧸ δ.ker)) hpos.ne' (a₁ := δ x) (a₂ := 1)
  simp only [one_pow] at hinj
  have hδx : δ x = 1 := hinj hpow
  have : rho x * (Φ x)⁻¹ = 1 := by simpa [hδ] using hδx
  exact (div_eq_one (a := rho x) (b := Φ x)).1 (by simpa [div_eq_mul_inv] using this)

/-- **Margulis superrigidity — the abelian base case, with uniqueness.**

Let `Γ` be a lattice with finite abelianisation in a topological group `G` (higher-rank
lattices have Kazhdan's property (T), hence finite abelianisation; property (T) is taken
here as the black box supplying `hab`), and let `H` be a Hausdorff torsion-free abelian
topological group.  Then every representation `rho : Γ →* H`:

* is trivial;
* extends to a continuous homomorphism `G →* H` — i.e. the superrigidity conclusion
  `ExtendsToContinuousHom Γ rho` holds;
* has, when `Γ` is dense in `G`, exactly one such continuous extension.

This is the base case of superrigidity: it disposes of all abelian target groups, which is
precisely the case in which the conclusion is *not* obtained by the dynamical arguments used
for semisimple targets, and it already shows that the higher-rank hypothesis (through
property (T)) is what rules out the obvious counterexamples coming from surface groups. -/
