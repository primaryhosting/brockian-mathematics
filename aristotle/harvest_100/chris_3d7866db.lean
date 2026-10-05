/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u v w

namespace Frontier

attribute [local instance] Classical.propDecidable

/-!
## Setting

We formalise the deterministic base case of the Conant–Ashby "good regulator" theorem.

* `S` is the set of states of the *system* (the disturbances acting on it),
* `R` is the set of *regulatory actions*,
* `Z` is the set of *outcomes*,
* `ψ : S → R → Z` is the system's outcome map: `ψ s r` is the outcome when the system is in
  state `s` and the regulator acts by `r`.

The *behaviour* of the system in state `s` is the whole function `ψ s : R → Z`; two states with
the same behaviour are indistinguishable from the outside. Thus `ψ : S → (R → Z)` presents the
system through its input/output behaviour, and a *model of the system contained in the regulator*
is a map `m : (R → Z) → R` reproducing the regulator's actions from that behaviour, i.e.
`ρ = m ∘ ψ`.
-/

/-- A regulator `ρ` is *good* (perfectly regulating) for the system `ψ` with target outcome `z₀`
if it forces the outcome `z₀` whatever the state of the system. -/
def IsGoodRegulator {S : Type u} {R : Type v} {Z : Type w}
    (psi : S → R → Z) (z0 : Z) (rho : S → R) : Prop :=
  ∀ s : S, psi s (rho s) = z0

/-- The system is *tight* at the target outcome `z0` if, in each state, at most one regulatory
action produces the target outcome. This is the deterministic counterpart of Conant and Ashby's
requirement that the optimal regulator's response be essentially unique. -/
def TightAt {S : Type u} {R : Type v} {Z : Type w} (psi : S → R → Z) (z0 : Z) : Prop :=
  ∀ (s : S) (r r' : R), psi s r = z0 → psi s r' = z0 → r = r'

/-- `m` is a *model of the system `psi` contained in the regulator `rho`* if the regulator's
action is computed by `m` from the system's behaviour: `rho s = m (psi s)` for every state `s`. -/
def IsModelIn {S : Type u} {R : Type v} {Z : Type w}
    (psi : S → R → Z) (rho : S → R) (m : (R → Z) → R) : Prop :=
  ∀ s : S, m (psi s) = rho s

/-- A good regulator of a tight system depends on the state of the system only through the
system's behaviour: indistinguishable states receive identical regulatory actions. -/
theorem good_regulator_factors {S : Type u} {R : Type v} {Z : Type w}
    {psi : S → R → Z} {z0 : Z} {rho : S → R}
    (hrho : IsGoodRegulator psi z0 rho) (htight : TightAt psi z0) :
    ∀ s s' : S, psi s = psi s' → rho s = rho s' := by
  intro s s' hss'
  have h1 : psi s' (rho s) = z0 := by
    have h2 : psi s (rho s) = z0 := hrho s
    rw [hss'] at h2
    exact h2
  exact htight s' (rho s) (rho s') h1 (hrho s')

/-- The model extracted from a good regulator: on behaviours realised by some state of the
system it returns the regulator's action there, and it is arbitrary elsewhere. -/
noncomputable def extractedModel {S : Type u} {R : Type v} {Z : Type w}
    [hR : Nonempty R] (psi : S → R → Z) (rho : S → R) : (R → Z) → R :=
  fun f => if h : ∃ s : S, psi s = f then rho (Classical.choose h) else Classical.choice hR

/-- **Every good regulator of a system is (contains) a model of that system** (Conant–Ashby,
deterministic base case).

Given a system `psi : S → R → Z` in which the target outcome `z0` pins down the regulatory
action (`TightAt`), any perfectly regulating `rho` satisfies:

1. **(model)** there is a map `m : (R → Z) → R` from the system's behaviour to regulatory actions
   with `rho = m ∘ psi`; the regulator is thus a mapping of the system's behaviour, and this
   model is itself a good regulator, since acting by `m (psi s)` always yields the target
   outcome;
2. **(uniqueness)** `rho` is the *only* good regulator, so no good regulator can avoid containing
   this model. -/
theorem good_regulator {S : Type u} {R : Type v} {Z : Type w} [Nonempty R]
    {psi : S → R → Z} {z0 : Z} {rho : S → R}
    (hrho : IsGoodRegulator psi z0 rho) (htight : TightAt psi z0) :
    (∃ m : (R → Z) → R, IsModelIn psi rho m ∧ ∀ s : S, psi s (m (psi s)) = z0) ∧
      (∀ rho' : S → R, IsGoodRegulator psi z0 rho' → rho' = rho) := by
  have hmodel : IsModelIn psi rho (extractedModel psi rho) := by
    intro s
    have hex : ∃ s' : S, psi s' = psi s := ⟨s, rfl⟩
    have hspec : psi (Classical.choose hex) = psi s := Classical.choose_spec hex
    show (if h : ∃ s' : S, psi s' = psi s then rho (Classical.choose h)
      else Classical.choice ‹Nonempty R›) = rho s
    rw [dif_pos hex]
    exact good_regulator_factors hrho htight _ s hspec
  refine ⟨⟨extractedModel psi rho, hmodel, ?_⟩, ?_⟩
  · intro s
    rw [hmodel s]
    exact hrho s
  · intro rho' hrho'
    funext s
    exact htight s (rho' s) (rho s) (hrho' s) (hrho s)

/-!
## Non-vacuity

The hypotheses of `good_regulator` are satisfiable: take the system in which the regulator must
match the disturbance, `psi s r = (s == r)`, with target outcome `true`. The identity regulator
is good, the system is tight, and hence the identity regulator is (contains) a model of the
system.
-/

/-- The matching system on `Bool`: the outcome is the target `true` exactly when the regulatory
action matches the state of the system. -/
def matchSystem : Bool → Bool → Bool := fun s r => (s == r)

theorem matchSystem_isGoodRegulator_id : IsGoodRegulator matchSystem true id := by
  intro s
  cases s <;> rfl

theorem matchSystem_tightAt : TightAt matchSystem true := by
  intro s r r' h h'
  cases s <;> cases r <;> cases r' <;> simp_all [matchSystem]

/-- Instance of the good regulator theorem for the matching system: the identity regulator
contains a model of the system and is the unique good regulator. -/
theorem good_regulator_matchSystem :
    (∃ m : (Bool → Bool) → Bool, IsModelIn matchSystem id m ∧
        ∀ s : Bool, matchSystem s (m (matchSystem s)) = true) ∧
      (∀ rho' : Bool → Bool, IsGoodRegulator matchSystem true rho' → rho' = id) :=
  good_regulator matchSystem_isGoodRegulator_id matchSystem_tightAt

end Frontier

