/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped TensorProduct
open Representation

namespace Phys

variable {k G U V W : Type*} [Field k] [Group G]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The space of intertwining (`G`-equivariant) linear maps between two representations,
as a subspace of all linear maps. -/

theorem rank_intertwiners_le_one [IsAlgClosed k] {ρ : Representation k G V}
    {σ : Representation k G W} [FiniteDimensional k W]
    [IsIrreducible ρ] [IsIrreducible σ] :
    Module.rank k (intertwiners ρ σ) ≤ 1 := by
  rw [rank_le_one_iff]
  by_cases h : ∀ f : intertwiners ρ σ, f = 0
  · exact ⟨0, fun f => ⟨0, by rw [h f, zero_smul]⟩⟩
  push_neg at h
  obtain ⟨g, hg⟩ := h
  set G' : IntertwiningMap ρ σ := toIntertwiningMap g.1 g.2 with hG'
  have hG'0 : G' ≠ 0 := by
    intro hh
    apply hg
    ext v
    have : G' v = 0 := by rw [hh]; rfl
    simpa [hG', toIntertwiningMap] using this
  have hbij : Function.Bijective G' :=
    (IsIrreducible.bijective_or_eq_zero G').resolve_right hG'0
  refine ⟨g, fun f => ?_⟩
  set F : IntertwiningMap ρ σ := toIntertwiningMap f.1 f.2 with hF
  obtain ⟨c, hc⟩ :=
    (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := σ)).surjective (F.comp (intertwinerInverse G' hbij))
  refine ⟨c, ?_⟩
  ext v
  have hv := congrArg (fun e : IntertwiningMap σ σ => e (G' v)) hc
  simp only [IntertwiningMap.algebraMap_apply] at hv
  have hcomp : (F.comp (intertwinerInverse G' hbij)) (G' v) = F v := by
    simp [IntertwiningMap.comp, IntertwiningMap.llcomp]
  rw [hcomp] at hv
  have hleft : ((c • (1 : IntertwiningMap σ σ)) : IntertwiningMap σ σ) (G' v) = c • (G' v) := rfl
  rw [hleft] at hv
  simpa [hF, hG', toIntertwiningMap] using hv

/-- **The Wigner–Eckart theorem.**

Let `τ`, `ρ`, `σ` be representations of a group `G` on `U`, `V`, `W`: think of `τ` as the spin-`k`
representation carrying the components `q` of a tensor operator `T^k_q`, of `ρ` as the spin-`j`
representation of the initial states `|j m⟩`, and of `σ` as the spin-`j'` representation of the
final states `|j' m'⟩`.  A tensor operator is precisely an equivariant map `T : τ ⊗ ρ → σ`, and
the Clebsch–Gordan map `CG` is a distinguished nonzero such equivariant map.

Assuming multiplicity one, i.e. that the space of equivariant maps `τ ⊗ ρ → σ` is at most one
dimensional (the standard `SU(2)` Clebsch–Gordan fact), there is a single scalar `red`, the
*reduced matrix element*, independent of the magnetic quantum numbers, such that every matrix
element `⟨j' m'| T^k_q |j m⟩` factors as `red` times the corresponding Clebsch–Gordan
coefficient `⟨j' m'| CG (q ⊗ m)⟩`. -/
