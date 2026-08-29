/-
# Molecular Orbital Count
Category: Chemistry
Target: Chem.molecular_orbital_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- **LCAO dimension preservation.**

Model: the one-electron orbital space `V` over the (scalar) field `K` is spanned by a set of
`n` atomic orbitals `ao : Module.Basis (Fin n) K V` (linearly independent atomic orbitals).
A family of molecular orbitals `mo : ι → V` obtained by linear combination of atomic
orbitals is required to be linearly independent (`hli`) and to span the same orbital space
(`hsp`) — i.e. the LCAO mixing is invertible.

Conclusion: the index type of the molecular orbitals is in bijection with `Fin n`, i.e. the
LCAO procedure applied to `n` atomic orbitals yields *exactly* `n` molecular orbitals. -/

theorem molecular_orbital_card
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} {ι : Type*} [Fintype ι] (ao : Module.Basis (Fin n) K V)
    (mo : ι → V) (hli : LinearIndependent K mo)
    (hsp : Submodule.span K (Set.range mo) = ⊤) :
    Fintype.card ι = n := by
  obtain ⟨e⟩ := molecular_orbital_count ao mo hli hsp
  simpa using Fintype.card_congr e

/-- **Concrete LCAO form.** If the `n` molecular orbitals are obtained from the `n` atomic
orbitals by an invertible mixing matrix `c` (`mo i = ∑ j, c i j • ao j`, with `det c` a unit),
then they themselves form a basis of the orbital space: the LCAO expansion produces exactly
`n` independent molecular orbitals spanning the same space. -/
