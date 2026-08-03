# Brockian Verified-Theorem Registry

> Generated from AXLE independent verification attestations. `register` is derived from axioms + AXLE verdict, never hand-asserted (spec §5).

> **PROVED** includes theorems closed by the kernel-checked `decide` tactic (finite `ZMod`/`Finset` checks — genuinely verified, ledger-consistent). `native_decide` (compiler-trusted, adds `Lean.ofReduceBool`) is excluded from PROVED by the axiom gate. `DEFINITION` = a supporting `def`; `CONJECTURE` = a named Prop container (never a claim).

## Summary

- **CONDITIONAL**: 21
- **CONJECTURE**: 2
- **DEFINITION**: 369
- **DISCHARGED**: 6
- **PROVED**: 2985

## Theorems

| Register | Name | Axioms clean | AXLE | Env | Ledger |
|---|---|---|---|---|---|
| PROVED | `Brockian.Admissibility.admissibility_count_five` | ✓ | verified | lean-4.32.0 | 74 (a0ce…) / 49 / 105 (independent replications) / 119 module 2 |
| PROVED | `Brockian.Admissibility.admissibility_count_three` | ✓ | verified | lean-4.32.0 | 74 (a0ce…) / 49 / 105 (independent replications) / 119 module 2 |
| DEFINITION | `Brockian.Admissibility.admissibleResidues` | ✓ | verified | lean-4.32.0 | 74 (a0ce…) / 49 / 105 (independent replications) / 119 module 2 |
| PROVED | `Brockian.Admissibility.universal_admissibility_count` | ✓ | verified | lean-4.32.0 | 74 (a0ce…) / 49 / 105 (independent replications) / 119 module 2 |
| PROVED | `Brockian.Admissibility.CRT.admissibleResidues_crt_card` | ✓ | verified | lean-4.32.0 | paper-audit target — CRT product |A_{q1q2}|=|A_q1|·|A_q2|; AXLE @4.32 |
| PROVED | `Brockian.Admissibility.CRT.admissibleResidues_crt_card_two_primes` | ✓ | verified | lean-4.32.0 | paper-audit target — CRT product |A_{q1q2}|=|A_q1|·|A_q2|; AXLE @4.32 |
| PROVED | `Brockian.Admissibility.CRT.admissible_count_three_five` | ✓ | verified | lean-4.32.0 | paper-audit target — CRT product |A_{q1q2}|=|A_q1|·|A_q2|; AXLE @4.32 |
| DEFINITION | `Brockian.Admissibility.CriterionScaffold.LocalIntegerTupleAdmissible` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Admissibility.CriterionScaffold.LocalTupleAdmissible` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Admissibility.CriterionScaffold.PrimeLocalAdmissible` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Admissibility.CriterionScaffold.localIntegerTupleAdmissible_iff_localNu_lt` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Admissibility.CriterionScaffold.localNu` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Admissibility.CriterionScaffold.localNu_eq_card_localResidueSet` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Admissibility.CriterionScaffold.localResidueSet` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Admissibility.CriterionScaffold.localTupleAdmissible_iff_exists_avoids` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Admissibility.CriterionScaffold.localTupleAdmissible_iff_obstruction_lt` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Admissibility.CriterionScaffold.not_localTupleAdmissible_iff_modulus_le_obstruction` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Admissibility.CriterionScaffold.not_localTupleAdmissible_iff_obstruction_eq_modulus` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Admissibility.CriterionScaffold.primeLocalAdmissible_iff_every_prime_has_local_start` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Admissibility.CriterionScaffold.residueSet_card_le_modulus` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.AdmissibilityCRTGeneral.admissibleTupleResidues_prodCRT_card` | ✓ | verified | lean-4.32.0 | roadmap #14 iterated — multi-factor CRT admissible count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityCRTGeneral.admissibleTupleResidues_prodCRT_primes_card` | ✓ | verified | lean-4.32.0 | roadmap #14 iterated — multi-factor CRT admissible count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityCRTGeneral.admissibleTuple_pi_card` | ✓ | verified | lean-4.32.0 | roadmap #14 iterated — multi-factor CRT admissible count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityCRTGeneral.admissible_crt_count_fifteen` | ✓ | verified | lean-4.32.0 | roadmap #14 iterated — multi-factor CRT admissible count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityCRTGeneral.admissible_ktuple_count_fifteen_factors` | ✓ | verified | lean-4.32.0 | roadmap #14 iterated — multi-factor CRT admissible count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityCRTGeneral.neZero_prod` | ✓ | verified | lean-4.32.0 | roadmap #14 iterated — multi-factor CRT admissible count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityCRTGeneral.pairwise_coprime_of_primes` | ✓ | verified | lean-4.32.0 | roadmap #14 iterated — multi-factor CRT admissible count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityDiagonal.admissibility_count_dichotomy` | ✓ | verified | lean-4.32.0 | parallel-tool (Grok) #12 divisible-case diagonal law; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.AdmissibilityDiagonal.admissibleResidues_zero_eq` | ✓ | verified | lean-4.32.0 | parallel-tool (Grok) #12 divisible-case diagonal law; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.AdmissibilityDiagonal.diagonal_admissibility_count` | ✓ | verified | lean-4.32.0 | parallel-tool (Grok) #12 divisible-case diagonal law; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.AdmissibilityDiagonal.diagonal_admissibility_count_of_eq_zero` | ✓ | verified | lean-4.32.0 | parallel-tool (Grok) #12 divisible-case diagonal law; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.AdmissibilityDiagonal.diagonal_count_five` | ✓ | verified | lean-4.32.0 | parallel-tool (Grok) #12 divisible-case diagonal law; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.AdmissibilityDiagonal.diagonal_count_three` | ✓ | verified | lean-4.32.0 | parallel-tool (Grok) #12 divisible-case diagonal law; AXLE @4.32; committed by Claude for tip coherence |
| DEFINITION | `Brockian.AdmissibilityHLCriterion.Admissible` | ✓ | verified | lean-4.32.0 | roadmap #11 — Hardy-Littlewood admissibility criterion; AXLE @4.32 |
| DEFINITION | `Brockian.AdmissibilityHLCriterion.OmitsResidue` | ✓ | verified | lean-4.32.0 | roadmap #11 — Hardy-Littlewood admissibility criterion; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityHLCriterion.admissible_iff_card_image_lt` | ✓ | verified | lean-4.32.0 | roadmap #11 — Hardy-Littlewood admissibility criterion; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityHLCriterion.admissible_iff_count_pos` | ✓ | verified | lean-4.32.0 | roadmap #11 — Hardy-Littlewood admissibility criterion; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityHLCriterion.admissible_iff_exists_avoiding_start` | ✓ | verified | lean-4.32.0 | roadmap #11 — Hardy-Littlewood admissibility criterion; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityHLCriterion.admissible_iff_nu_lt` | ✓ | verified | lean-4.32.0 | roadmap #11 — Hardy-Littlewood admissibility criterion; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityHLCriterion.admissible_iff_nu_lt_of_le_card` | ✓ | verified | lean-4.32.0 | roadmap #11 — Hardy-Littlewood admissibility criterion; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityHLCriterion.admissible_zero_two` | ✓ | verified | lean-4.32.0 | roadmap #11 — Hardy-Littlewood admissibility criterion; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityHLCriterion.not_admissible_zero_two_four` | ✓ | verified | lean-4.32.0 | roadmap #11 — Hardy-Littlewood admissibility criterion; AXLE @4.32 |
| DEFINITION | `Brockian.AdmissibilityHLCriterion.nu` | ✓ | verified | lean-4.32.0 | roadmap #11 — Hardy-Littlewood admissibility criterion; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityHLCriterion.omitsResidue_iff_ne_univ` | ✓ | verified | lean-4.32.0 | roadmap #11 — Hardy-Littlewood admissibility criterion; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityHLCriterion.omitsResidue_iff_nu_lt` | ✓ | verified | lean-4.32.0 | roadmap #11 — Hardy-Littlewood admissibility criterion; AXLE @4.32 |
| DEFINITION | `Brockian.AdmissibilityHLCriterion.residueImage` | ✓ | verified | lean-4.32.0 | roadmap #11 — Hardy-Littlewood admissibility criterion; AXLE @4.32 |
| DEFINITION | `Brockian.AdmissibilityKTuple.admissibleTupleResidues` | ✓ | verified | lean-4.32.0 | roadmap #14 — general admissible k-tuple configuration count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityKTuple.admissibleTupleResidues_card` | ✓ | verified | lean-4.32.0 | roadmap #14 — general admissible k-tuple configuration count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityKTuple.admissibleTupleResidues_card_pair` | ✓ | verified | lean-4.32.0 | roadmap #14 — general admissible k-tuple configuration count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityKTuple.admissibleTupleResidues_card_triple` | ✓ | verified | lean-4.32.0 | roadmap #14 — general admissible k-tuple configuration count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityKTuple.admissibleTupleResidues_crt_card` | ✓ | verified | lean-4.32.0 | roadmap #14 — general admissible k-tuple configuration count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityKTuple.admissibleTupleResidues_crt_card_pair` | ✓ | verified | lean-4.32.0 | roadmap #14 — general admissible k-tuple configuration count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityKTuple.admissibleTupleResidues_pair_eq` | ✓ | verified | lean-4.32.0 | roadmap #14 — general admissible k-tuple configuration count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityKTuple.admissible_ktuple_count_five` | ✓ | verified | lean-4.32.0 | roadmap #14 — general admissible k-tuple configuration count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityKTuple.admissible_ktuple_count_three` | ✓ | verified | lean-4.32.0 | roadmap #14 — general admissible k-tuple configuration count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityKTuple.crt_filter_card` | ✓ | verified | lean-4.32.0 | roadmap #14 — general admissible k-tuple configuration count; AXLE @4.32 |
| PROVED | `Brockian.AdmissibilityKTuple.mem_admissibleTupleResidues` | ✓ | verified | lean-4.32.0 | roadmap #14 — general admissible k-tuple configuration count; AXLE @4.32 |
| DEFINITION | `Brockian.AffineSymmetry.additiveAutEquivUnits` | ✓ | verified | lean-4.32.0 | paper-audit target — separates additive-aut / graph-aut / affine-dihedral; AXLE @4.32 |
| PROVED | `Brockian.AffineSymmetry.additiveAut_card` | ✓ | verified | lean-4.32.0 | paper-audit target — separates additive-aut / graph-aut / affine-dihedral; AXLE @4.32 |
| PROVED | `Brockian.AffineSymmetry.additiveAut_card_five` | ✓ | verified | lean-4.32.0 | paper-audit target — separates additive-aut / graph-aut / affine-dihedral; AXLE @4.32 |
| DEFINITION | `Brockian.AffineSymmetry.affineGroup` | ✓ | verified | lean-4.32.0 | paper-audit target — separates additive-aut / graph-aut / affine-dihedral; AXLE @4.32 |
| DEFINITION | `Brockian.AffineSymmetry.affinePerm` | ✓ | verified | lean-4.32.0 | paper-audit target — separates additive-aut / graph-aut / affine-dihedral; AXLE @4.32 |
| DEFINITION | `Brockian.AffineSymmetry.dihAct` | ✓ | verified | lean-4.32.0 | paper-audit target — separates additive-aut / graph-aut / affine-dihedral; AXLE @4.32 |
| DEFINITION | `Brockian.AffineSymmetry.dihedralToPerm` | ✓ | verified | lean-4.32.0 | paper-audit target — separates additive-aut / graph-aut / affine-dihedral; AXLE @4.32 |
| PROVED | `Brockian.AffineSymmetry.dihedralToPerm_card` | ✓ | verified | lean-4.32.0 | paper-audit target — separates additive-aut / graph-aut / affine-dihedral; AXLE @4.32 |
| PROVED | `Brockian.AffineSymmetry.dihedralToPerm_injective` | ✓ | verified | lean-4.32.0 | paper-audit target — separates additive-aut / graph-aut / affine-dihedral; AXLE @4.32 |
| PROVED | `Brockian.AffineSymmetry.dihedralToPerm_range_le_affineGroup` | ✓ | verified | lean-4.32.0 | paper-audit target — separates additive-aut / graph-aut / affine-dihedral; AXLE @4.32 |
| PROVED | `Brockian.AffineSymmetry.symmetry_separation` | ✓ | verified | lean-4.32.0 | paper-audit target — separates additive-aut / graph-aut / affine-dihedral; AXLE @4.32 |
| PROVED | `Brockian.AffineSymmetry.units_isCyclic` | ✓ | verified | lean-4.32.0 | paper-audit target — separates additive-aut / graph-aut / affine-dihedral; AXLE @4.32 |
| DEFINITION | `Brockian.Automorphism.C5` | ✓ | verified | lean-4.32.0 | run 54 (bce0…) — re-proved fresh @ v4.32; faithful D₅ action (full iso open) |
| DEFINITION | `Brockian.Automorphism.act` | ✓ | verified | lean-4.32.0 | run 54 (bce0…) — re-proved fresh @ v4.32; faithful D₅ action (full iso open) |
| DEFINITION | `Brockian.Automorphism.dihedralHom` | ✓ | verified | lean-4.32.0 | run 54 (bce0…) — re-proved fresh @ v4.32; faithful D₅ action (full iso open) |
| PROVED | `Brockian.Automorphism.dihedral_action_faithful` | ✓ | verified | lean-4.32.0 | run 54 (bce0…) — re-proved fresh @ v4.32; faithful D₅ action (full iso open) |
| PROVED | `Brockian.Automorphism.mul_rr` | ✓ | verified | lean-4.32.0 | run 54 (bce0…) — re-proved fresh @ v4.32; faithful D₅ action (full iso open) |
| PROVED | `Brockian.Automorphism.mul_rsr` | ✓ | verified | lean-4.32.0 | run 54 (bce0…) — re-proved fresh @ v4.32; faithful D₅ action (full iso open) |
| PROVED | `Brockian.Automorphism.mul_srr` | ✓ | verified | lean-4.32.0 | run 54 (bce0…) — re-proved fresh @ v4.32; faithful D₅ action (full iso open) |
| PROVED | `Brockian.Automorphism.mul_srsr` | ✓ | verified | lean-4.32.0 | run 54 (bce0…) — re-proved fresh @ v4.32; faithful D₅ action (full iso open) |
| DEFINITION | `Brockian.Automorphism.reflEquiv` | ✓ | verified | lean-4.32.0 | run 54 (bce0…) — re-proved fresh @ v4.32; faithful D₅ action (full iso open) |
| DEFINITION | `Brockian.Automorphism.reflIso` | ✓ | verified | lean-4.32.0 | run 54 (bce0…) — re-proved fresh @ v4.32; faithful D₅ action (full iso open) |
| PROVED | `Brockian.Automorphism.refl_map_adj` | ✓ | verified | lean-4.32.0 | run 54 (bce0…) — re-proved fresh @ v4.32; faithful D₅ action (full iso open) |
| DEFINITION | `Brockian.Automorphism.rotEquiv` | ✓ | verified | lean-4.32.0 | run 54 (bce0…) — re-proved fresh @ v4.32; faithful D₅ action (full iso open) |
| DEFINITION | `Brockian.Automorphism.rotIso` | ✓ | verified | lean-4.32.0 | run 54 (bce0…) — re-proved fresh @ v4.32; faithful D₅ action (full iso open) |
| PROVED | `Brockian.Automorphism.rot_map_adj` | ✓ | verified | lean-4.32.0 | run 54 (bce0…) — re-proved fresh @ v4.32; faithful D₅ action (full iso open) |
| PROVED | `Brockian.Automorphism.ten_le_card_aut` | ✓ | verified | lean-4.32.0 | run 54 (bce0…) — re-proved fresh @ v4.32; faithful D₅ action (full iso open) |
| DEFINITION | `Brockian.Automorphism.Full.autEquivDihedral` | ✓ | verified | lean-4.32.0 | run 54 completed 2026-08-01 — |Aut(C5)|<=10 reverse bound + full iso |
| PROVED | `Brockian.Automorphism.Full.aut_card_eq_ten` | ✓ | verified | lean-4.32.0 | run 54 completed 2026-08-01 — |Aut(C5)|<=10 reverse bound + full iso |
| PROVED | `Brockian.Automorphism.Full.aut_equiv_dihedral` | ✓ | verified | lean-4.32.0 | run 54 completed 2026-08-01 — |Aut(C5)|<=10 reverse bound + full iso |
| PROVED | `Brockian.Automorphism.Full.card_aut_le_ten` | ✓ | verified | lean-4.32.0 | run 54 completed 2026-08-01 — |Aut(C5)|<=10 reverse bound + full iso |
| PROVED | `Brockian.Automorphism.Full.dihedralHom_bijective` | ✓ | verified | lean-4.32.0 | run 54 completed 2026-08-01 — |Aut(C5)|<=10 reverse bound + full iso |
| PROVED | `Brockian.Automorphism.Full.dihedralHom_surjective` | ✓ | verified | lean-4.32.0 | run 54 completed 2026-08-01 — |Aut(C5)|<=10 reverse bound + full iso |
| DEFINITION | `Brockian.C5SpectralMultiplicities.c5DistinctEigs` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5DistinctEigs_card` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| DEFINITION | `Brockian.C5SpectralMultiplicities.c5LapMode` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5LapMode_four` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5LapMode_one` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5LapMode_three` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5LapMode_two` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5LapMode_zero` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| DEFINITION | `Brockian.C5SpectralMultiplicities.c5LaplacianMultiset` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5LaplacianMultiset_eq` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| DEFINITION | `Brockian.C5SpectralMultiplicities.c5Mode` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5Mode_four` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5Mode_mem_cycleSpectrum` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5Mode_one` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5Mode_one_eq_four` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5Mode_three` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5Mode_two` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5Mode_two_eq_three` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5Mode_zero` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| DEFINITION | `Brockian.C5SpectralMultiplicities.c5SpectrumMultiset` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5SpectrumMultiset_card` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5SpectrumMultiset_eq` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5SpectrumMultiset_toFinset` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5_arg_four` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5_arg_one` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5_arg_three` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5_arg_two` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.c5_eigs_pairwise_distinct` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.goldenRatio_lt_two` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.golden_sub_one_mem_C5` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.golden_unique_to_five_setlevel` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.lap_gap_eq_connectivity` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.lap_large_eq` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.mem_c5SpectrumMultiset_iff` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.multiplicity_connectivity_gap` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.multiplicity_golden_sub_one` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.multiplicity_lap_gap` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.multiplicity_lap_large` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.multiplicity_lap_two_plus_phi` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.multiplicity_lap_zero` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.multiplicity_neg_golden` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.multiplicity_two` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.neg_golden_mem_C5` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.C5SpectralMultiplicities.two_mem_C5` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Connectivity.cos_2pi_5` | ✓ | verified | lean-4.32.0 | run 88 (1d2a…) — re-proved fresh @ v4.32 via concrete Laplacian eigenvalues |
| PROVED | `Brockian.Connectivity.lambda2_eq` | ✓ | verified | lean-4.32.0 | run 88 (1d2a…) — re-proved fresh @ v4.32 via concrete Laplacian eigenvalues |
| DEFINITION | `Brockian.Connectivity.laplacianEigs5` | ✓ | verified | lean-4.32.0 | run 88 (1d2a…) — re-proved fresh @ v4.32 via concrete Laplacian eigenvalues |
| PROVED | `Brockian.Connectivity.one_div_phi` | ✓ | verified | lean-4.32.0 | run 88 (1d2a…) — re-proved fresh @ v4.32 via concrete Laplacian eigenvalues |
| PROVED | `Brockian.Connectivity.pentagon_lambda2_phi` | ✓ | verified | lean-4.32.0 | run 88 (1d2a…) — re-proved fresh @ v4.32 via concrete Laplacian eigenvalues |
| PROVED | `Brockian.Connectivity.pentagon_ratio` | ✓ | verified | lean-4.32.0 | run 88 (1d2a…) — re-proved fresh @ v4.32 via concrete Laplacian eigenvalues |
| PROVED | `Brockian.Connectivity.two_cos_4pi_5` | ✓ | verified | lean-4.32.0 | run 88 (1d2a…) — re-proved fresh @ v4.32 via concrete Laplacian eigenvalues |
| PROVED | `Brockian.ConnectivityGoldenBridge.algebraic_connectivity_C5` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.algebraic_connectivity_C5_schema` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.algebraic_connectivity_schema` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.cos_two_pi_div_five_eq` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.golden_sub_one_eq_two_cos` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.golden_sub_one_mem_adjacency_C5` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.inv_phi_eq_phi_sub_one` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.lambda2_eq_cos_form` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.lambda2_eq_three_minus_phi` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.lambda2_eq_two_minus_phi_sub_one` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.lambda2_eq_two_minus_two_cos` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.lambda2_le_large_eig` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.lambda2_le_two_plus_phi` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.lambda2_mem_laplacianEigs5` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.lambda2_over_degree` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.lambda2_pos` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.lambda2_triple_identity` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.laplacian_gap_from_adjacency_mode` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.large_eig_eq_two_plus_phi` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.neg_phi_mem_adjacency_C5` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.two_cos_four_pi_div_five_eq_neg_phi` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.ConnectivityGoldenBridge.two_cos_four_pi_div_five_geometry` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| DEFINITION | `Brockian.Core.Ray` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.binet_formula` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.cos_2pi_5` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.cos_pi_div_five_eq_phi_div_two` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.each_ray_has_infinitely_many_primes` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.fib_five_dvd` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.fifth_root_of_unity` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.one_lt_phi` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| DEFINITION | `Brockian.Core.phi` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.phi_pos` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.phi_sq` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.ray_add` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.ray_mul` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.ray_ne_zero_infinite` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.ray_zero_iff_dvd` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.CosAlgebraicInteger.aeval_spectralGen_five_X_sq_add_X_sub_one` | ✓ | verified | lean-4.32.0 | parallel-tool module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.CosAlgebraicInteger.aeval_spectralGen_seven_cubic7` | ✓ | verified | lean-4.32.0 | parallel-tool module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.CosAlgebraicInteger.aeval_spectralGen_three_X_add_one` | ✓ | verified | lean-4.32.0 | parallel-tool module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.CosAlgebraicInteger.degree_five_pack` | ✓ | verified | lean-4.32.0 | parallel-tool module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.CosAlgebraicInteger.degree_seven_pack` | ✓ | verified | lean-4.32.0 | parallel-tool module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.CosAlgebraicInteger.degree_three_pack` | ✓ | verified | lean-4.32.0 | parallel-tool module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.CosAlgebraicInteger.isIntegral_and_degree` | ✓ | verified | lean-4.32.0 | parallel-tool module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.CosAlgebraicInteger.isIntegral_spectralGen` | ✓ | verified | lean-4.32.0 | parallel-tool module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.CosAlgebraicInteger.isIntegral_spectralGen_ℚ` | ✓ | verified | lean-4.32.0 | parallel-tool module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.CosAlgebraicInteger.isIntegral_two_cos_two_pi_div` | ✓ | verified | lean-4.32.0 | parallel-tool module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.CosAlgebraicInteger.isIntegral_two_cos_two_pi_div_ℚ` | ✓ | verified | lean-4.32.0 | parallel-tool module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.CosAlgebraicInteger.quadratic_iff_five_pack` | ✓ | verified | lean-4.32.0 | parallel-tool module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.CosAlgebraicInteger.real_subfield_degree_pack` | ✓ | verified | lean-4.32.0 | parallel-tool module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.CosAlgebraicInteger.two_pi_div_eq_rat_mul_pi` | ✓ | verified | lean-4.32.0 | parallel-tool module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.CosTraceNorm.coeff_zero_minpoly_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.coeff_zero_minpoly_seven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.coeff_zero_minpoly_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.isIntegral_spectralGen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.isIntegral_spectralGen_five_ℚ` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.isIntegral_spectralGen_seven_ℚ` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.isIntegral_spectralGen_three_ℚ` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.isIntegral_spectralGen_ℚ` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.isIntegral_two_cos_two_pi_div` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.isIntegral_two_cos_two_pi_div_ℚ` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.minpoly_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.minpoly_seven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.minpoly_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.nextCoeff_minpoly_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.nextCoeff_minpoly_seven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.nextCoeff_minpoly_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.norm_adjoin_gen_eq_coeff_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.norm_spectralGen_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.norm_spectralGen_seven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.norm_spectralGen_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.trace_adjoin_gen_eq_neg_nextCoeff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.trace_norm_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.trace_spectralGen_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.trace_spectralGen_seven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNorm.trace_spectralGen_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEightyNine.degree_eightyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEightyNine.eightyNine_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEightyNine.eightyNine_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEightyNine.isIntegral_and_degree_eightyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEightyNine.isIntegral_spectralGen_eightyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEightyNine.isIntegral_spectralGen_eightyNine_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEightyNine.prime_eightyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEightyThree.degree_eightyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEightyThree.eightyThree_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEightyThree.eightyThree_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEightyThree.isIntegral_and_degree_eightyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEightyThree.isIntegral_spectralGen_eightyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEightyThree.isIntegral_spectralGen_eightyThree_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEightyThree.prime_eightyThree` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.CosTraceNormEleven.P11` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.P11_monic` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.P11_natDegree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.Psi_eleven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.coeff_zero_minpoly_eleven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.degree_eleven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.degree_eleven_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.degree_odd_prime` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.eleven_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.eleven_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.isIntegral_and_degree_eleven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.isIntegral_and_degree_odd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.isIntegral_spectralGen_eleven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.isIntegral_spectralGen_eleven_ℚ` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.isIntegral_spectralGen_odd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.isIntegral_spectralGen_odd_ℚ` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.minpoly_eleven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.minpoly_eq_Psi` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.nextCoeff_minpoly_eleven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.norm_adjoin_gen_eq_coeff_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.norm_spectralGen_eleven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.prime_eleven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.trace_adjoin_gen_eq_neg_nextCoeff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.trace_norm_eleven_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormEleven.trace_spectralGen_eleven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFiftyNine.degree_fiftyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFiftyNine.fiftyNine_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFiftyNine.fiftyNine_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFiftyNine.isIntegral_and_degree_fiftyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFiftyNine.isIntegral_spectralGen_fiftyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFiftyNine.isIntegral_spectralGen_fiftyNine_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFiftyNine.prime_fiftyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFiftyThree.degree_fiftyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFiftyThree.fiftyThree_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFiftyThree.fiftyThree_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFiftyThree.isIntegral_and_degree_fiftyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFiftyThree.isIntegral_spectralGen_fiftyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFiftyThree.isIntegral_spectralGen_fiftyThree_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFiftyThree.prime_fiftyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortyOne.degree_fortyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortyOne.fortyOne_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortyOne.fortyOne_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortyOne.isIntegral_and_degree_fortyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortyOne.isIntegral_spectralGen_fortyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortyOne.isIntegral_spectralGen_fortyOne_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortyOne.prime_fortyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortySeven.degree_fortySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortySeven.fortySeven_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortySeven.fortySeven_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortySeven.isIntegral_and_degree_fortySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortySeven.isIntegral_spectralGen_fortySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortySeven.isIntegral_spectralGen_fortySeven_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortySeven.prime_fortySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortyThree.degree_fortyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortyThree.fortyThree_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortyThree.fortyThree_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortyThree.isIntegral_and_degree_fortyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortyThree.isIntegral_spectralGen_fortyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortyThree.isIntegral_spectralGen_fortyThree_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormFortyThree.prime_fortyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormNineteen.degree_nineteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormNineteen.isIntegral_and_degree_nineteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormNineteen.isIntegral_spectralGen_nineteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormNineteen.isIntegral_spectralGen_nineteen_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormNineteen.nineteen_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormNineteen.nineteen_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormNineteen.prime_nineteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormNinetySeven.degree_ninetySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormNinetySeven.isIntegral_and_degree_ninetySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormNinetySeven.isIntegral_spectralGen_ninetySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormNinetySeven.isIntegral_spectralGen_ninetySeven_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormNinetySeven.ninetySeven_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormNinetySeven.ninetySeven_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormNinetySeven.prime_ninetySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredNine.degree_oneHundredNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredNine.isIntegral_and_degree_oneHundredNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredNine.isIntegral_spectralGen_oneHundredNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredNine.isIntegral_spectralGen_oneHundredNine_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredNine.oneHundredNine_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredNine.oneHundredNine_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredNine.prime_oneHundredNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredOne.degree_oneHundredOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredOne.isIntegral_and_degree_oneHundredOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredOne.isIntegral_spectralGen_oneHundredOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredOne.isIntegral_spectralGen_oneHundredOne_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredOne.oneHundredOne_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredOne.oneHundredOne_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredOne.prime_oneHundredOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredSeven.degree_oneHundredSeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredSeven.isIntegral_and_degree_oneHundredSeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredSeven.isIntegral_spectralGen_oneHundredSeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredSeven.isIntegral_spectralGen_oneHundredSeven_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredSeven.oneHundredSeven_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredSeven.oneHundredSeven_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredSeven.prime_oneHundredSeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirteen.degree_oneHundredThirteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirteen.isIntegral_and_degree_oneHundredThirteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirteen.isIntegral_spectralGen_oneHundredThirteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirteen.isIntegral_spectralGen_oneHundredThirteen_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirteen.oneHundredThirteen_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirteen.oneHundredThirteen_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirteen.prime_oneHundredThirteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirtyOne.degree_oneHundredThirtyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirtyOne.isIntegral_and_degree_oneHundredThirtyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirtyOne.isIntegral_spectralGen_oneHundredThirtyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirtyOne.isIntegral_spectralGen_oneHundredThirtyOne_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirtyOne.oneHundredThirtyOne_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirtyOne.oneHundredThirtyOne_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirtyOne.prime_oneHundredThirtyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirtySeven.degree_oneHundredThirtySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirtySeven.isIntegral_and_degree_oneHundredThirtySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirtySeven.isIntegral_spectralGen_oneHundredThirtySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirtySeven.isIntegral_spectralGen_oneHundredThirtySeven_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirtySeven.oneHundredThirtySeven_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirtySeven.oneHundredThirtySeven_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThirtySeven.prime_oneHundredThirtySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThree.degree_oneHundredThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThree.isIntegral_and_degree_oneHundredThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThree.isIntegral_spectralGen_oneHundredThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThree.isIntegral_spectralGen_oneHundredThree_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThree.oneHundredThree_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThree.oneHundredThree_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredThree.prime_oneHundredThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredTwentySeven.degree_oneHundredTwentySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredTwentySeven.isIntegral_and_degree_oneHundredTwentySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredTwentySeven.isIntegral_spectralGen_oneHundredTwentySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredTwentySeven.isIntegral_spectralGen_oneHundredTwentySeven_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredTwentySeven.oneHundredTwentySeven_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredTwentySeven.oneHundredTwentySeven_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormOneHundredTwentySeven.prime_oneHundredTwentySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventeen.degree_seventeen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventeen.isIntegral_and_degree_seventeen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventeen.isIntegral_spectralGen_seventeen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventeen.isIntegral_spectralGen_seventeen_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventeen.prime_seventeen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventeen.seventeen_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventeen.seventeen_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyNine.degree_seventyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyNine.isIntegral_and_degree_seventyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyNine.isIntegral_spectralGen_seventyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyNine.isIntegral_spectralGen_seventyNine_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyNine.prime_seventyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyNine.seventyNine_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyNine.seventyNine_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyOne.degree_seventyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyOne.isIntegral_and_degree_seventyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyOne.isIntegral_spectralGen_seventyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyOne.isIntegral_spectralGen_seventyOne_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyOne.prime_seventyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyOne.seventyOne_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyOne.seventyOne_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyThree.degree_seventyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyThree.isIntegral_and_degree_seventyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyThree.isIntegral_spectralGen_seventyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyThree.isIntegral_spectralGen_seventyThree_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyThree.prime_seventyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyThree.seventyThree_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSeventyThree.seventyThree_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSixtyOne.degree_sixtyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSixtyOne.isIntegral_and_degree_sixtyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSixtyOne.isIntegral_spectralGen_sixtyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSixtyOne.isIntegral_spectralGen_sixtyOne_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSixtyOne.prime_sixtyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSixtyOne.sixtyOne_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSixtyOne.sixtyOne_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSixtySeven.degree_sixtySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSixtySeven.isIntegral_and_degree_sixtySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSixtySeven.isIntegral_spectralGen_sixtySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSixtySeven.isIntegral_spectralGen_sixtySeven_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSixtySeven.prime_sixtySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSixtySeven.sixtySeven_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormSixtySeven.sixtySeven_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirteen.degree_thirteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirteen.isIntegral_and_degree_thirteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirteen.isIntegral_spectralGen_thirteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirteen.isIntegral_spectralGen_thirteen_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirteen.prime_thirteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirteen.thirteen_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirteen.thirteen_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirtyOne.degree_thirtyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirtyOne.isIntegral_and_degree_thirtyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirtyOne.isIntegral_spectralGen_thirtyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirtyOne.isIntegral_spectralGen_thirtyOne_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirtyOne.prime_thirtyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirtyOne.thirtyOne_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirtyOne.thirtyOne_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirtySeven.degree_thirtySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirtySeven.isIntegral_and_degree_thirtySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirtySeven.isIntegral_spectralGen_thirtySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirtySeven.isIntegral_spectralGen_thirtySeven_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirtySeven.prime_thirtySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirtySeven.thirtySeven_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormThirtySeven.thirtySeven_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormTwentyNine.degree_twentyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormTwentyNine.isIntegral_and_degree_twentyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormTwentyNine.isIntegral_spectralGen_twentyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormTwentyNine.isIntegral_spectralGen_twentyNine_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormTwentyNine.prime_twentyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormTwentyNine.twentyNine_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormTwentyNine.twentyNine_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormTwentyThree.degree_twentyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormTwentyThree.isIntegral_and_degree_twentyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormTwentyThree.isIntegral_spectralGen_twentyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormTwentyThree.isIntegral_spectralGen_twentyThree_Q` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormTwentyThree.prime_twentyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormTwentyThree.twentyThree_ne_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CosTraceNormTwentyThree.twentyThree_pack` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.CycleSpectrumFamily.algebraic_connectivity_five` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.algebraic_connectivity_five_props` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.algebraic_connectivity_le_four` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.algebraic_connectivity_mem` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.algebraic_connectivity_pos` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cos_four_pi_div_three` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cos_two_pi_div_three` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycle3_eig_one` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycle3_eig_two` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycle3_eig_zero` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycle4_eig_one` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycle4_eig_three` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycle4_eig_two` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycle4_eig_zero` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycle6_eig_five` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycle6_eig_four` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycle6_eig_one` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycle6_eig_three` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycle6_eig_two` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycle6_eig_zero` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycleSpectrum_ge_neg_two` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycleSpectrum_le_two` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycleSpectrum_subset_Icc` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.cycle_eig_one` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.golden_in_C5` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.golden_unique_among_prime_cycles` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.lambda_max_cycle` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| DEFINITION | `Brockian.CycleSpectrumFamily.laplacianCycleSpectrum` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.laplacianCycleSpectrum_le_four` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.laplacianCycleSpectrum_nonneg` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.mem_cycleSpectrum` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.mem_laplacianCycleSpectrum` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.neg_golden_in_C5` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.two_cos_pi_div_three` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.two_cos_two_pi_div_five_eq_golden_sub_one` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.two_cos_two_pi_div_three` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.two_mem_cycleSpectrum` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CycleSpectrumFamily.zero_mem_laplacianCycleSpectrum` | ✓ | verified | lean-4.32.0 | Spectral generalization — cycle spectrum for general C_n; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicGaloisGroup.realSubfield_facts_general` | ✓ | verified | lean-4.32.0 | batch — composite-n Galois group of the real cyclotomic subfield; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicGaloisGroup.realSubfield_gal_card` | ✓ | verified | lean-4.32.0 | batch — composite-n Galois group of the real cyclotomic subfield; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicGaloisGroup.realSubfield_gal_equivUnitsQuotient` | ✓ | verified | lean-4.32.0 | batch — composite-n Galois group of the real cyclotomic subfield; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicGaloisGroup.realSubfield_gal_isCyclic_of_prime` | ✓ | verified | lean-4.32.0 | batch — composite-n Galois group of the real cyclotomic subfield; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicGaloisGroup.realSubfield_gal_isQuotientOfUnits` | ✓ | verified | lean-4.32.0 | batch — composite-n Galois group of the real cyclotomic subfield; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicGaloisGroup.realSubfield_gal_units_presentation` | ✓ | verified | lean-4.32.0 | batch — composite-n Galois group of the real cyclotomic subfield; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicGaloisGroup.realSubfield_isAbelianGalois` | ✓ | verified | lean-4.32.0 | batch — composite-n Galois group of the real cyclotomic subfield; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicGaloisGroup.realSubfield_isGalois` | ✓ | verified | lean-4.32.0 | batch — composite-n Galois group of the real cyclotomic subfield; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicRealDegree.pentagon_quadratic` | ✓ | verified | lean-4.32.0 | roadmap #6+#8 — composite-n real cyclotomic degree + quadratic classification; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicRealDegree.quadratic_iff_mem` | ✓ | verified | lean-4.32.0 | roadmap #6+#8 — composite-n real cyclotomic degree + quadratic classification; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicRealDegree.quadratic_iff_totient_four` | ✓ | verified | lean-4.32.0 | roadmap #6+#8 — composite-n real cyclotomic degree + quadratic classification; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicRealDegree.spectral_degree_general` | ✓ | verified | lean-4.32.0 | roadmap #6+#8 — composite-n real cyclotomic degree + quadratic classification; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicRealDegree.spectral_natDegree_two_mul` | ✓ | verified | lean-4.32.0 | roadmap #6+#8 — composite-n real cyclotomic degree + quadratic classification; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicRealDegree.totient_eq_four_iff` | ✓ | verified | lean-4.32.0 | roadmap #6+#8 — composite-n real cyclotomic degree + quadratic classification; AXLE @4.32 |
| DEFINITION | `Brockian.D5CharacterComplete.charInner` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.charInner_eq_pairSum` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| DEFINITION | `Brockian.D5CharacterComplete.chiConjugate` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.chiConjugate_one` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.chiConjugate_real` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| DEFINITION | `Brockian.D5CharacterComplete.chiGolden` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.chiGolden_one` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.chiGolden_real` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| DEFINITION | `Brockian.D5CharacterComplete.chiSign` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.chiSign_one` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.chiSign_real` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| DEFINITION | `Brockian.D5CharacterComplete.chiTrivial` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.chiTrivial_one` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.chiTrivial_real` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| DEFINITION | `Brockian.D5CharacterComplete.colInner` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.colInner_one_one` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.colInner_one_r1` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.colInner_one_r2` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.colInner_one_sr0` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.colInner_r1_r1` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.colInner_r1_r2` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.colInner_r1_sr0` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.colInner_r2_r2` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.colInner_r2_sr0` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.colInner_sr0_sr0` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.col_orthogonal` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| DEFINITION | `Brockian.D5CharacterComplete.conjRot` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.conjRot_col` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.conjRot_one` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.conjRot_real` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.conjRot_two` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.conjRot_zero` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.dimension_identity` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.dimension_identity_card` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.goldenRatio_sq_complex` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| DEFINITION | `Brockian.D5CharacterComplete.goldenRot` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.goldenRot_col` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.goldenRot_eq_adjEigenvalue` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.goldenRot_one` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.goldenRot_real` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.goldenRot_two` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.goldenRot_zero` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.golden_char_eq_two_cos` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.golden_char_rotation_class` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.omegaPow_col_mul` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.one_eq_r0` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| DEFINITION | `Brockian.D5CharacterComplete.pairSum` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.pairSum_split` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.rot_CC` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.rot_C_sum` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.rot_GC` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.rot_GG` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.rot_G_sum` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.row_CC` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.row_GC` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.row_GG` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.row_SC` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.row_SG` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.row_SS` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.row_TC` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.row_TG` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.row_TS` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.row_TT` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.row_orthonormal` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.star_omega` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.star_omegaPow` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.sum_dihedral5` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.sum_omega_binom` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| PROVED | `Brockian.D5CharacterComplete.sum_omega_binom_prod` | ✓ | verified | lean-4.32.0 | batch — full D5 irreducible character table + orthogonality; AXLE @4.32 |
| DEFINITION | `Brockian.D5CharacterTable.d5Character` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5CharacterTable.d5Character_eq_sum_fixed` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5CharacterTable.d5Character_one` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5CharacterTable.d5Character_reflection` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5CharacterTable.d5Character_rotation` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5CharacterTable.d5Character_rotation_ne_zero` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.D5CharacterTable.d5PermutationMatrix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5CharacterTable.d5PermutationMatrix_apply` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5CharacterTable.d5PermutationMatrix_mulVec` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.D5FourierInversion.fourierCoeff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5FourierInversion.fourierCoeff_add` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5FourierInversion.fourierCoeff_eigenmode` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5FourierInversion.fourierCoeff_smul` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5FourierInversion.fourier_inversion` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5FourierInversion.isotypicProjector_add` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5FourierInversion.isotypicProjector_eq_fourierCoeff_smul` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5FourierInversion.isotypicProjector_idempotent` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5FourierInversion.isotypicProjector_orthogonal` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5FourierInversion.sum_isotypicProjectors` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.character_orthogonality` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.coordSum_eigenmode` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.d5Pull_r_apply` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.d5Pull_r_eigenmode` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.d5Pull_r_mul` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.d5Pull_r_one_apply` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.d5Pull_r_one_eigenmode` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.D5Isotypic.eigenmode` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.eigenmode_mem_zeroSumSubmodule` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.eigenmode_zero` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.D5Isotypic.isotypicProjector` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.isotypicProjector_apply` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.isotypicProjector_eigenmode` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.isotypicProjector_eigenmode_of_ne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.isotypicProjector_eigenmode_self` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.isotypicProjector_idempotent_eigenmode` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.isotypicProjector_idempotent_self` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.isotypicProjector_orthogonal_eigenmode` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.isotypicProjector_smul` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.D5Isotypic.omega` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.D5Isotypic.omegaPow` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.omegaPow_add` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.omegaPow_neg` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.omega_isPrimitiveRoot` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.omega_pow_eq_one_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.omega_pow_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.omega_pow_modEq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.orderOf_omega` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.sum_omegaPow` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.D5Isotypic.sum_omegaPow_ne_zero` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.D5LaplacianModes.adjacency` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| DEFINITION | `Brockian.D5LaplacianModes.adjacencyLinear` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.adjacencyLinear_apply` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.adjacency_add` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.adjacency_apply` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.adjacency_commute_isotypicProjector_eigenmode` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.adjacency_eigenmode` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.adjacency_eigenmode_cos` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.adjacency_eigenmode_zero` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.adjacency_eq_pullbacks` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.adjacency_isotypicProjector_eigenmode` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.adjacency_smul` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| DEFINITION | `Brockian.D5LaplacianModes.laplacian` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| DEFINITION | `Brockian.D5LaplacianModes.laplacianLinear` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.laplacianLinear_apply` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.laplacian_add` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.laplacian_apply` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.laplacian_commute_isotypicProjector_eigenmode` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.laplacian_eigenmode` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.laplacian_eigenmode_zero` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.laplacian_eq` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.laplacian_isotypicProjector_eigenmode` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.laplacian_smul` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.omegaPow_add_inv_eq_two_cos` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.omegaPow_eq_exp` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.D5LaplacianModes.omegaPow_eq_exp_mul_I` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| DEFINITION | `Brockian.D5Representation.VertexSpace` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| DEFINITION | `Brockian.D5Representation.autPull` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| PROVED | `Brockian.D5Representation.autPull_apply` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| PROVED | `Brockian.D5Representation.autPull_constant` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| PROVED | `Brockian.D5Representation.autPull_mem_constantLine` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| PROVED | `Brockian.D5Representation.autPull_mem_zeroSumSubmodule` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| DEFINITION | `Brockian.D5Representation.constantLine` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| DEFINITION | `Brockian.D5Representation.constantLinear` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| PROVED | `Brockian.D5Representation.constantLinear_apply` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| DEFINITION | `Brockian.D5Representation.constantVector` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| PROVED | `Brockian.D5Representation.constantVector_mem_zeroSumSubmodule_iff` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| DEFINITION | `Brockian.D5Representation.coordSum` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| DEFINITION | `Brockian.D5Representation.coordSumLinear` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| PROVED | `Brockian.D5Representation.coordSumLinear_apply` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| PROVED | `Brockian.D5Representation.coordSum_autPull` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| PROVED | `Brockian.D5Representation.coordSum_constantVector` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| PROVED | `Brockian.D5Representation.coordSum_d5Pull` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| DEFINITION | `Brockian.D5Representation.d5AutEquiv` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| DEFINITION | `Brockian.D5Representation.d5Pull` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| PROVED | `Brockian.D5Representation.d5Pull_apply` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| PROVED | `Brockian.D5Representation.d5Pull_constant` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| PROVED | `Brockian.D5Representation.d5Pull_mem_constantLine` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| PROVED | `Brockian.D5Representation.d5Pull_mem_zeroSumSubmodule` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| DEFINITION | `Brockian.D5Representation.zeroSumSubmodule` | ✓ | verified | lean-4.32.0 | 2026-08-01 — finite D5 permutation representation foothold |
| DEFINITION | `Brockian.Equidistribution.AsymptoticExists` | ✓ | verified | lean-4.32.0 | paper-audit target #1 2026-08-01 — HL/BV asymptotic ⇒ 1/(q−2) density (schema) |
| DEFINITION | `Brockian.Equidistribution.PrimePairAsymptotic` | ✓ | verified | lean-4.32.0 | paper-audit target #1 2026-08-01 — HL/BV asymptotic ⇒ 1/(q−2) density (schema) |
| PROVED | `Brockian.Equidistribution.asymptotic_shape_consistent` | ✓ | verified | lean-4.32.0 | paper-audit target #1 2026-08-01 — HL/BV asymptotic ⇒ 1/(q−2) density (schema) |
| DEFINITION | `Brockian.Equidistribution.configCount` | ✓ | verified | lean-4.32.0 | paper-audit target #1 2026-08-01 — HL/BV asymptotic ⇒ 1/(q−2) density (schema) |
| PROVED | `Brockian.Equidistribution.configCount_twelve_five_two_one` | ✓ | verified | lean-4.32.0 | paper-audit target #1 2026-08-01 — HL/BV asymptotic ⇒ 1/(q−2) density (schema) |
| PROVED | `Brockian.Equidistribution.configCount_twenty_five_two_two` | ✓ | verified | lean-4.32.0 | paper-audit target #1 2026-08-01 — HL/BV asymptotic ⇒ 1/(q−2) density (schema) |
| CONDITIONAL | `Brockian.Equidistribution.equidistribution_of_asymptotic` | ✓ | verified | lean-4.32.0 | paper-audit target #1 2026-08-01 — HL/BV asymptotic ⇒ 1/(q−2) density (schema) |
| CONDITIONAL | `Brockian.Equidistribution.equidistribution_of_asymptotic_exists` | ✓ | verified | lean-4.32.0 | paper-audit target #1 2026-08-01 — HL/BV asymptotic ⇒ 1/(q−2) density (schema) |
| PROVED | `Brockian.Equidistribution.prime_pair_config_admissible` | ✓ | verified | lean-4.32.0 | paper-audit target #1 2026-08-01 — HL/BV asymptotic ⇒ 1/(q−2) density (schema) |
| DEFINITION | `Brockian.Equidistribution.totalConfigCount` | ✓ | verified | lean-4.32.0 | paper-audit target #1 2026-08-01 — HL/BV asymptotic ⇒ 1/(q−2) density (schema) |
| DEFINITION | `Brockian.Equidistribution.DeviationBound.FiniteRangeErrorBudget` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.DeviationBound.pairCount_deviation_le_scaled_err_of_large_pairs` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.DeviationBound.pairCount_normalized_deviation_le_scaled_epsilon_of_large_pairs` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.DeviationBound.perConfig_deviation_le_err` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.DeviationBound.perConfig_normalized_deviation_le_epsilon` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.DeviationBound.perConfig_normalized_deviation_le_one_third` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.DeviationBound.totalConfig_deviation_le_scaled_err` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.DeviationBound.totalConfig_normalized_deviation_le_one_third_scaled` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.DeviationBound.totalConfig_normalized_deviation_le_scaled_epsilon` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.FiniteScaffold.configCount_deviation_bound` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.FiniteScaffold.configCount_eq_zero_of_not_admissible_of_large_pairs` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.FiniteScaffold.configCount_le_window` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.FiniteScaffold.mem_pairStarts` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Equidistribution.FiniteScaffold.pairCount` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Equidistribution.FiniteScaffold.pairStarts` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.FiniteScaffold.sum_configCount_univ_eq_pairCount` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.FiniteScaffold.totalConfigCount_deviation_bound` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.FiniteScaffold.totalConfigCount_eq_pairCount_of_large_pairs` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.FiniteScaffold.totalConfigCount_le_admissible_card_mul_window` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Equidistribution.FiniteScaffold.totalConfigCount_le_q_sub_two_mul_window` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.EquidistributionBVReduction.BVPrimePairAsymptotic` | ✓ | verified | lean-4.32.0 | roadmap #18 — honest reduction of equidistribution to a named BV hypothesis (rung open->literature); AXLE @4.32 |
| PROVED | `Brockian.EquidistributionBVReduction.admissible_reflection_symmetry` | ✓ | verified | lean-4.32.0 | roadmap #18 — honest reduction of equidistribution to a named BV hypothesis (rung open->literature); AXLE @4.32 |
| PROVED | `Brockian.EquidistributionBVReduction.bv_shape_consistent` | ✓ | verified | lean-4.32.0 | roadmap #18 — honest reduction of equidistribution to a named BV hypothesis (rung open->literature); AXLE @4.32 |
| CONDITIONAL | `Brockian.EquidistributionBVReduction.configCount_density_of_BV` | ✓ | verified | lean-4.32.0 | roadmap #18 — honest reduction of equidistribution to a named BV hypothesis (rung open->literature); AXLE @4.32 |
| CONDITIONAL | `Brockian.EquidistributionBVReduction.configCount_over_main_tendsto` | ✓ | verified | lean-4.32.0 | roadmap #18 — honest reduction of equidistribution to a named BV hypothesis (rung open->literature); AXLE @4.32 |
| CONDITIONAL | `Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform` | ✓ | verified | lean-4.32.0 | roadmap #18 — honest reduction of equidistribution to a named BV hypothesis (rung open->literature); AXLE @4.32 |
| CONDITIONAL | `Brockian.EquidistributionBVReduction.total_over_main_tendsto` | ✓ | verified | lean-4.32.0 | roadmap #18 — honest reduction of equidistribution to a named BV hypothesis (rung open->literature); AXLE @4.32 |
| DEFINITION | `Brockian.EquidistributionUniformity.IterTransitive` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| DEFINITION | `Brockian.EquidistributionUniformity.PreservesAdmissible` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| DEFINITION | `Brockian.EquidistributionUniformity.SingInvariant` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| CONDITIONAL | `Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformity.equidistribution_three` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformity.iterate_mem_admissible` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| DEFINITION | `Brockian.EquidistributionUniformity.reflect` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformity.reflect_affine` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformity.reflect_five_fixes_four` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformity.reflect_five_four_orbit` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformity.reflect_five_swaps_one` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformity.reflect_five_swaps_two` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformity.reflect_involutive` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformity.reflect_preservesAdmissible` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformity.reflect_preserves_admissible` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformity.reflection_not_transitive_five` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformity.sing_iterate` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| CONDITIONAL | `Brockian.EquidistributionUniformity.sing_uniform_of_transitive` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformity.sing_uniform_three` | ✓ | verified | lean-4.32.0 | roadmap B1 — equidistribution uniformity symmetry; q=3 unconditional, q=5 obstruction proved; AXLE @4.32 |
| DEFINITION | `Brockian.EquidistributionUniformityClosure.AffineStabilizesForbiddenFive` | ✓ | verified | lean-4.32.0 | roadmap B1 closure — q=5 affine endpoint-stabilizer obstruction; AXLE @4.32 |
| DEFINITION | `Brockian.EquidistributionUniformityClosure.affineMapFive` | ✓ | verified | lean-4.32.0 | roadmap B1 closure — q=5 affine endpoint-stabilizer obstruction; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformityClosure.affine_stabilizer_five_classification` | ✓ | verified | lean-4.32.0 | roadmap B1 closure — q=5 affine endpoint-stabilizer obstruction; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformityClosure.affine_stabilizer_five_fixes_four` | ✓ | verified | lean-4.32.0 | roadmap B1 closure — q=5 affine endpoint-stabilizer obstruction; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformityClosure.affine_stabilizer_five_four_orbit` | ✓ | verified | lean-4.32.0 | roadmap B1 closure — q=5 affine endpoint-stabilizer obstruction; AXLE @4.32 |
| PROVED | `Brockian.EquidistributionUniformityClosure.affine_stabilizer_five_not_transitive` | ✓ | verified | lean-4.32.0 | roadmap B1 closure — q=5 affine endpoint-stabilizer obstruction; AXLE @4.32 |
| DEFINITION | `Brockian.EquidistributionUniformityClosure.forbiddenFive` | ✓ | verified | lean-4.32.0 | roadmap B1 closure — q=5 affine endpoint-stabilizer obstruction; AXLE @4.32 |
| DEFINITION | `Brockian.EquidistributionUniformityClosure.forbiddenImageFive` | ✓ | verified | lean-4.32.0 | roadmap B1 closure — q=5 affine endpoint-stabilizer obstruction; AXLE @4.32 |
| DEFINITION | `Brockian.Erdos236.f` | ✓ | verified | lean-4.32.0 | Erdős #236 harvest — ONLY the verified unconditional trivial bound; AXLE @4.32 |
| PROVED | `Brockian.Erdos236.f_le_log` | ✓ | verified | lean-4.32.0 | Erdős #236 harvest — ONLY the verified unconditional trivial bound; AXLE @4.32 |
| PROVED | `Brockian.ErdosPinned.entropy_le_log_card` | ✓ | verified | lean-4.32.0 | Erdős #604 harvest — verified unconditional entropy inequalities (one omitted in the paper); AXLE @4.32 |
| PROVED | `Brockian.ErdosPinned.exp_neg_entropy_le_sum_sq` | ✓ | verified | lean-4.32.0 | Erdős #604 harvest — verified unconditional entropy inequalities (one omitted in the paper); AXLE @4.32 |
| DEFINITION | `Brockian.ErdosStraus.ErdosStraus` | ✓ | verified | lean-4.32.0 | open-territory swarm; AXLE @4.32 |
| CONJECTURE | `Brockian.ErdosStraus.ErdosStrausConjecture` | ✓ | verified | lean-4.32.0 | open-territory swarm; AXLE @4.32 |
| PROVED | `Brockian.ErdosStraus.erdosStraus_dvd_three` | ✓ | verified | lean-4.32.0 | open-territory swarm; AXLE @4.32 |
| PROVED | `Brockian.ErdosStraus.erdosStraus_even` | ✓ | verified | lean-4.32.0 | open-territory swarm; AXLE @4.32 |
| PROVED | `Brockian.ErdosStraus.erdosStraus_mod3_two` | ✓ | verified | lean-4.32.0 | open-territory swarm; AXLE @4.32 |
| PROVED | `Brockian.ErdosStraus.erdosStraus_mod4_three` | ✓ | verified | lean-4.32.0 | open-territory swarm; AXLE @4.32 |
| PROVED | `Brockian.ErdosStraus.erdosStraus_of_covered` | ✓ | verified | lean-4.32.0 | open-territory swarm; AXLE @4.32 |
| PROVED | `Brockian.ErdosStraus.erdosStraus_of_dvd` | ✓ | verified | lean-4.32.0 | open-territory swarm; AXLE @4.32 |
| PROVED | `Brockian.ErdosStraus.erdosStraus_of_prime_case` | ✓ | verified | lean-4.32.0 | open-territory swarm; AXLE @4.32 |
| PROVED | `Brockian.Fin5InnerProduct.conj_omega` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Fin5InnerProduct.conj_omegaPow` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Fin5InnerProduct.conj_omega_pow` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Fin5InnerProduct.eigenmode_orthogonal` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Fin5InnerProduct.hermInner` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Fin5InnerProduct.hermInner_add_left` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Fin5InnerProduct.hermInner_add_right` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Fin5InnerProduct.hermInner_conj_symm` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Fin5InnerProduct.hermInner_eigenmode` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Fin5InnerProduct.hermInner_eigenmode_self` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Fin5InnerProduct.hermInner_eigenmode_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Fin5InnerProduct.hermInner_self` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Fin5InnerProduct.hermInner_self_eq_zero_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Fin5InnerProduct.hermInner_smul_left` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Fin5InnerProduct.hermInner_smul_right` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Fin5InnerProduct.norm_omega` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.FranklinFixedPoint.downMs_upPart` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.downOverlap_stair` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.downPart_largest` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.downPart_notFixed` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.downPart_sPart_gt` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.downPart_tDiag` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.down_L_ge` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.fixedPart_mem_iff` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.fixedPart_overlap` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinFixedPoint.franklinMap_exists` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.hd_of_mem` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.hu_of_mem` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.largestPart_eq_of` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.largestPart_of_stair_neg` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.largestPart_of_stair_pos` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.mem_stair_natCast` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.mem_stair_neg_natCast` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.parts_ne_zero_of_mem` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.pentagonalNumberTheorem` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.phi_notFixed` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.phi_parts` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.phi_phi_eq` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.sPart_eq_of` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.sPart_of_stair_neg` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.sPart_of_stair_pos` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.stair_mem_iff` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.tDiag_of_stair_neg` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.tDiag_of_stair_pos` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.upMs_downPart` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.upOverlap_stair` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.upPart_largest` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.upPart_le_branch` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.upPart_notFixed` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.upPart_sPart` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| PROVED | `Brockian.FranklinFixedPoint.up_L_gt` | ✓ | verified | lean-4.32.0 | roadmap #1 CLOSED — Euler pentagonal number theorem proved UNCONDITIONALLY; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinInvolution.FranklinData` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| DISCHARGED | `Brockian.FranklinInvolution.franklin_of_franklinData` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinInvolution.largestPart` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.largestPart_mem` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.le_largestPart` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.mem_of_lt_tDiag` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.one_le_tDiag` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| DISCHARGED | `Brockian.FranklinInvolution.pentagonalNumberTheorem_of_franklinData` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinInvolution.sPart` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.sPart_le` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.sPart_mem` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinInvolution.signOf` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.signOf_ne_zero` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.signedSum_eq_fixed_of_involution` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| DISCHARGED | `Brockian.FranklinInvolution.signedSum_eq_pentCoeff_of_franklinData` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinInvolution.tDiag` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.tDiag_gap_exists` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.tDiag_notMem` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinInvolutionProof.FranklinMap` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinInvolutionProof.fixedPart` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolutionProof.fixedPart_subset` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolutionProof.fixedPart_sum` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinInvolutionProof.franklinData_of_franklinMap` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolutionProof.franklin_sum_invariant_down` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolutionProof.franklin_sum_invariant_up` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolutionProof.gauss_int` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolutionProof.neg_one_pow_natAbs` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| DISCHARGED | `Brockian.FranklinInvolutionProof.pentagonalNumberTheorem_of_franklinMap` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinInvolutionProof.stair` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinInvolutionProof.stairBase` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinInvolutionProof.stairPartAt` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolutionProof.stair_card` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolutionProof.stair_nodup` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolutionProof.stair_pos` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolutionProof.stair_sum` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolutionProof.stair_sum_eq` | ✓ | verified | lean-4.32.0 | roadmap #1 sharpening — Franklin fixed-point side (F2) proved; residual reduced to FranklinMap; AXLE @4.32 |
| PROVED | `Brockian.FranklinMapConstruction.d_mem` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinMapConstruction.downMs` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| PROVED | `Brockian.FranklinMapConstruction.downMs_card` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| PROVED | `Brockian.FranklinMapConstruction.downMs_nodup` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinMapConstruction.downPart` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| PROVED | `Brockian.FranklinMapConstruction.downPart_ne` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| PROVED | `Brockian.FranklinMapConstruction.downPart_sign` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinMapConstruction.franklinMap_of` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| PROVED | `Brockian.FranklinMapConstruction.nodup_of_sdiff` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinMapConstruction.phi` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| PROVED | `Brockian.FranklinMapConstruction.phiMem` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| PROVED | `Brockian.FranklinMapConstruction.phi_ne` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| PROVED | `Brockian.FranklinMapConstruction.phi_parts_nodup` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| PROVED | `Brockian.FranklinMapConstruction.phi_sign` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| PROVED | `Brockian.FranklinMapConstruction.sPart_le_largest` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| PROVED | `Brockian.FranklinMapConstruction.sPart_pos` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinMapConstruction.upMs` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| PROVED | `Brockian.FranklinMapConstruction.upMs_card` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| PROVED | `Brockian.FranklinMapConstruction.upMs_nodup` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinMapConstruction.upPart` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| PROVED | `Brockian.FranklinMapConstruction.upPart_ne` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| PROVED | `Brockian.FranklinMapConstruction.upPart_sign` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin involution CONSTRUCTED, 3/4 fields proved; residual = one fixed-point classification lemma; AXLE @4.32 |
| DEFINITION | `Brockian.FreeLaplacianPlancherel.L2R` | ✓ | verified | lean-4.32.0 | roadmap A3 — free-Laplacian ESA: unitary half discharged via genuine Mathlib Plancherel; AXLE @4.32 |
| PROVED | `Brockian.FreeLaplacianPlancherel.essentiallySelfAdjoint_fourierConj` | ✓ | verified | lean-4.32.0 | roadmap A3 — free-Laplacian ESA: unitary half discharged via genuine Mathlib Plancherel; AXLE @4.32 |
| DEFINITION | `Brockian.FreeLaplacianPlancherel.fourierL2` | ✓ | verified | lean-4.32.0 | roadmap A3 — free-Laplacian ESA: unitary half discharged via genuine Mathlib Plancherel; AXLE @4.32 |
| PROVED | `Brockian.FreeLaplacianPlancherel.fourierL2_inner_map` | ✓ | verified | lean-4.32.0 | roadmap A3 — free-Laplacian ESA: unitary half discharged via genuine Mathlib Plancherel; AXLE @4.32 |
| PROVED | `Brockian.FreeLaplacianPlancherel.fourierL2_norm_map` | ✓ | verified | lean-4.32.0 | roadmap A3 — free-Laplacian ESA: unitary half discharged via genuine Mathlib Plancherel; AXLE @4.32 |
| CONDITIONAL | `Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel` | ✓ | verified | lean-4.32.0 | roadmap A3 — free-Laplacian ESA: unitary half discharged via genuine Mathlib Plancherel; AXLE @4.32 |
| DEFINITION | `Brockian.GaloisCyclicGroup.alphaSub` | ✓ | verified | lean-4.32.0 | roadmap #7 — Galois group of the real cyclotomic subfield is cyclic of order (p-1)/2; AXLE @4.32 |
| PROVED | `Brockian.GaloisCyclicGroup.cycExt` | ✓ | verified | lean-4.32.0 | roadmap #7 — Galois group of the real cyclotomic subfield is cyclic of order (p-1)/2; AXLE @4.32 |
| PROVED | `Brockian.GaloisCyclicGroup.primRoot` | ✓ | verified | lean-4.32.0 | roadmap #7 — Galois group of the real cyclotomic subfield is cyclic of order (p-1)/2; AXLE @4.32 |
| DEFINITION | `Brockian.GaloisCyclicGroup.realSubfield` | ✓ | verified | lean-4.32.0 | roadmap #7 — Galois group of the real cyclotomic subfield is cyclic of order (p-1)/2; AXLE @4.32 |
| PROVED | `Brockian.GaloisCyclicGroup.realSubfield_facts` | ✓ | verified | lean-4.32.0 | roadmap #7 — Galois group of the real cyclotomic subfield is cyclic of order (p-1)/2; AXLE @4.32 |
| PROVED | `Brockian.GaloisCyclicGroup.realSubfield_gal_card` | ✓ | verified | lean-4.32.0 | roadmap #7 — Galois group of the real cyclotomic subfield is cyclic of order (p-1)/2; AXLE @4.32 |
| PROVED | `Brockian.GaloisCyclicGroup.realSubfield_gal_isCyclic` | ✓ | verified | lean-4.32.0 | roadmap #7 — Galois group of the real cyclotomic subfield is cyclic of order (p-1)/2; AXLE @4.32 |
| PROVED | `Brockian.GaloisCyclicGroup.realSubfield_isGalois` | ✓ | verified | lean-4.32.0 | roadmap #7 — Galois group of the real cyclotomic subfield is cyclic of order (p-1)/2; AXLE @4.32 |
| DEFINITION | `Brockian.GaloisCyclicGroup.zetaC` | ✓ | verified | lean-4.32.0 | roadmap #7 — Galois group of the real cyclotomic subfield is cyclic of order (p-1)/2; AXLE @4.32 |
| DEFINITION | `Brockian.GaloisCyclicGroup.zetaSub` | ✓ | verified | lean-4.32.0 | roadmap #7 — Galois group of the real cyclotomic subfield is cyclic of order (p-1)/2; AXLE @4.32 |
| PROVED | `Brockian.GaloisGeneralDegree.quadratic_iff_five_general` | ✓ | verified | lean-4.32.0 | roadmap #13 GENERAL — full why-five degree theorem for all odd primes; AXLE @4.32 |
| PROVED | `Brockian.GaloisGeneralDegree.real_subfield_degree` | ✓ | verified | lean-4.32.0 | roadmap #13 GENERAL — full why-five degree theorem for all odd primes; AXLE @4.32 |
| PROVED | `Brockian.GaloisMinPolyFamily.C_facts` | ✓ | verified | lean-4.32.0 | roadmap #5 — explicit minimal polynomial family of 2cos(2pi/p); AXLE @4.32 |
| DEFINITION | `Brockian.GaloisMinPolyFamily.Psi` | ✓ | verified | lean-4.32.0 | roadmap #5 — explicit minimal polynomial family of 2cos(2pi/p); AXLE @4.32 |
| PROVED | `Brockian.GaloisMinPolyFamily.Psi_eq_minpoly` | ✓ | verified | lean-4.32.0 | roadmap #5 — explicit minimal polynomial family of 2cos(2pi/p); AXLE @4.32 |
| PROVED | `Brockian.GaloisMinPolyFamily.Psi_five` | ✓ | verified | lean-4.32.0 | roadmap #5 — explicit minimal polynomial family of 2cos(2pi/p); AXLE @4.32 |
| PROVED | `Brockian.GaloisMinPolyFamily.Psi_monic` | ✓ | verified | lean-4.32.0 | roadmap #5 — explicit minimal polynomial family of 2cos(2pi/p); AXLE @4.32 |
| PROVED | `Brockian.GaloisMinPolyFamily.Psi_natDegree` | ✓ | verified | lean-4.32.0 | roadmap #5 — explicit minimal polynomial family of 2cos(2pi/p); AXLE @4.32 |
| PROVED | `Brockian.GaloisMinPolyFamily.Psi_seven` | ✓ | verified | lean-4.32.0 | roadmap #5 — explicit minimal polynomial family of 2cos(2pi/p); AXLE @4.32 |
| PROVED | `Brockian.GaloisMinPolyFamily.aeval_spectralGen_Psi` | ✓ | verified | lean-4.32.0 | roadmap #5 — explicit minimal polynomial family of 2cos(2pi/p); AXLE @4.32 |
| PROVED | `Brockian.GaloisMinPolyFamily.minpoly_five` | ✓ | verified | lean-4.32.0 | roadmap #5 — explicit minimal polynomial family of 2cos(2pi/p); AXLE @4.32 |
| PROVED | `Brockian.GaloisMinPolyFamily.minpoly_seven` | ✓ | verified | lean-4.32.0 | roadmap #5 — explicit minimal polynomial family of 2cos(2pi/p); AXLE @4.32 |
| PROVED | `Brockian.GaloisMinPolyFamily.psiAux` | ✓ | verified | lean-4.32.0 | roadmap #5 — explicit minimal polynomial family of 2cos(2pi/p); AXLE @4.32 |
| PROVED | `Brockian.GaloisNgonClassification.aeval_spectralGen_eight` | ✓ | verified | lean-4.32.0 | swarm capstone; AXLE @4.32 |
| PROVED | `Brockian.GaloisNgonClassification.aeval_spectralGen_ten` | ✓ | verified | lean-4.32.0 | swarm capstone; AXLE @4.32 |
| PROVED | `Brockian.GaloisNgonClassification.aeval_spectralGen_twelve` | ✓ | verified | lean-4.32.0 | swarm capstone; AXLE @4.32 |
| PROVED | `Brockian.GaloisNgonClassification.disc_eight` | ✓ | verified | lean-4.32.0 | swarm capstone; AXLE @4.32 |
| PROVED | `Brockian.GaloisNgonClassification.disc_five` | ✓ | verified | lean-4.32.0 | swarm capstone; AXLE @4.32 |
| PROVED | `Brockian.GaloisNgonClassification.disc_ten` | ✓ | verified | lean-4.32.0 | swarm capstone; AXLE @4.32 |
| PROVED | `Brockian.GaloisNgonClassification.disc_twelve` | ✓ | verified | lean-4.32.0 | swarm capstone; AXLE @4.32 |
| PROVED | `Brockian.GaloisNgonClassification.golden_ngons_are_five_and_ten` | ✓ | verified | lean-4.32.0 | swarm capstone; AXLE @4.32 |
| DEFINITION | `Brockian.GaloisNgonClassification.ngonDisc` | ✓ | verified | lean-4.32.0 | swarm capstone; AXLE @4.32 |
| PROVED | `Brockian.GaloisNgonClassification.quadratic_ngon_tfae` | ✓ | verified | lean-4.32.0 | swarm capstone; AXLE @4.32 |
| PROVED | `Brockian.GaloisNgonClassification.spectralGen_eight` | ✓ | verified | lean-4.32.0 | swarm capstone; AXLE @4.32 |
| PROVED | `Brockian.GaloisNgonClassification.spectralGen_ten` | ✓ | verified | lean-4.32.0 | swarm capstone; AXLE @4.32 |
| PROVED | `Brockian.GaloisNgonClassification.spectralGen_twelve` | ✓ | verified | lean-4.32.0 | swarm capstone; AXLE @4.32 |
| DEFINITION | `Brockian.GaloisWhyFive.P7` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.P7_irreducible` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.P7_monic` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.P7_natDegree` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| DEFINITION | `Brockian.GaloisWhyFive.Q5` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.Q5_monic` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.Q5_natDegree` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.aeval_spectralGen_seven` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| DEFINITION | `Brockian.GaloisWhyFive.cubic7` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.cubic7_monic` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.cubic_identity_seven` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.degree_five` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.degree_seven` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.degree_three` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.goldenSubOne_irrational` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.quadratic_iff_five` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| DEFINITION | `Brockian.GaloisWhyFive.spectralGen` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.spectralGen_five` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.spectralGen_seven` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.spectralGen_three` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.GaloisWhyFive.why_five` | ✓ | verified | lean-4.32.0 | roadmap #13 — Galois-degree why-five rigidity; AXLE @4.32 |
| PROVED | `Brockian.Geometry.d5_card` | ✓ | verified | lean-4.32.0 | runs 16 / 54 / 70 / 73 — pentagon golden diagonal, two-distance, C₅ spectrum |
| PROVED | `Brockian.Geometry.golden_ratio_in_C5_spectrum` | ✓ | verified | lean-4.32.0 | runs 16 / 54 / 70 / 73 — pentagon golden diagonal, two-distance, C₅ spectrum |
| PROVED | `Brockian.Geometry.pentagon_golden_diagonal` | ✓ | verified | lean-4.32.0 | runs 16 / 54 / 70 / 73 — pentagon golden diagonal, two-distance, C₅ spectrum |
| PROVED | `Brockian.Geometry.pentagon_two_distances` | ✓ | verified | lean-4.32.0 | runs 16 / 54 / 70 / 73 — pentagon golden diagonal, two-distance, C₅ spectrum |
| DEFINITION | `Brockian.Goldbach.CovarianceScaffold.K23` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.CovarianceScaffold.K23_above_even_nonthree_baseline_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.CovarianceScaffold.K23_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.CovarianceScaffold.K23_of_two_dvd_not_three_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.CovarianceScaffold.K23_of_two_dvd_three_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.CovarianceScaffold.K23_pos_iff_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.CovarianceScaffold.Kp_three_excess_neg_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.CovarianceScaffold.Kp_three_excess_pos_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.CovarianceScaffold.Kp_three_gt_one_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.CovarianceScaffold.Kp_three_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.CovarianceScaffold.Kp_three_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.CovarianceScaffold.Kp_two_eq_zero_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.CovarianceScaffold.Kp_two_pos_iff` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.CovarianceScaffold.goldbachPairTuple` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.CovarianceScaffold.goldbachPairTuple_card_le_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.CovarianceScaffold.goldbachPairTuple_raw_admissible_of_even` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.CovarianceScaffold.scaledK23Excess` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.CovarianceScaffold.scaledK23Excess_pos_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.CovarianceScaffold.singular_series_finite_goldbachPairTuple_pos_of_even` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.LocalWheel.K23` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.K23_above_even_nonthree_baseline_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.K23_aligned_gt_baseline` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.K23_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.K23_eq_nine_quarters_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.K23_excess_nonneg_of_even` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.K23_excess_pos_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.K23_le_nine_quarters` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.K23_nonneg` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.K23_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.K23_of_two_dvd_not_three_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.K23_of_two_dvd_three_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.K23_pos_iff_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.Kp_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.Kp_five_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.Kp_five_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.Kp_seven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.Kp_seven_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.Kp_seven_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.Kp_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.Kp_three_aligned_gt_misaligned` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.Kp_three_gt_one_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.Kp_three_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.Kp_three_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.gCount_seven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.gCount_seven_of_ne_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.gCount_seven_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.gCount_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.gCount_three_eq_gResidues_card` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.gCount_three_of_ne_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.gCount_three_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.gResidues_three_card` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.local_covariance_three_ne_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.local_covariance_three_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.local_covariance_three_zero_gt_ne_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.local_covariance_two_ne_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.LocalWheel.local_covariance_two_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.Parity.Kp_two` | ✓ | verified | lean-4.32.0 | Goldbach parity rung — elementary unconditional facts; AXLE @4.32 |
| PROVED | `Brockian.Goldbach.Parity.Kp_two_of_dvd` | ✓ | verified | lean-4.32.0 | Goldbach parity rung — elementary unconditional facts; AXLE @4.32 |
| PROVED | `Brockian.Goldbach.Parity.Kp_two_of_not_dvd` | ✓ | verified | lean-4.32.0 | Goldbach parity rung — elementary unconditional facts; AXLE @4.32 |
| PROVED | `Brockian.Goldbach.Parity.even_ge_four_eq_two_plus_even` | ✓ | verified | lean-4.32.0 | Goldbach parity rung — elementary unconditional facts; AXLE @4.32 |
| PROVED | `Brockian.Goldbach.Parity.even_of_odd_prime_add_odd_prime` | ✓ | verified | lean-4.32.0 | Goldbach parity rung — elementary unconditional facts; AXLE @4.32 |
| PROVED | `Brockian.Goldbach.Parity.gCount_eq_gResidues_card` | ✓ | verified | lean-4.32.0 | Goldbach parity rung — elementary unconditional facts; AXLE @4.32 |
| PROVED | `Brockian.Goldbach.Parity.gCount_five` | ✓ | verified | lean-4.32.0 | Goldbach parity rung — elementary unconditional facts; AXLE @4.32 |
| PROVED | `Brockian.Goldbach.Parity.gCount_two` | ✓ | verified | lean-4.32.0 | Goldbach parity rung — elementary unconditional facts; AXLE @4.32 |
| PROVED | `Brockian.Goldbach.Parity.gCount_two_of_ne_zero` | ✓ | verified | lean-4.32.0 | Goldbach parity rung — elementary unconditional facts; AXLE @4.32 |
| PROVED | `Brockian.Goldbach.Parity.gCount_two_one` | ✓ | verified | lean-4.32.0 | Goldbach parity rung — elementary unconditional facts; AXLE @4.32 |
| PROVED | `Brockian.Goldbach.Parity.gCount_two_zero` | ✓ | verified | lean-4.32.0 | Goldbach parity rung — elementary unconditional facts; AXLE @4.32 |
| PROVED | `Brockian.Goldbach.Parity.gResidues_five_card` | ✓ | verified | lean-4.32.0 | Goldbach parity rung — elementary unconditional facts; AXLE @4.32 |
| PROVED | `Brockian.Goldbach.Parity.hasGoldbachRep_odd_iff` | ✓ | verified | lean-4.32.0 | Goldbach parity rung — elementary unconditional facts; AXLE @4.32 |
| PROVED | `Brockian.Goldbach.Parity.hasGoldbachRep_odd_imp_two` | ✓ | verified | lean-4.32.0 | Goldbach parity rung — elementary unconditional facts; AXLE @4.32 |
| PROVED | `Brockian.Goldbach.Parity.hasGoldbachRep_two_plus_prime` | ✓ | verified | lean-4.32.0 | Goldbach parity rung — elementary unconditional facts; AXLE @4.32 |
| PROVED | `Brockian.Goldbach.Parity.odd_sub_of_even_sub_odd_prime` | ✓ | verified | lean-4.32.0 | Goldbach parity rung — elementary unconditional facts; AXLE @4.32 |
| DEFINITION | `Brockian.Goldbach.WheelExtended.K235` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.K235_above_even_baseline_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.K235_aligned_gt_K23_aligned` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.K235_aligned_gt_baseline` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.K235_cases` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.K235_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.K235_eq_K23_mul_Kp_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.K235_eq_aligned_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.K235_excess_nonneg_of_even` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.K235_le_aligned` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.K235_nonneg` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.K235_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.K235_of_two_dvd_not_three_not_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.K235_of_two_five_dvd_not_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.K235_of_two_three_dvd_not_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.K235_of_two_three_five_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.K235_pos_iff_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.Kp_eleven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.Kp_eleven_aligned_gt_misaligned` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.Kp_eleven_gt_one_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.Kp_eleven_le_aligned` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.Kp_eleven_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.Kp_eleven_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.Kp_eleven_pos` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.Kp_thirteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.Kp_thirteen_aligned_gt_misaligned` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.Kp_thirteen_gt_one_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.Kp_thirteen_le_aligned` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.Kp_thirteen_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.Kp_thirteen_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.Kp_thirteen_pos` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.gCount_eleven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.gCount_eleven_eq_gResidues_card` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.gCount_eleven_of_ne_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.gCount_eleven_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.gCount_thirteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.gCount_thirteen_eq_gResidues_card` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.gCount_thirteen_of_ne_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.gCount_thirteen_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.gResidues_eleven_card` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelExtended.gResidues_thirteen_card` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2357.K2357` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_aligned_gt_K235_aligned` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_aligned_gt_K23_aligned` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_aligned_gt_baseline` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_cases` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_eq_K235_mul_Kp_seven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_eq_K23_mul_Kp_five_mul_Kp_seven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_eq_aligned_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_eq_zero_iff_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_excess_nonneg_of_even` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_le_aligned` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_nonneg` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_of_two_dvd_not_three_not_five_not_seven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_of_two_five_dvd_not_three_not_seven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_of_two_five_seven_dvd_not_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_of_two_seven_dvd_not_three_not_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_of_two_three_dvd_not_five_not_seven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_of_two_three_five_dvd_not_seven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_of_two_three_five_seven_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_of_two_three_seven_dvd_not_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2357.K2357_pos_iff_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK235711.K2_11` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK235711.K2_11_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK235711.K2_11_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK235711.K2_11_of_two_and_eleven_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_101.K2_101` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_101.K2_101_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_101.K2_101_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_101.K2_101_of_two_and_oneHundredOne_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_101.Kp_oneHundredOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_101.Kp_oneHundredOne_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_101.Kp_oneHundredOne_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_13.K2_13` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_13.K2_13_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_13.K2_13_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_13.K2_13_of_two_and_thirteen_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_17.K2_17` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_17.K2_17_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_17.K2_17_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_17.K2_17_of_two_and_seventeen_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_17.Kp_seventeen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_17.Kp_seventeen_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_17.Kp_seventeen_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_19.K2_19` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_19.K2_19_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_19.K2_19_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_19.K2_19_of_two_and_nineteen_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_19.Kp_nineteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_19.Kp_nineteen_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_19.Kp_nineteen_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_23.K2_23` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_23.K2_23_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_23.K2_23_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_23.K2_23_of_two_and_twentyThree_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_23.Kp_twentyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_23.Kp_twentyThree_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_23.Kp_twentyThree_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_29.K2_29` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_29.K2_29_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_29.K2_29_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_29.K2_29_of_two_and_twentyNine_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_29.Kp_twentyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_29.Kp_twentyNine_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_29.Kp_twentyNine_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_31.K2_31` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_31.K2_31_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_31.K2_31_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_31.K2_31_of_two_and_thirtyOne_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_31.Kp_thirtyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_31.Kp_thirtyOne_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_31.Kp_thirtyOne_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_37.K2_37` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_37.K2_37_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_37.K2_37_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_37.K2_37_of_two_and_thirtySeven_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_37.Kp_thirtySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_37.Kp_thirtySeven_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_37.Kp_thirtySeven_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_41.K2_41` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_41.K2_41_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_41.K2_41_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_41.K2_41_of_two_and_fortyOne_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_41.Kp_fortyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_41.Kp_fortyOne_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_41.Kp_fortyOne_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_43.K2_43` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_43.K2_43_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_43.K2_43_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_43.K2_43_of_two_and_fortyThree_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_43.Kp_fortyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_43.Kp_fortyThree_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_43.Kp_fortyThree_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_47.K2_47` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_47.K2_47_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_47.K2_47_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_47.K2_47_of_two_and_fortySeven_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_47.Kp_fortySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_47.Kp_fortySeven_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_47.Kp_fortySeven_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_53.K2_53` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_53.K2_53_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_53.K2_53_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_53.K2_53_of_two_and_fiftyThree_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_53.Kp_fiftyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_53.Kp_fiftyThree_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_53.Kp_fiftyThree_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_59.K2_59` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_59.K2_59_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_59.K2_59_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_59.K2_59_of_two_and_fiftyNine_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_59.Kp_fiftyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_59.Kp_fiftyNine_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_59.Kp_fiftyNine_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_61.K2_61` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_61.K2_61_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_61.K2_61_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_61.K2_61_of_two_and_sixtyOne_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_61.Kp_sixtyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_61.Kp_sixtyOne_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_61.Kp_sixtyOne_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_67.K2_67` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_67.K2_67_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_67.K2_67_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_67.K2_67_of_two_and_sixtySeven_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_67.Kp_sixtySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_67.Kp_sixtySeven_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_67.Kp_sixtySeven_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_71.K2_71` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_71.K2_71_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_71.K2_71_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_71.K2_71_of_two_and_seventyOne_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_71.Kp_seventyOne` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_71.Kp_seventyOne_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_71.Kp_seventyOne_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_73.K2_73` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_73.K2_73_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_73.K2_73_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_73.K2_73_of_two_and_seventyThree_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_73.Kp_seventyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_73.Kp_seventyThree_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_73.Kp_seventyThree_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_79.K2_79` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_79.K2_79_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_79.K2_79_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_79.K2_79_of_two_and_seventyNine_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_79.Kp_seventyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_79.Kp_seventyNine_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_79.Kp_seventyNine_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_83.K2_83` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_83.K2_83_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_83.K2_83_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_83.K2_83_of_two_and_eightyThree_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_83.Kp_eightyThree` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_83.Kp_eightyThree_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_83.Kp_eightyThree_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_89.K2_89` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_89.K2_89_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_89.K2_89_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_89.K2_89_of_two_and_eightyNine_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_89.Kp_eightyNine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_89.Kp_eightyNine_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_89.Kp_eightyNine_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Goldbach.WheelK2_97.K2_97` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_97.K2_97_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_97.K2_97_of_not_two_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_97.K2_97_of_two_and_ninetySeven_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_97.Kp_ninetySeven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_97.Kp_ninetySeven_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Goldbach.WheelK2_97.Kp_ninetySeven_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| CONJECTURE | `Brockian.GoldbachComb.GoldbachCovarianceTransfer` | ✓ | verified | lean-4.32.0 | intake 18 (cabbba6e) — GC-1/2/3 KEEPER, exemplary |
| DEFINITION | `Brockian.GoldbachComb.Kp` | ✓ | verified | lean-4.32.0 | intake 18 (cabbba6e) — GC-1/2/3 KEEPER, exemplary |
| DEFINITION | `Brockian.GoldbachComb.gCount` | ✓ | verified | lean-4.32.0 | intake 18 (cabbba6e) — GC-1/2/3 KEEPER, exemplary |
| PROVED | `Brockian.GoldbachComb.gCount_centered` | ✓ | verified | lean-4.32.0 | intake 18 (cabbba6e) — GC-1/2/3 KEEPER, exemplary |
| PROVED | `Brockian.GoldbachComb.gCount_eq` | ✓ | verified | lean-4.32.0 | intake 18 (cabbba6e) — GC-1/2/3 KEEPER, exemplary |
| PROVED | `Brockian.GoldbachComb.local_covariance` | ✓ | verified | lean-4.32.0 | intake 18 (cabbba6e) — GC-1/2/3 KEEPER, exemplary |
| PROVED | `Brockian.GoldbachLemmas.factor_ratio` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| DEFINITION | `Brockian.GoldbachLemmas.gFactor` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| PROVED | `Brockian.GoldbachLemmas.gFactor_eq_one_add` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| PROVED | `Brockian.GoldbachLemmas.gFactor_pos` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| PROVED | `Brockian.GoldbachLemmas.gFactor_pos_prime` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| DEFINITION | `Brockian.GoldbachLemmas.gProduct` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| PROVED | `Brockian.GoldbachLemmas.gProduct_le_of_subset` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| PROVED | `Brockian.GoldbachLemmas.gProduct_pos` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| DEFINITION | `Brockian.GoldbachLemmas.gResidues` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| PROVED | `Brockian.GoldbachLemmas.gResidues_card_ne_zero` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| PROVED | `Brockian.GoldbachLemmas.gResidues_card_zero` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| PROVED | `Brockian.GoldbachLemmas.localDensity_ne` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| PROVED | `Brockian.GoldbachLemmas.localDensity_zero` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| PROVED | `Brockian.GoldbachLemmas.one_le_gProduct` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| PROVED | `Brockian.GoldbachLemmas.one_lt_gFactor` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| PROVED | `Brockian.GoldbachLemmas.one_lt_gFactor_prime` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| DEFINITION | `Brockian.GoldbachLemmas.tFactor` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| PROVED | `Brockian.GoldbachLemmas.tFactor_eq` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| PROVED | `Brockian.GoldbachLemmas.tFactor_lt_one` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| PROVED | `Brockian.GoldbachLemmas.tFactor_pos` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| PROVED | `Brockian.GoldbachLemmas.three_le_of_prime_ne_two` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Hardy-Littlewood Goldbach factor lemmas (unconditional) |
| DEFINITION | `Brockian.GoldbachSchema.HasGoldbachRep` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — spectral-model ⇒ Goldbach implication (schema) |
| DEFINITION | `Brockian.GoldbachSchema.SpectralModel` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — spectral-model ⇒ Goldbach implication (schema) |
| DEFINITION | `Brockian.GoldbachSchema.SpectralModelBeyond` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — spectral-model ⇒ Goldbach implication (schema) |
| DEFINITION | `Brockian.GoldbachSchema.goldbachCount` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — spectral-model ⇒ Goldbach implication (schema) |
| PROVED | `Brockian.GoldbachSchema.goldbachCount_four` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — spectral-model ⇒ Goldbach implication (schema) |
| PROVED | `Brockian.GoldbachSchema.goldbachCount_ten` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — spectral-model ⇒ Goldbach implication (schema) |
| CONDITIONAL | `Brockian.GoldbachSchema.goldbach_beyond_of_model` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — spectral-model ⇒ Goldbach implication (schema) |
| CONDITIONAL | `Brockian.GoldbachSchema.goldbach_from_spectral_model` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — spectral-model ⇒ Goldbach implication (schema) |
| PROVED | `Brockian.GoldbachSchema.hasGoldbachRep_eight` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — spectral-model ⇒ Goldbach implication (schema) |
| PROVED | `Brockian.GoldbachSchema.hasGoldbachRep_four` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — spectral-model ⇒ Goldbach implication (schema) |
| PROVED | `Brockian.GoldbachSchema.hasGoldbachRep_of_count_pos` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — spectral-model ⇒ Goldbach implication (schema) |
| PROVED | `Brockian.GoldbachSchema.hasGoldbachRep_six` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — spectral-model ⇒ Goldbach implication (schema) |
| DEFINITION | `Brockian.GoldbachSelectionRule.admissibleUnits` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.admissibleUnits_card` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.admissibleUnits_card_totient` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.admissibleUnits_eq_sdiff` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.admissibleUnits_reflection_eq_residues` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.admissibleUnits_translation_eq_residues` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.admissible_card_dihedral` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.admissible_reflection_card` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.admissible_translation_card` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.admissible_translation_matches_dichotomy` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| DEFINITION | `Brockian.GoldbachSelectionRule.gapPairs` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.gapPairs_card` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.gap_pairs_eq_translation_admissible` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| DEFINITION | `Brockian.GoldbachSelectionRule.goldbachPairs` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.goldbachPairs_card` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.goldbach_pairs_eq_reflection_admissible` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.mem_admissibleUnits_iff` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| DEFINITION | `Brockian.GoldbachSelectionRule.reflection` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.reflection_eq_dihedral` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.sigma_card` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| DEFINITION | `Brockian.GoldbachSelectionRule.translation` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.translation_eq_dihedral` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldbachSelectionRule.units_card` | ✓ | verified | lean-4.32.0 | harvest (Chris's Affine Selection Rules paper) — unified dihedral selection rule; AXLE @4.32 |
| PROVED | `Brockian.GoldenDivisibility.golden_in_cycleSpectrum_iff_five_dvd` | ✓ | verified | lean-4.32.0 | swarm capstone; AXLE @4.32 |
| PROVED | `Brockian.GoldenDivisibility.golden_unique_to_five_recovered` | ✓ | verified | lean-4.32.0 | swarm capstone; AXLE @4.32 |
| PROVED | `Brockian.GoldenSpectralCharacterization.golden_quadratic_roots` | ✓ | verified | lean-4.32.0 | swarm/Harmonic; AXLE @4.32 |
| PROVED | `Brockian.GoldenSpectralCharacterization.golden_ratio_spectral_characterization` | ✓ | verified | lean-4.32.0 | swarm/Harmonic; AXLE @4.32 |
| PROVED | `Brockian.GoldenSpectralCharacterization.golden_roots_mem_pentagon_spectrum` | ✓ | verified | lean-4.32.0 | swarm/Harmonic; AXLE @4.32 |
| PROVED | `Brockian.GoldenSpectralCharacterization.golden_roots_sign_split` | ✓ | verified | lean-4.32.0 | swarm/Harmonic; AXLE @4.32 |
| PROVED | `Brockian.GoldenUniqueness.C5_membership_layer` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.algebraic_connectivity_C5_eq` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.algebraic_connectivity_C5_props` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.algebraic_layer` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.cos_two_pi_div_five_eq_phi_sub_one_div_two` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.five_carries_golden` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.golden_algebraic_identity` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.golden_in_C5_family` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.golden_mem_C5` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.golden_not_in_prime_cycle_ne_five` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.golden_ratio_in_C5_geometry` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.golden_sub_one_eq_two_cos` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.golden_unique_among_prime_cycles` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.golden_unique_to_five` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.inv_golden_eq_sub_one` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.neg_golden_mem_C5` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.prime_cycle_golden_forces_five` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.prime_rigidity_layer` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.two_cos_four_pi_div_five_eq_neg_golden` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.GoldenUniqueness.two_cos_fundamental_mode_C5` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.MagmaLawRefutations.countermodel_assoc` | ✓ | verified | lean-4.32.0 | swarm/Harmonic; AXLE @4.32 |
| PROVED | `Brockian.MagmaLawRefutations.countermodel_comm` | ✓ | verified | lean-4.32.0 | swarm/Harmonic; AXLE @4.32 |
| PROVED | `Brockian.MagmaLawRefutations.countermodel_idem` | ✓ | verified | lean-4.32.0 | swarm/Harmonic; AXLE @4.32 |
| PROVED | `Brockian.MagmaLawRefutations.countermodel_mid` | ✓ | verified | lean-4.32.0 | swarm/Harmonic; AXLE @4.32 |
| PROVED | `Brockian.MagmaLawRefutations.not_entails_assoc` | ✓ | verified | lean-4.32.0 | swarm/Harmonic; AXLE @4.32 |
| PROVED | `Brockian.MagmaLawRefutations.not_entails_comm` | ✓ | verified | lean-4.32.0 | swarm/Harmonic; AXLE @4.32 |
| PROVED | `Brockian.MagmaLawRefutations.not_entails_idem` | ✓ | verified | lean-4.32.0 | swarm/Harmonic; AXLE @4.32 |
| PROVED | `Brockian.MagmaLawRefutations.not_entails_mid` | ✓ | verified | lean-4.32.0 | swarm/Harmonic; AXLE @4.32 |
| DEFINITION | `Brockian.MagmaLawRefutations.op_assoc` | ✓ | verified | lean-4.32.0 | swarm/Harmonic; AXLE @4.32 |
| DEFINITION | `Brockian.MagmaLawRefutations.op_comm` | ✓ | verified | lean-4.32.0 | swarm/Harmonic; AXLE @4.32 |
| DEFINITION | `Brockian.MagmaLawRefutations.op_idem` | ✓ | verified | lean-4.32.0 | swarm/Harmonic; AXLE @4.32 |
| DEFINITION | `Brockian.MagmaLawRefutations.op_mid` | ✓ | verified | lean-4.32.0 | swarm/Harmonic; AXLE @4.32 |
| PROVED | `Brockian.MetallicFamily.H3_ground_metallic` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.MetallicFamily.inv_metallicMean_eq_sub` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.MetallicFamily.metallicConj_sq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.MetallicFamily.metallicMean_add_conj` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.MetallicFamily.metallicMean_mul_conj` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.MetallicFamily.metallicMean_one` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.MetallicFamily.metallicMean_pos_of_nonneg` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.MetallicFamily.metallicMean_sq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.MetallicFamily.metallicMean_sub_conj` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.MetallicFamily.metallicMean_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.MetallicFamily.metallic_one_unique_to_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.MetallicFamily.metallic_radicand_nonneg` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.MetallicFamily.silverGap_eq_three_sub_metallicMean_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.MetallicRealization.det_eq_prod_roots` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.eigvec_conj_ne_zero` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.eigvec_mean_ne_zero` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.fibQ_charpoly` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.fibQ_mulVec_golden` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.goldenRatio_irrational` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.golden_hasEigenvalue` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicConj_isRoot` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| DEFINITION | `Brockian.MetallicRealization.metallicMatrix` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicMatrix_charpoly` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicMatrix_charpoly_natDegree` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicMatrix_det` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicMatrix_eigenvalue_iff` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicMatrix_hasEigenvalue_conj` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicMatrix_hasEigenvalue_mean` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicMatrix_isSymm` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicMatrix_mulVec_conj` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicMatrix_mulVec_mean` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicMatrix_one` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicMatrix_trace` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicMean_irrational` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicMean_isRoot` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicMean_notMem_cycleSpectrum` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicMean_two_notMem_cycleSpectrum` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicPoly_factor` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.metallicPoly_natDegree` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.trace_eq_sum_roots` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| PROVED | `Brockian.MetallicRealization.two_lt_metallicMean` | ✓ | verified | lean-4.32.0 | roadmap #9 — metallic-mean spectral realization; AXLE @4.32 |
| DEFINITION | `Brockian.NewEra.ReadingPath` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.NewEra.brockian_admissible_count` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.NewEra.decaying_potential_cannot_realize_large_zeros` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.NewEra.golden_lives_on_the_pentagon` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.NewEra.neg_golden_lives_on_the_pentagon` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.NewEra.pentagon_cosine_is_golden` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.NewEra.primeGaussian_not_confining` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.NewEra.quadratic_is_confining` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.NewEra.readingPath` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.NewEra.twin_admissible_count` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.NewEra.why_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.card_distincts_le_partition` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.card_distincts_le_powerset` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.card_oddDistincts_le_distincts` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.card_oddDistincts_le_odds` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.card_odds_le_partition` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.countRestricted_two_eq_distincts` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.distincts_one_card` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.distincts_zero_card` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.euler_odd_eq_distinct` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.euler_one` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.euler_via_glaisher` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.euler_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.glaisher` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.mem_distincts_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.mem_odds_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.oddDistincts_subset_distincts` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.oddDistincts_subset_odds` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.odds_one_card` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.odds_zero_card` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.parts_nodup_of_mem_distincts` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.parts_odd_of_mem_odds` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.parts_subset_Icc` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.powerSeries_odds_eq_distincts` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.OddDistinctPartition.toFinset_inj_on_distincts` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.PartitionRecurrence.factor_eq_geo` | ✓ | verified | lean-4.32.0 | batch — Euler partition recurrence UNCONDITIONAL from the proved PST; AXLE @4.32 |
| DEFINITION | `Brockian.PartitionRecurrence.geo` | ✓ | verified | lean-4.32.0 | batch — Euler partition recurrence UNCONDITIONAL from the proved PST; AXLE @4.32 |
| PROVED | `Brockian.PartitionRecurrence.geo_mul` | ✓ | verified | lean-4.32.0 | batch — Euler partition recurrence UNCONDITIONAL from the proved PST; AXLE @4.32 |
| PROVED | `Brockian.PartitionRecurrence.partitionGF_eq_tprod_geo` | ✓ | verified | lean-4.32.0 | batch — Euler partition recurrence UNCONDITIONAL from the proved PST; AXLE @4.32 |
| PROVED | `Brockian.PartitionRecurrence.partitionGF_mul_pentagonalProduct` | ✓ | verified | lean-4.32.0 | batch — Euler partition recurrence UNCONDITIONAL from the proved PST; AXLE @4.32 |
| PROVED | `Brockian.PartitionRecurrence.partition_pentagonal_convolution` | ✓ | verified | lean-4.32.0 | batch — Euler partition recurrence UNCONDITIONAL from the proved PST; AXLE @4.32 |
| PROVED | `Brockian.PartitionRecurrence.partition_pentagonal_convolution_range` | ✓ | verified | lean-4.32.0 | batch — Euler partition recurrence UNCONDITIONAL from the proved PST; AXLE @4.32 |
| PROVED | `Brockian.PartitionRecurrence.partition_recurrence` | ✓ | verified | lean-4.32.0 | batch — Euler partition recurrence UNCONDITIONAL from the proved PST; AXLE @4.32 |
| PROVED | `Brockian.PartitionRecurrence.pentCoeff_zero` | ✓ | verified | lean-4.32.0 | batch — Euler partition recurrence UNCONDITIONAL from the proved PST; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.A` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.A_ae` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.A_ae_add` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.A_ae_coeFn` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.A_ae_memLp` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.A_ae_smul` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.A_raw` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.A_raw_bound` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.A_raw_ptwise_bound` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.D` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.D_ae` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.D_ae_add` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.D_ae_coeFn` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.D_ae_memLp` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.D_ae_smul` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.D_raw` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.D_raw_bound_ptwise` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.D_raw_norm_bound` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.Delta` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.Delta_bounded` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.L2` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.PenroseGraph` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.Vertices` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.Window` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.adjacent` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.adjacent_loopless` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.adjacent_symm` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.ae_eq_of_count` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.deg_fn` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.deg_fn_bound` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.degree_bound` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.gamma` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.lintegral_count_eq_tsum` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.lintegral_sum_neighbors_le` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.memLp_A_raw` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.memLp_D_raw` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.mu` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.neighbor_subset` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.norm_A_le` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.norm_D_le` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.pentagonVertex` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.pentagonVertex_norm` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.phi` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.phi_bar` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.phi_equation` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.phi_gt_one` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.phi_ne_zero` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.phi_pos` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.phi_product_conjugate` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.phi_reciprocal` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.phi_squared` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.phi_sum_conjugate` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.potentialNeighbors` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.potentialNeighbors_finite` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.proj_para` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.proj_perp` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.proj_perp_real` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.rotation_is_multiplication` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.sqrt5_gt_one` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.sqrt5_gt_two` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.sum_sq_le_card_mul_sum_sq` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| DEFINITION | `Brockian.Penrose.zeta5` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.zeta5_norm` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.Penrose.zeta5_pow_five` | ✓ | verified | lean-4.32.0 | run 13 lineage / old PenroseTiling.lean ported to v4.32; AXLE @4.32 |
| PROVED | `Brockian.PentagonCharacterMultiplicity.chiConjugate_one` | ✓ | verified | lean-4.32.0 | rep-theory swarm; AXLE @4.32 |
| PROVED | `Brockian.PentagonCharacterMultiplicity.chiGolden_one` | ✓ | verified | lean-4.32.0 | rep-theory swarm; AXLE @4.32 |
| PROVED | `Brockian.PentagonCharacterMultiplicity.golden_isotypic_multiplicity` | ✓ | verified | lean-4.32.0 | rep-theory swarm; AXLE @4.32 |
| PROVED | `Brockian.PentagonCharacterMultiplicity.golden_multiplicity_eq_irrep_dim` | ✓ | verified | lean-4.32.0 | rep-theory swarm; AXLE @4.32 |
| PROVED | `Brockian.PentagonCharacterMultiplicity.golden_self_inner` | ✓ | verified | lean-4.32.0 | rep-theory swarm; AXLE @4.32 |
| PROVED | `Brockian.PentagonCharacterMultiplicity.multiplicity_table` | ✓ | verified | lean-4.32.0 | rep-theory swarm; AXLE @4.32 |
| PROVED | `Brockian.PentagonCharacterMultiplicity.neg_golden_multiplicity_eq_irrep_dim` | ✓ | verified | lean-4.32.0 | rep-theory swarm; AXLE @4.32 |
| DEFINITION | `Brockian.PentagonCharacterMultiplicity.permCharacter` | ✓ | verified | lean-4.32.0 | rep-theory swarm; AXLE @4.32 |
| PROVED | `Brockian.PentagonCharacterMultiplicity.permInner_golden` | ✓ | verified | lean-4.32.0 | rep-theory swarm; AXLE @4.32 |
| PROVED | `Brockian.PentagonEquivariance.adjacency_comm_d5` | ✓ | verified | lean-4.32.0 | rep-theory swarm; AXLE @4.32 |
| PROVED | `Brockian.PentagonEquivariance.adjacency_comm_rot` | ✓ | verified | lean-4.32.0 | rep-theory swarm; AXLE @4.32 |
| PROVED | `Brockian.PentagonEquivariance.d5Pull_sr_apply` | ✓ | verified | lean-4.32.0 | rep-theory swarm; AXLE @4.32 |
| PROVED | `Brockian.PentagonEquivariance.golden_eigenspace_invariant_d5` | ✓ | verified | lean-4.32.0 | rep-theory swarm; AXLE @4.32 |
| PROVED | `Brockian.PentagonEquivariance.golden_eigenspace_invariant_rot` | ✓ | verified | lean-4.32.0 | rep-theory swarm; AXLE @4.32 |
| PROVED | `Brockian.PentagonEquivariance.golden_eigenspace_is_subrep` | ✓ | verified | lean-4.32.0 | rep-theory swarm; AXLE @4.32 |
| PROVED | `Brockian.PentagonEquivariance.golden_eigenspace_is_subrep_d5` | ✓ | verified | lean-4.32.0 | rep-theory swarm; AXLE @4.32 |
| PROVED | `Brockian.PentagonGrandEquivalence.pentagon_grand_equivalence` | ✓ | verified | lean-4.32.0 | swarm capstone; AXLE @4.32 |
| DEFINITION | `Brockian.PentagonIsotypic.adjEigenvalue` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.adjEigenvalue_eq_two_cos` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.adjEigenvalue_four` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.adjEigenvalue_neg` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.adjEigenvalue_one` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.adjEigenvalue_three` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.adjEigenvalue_two` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.adjEigenvalue_zero` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| DEFINITION | `Brockian.PentagonIsotypic.adjacency` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.adjacency_apply` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.adjacency_eigenmode` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.adjacency_isotypicProjector` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| DEFINITION | `Brockian.PentagonIsotypic.eigenBasis` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.eigenmode_linearIndependent` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.eigenmode_ne_zero` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.eigenvalues_distinct` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.golden_eigenfrequencies` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.golden_eigenvector` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| DEFINITION | `Brockian.PentagonIsotypic.isotypicProjectorL` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.isotypicProjector_add` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.isotypicProjector_comp` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.isotypicProjector_completeness` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.isotypicProjector_idempotent` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.isotypicProjector_orthogonal` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.multiplicities` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.neg_golden_eigenfrequencies` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.rot_isotypic` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| PROVED | `Brockian.PentagonIsotypic.two_eigenfrequency` | ✓ | verified | lean-4.32.0 | roadmap #9-12 — D5/C5 isotypic decomposition; AXLE @4.32 |
| DEFINITION | `Brockian.PentagonMultiplicities.adjL` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.adjL_apply` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.adjL_eigenmode` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.eigenBasis_apply` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.eigenIndices_golden` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.eigenIndices_neg_golden` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.eigenIndices_two` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.eigenspace_eq_span_group` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.eigenspace_golden_eq` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.eigenspace_neg_golden_eq` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.eigenspace_two_eq` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.eigenspaces_span_top` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.finrank_eigenspace_golden` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.finrank_eigenspace_neg_golden` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.finrank_eigenspace_pair` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.finrank_eigenspace_two` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.finrank_vertexSpace` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.hasEigenvalue_golden` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.hasEigenvalue_neg_golden` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.hasEigenvalue_two` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.hasEigenvector_eigenmode` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.multiplicities_sum_eq_finrank` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.range_matrix_two` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonMultiplicities.repr_eq_zero_of_ne` | ✓ | verified | lean-4.32.0 | roadmap #12 — C5 eigenspace/finrank geometric multiplicities; AXLE @4.32 |
| PROVED | `Brockian.PentagonalPartition.partition_zero_card` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler pentagonal numbers + partition contact; AXLE @4.32 |
| DEFINITION | `Brockian.PentagonalPartition.pent` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler pentagonal numbers + partition contact; AXLE @4.32 |
| PROVED | `Brockian.PentagonalPartition.pent_injective` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler pentagonal numbers + partition contact; AXLE @4.32 |
| PROVED | `Brockian.PentagonalPartition.pent_lt_succ` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler pentagonal numbers + partition contact; AXLE @4.32 |
| PROVED | `Brockian.PentagonalPartition.pent_nonneg` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler pentagonal numbers + partition contact; AXLE @4.32 |
| PROVED | `Brockian.PentagonalPartition.pent_reflect` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler pentagonal numbers + partition contact; AXLE @4.32 |
| PROVED | `Brockian.PentagonalPartition.pent_succ` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler pentagonal numbers + partition contact; AXLE @4.32 |
| PROVED | `Brockian.PentagonalPartition.pent_values` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler pentagonal numbers + partition contact; AXLE @4.32 |
| PROVED | `Brockian.PentagonalPartition.two_dvd_pentNum` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler pentagonal numbers + partition contact; AXLE @4.32 |
| PROVED | `Brockian.PentagonalPartition.two_mul_pent` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler pentagonal numbers + partition contact; AXLE @4.32 |
| PROVED | `Brockian.PentagonalPartition.two_mul_pent_expand` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler pentagonal numbers + partition contact; AXLE @4.32 |
| PROVED | `Brockian.PentagonalTheoremFranklin.coeff_genFun_pstChar` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler PST reduced to Franklin involution; AXLE @4.32 |
| PROVED | `Brockian.PentagonalTheoremFranklin.genFun_pstChar_eq_prod` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler PST reduced to Franklin involution; AXLE @4.32 |
| PROVED | `Brockian.PentagonalTheoremFranklin.natCast_pentagonal_eq_pent` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler PST reduced to Franklin involution; AXLE @4.32 |
| DEFINITION | `Brockian.PentagonalTheoremFranklin.pentCoeff` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler PST reduced to Franklin involution; AXLE @4.32 |
| DEFINITION | `Brockian.PentagonalTheoremFranklin.pentSign` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler PST reduced to Franklin involution; AXLE @4.32 |
| DISCHARGED | `Brockian.PentagonalTheoremFranklin.pentagonalNumberTheorem_of_franklin` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler PST reduced to Franklin involution; AXLE @4.32 |
| DISCHARGED | `Brockian.PentagonalTheoremFranklin.pentagonalProduct_coeff_of_franklin` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler PST reduced to Franklin involution; AXLE @4.32 |
| PROVED | `Brockian.PentagonalTheoremFranklin.prod_pstChar_eq` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler PST reduced to Franklin involution; AXLE @4.32 |
| DEFINITION | `Brockian.PentagonalTheoremFranklin.pstChar` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler PST reduced to Franklin involution; AXLE @4.32 |
| PROVED | `Brockian.RamanujanCongruence.coeff_partitionGF` | ✓ | verified | lean-4.32.0 | roadmap #3 — genFin<->partition-count bridge; Ramanujan congruence documented OPEN; AXLE @4.32 |
| PROVED | `Brockian.RamanujanCongruence.coeff_partitionGF_zero` | ✓ | verified | lean-4.32.0 | roadmap #3 — genFin<->partition-count bridge; Ramanujan congruence documented OPEN; AXLE @4.32 |
| PROVED | `Brockian.RamanujanCongruence.five_dvd_of_dissection` | ✓ | verified | lean-4.32.0 | roadmap #3 — genFin<->partition-count bridge; Ramanujan congruence documented OPEN; AXLE @4.32 |
| DEFINITION | `Brockian.RamanujanCongruence.p` | ✓ | verified | lean-4.32.0 | roadmap #3 — genFin<->partition-count bridge; Ramanujan congruence documented OPEN; AXLE @4.32 |
| DEFINITION | `Brockian.RamanujanCongruence.partitionGF` | ✓ | verified | lean-4.32.0 | roadmap #3 — genFin<->partition-count bridge; Ramanujan congruence documented OPEN; AXLE @4.32 |
| DEFINITION | `Brockian.RiemannScaffold.BrockianSystem` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — ξ-bridge (unconditional) + Hilbert-Pólya conditional (OPEN) |
| PROVED | `Brockian.RiemannScaffold.Gammaℝ_ne_zero_of_nontrivial` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — ξ-bridge (unconditional) + Hilbert-Pólya conditional (OPEN) |
| CONDITIONAL | `Brockian.RiemannScaffold.RH_of_BrockianSystem` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — ξ-bridge (unconditional) + Hilbert-Pólya conditional (OPEN) |
| PROVED | `Brockian.RiemannScaffold.RiemannHypothesis_of_forall_xi_zero` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — ξ-bridge (unconditional) + Hilbert-Pólya conditional (OPEN) |
| DEFINITION | `Brockian.RiemannScaffold.riemannXi` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — ξ-bridge (unconditional) + Hilbert-Pólya conditional (OPEN) |
| PROVED | `Brockian.RiemannScaffold.riemannXi_eq_zero_of_nontrivial_zeta_zero` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — ξ-bridge (unconditional) + Hilbert-Pólya conditional (OPEN) |
| PROVED | `Brockian.RiemannScaffold.symmetric_eigenvalue_im_zero` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — ξ-bridge (unconditional) + Hilbert-Pólya conditional (OPEN) |
| PROVED | `Brockian.RiemannXiFunctionalEquation.completedRiemannZeta_functional_equation` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiFunctionalEquation.riemannXi_one_sub` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiFunctionalEquation.riemannXi_one_sub_eq_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiFunctionalEquation.riemannXi_one_sub_eq_zero_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiSymmetry.criticalLine_re_iff_reflect_re_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiSymmetry.reflect_fixed_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiSymmetry.reflect_re` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiSymmetry.reflect_re_eq_half_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiSymmetry.reflect_re_eq_self_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiSymmetry.reflect_reflect` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiSymmetry.riemannXi_eq_zero_iff_reflect` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiSymmetry.riemannXi_eq_zero_reflect` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiSymmetry.riemannXi_reflect` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiSymmetry.riemannXi_reflect_eq_zero_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiSymmetry.riemannXi_reflect_zero_and_criticalLine` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiSymmetry.riemannXi_zeroSet_image_reflect` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiSymmetry.riemannXi_zeroSet_preimage_reflect` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiSymmetry.riemannXi_zero_pair_of_reflect_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.RiemannXiSymmetry.riemannXi_zero_pair_of_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Sanity.brockian_sanity` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Sieve.H3` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.H3_det` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.H3_ground` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.H3_middle` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.H3_top` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.H3_trace` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| DEFINITION | `Brockian.Sieve.SilverGapRigidityTarget` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| DEFINITION | `Brockian.Sieve.TwinAdmissibleAt` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.compatible_closure` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.no_adjacent_admissible` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| DEFINITION | `Brockian.Sieve.phi` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.run3_signature` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.run_cap` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| DEFINITION | `Brockian.Sieve.silverGap` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.silver_gap_rigidity_finite` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| DEFINITION | `Brockian.Sieve.tau` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.tau_injective_on_period` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.tau_minimal_period` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.tau_period` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.twin_admissible_card` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.twin_pins_mod_three` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| DEFINITION | `Brockian.SingularSeries.compute_local_factor` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| DEFINITION | `Brockian.SingularSeries.compute_nu_p` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| DEFINITION | `Brockian.SingularSeries.compute_singular_series_finite` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| DEFINITION | `Brockian.SingularSeries.localFactor` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| DEFINITION | `Brockian.SingularSeries.localFactorAt` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.localFactorAt_eq` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.localFactorAt_of_not_prime` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.localFactorAt_pos` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.local_factor_asymptotic` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.local_factor_denom_ne_zero` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.local_factor_of_nu_p_eq_p` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.local_factor_of_nu_p_eq_zero` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.local_factor_pos` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| DEFINITION | `Brockian.SingularSeries.nu_p` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.nu_p'` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.nu_p_eq_image_card` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.nu_p_lt_p_of_admissible` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| DEFINITION | `Brockian.SingularSeries.singularSeries` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| DEFINITION | `Brockian.SingularSeries.singularSeriesFinite` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.singular_series_finite_pos` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.singular_series_pos` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.Convergence.err_bound` | ✓ | verified | lean-4.32.0 | roadmap #17 — infinite-product convergence; AXLE @4.32 |
| PROVED | `Brockian.SingularSeries.Convergence.localFactor_sub_one_bound` | ✓ | verified | lean-4.32.0 | roadmap #17 — infinite-product convergence; AXLE @4.32 |
| PROVED | `Brockian.SingularSeries.Convergence.nu_p_eq_card_of_lt` | ✓ | verified | lean-4.32.0 | roadmap #17 — infinite-product convergence; AXLE @4.32 |
| PROVED | `Brockian.SingularSeries.Convergence.singularSeriesFinite_tendsto_pos` | ✓ | verified | lean-4.32.0 | roadmap #17 — infinite-product convergence; AXLE @4.32 |
| PROVED | `Brockian.SingularSeries.Convergence.singular_series_pos'` | ✓ | verified | lean-4.32.0 | roadmap #17 — infinite-product convergence; AXLE @4.32 |
| PROVED | `Brockian.SingularSeries.Convergence.summable_localFactorAt_sub_one` | ✓ | verified | lean-4.32.0 | roadmap #17 — infinite-product convergence; AXLE @4.32 |
| PROVED | `Brockian.SingularSeries.EvenMore.evenPair_card_eighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.evenPair_card_fourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.evenPair_card_sixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.evenPair_card_twelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.evenPair_card_twenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.isAdmissible_evenPair_eighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.isAdmissible_evenPair_fourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.isAdmissible_evenPair_sixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.isAdmissible_evenPair_twelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.isAdmissible_evenPair_twenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.localFactorAt_eighteen_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.localFactorAt_fourteen_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.localFactorAt_sixteen_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.localFactorAt_twelve_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.localFactorAt_twelve_odd_ne_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.localFactorAt_twelve_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.localFactorAt_twelve_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.localFactorAt_twenty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.localFactor_eighteen_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.localFactor_fourteen_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.localFactor_sixteen_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.localFactor_twelve_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.localFactor_twelve_odd_ne_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.localFactor_twelve_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.localFactor_twelve_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.localFactor_twenty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.nu_p_eighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.nu_p_eighteen_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.nu_p_fourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.nu_p_fourteen_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.nu_p_sixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.nu_p_sixteen_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.nu_p_twelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.nu_p_twelve_odd_ne_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.nu_p_twelve_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.nu_p_twelve_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.nu_p_twenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.nu_p_twenty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.singular_series_finite_pos_evenPair_eighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.singular_series_finite_pos_evenPair_fourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.singular_series_finite_pos_evenPair_sixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.singular_series_finite_pos_evenPair_twelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.singular_series_finite_pos_evenPair_twenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.singular_series_pos_evenPair_eighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.singular_series_pos_evenPair_fourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.singular_series_pos_evenPair_sixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.singular_series_pos_evenPair_twelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.EvenMore.singular_series_pos_evenPair_twenty` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.SingularSeries.Examples.evenPair` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Examples.evenPair_card_le_two` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Examples.isAdmissible_evenPair` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Examples.isAdmissible_evenPair_four` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Examples.isAdmissible_evenPair_six` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Examples.isAdmissible_evenPair_two` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Examples.isAdmissible_twinGap` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Examples.singular_series_finite_pos_twinGap` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Examples.singular_series_pos_evenPair` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Examples.singular_series_pos_evenPair_four` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Examples.singular_series_pos_evenPair_six` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Examples.singular_series_pos_evenPair_two` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Examples.singular_series_pos_twinGap` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| DEFINITION | `Brockian.SingularSeries.Examples.twinGap` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Examples.twinGap_eq` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; committed by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Gaps102110.evenPair_card_oneHundredEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.evenPair_card_oneHundredFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.evenPair_card_oneHundredSix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.evenPair_card_oneHundredTen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.evenPair_card_oneHundredTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.isAdmissible_evenPair_oneHundredEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.isAdmissible_evenPair_oneHundredFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.isAdmissible_evenPair_oneHundredSix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.isAdmissible_evenPair_oneHundredTen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.isAdmissible_evenPair_oneHundredTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.localFactor_oneHundredTen_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.localFactor_oneHundredTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.nu_p_oneHundredEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.nu_p_oneHundredFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.nu_p_oneHundredSix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.nu_p_oneHundredTen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.nu_p_oneHundredTen_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.nu_p_oneHundredTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.nu_p_oneHundredTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.singular_series_finite_pos_evenPair_oneHundredEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.singular_series_finite_pos_evenPair_oneHundredFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.singular_series_finite_pos_evenPair_oneHundredSix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.singular_series_finite_pos_evenPair_oneHundredTen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.singular_series_finite_pos_evenPair_oneHundredTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.singular_series_pos_evenPair_oneHundredEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.singular_series_pos_evenPair_oneHundredFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.singular_series_pos_evenPair_oneHundredSix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.singular_series_pos_evenPair_oneHundredTen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps102110.singular_series_pos_evenPair_oneHundredTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.evenPair_card_oneHundredEighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.evenPair_card_oneHundredFourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.evenPair_card_oneHundredSixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.evenPair_card_oneHundredTwelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.evenPair_card_oneHundredTwenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.isAdmissible_evenPair_oneHundredEighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.isAdmissible_evenPair_oneHundredFourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.isAdmissible_evenPair_oneHundredSixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.isAdmissible_evenPair_oneHundredTwelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.isAdmissible_evenPair_oneHundredTwenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.localFactor_oneHundredTwelve_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.localFactor_oneHundredTwenty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.nu_p_oneHundredEighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.nu_p_oneHundredFourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.nu_p_oneHundredSixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.nu_p_oneHundredTwelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.nu_p_oneHundredTwelve_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.nu_p_oneHundredTwenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.nu_p_oneHundredTwenty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.singular_series_finite_pos_evenPair_oneHundredEighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.singular_series_finite_pos_evenPair_oneHundredFourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.singular_series_finite_pos_evenPair_oneHundredSixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.singular_series_finite_pos_evenPair_oneHundredTwelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.singular_series_finite_pos_evenPair_oneHundredTwenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.singular_series_pos_evenPair_oneHundredEighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.singular_series_pos_evenPair_oneHundredFourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.singular_series_pos_evenPair_oneHundredSixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.singular_series_pos_evenPair_oneHundredTwelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps112120.singular_series_pos_evenPair_oneHundredTwenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.evenPair_card_oneHundredThirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.evenPair_card_oneHundredTwentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.evenPair_card_oneHundredTwentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.evenPair_card_oneHundredTwentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.evenPair_card_oneHundredTwentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.isAdmissible_evenPair_oneHundredThirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.isAdmissible_evenPair_oneHundredTwentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.isAdmissible_evenPair_oneHundredTwentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.isAdmissible_evenPair_oneHundredTwentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.isAdmissible_evenPair_oneHundredTwentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.localFactor_oneHundredThirty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.localFactor_oneHundredTwentyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.nu_p_oneHundredThirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.nu_p_oneHundredThirty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.nu_p_oneHundredTwentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.nu_p_oneHundredTwentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.nu_p_oneHundredTwentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.nu_p_oneHundredTwentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.nu_p_oneHundredTwentyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.singular_series_finite_pos_evenPair_oneHundredThirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.singular_series_finite_pos_evenPair_oneHundredTwentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.singular_series_finite_pos_evenPair_oneHundredTwentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.singular_series_finite_pos_evenPair_oneHundredTwentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.singular_series_finite_pos_evenPair_oneHundredTwentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.singular_series_pos_evenPair_oneHundredThirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.singular_series_pos_evenPair_oneHundredTwentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.singular_series_pos_evenPair_oneHundredTwentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.singular_series_pos_evenPair_oneHundredTwentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps122130.singular_series_pos_evenPair_oneHundredTwentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.evenPair_card_oneHundredForty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.evenPair_card_oneHundredThirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.evenPair_card_oneHundredThirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.evenPair_card_oneHundredThirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.evenPair_card_oneHundredThirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.isAdmissible_evenPair_oneHundredForty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.isAdmissible_evenPair_oneHundredThirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.isAdmissible_evenPair_oneHundredThirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.isAdmissible_evenPair_oneHundredThirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.isAdmissible_evenPair_oneHundredThirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.localFactor_oneHundredForty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.localFactor_oneHundredThirtyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.nu_p_oneHundredForty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.nu_p_oneHundredForty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.nu_p_oneHundredThirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.nu_p_oneHundredThirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.nu_p_oneHundredThirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.nu_p_oneHundredThirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.nu_p_oneHundredThirtyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.singular_series_finite_pos_evenPair_oneHundredForty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.singular_series_finite_pos_evenPair_oneHundredThirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.singular_series_finite_pos_evenPair_oneHundredThirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.singular_series_finite_pos_evenPair_oneHundredThirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.singular_series_finite_pos_evenPair_oneHundredThirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.singular_series_pos_evenPair_oneHundredForty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.singular_series_pos_evenPair_oneHundredThirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.singular_series_pos_evenPair_oneHundredThirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.singular_series_pos_evenPair_oneHundredThirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps132140.singular_series_pos_evenPair_oneHundredThirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.evenPair_card_oneHundredFifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.evenPair_card_oneHundredFortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.evenPair_card_oneHundredFortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.evenPair_card_oneHundredFortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.evenPair_card_oneHundredFortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.isAdmissible_evenPair_oneHundredFifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.isAdmissible_evenPair_oneHundredFortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.isAdmissible_evenPair_oneHundredFortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.isAdmissible_evenPair_oneHundredFortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.isAdmissible_evenPair_oneHundredFortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.localFactor_oneHundredFifty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.localFactor_oneHundredFortyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.nu_p_oneHundredFifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.nu_p_oneHundredFifty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.nu_p_oneHundredFortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.nu_p_oneHundredFortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.nu_p_oneHundredFortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.nu_p_oneHundredFortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.nu_p_oneHundredFortyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.singular_series_finite_pos_evenPair_oneHundredFifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.singular_series_finite_pos_evenPair_oneHundredFortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.singular_series_finite_pos_evenPair_oneHundredFortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.singular_series_finite_pos_evenPair_oneHundredFortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.singular_series_finite_pos_evenPair_oneHundredFortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.singular_series_pos_evenPair_oneHundredFifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.singular_series_pos_evenPair_oneHundredFortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.singular_series_pos_evenPair_oneHundredFortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.singular_series_pos_evenPair_oneHundredFortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps142150.singular_series_pos_evenPair_oneHundredFortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.evenPair_card_oneHundredFiftyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.evenPair_card_oneHundredFiftyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.evenPair_card_oneHundredFiftySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.evenPair_card_oneHundredFiftyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.evenPair_card_oneHundredSixty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.isAdmissible_evenPair_oneHundredFiftyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.isAdmissible_evenPair_oneHundredFiftyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.isAdmissible_evenPair_oneHundredFiftySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.isAdmissible_evenPair_oneHundredFiftyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.isAdmissible_evenPair_oneHundredSixty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.localFactor_oneHundredFiftyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.localFactor_oneHundredSixty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.nu_p_oneHundredFiftyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.nu_p_oneHundredFiftyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.nu_p_oneHundredFiftySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.nu_p_oneHundredFiftyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.nu_p_oneHundredFiftyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.nu_p_oneHundredSixty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.nu_p_oneHundredSixty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.singular_series_finite_pos_evenPair_oneHundredFiftyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.singular_series_finite_pos_evenPair_oneHundredFiftyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.singular_series_finite_pos_evenPair_oneHundredFiftySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.singular_series_finite_pos_evenPair_oneHundredFiftyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.singular_series_finite_pos_evenPair_oneHundredSixty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.singular_series_pos_evenPair_oneHundredFiftyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.singular_series_pos_evenPair_oneHundredFiftyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.singular_series_pos_evenPair_oneHundredFiftySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.singular_series_pos_evenPair_oneHundredFiftyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps152160.singular_series_pos_evenPair_oneHundredSixty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.evenPair_card_oneHundredSeventy` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.evenPair_card_oneHundredSixtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.evenPair_card_oneHundredSixtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.evenPair_card_oneHundredSixtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.evenPair_card_oneHundredSixtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.isAdmissible_evenPair_oneHundredSeventy` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.isAdmissible_evenPair_oneHundredSixtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.isAdmissible_evenPair_oneHundredSixtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.isAdmissible_evenPair_oneHundredSixtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.isAdmissible_evenPair_oneHundredSixtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.localFactor_oneHundredSeventy_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.localFactor_oneHundredSixtyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.nu_p_oneHundredSeventy` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.nu_p_oneHundredSeventy_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.nu_p_oneHundredSixtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.nu_p_oneHundredSixtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.nu_p_oneHundredSixtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.nu_p_oneHundredSixtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.nu_p_oneHundredSixtyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.singular_series_finite_pos_evenPair_oneHundredSeventy` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.singular_series_finite_pos_evenPair_oneHundredSixtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.singular_series_finite_pos_evenPair_oneHundredSixtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.singular_series_finite_pos_evenPair_oneHundredSixtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.singular_series_finite_pos_evenPair_oneHundredSixtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.singular_series_pos_evenPair_oneHundredSeventy` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.singular_series_pos_evenPair_oneHundredSixtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.singular_series_pos_evenPair_oneHundredSixtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.singular_series_pos_evenPair_oneHundredSixtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps162170.singular_series_pos_evenPair_oneHundredSixtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.evenPair_card_oneHundredEighty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.evenPair_card_oneHundredSeventyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.evenPair_card_oneHundredSeventyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.evenPair_card_oneHundredSeventySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.evenPair_card_oneHundredSeventyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.isAdmissible_evenPair_oneHundredEighty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.isAdmissible_evenPair_oneHundredSeventyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.isAdmissible_evenPair_oneHundredSeventyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.isAdmissible_evenPair_oneHundredSeventySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.isAdmissible_evenPair_oneHundredSeventyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.localFactor_oneHundredEighty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.localFactor_oneHundredSeventyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.nu_p_oneHundredEighty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.nu_p_oneHundredEighty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.nu_p_oneHundredSeventyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.nu_p_oneHundredSeventyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.nu_p_oneHundredSeventySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.nu_p_oneHundredSeventyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.nu_p_oneHundredSeventyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.singular_series_finite_pos_evenPair_oneHundredEighty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.singular_series_finite_pos_evenPair_oneHundredSeventyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.singular_series_finite_pos_evenPair_oneHundredSeventyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.singular_series_finite_pos_evenPair_oneHundredSeventySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.singular_series_finite_pos_evenPair_oneHundredSeventyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.singular_series_pos_evenPair_oneHundredEighty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.singular_series_pos_evenPair_oneHundredSeventyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.singular_series_pos_evenPair_oneHundredSeventyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.singular_series_pos_evenPair_oneHundredSeventySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps172180.singular_series_pos_evenPair_oneHundredSeventyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.evenPair_card_oneHundredEightyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.evenPair_card_oneHundredEightyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.evenPair_card_oneHundredEightySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.evenPair_card_oneHundredEightyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.evenPair_card_oneHundredNinety` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.isAdmissible_evenPair_oneHundredEightyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.isAdmissible_evenPair_oneHundredEightyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.isAdmissible_evenPair_oneHundredEightySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.isAdmissible_evenPair_oneHundredEightyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.isAdmissible_evenPair_oneHundredNinety` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.localFactor_oneHundredEightyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.localFactor_oneHundredNinety_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.nu_p_oneHundredEightyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.nu_p_oneHundredEightyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.nu_p_oneHundredEightySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.nu_p_oneHundredEightyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.nu_p_oneHundredEightyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.nu_p_oneHundredNinety` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.nu_p_oneHundredNinety_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.singular_series_finite_pos_evenPair_oneHundredEightyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.singular_series_finite_pos_evenPair_oneHundredEightyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.singular_series_finite_pos_evenPair_oneHundredEightySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.singular_series_finite_pos_evenPair_oneHundredEightyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.singular_series_finite_pos_evenPair_oneHundredNinety` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.singular_series_pos_evenPair_oneHundredEightyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.singular_series_pos_evenPair_oneHundredEightyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.singular_series_pos_evenPair_oneHundredEightySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.singular_series_pos_evenPair_oneHundredEightyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps182190.singular_series_pos_evenPair_oneHundredNinety` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.evenPair_card_oneHundredNinetyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.evenPair_card_oneHundredNinetyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.evenPair_card_oneHundredNinetySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.evenPair_card_oneHundredNinetyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.evenPair_card_twoHundred` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.isAdmissible_evenPair_oneHundredNinetyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.isAdmissible_evenPair_oneHundredNinetyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.isAdmissible_evenPair_oneHundredNinetySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.isAdmissible_evenPair_oneHundredNinetyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.isAdmissible_evenPair_twoHundred` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.localFactor_oneHundredNinetyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.localFactor_twoHundred_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.nu_p_oneHundredNinetyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.nu_p_oneHundredNinetyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.nu_p_oneHundredNinetySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.nu_p_oneHundredNinetyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.nu_p_oneHundredNinetyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.nu_p_twoHundred` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.nu_p_twoHundred_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.singular_series_finite_pos_evenPair_oneHundredNinetyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.singular_series_finite_pos_evenPair_oneHundredNinetyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.singular_series_finite_pos_evenPair_oneHundredNinetySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.singular_series_finite_pos_evenPair_oneHundredNinetyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.singular_series_finite_pos_evenPair_twoHundred` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.singular_series_pos_evenPair_oneHundredNinetyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.singular_series_pos_evenPair_oneHundredNinetyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.singular_series_pos_evenPair_oneHundredNinetySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.singular_series_pos_evenPair_oneHundredNinetyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps192200.singular_series_pos_evenPair_twoHundred` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.evenPair_card_twoHundredEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.evenPair_card_twoHundredFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.evenPair_card_twoHundredSix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.evenPair_card_twoHundredTen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.evenPair_card_twoHundredTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.isAdmissible_evenPair_twoHundredEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.isAdmissible_evenPair_twoHundredFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.isAdmissible_evenPair_twoHundredSix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.isAdmissible_evenPair_twoHundredTen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.isAdmissible_evenPair_twoHundredTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.localFactor_twoHundredTen_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.localFactor_twoHundredTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.nu_p_twoHundredEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.nu_p_twoHundredFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.nu_p_twoHundredSix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.nu_p_twoHundredTen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.nu_p_twoHundredTen_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.nu_p_twoHundredTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.nu_p_twoHundredTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.singular_series_finite_pos_evenPair_twoHundredEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.singular_series_finite_pos_evenPair_twoHundredFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.singular_series_finite_pos_evenPair_twoHundredSix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.singular_series_finite_pos_evenPair_twoHundredTen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.singular_series_finite_pos_evenPair_twoHundredTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.singular_series_pos_evenPair_twoHundredEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.singular_series_pos_evenPair_twoHundredFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.singular_series_pos_evenPair_twoHundredSix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.singular_series_pos_evenPair_twoHundredTen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps202210.singular_series_pos_evenPair_twoHundredTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.evenPair_card_twoHundredEighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.evenPair_card_twoHundredFourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.evenPair_card_twoHundredSixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.evenPair_card_twoHundredTwelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.evenPair_card_twoHundredTwenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.isAdmissible_evenPair_twoHundredEighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.isAdmissible_evenPair_twoHundredFourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.isAdmissible_evenPair_twoHundredSixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.isAdmissible_evenPair_twoHundredTwelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.isAdmissible_evenPair_twoHundredTwenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.localFactor_twoHundredTwelve_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.localFactor_twoHundredTwenty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.nu_p_twoHundredEighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.nu_p_twoHundredFourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.nu_p_twoHundredSixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.nu_p_twoHundredTwelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.nu_p_twoHundredTwelve_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.nu_p_twoHundredTwenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.nu_p_twoHundredTwenty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.singular_series_finite_pos_evenPair_twoHundredEighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.singular_series_finite_pos_evenPair_twoHundredFourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.singular_series_finite_pos_evenPair_twoHundredSixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.singular_series_finite_pos_evenPair_twoHundredTwelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.singular_series_finite_pos_evenPair_twoHundredTwenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.singular_series_pos_evenPair_twoHundredEighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.singular_series_pos_evenPair_twoHundredFourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.singular_series_pos_evenPair_twoHundredSixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.singular_series_pos_evenPair_twoHundredTwelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps212220.singular_series_pos_evenPair_twoHundredTwenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.evenPair_card_twoHundredThirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.evenPair_card_twoHundredTwentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.evenPair_card_twoHundredTwentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.evenPair_card_twoHundredTwentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.evenPair_card_twoHundredTwentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.isAdmissible_evenPair_twoHundredThirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.isAdmissible_evenPair_twoHundredTwentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.isAdmissible_evenPair_twoHundredTwentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.isAdmissible_evenPair_twoHundredTwentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.isAdmissible_evenPair_twoHundredTwentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.localFactor_twoHundredThirty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.localFactor_twoHundredTwentyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.nu_p_twoHundredThirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.nu_p_twoHundredThirty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.nu_p_twoHundredTwentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.nu_p_twoHundredTwentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.nu_p_twoHundredTwentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.nu_p_twoHundredTwentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.nu_p_twoHundredTwentyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.singular_series_finite_pos_evenPair_twoHundredThirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.singular_series_finite_pos_evenPair_twoHundredTwentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.singular_series_finite_pos_evenPair_twoHundredTwentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.singular_series_finite_pos_evenPair_twoHundredTwentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.singular_series_finite_pos_evenPair_twoHundredTwentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.singular_series_pos_evenPair_twoHundredThirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.singular_series_pos_evenPair_twoHundredTwentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.singular_series_pos_evenPair_twoHundredTwentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.singular_series_pos_evenPair_twoHundredTwentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps222230.singular_series_pos_evenPair_twoHundredTwentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.evenPair_card_thirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.evenPair_card_twentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.evenPair_card_twentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.evenPair_card_twentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.evenPair_card_twentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.isAdmissible_evenPair_thirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.isAdmissible_evenPair_twentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.isAdmissible_evenPair_twentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.isAdmissible_evenPair_twentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.isAdmissible_evenPair_twentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.localFactor_thirty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.localFactor_twentyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.nu_p_thirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.nu_p_thirty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.nu_p_twentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.nu_p_twentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.nu_p_twentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.nu_p_twentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.nu_p_twentyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.singular_series_finite_pos_evenPair_thirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.singular_series_finite_pos_evenPair_twentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.singular_series_finite_pos_evenPair_twentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.singular_series_finite_pos_evenPair_twentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.singular_series_finite_pos_evenPair_twentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.singular_series_pos_evenPair_thirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.singular_series_pos_evenPair_twentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.singular_series_pos_evenPair_twentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.singular_series_pos_evenPair_twentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps2230.singular_series_pos_evenPair_twentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.evenPair_card_twoHundredForty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.evenPair_card_twoHundredThirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.evenPair_card_twoHundredThirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.evenPair_card_twoHundredThirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.evenPair_card_twoHundredThirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.isAdmissible_evenPair_twoHundredForty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.isAdmissible_evenPair_twoHundredThirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.isAdmissible_evenPair_twoHundredThirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.isAdmissible_evenPair_twoHundredThirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.isAdmissible_evenPair_twoHundredThirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.localFactor_twoHundredForty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.localFactor_twoHundredThirtyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.nu_p_twoHundredForty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.nu_p_twoHundredForty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.nu_p_twoHundredThirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.nu_p_twoHundredThirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.nu_p_twoHundredThirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.nu_p_twoHundredThirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.nu_p_twoHundredThirtyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.singular_series_finite_pos_evenPair_twoHundredForty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.singular_series_finite_pos_evenPair_twoHundredThirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.singular_series_finite_pos_evenPair_twoHundredThirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.singular_series_finite_pos_evenPair_twoHundredThirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.singular_series_finite_pos_evenPair_twoHundredThirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.singular_series_pos_evenPair_twoHundredForty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.singular_series_pos_evenPair_twoHundredThirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.singular_series_pos_evenPair_twoHundredThirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.singular_series_pos_evenPair_twoHundredThirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps232240.singular_series_pos_evenPair_twoHundredThirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.evenPair_card_twoHundredFifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.evenPair_card_twoHundredFortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.evenPair_card_twoHundredFortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.evenPair_card_twoHundredFortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.evenPair_card_twoHundredFortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.isAdmissible_evenPair_twoHundredFifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.isAdmissible_evenPair_twoHundredFortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.isAdmissible_evenPair_twoHundredFortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.isAdmissible_evenPair_twoHundredFortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.isAdmissible_evenPair_twoHundredFortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.localFactor_twoHundredFifty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.localFactor_twoHundredFortyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.nu_p_twoHundredFifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.nu_p_twoHundredFifty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.nu_p_twoHundredFortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.nu_p_twoHundredFortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.nu_p_twoHundredFortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.nu_p_twoHundredFortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.nu_p_twoHundredFortyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.singular_series_finite_pos_evenPair_twoHundredFifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.singular_series_finite_pos_evenPair_twoHundredFortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.singular_series_finite_pos_evenPair_twoHundredFortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.singular_series_finite_pos_evenPair_twoHundredFortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.singular_series_finite_pos_evenPair_twoHundredFortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.singular_series_pos_evenPair_twoHundredFifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.singular_series_pos_evenPair_twoHundredFortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.singular_series_pos_evenPair_twoHundredFortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.singular_series_pos_evenPair_twoHundredFortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps242250.singular_series_pos_evenPair_twoHundredFortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.evenPair_card_twoHundredFiftyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.evenPair_card_twoHundredFiftyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.evenPair_card_twoHundredFiftySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.evenPair_card_twoHundredFiftyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.evenPair_card_twoHundredSixty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.isAdmissible_evenPair_twoHundredFiftyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.isAdmissible_evenPair_twoHundredFiftyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.isAdmissible_evenPair_twoHundredFiftySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.isAdmissible_evenPair_twoHundredFiftyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.isAdmissible_evenPair_twoHundredSixty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.localFactor_twoHundredFiftyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.localFactor_twoHundredSixty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.nu_p_twoHundredFiftyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.nu_p_twoHundredFiftyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.nu_p_twoHundredFiftySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.nu_p_twoHundredFiftyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.nu_p_twoHundredFiftyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.nu_p_twoHundredSixty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.nu_p_twoHundredSixty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.singular_series_finite_pos_evenPair_twoHundredFiftyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.singular_series_finite_pos_evenPair_twoHundredFiftyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.singular_series_finite_pos_evenPair_twoHundredFiftySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.singular_series_finite_pos_evenPair_twoHundredFiftyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.singular_series_finite_pos_evenPair_twoHundredSixty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.singular_series_pos_evenPair_twoHundredFiftyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.singular_series_pos_evenPair_twoHundredFiftyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.singular_series_pos_evenPair_twoHundredFiftySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.singular_series_pos_evenPair_twoHundredFiftyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps252260.singular_series_pos_evenPair_twoHundredSixty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.evenPair_card_twoHundredSeventy` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.evenPair_card_twoHundredSixtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.evenPair_card_twoHundredSixtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.evenPair_card_twoHundredSixtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.evenPair_card_twoHundredSixtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.isAdmissible_evenPair_twoHundredSeventy` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.isAdmissible_evenPair_twoHundredSixtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.isAdmissible_evenPair_twoHundredSixtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.isAdmissible_evenPair_twoHundredSixtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.isAdmissible_evenPair_twoHundredSixtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.localFactor_twoHundredSeventy_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.localFactor_twoHundredSixtyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.nu_p_twoHundredSeventy` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.nu_p_twoHundredSeventy_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.nu_p_twoHundredSixtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.nu_p_twoHundredSixtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.nu_p_twoHundredSixtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.nu_p_twoHundredSixtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.nu_p_twoHundredSixtyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.singular_series_finite_pos_evenPair_twoHundredSeventy` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.singular_series_finite_pos_evenPair_twoHundredSixtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.singular_series_finite_pos_evenPair_twoHundredSixtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.singular_series_finite_pos_evenPair_twoHundredSixtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.singular_series_finite_pos_evenPair_twoHundredSixtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.singular_series_pos_evenPair_twoHundredSeventy` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.singular_series_pos_evenPair_twoHundredSixtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.singular_series_pos_evenPair_twoHundredSixtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.singular_series_pos_evenPair_twoHundredSixtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps262270.singular_series_pos_evenPair_twoHundredSixtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.evenPair_card_twoHundredEighty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.evenPair_card_twoHundredSeventyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.evenPair_card_twoHundredSeventyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.evenPair_card_twoHundredSeventySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.evenPair_card_twoHundredSeventyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.isAdmissible_evenPair_twoHundredEighty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.isAdmissible_evenPair_twoHundredSeventyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.isAdmissible_evenPair_twoHundredSeventyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.isAdmissible_evenPair_twoHundredSeventySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.isAdmissible_evenPair_twoHundredSeventyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.localFactor_twoHundredEighty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.localFactor_twoHundredSeventyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.nu_p_twoHundredEighty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.nu_p_twoHundredEighty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.nu_p_twoHundredSeventyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.nu_p_twoHundredSeventyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.nu_p_twoHundredSeventySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.nu_p_twoHundredSeventyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.nu_p_twoHundredSeventyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.singular_series_finite_pos_evenPair_twoHundredEighty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.singular_series_finite_pos_evenPair_twoHundredSeventyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.singular_series_finite_pos_evenPair_twoHundredSeventyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.singular_series_finite_pos_evenPair_twoHundredSeventySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.singular_series_finite_pos_evenPair_twoHundredSeventyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.singular_series_pos_evenPair_twoHundredEighty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.singular_series_pos_evenPair_twoHundredSeventyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.singular_series_pos_evenPair_twoHundredSeventyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.singular_series_pos_evenPair_twoHundredSeventySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps272280.singular_series_pos_evenPair_twoHundredSeventyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.evenPair_card_twoHundredEightyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.evenPair_card_twoHundredEightyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.evenPair_card_twoHundredEightySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.evenPair_card_twoHundredEightyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.evenPair_card_twoHundredNinety` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.isAdmissible_evenPair_twoHundredEightyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.isAdmissible_evenPair_twoHundredEightyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.isAdmissible_evenPair_twoHundredEightySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.isAdmissible_evenPair_twoHundredEightyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.isAdmissible_evenPair_twoHundredNinety` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.localFactor_twoHundredEightyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.localFactor_twoHundredNinety_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.nu_p_twoHundredEightyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.nu_p_twoHundredEightyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.nu_p_twoHundredEightySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.nu_p_twoHundredEightyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.nu_p_twoHundredEightyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.nu_p_twoHundredNinety` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.nu_p_twoHundredNinety_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.singular_series_finite_pos_evenPair_twoHundredEightyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.singular_series_finite_pos_evenPair_twoHundredEightyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.singular_series_finite_pos_evenPair_twoHundredEightySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.singular_series_finite_pos_evenPair_twoHundredEightyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.singular_series_finite_pos_evenPair_twoHundredNinety` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.singular_series_pos_evenPair_twoHundredEightyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.singular_series_pos_evenPair_twoHundredEightyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.singular_series_pos_evenPair_twoHundredEightySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.singular_series_pos_evenPair_twoHundredEightyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps282290.singular_series_pos_evenPair_twoHundredNinety` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.evenPair_card_threeHundred` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.evenPair_card_twoHundredNinetyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.evenPair_card_twoHundredNinetyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.evenPair_card_twoHundredNinetySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.evenPair_card_twoHundredNinetyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.isAdmissible_evenPair_threeHundred` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.isAdmissible_evenPair_twoHundredNinetyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.isAdmissible_evenPair_twoHundredNinetyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.isAdmissible_evenPair_twoHundredNinetySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.isAdmissible_evenPair_twoHundredNinetyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.localFactor_threeHundred_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.localFactor_twoHundredNinetyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.nu_p_threeHundred` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.nu_p_threeHundred_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.nu_p_twoHundredNinetyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.nu_p_twoHundredNinetyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.nu_p_twoHundredNinetySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.nu_p_twoHundredNinetyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.nu_p_twoHundredNinetyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.singular_series_finite_pos_evenPair_threeHundred` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.singular_series_finite_pos_evenPair_twoHundredNinetyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.singular_series_finite_pos_evenPair_twoHundredNinetyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.singular_series_finite_pos_evenPair_twoHundredNinetySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.singular_series_finite_pos_evenPair_twoHundredNinetyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.singular_series_pos_evenPair_threeHundred` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.singular_series_pos_evenPair_twoHundredNinetyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.singular_series_pos_evenPair_twoHundredNinetyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.singular_series_pos_evenPair_twoHundredNinetySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps292300.singular_series_pos_evenPair_twoHundredNinetyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.evenPair_card_threeHundredEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.evenPair_card_threeHundredFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.evenPair_card_threeHundredSix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.evenPair_card_threeHundredTen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.evenPair_card_threeHundredTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.isAdmissible_evenPair_threeHundredEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.isAdmissible_evenPair_threeHundredFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.isAdmissible_evenPair_threeHundredSix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.isAdmissible_evenPair_threeHundredTen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.isAdmissible_evenPair_threeHundredTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.localFactor_threeHundredTen_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.localFactor_threeHundredTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.nu_p_threeHundredEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.nu_p_threeHundredFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.nu_p_threeHundredSix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.nu_p_threeHundredTen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.nu_p_threeHundredTen_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.nu_p_threeHundredTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.nu_p_threeHundredTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.singular_series_finite_pos_evenPair_threeHundredEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.singular_series_finite_pos_evenPair_threeHundredFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.singular_series_finite_pos_evenPair_threeHundredSix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.singular_series_finite_pos_evenPair_threeHundredTen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.singular_series_finite_pos_evenPair_threeHundredTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.singular_series_pos_evenPair_threeHundredEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.singular_series_pos_evenPair_threeHundredFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.singular_series_pos_evenPair_threeHundredSix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.singular_series_pos_evenPair_threeHundredTen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps302310.singular_series_pos_evenPair_threeHundredTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.evenPair_card_threeHundredEighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.evenPair_card_threeHundredFourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.evenPair_card_threeHundredSixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.evenPair_card_threeHundredTwelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.evenPair_card_threeHundredTwenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.isAdmissible_evenPair_threeHundredEighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.isAdmissible_evenPair_threeHundredFourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.isAdmissible_evenPair_threeHundredSixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.isAdmissible_evenPair_threeHundredTwelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.isAdmissible_evenPair_threeHundredTwenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.localFactor_threeHundredTwelve_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.localFactor_threeHundredTwenty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.nu_p_threeHundredEighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.nu_p_threeHundredFourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.nu_p_threeHundredSixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.nu_p_threeHundredTwelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.nu_p_threeHundredTwelve_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.nu_p_threeHundredTwenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.nu_p_threeHundredTwenty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.singular_series_finite_pos_evenPair_threeHundredEighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.singular_series_finite_pos_evenPair_threeHundredFourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.singular_series_finite_pos_evenPair_threeHundredSixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.singular_series_finite_pos_evenPair_threeHundredTwelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.singular_series_finite_pos_evenPair_threeHundredTwenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.singular_series_pos_evenPair_threeHundredEighteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.singular_series_pos_evenPair_threeHundredFourteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.singular_series_pos_evenPair_threeHundredSixteen` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.singular_series_pos_evenPair_threeHundredTwelve` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps312320.singular_series_pos_evenPair_threeHundredTwenty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.evenPair_card_threeHundredThirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.evenPair_card_threeHundredTwentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.evenPair_card_threeHundredTwentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.evenPair_card_threeHundredTwentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.evenPair_card_threeHundredTwentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.isAdmissible_evenPair_threeHundredThirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.isAdmissible_evenPair_threeHundredTwentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.isAdmissible_evenPair_threeHundredTwentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.isAdmissible_evenPair_threeHundredTwentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.isAdmissible_evenPair_threeHundredTwentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.localFactor_threeHundredThirty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.localFactor_threeHundredTwentyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.nu_p_threeHundredThirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.nu_p_threeHundredThirty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.nu_p_threeHundredTwentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.nu_p_threeHundredTwentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.nu_p_threeHundredTwentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.nu_p_threeHundredTwentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.nu_p_threeHundredTwentyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.singular_series_finite_pos_evenPair_threeHundredThirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.singular_series_finite_pos_evenPair_threeHundredTwentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.singular_series_finite_pos_evenPair_threeHundredTwentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.singular_series_finite_pos_evenPair_threeHundredTwentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.singular_series_finite_pos_evenPair_threeHundredTwentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.singular_series_pos_evenPair_threeHundredThirty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.singular_series_pos_evenPair_threeHundredTwentyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.singular_series_pos_evenPair_threeHundredTwentyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.singular_series_pos_evenPair_threeHundredTwentySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps322330.singular_series_pos_evenPair_threeHundredTwentyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.evenPair_card_forty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.evenPair_card_thirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.evenPair_card_thirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.evenPair_card_thirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.evenPair_card_thirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.isAdmissible_evenPair_forty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.isAdmissible_evenPair_thirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.isAdmissible_evenPair_thirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.isAdmissible_evenPair_thirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.isAdmissible_evenPair_thirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.localFactor_forty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.localFactor_thirtyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.nu_p_forty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.nu_p_forty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.nu_p_thirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.nu_p_thirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.nu_p_thirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.nu_p_thirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.nu_p_thirtyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.singular_series_finite_pos_evenPair_forty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.singular_series_finite_pos_evenPair_thirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.singular_series_finite_pos_evenPair_thirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.singular_series_finite_pos_evenPair_thirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.singular_series_finite_pos_evenPair_thirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.singular_series_pos_evenPair_forty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.singular_series_pos_evenPair_thirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.singular_series_pos_evenPair_thirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.singular_series_pos_evenPair_thirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps3240.singular_series_pos_evenPair_thirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.evenPair_card_threeHundredForty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.evenPair_card_threeHundredThirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.evenPair_card_threeHundredThirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.evenPair_card_threeHundredThirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.evenPair_card_threeHundredThirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.isAdmissible_evenPair_threeHundredForty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.isAdmissible_evenPair_threeHundredThirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.isAdmissible_evenPair_threeHundredThirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.isAdmissible_evenPair_threeHundredThirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.isAdmissible_evenPair_threeHundredThirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.localFactor_threeHundredForty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.localFactor_threeHundredThirtyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.nu_p_threeHundredForty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.nu_p_threeHundredForty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.nu_p_threeHundredThirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.nu_p_threeHundredThirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.nu_p_threeHundredThirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.nu_p_threeHundredThirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.nu_p_threeHundredThirtyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.singular_series_finite_pos_evenPair_threeHundredForty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.singular_series_finite_pos_evenPair_threeHundredThirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.singular_series_finite_pos_evenPair_threeHundredThirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.singular_series_finite_pos_evenPair_threeHundredThirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.singular_series_finite_pos_evenPair_threeHundredThirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.singular_series_pos_evenPair_threeHundredForty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.singular_series_pos_evenPair_threeHundredThirtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.singular_series_pos_evenPair_threeHundredThirtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.singular_series_pos_evenPair_threeHundredThirtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps332340.singular_series_pos_evenPair_threeHundredThirtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.evenPair_card_threeHundredFifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.evenPair_card_threeHundredFortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.evenPair_card_threeHundredFortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.evenPair_card_threeHundredFortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.evenPair_card_threeHundredFortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.isAdmissible_evenPair_threeHundredFifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.isAdmissible_evenPair_threeHundredFortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.isAdmissible_evenPair_threeHundredFortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.isAdmissible_evenPair_threeHundredFortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.isAdmissible_evenPair_threeHundredFortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.localFactor_threeHundredFifty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.localFactor_threeHundredFortyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.nu_p_threeHundredFifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.nu_p_threeHundredFifty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.nu_p_threeHundredFortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.nu_p_threeHundredFortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.nu_p_threeHundredFortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.nu_p_threeHundredFortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.nu_p_threeHundredFortyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.singular_series_finite_pos_evenPair_threeHundredFifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.singular_series_finite_pos_evenPair_threeHundredFortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.singular_series_finite_pos_evenPair_threeHundredFortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.singular_series_finite_pos_evenPair_threeHundredFortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.singular_series_finite_pos_evenPair_threeHundredFortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.singular_series_pos_evenPair_threeHundredFifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.singular_series_pos_evenPair_threeHundredFortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.singular_series_pos_evenPair_threeHundredFortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.singular_series_pos_evenPair_threeHundredFortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps342350.singular_series_pos_evenPair_threeHundredFortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.evenPair_card_fifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.evenPair_card_fortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.evenPair_card_fortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.evenPair_card_fortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.evenPair_card_fortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.isAdmissible_evenPair_fifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.isAdmissible_evenPair_fortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.isAdmissible_evenPair_fortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.isAdmissible_evenPair_fortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.isAdmissible_evenPair_fortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.localFactor_fifty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.localFactor_fortyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.nu_p_fifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.nu_p_fifty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.nu_p_fortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.nu_p_fortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.nu_p_fortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.nu_p_fortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.nu_p_fortyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.singular_series_finite_pos_evenPair_fifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.singular_series_finite_pos_evenPair_fortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.singular_series_finite_pos_evenPair_fortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.singular_series_finite_pos_evenPair_fortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.singular_series_finite_pos_evenPair_fortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.singular_series_pos_evenPair_fifty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.singular_series_pos_evenPair_fortyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.singular_series_pos_evenPair_fortyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.singular_series_pos_evenPair_fortySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps4250.singular_series_pos_evenPair_fortyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.evenPair_card_fiftyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.evenPair_card_fiftyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.evenPair_card_fiftySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.evenPair_card_fiftyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.evenPair_card_sixty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.isAdmissible_evenPair_fiftyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.isAdmissible_evenPair_fiftyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.isAdmissible_evenPair_fiftySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.isAdmissible_evenPair_fiftyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.isAdmissible_evenPair_sixty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.localFactor_fiftyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.localFactor_sixty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.nu_p_fiftyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.nu_p_fiftyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.nu_p_fiftySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.nu_p_fiftyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.nu_p_fiftyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.nu_p_sixty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.nu_p_sixty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.singular_series_finite_pos_evenPair_fiftyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.singular_series_finite_pos_evenPair_fiftyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.singular_series_finite_pos_evenPair_fiftySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.singular_series_finite_pos_evenPair_fiftyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.singular_series_finite_pos_evenPair_sixty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.singular_series_pos_evenPair_fiftyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.singular_series_pos_evenPair_fiftyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.singular_series_pos_evenPair_fiftySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.singular_series_pos_evenPair_fiftyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps5260.singular_series_pos_evenPair_sixty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.evenPair_card_seventy` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.evenPair_card_sixtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.evenPair_card_sixtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.evenPair_card_sixtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.evenPair_card_sixtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.isAdmissible_evenPair_seventy` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.isAdmissible_evenPair_sixtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.isAdmissible_evenPair_sixtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.isAdmissible_evenPair_sixtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.isAdmissible_evenPair_sixtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.localFactor_seventy_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.localFactor_sixtyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.nu_p_seventy` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.nu_p_seventy_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.nu_p_sixtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.nu_p_sixtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.nu_p_sixtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.nu_p_sixtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.nu_p_sixtyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.singular_series_finite_pos_evenPair_seventy` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.singular_series_finite_pos_evenPair_sixtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.singular_series_finite_pos_evenPair_sixtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.singular_series_finite_pos_evenPair_sixtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.singular_series_finite_pos_evenPair_sixtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.singular_series_pos_evenPair_seventy` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.singular_series_pos_evenPair_sixtyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.singular_series_pos_evenPair_sixtyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.singular_series_pos_evenPair_sixtySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps6270.singular_series_pos_evenPair_sixtyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.evenPair_card_eighty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.evenPair_card_seventyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.evenPair_card_seventyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.evenPair_card_seventySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.evenPair_card_seventyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.isAdmissible_evenPair_eighty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.isAdmissible_evenPair_seventyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.isAdmissible_evenPair_seventyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.isAdmissible_evenPair_seventySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.isAdmissible_evenPair_seventyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.localFactor_eighty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.localFactor_seventyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.nu_p_eighty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.nu_p_eighty_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.nu_p_seventyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.nu_p_seventyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.nu_p_seventySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.nu_p_seventyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.nu_p_seventyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.singular_series_finite_pos_evenPair_eighty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.singular_series_finite_pos_evenPair_seventyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.singular_series_finite_pos_evenPair_seventyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.singular_series_finite_pos_evenPair_seventySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.singular_series_finite_pos_evenPair_seventyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.singular_series_pos_evenPair_eighty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.singular_series_pos_evenPair_seventyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.singular_series_pos_evenPair_seventyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.singular_series_pos_evenPair_seventySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps7280.singular_series_pos_evenPair_seventyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.evenPair_card_eightyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.evenPair_card_eightyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.evenPair_card_eightySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.evenPair_card_eightyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.evenPair_card_ninety` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.isAdmissible_evenPair_eightyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.isAdmissible_evenPair_eightyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.isAdmissible_evenPair_eightySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.isAdmissible_evenPair_eightyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.isAdmissible_evenPair_ninety` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.localFactor_eightyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.localFactor_ninety_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.nu_p_eightyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.nu_p_eightyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.nu_p_eightySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.nu_p_eightyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.nu_p_eightyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.nu_p_ninety` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.nu_p_ninety_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.singular_series_finite_pos_evenPair_eightyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.singular_series_finite_pos_evenPair_eightyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.singular_series_finite_pos_evenPair_eightySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.singular_series_finite_pos_evenPair_eightyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.singular_series_finite_pos_evenPair_ninety` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.singular_series_pos_evenPair_eightyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.singular_series_pos_evenPair_eightyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.singular_series_pos_evenPair_eightySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.singular_series_pos_evenPair_eightyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps8290.singular_series_pos_evenPair_ninety` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.evenPair_card_ninetyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.evenPair_card_ninetyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.evenPair_card_ninetySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.evenPair_card_ninetyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.evenPair_card_oneHundred` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.isAdmissible_evenPair_ninetyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.isAdmissible_evenPair_ninetyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.isAdmissible_evenPair_ninetySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.isAdmissible_evenPair_ninetyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.isAdmissible_evenPair_oneHundred` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.localFactor_ninetyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.localFactor_oneHundred_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.nu_p_ninetyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.nu_p_ninetyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.nu_p_ninetySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.nu_p_ninetyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.nu_p_ninetyTwo_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.nu_p_oneHundred` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.nu_p_oneHundred_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.singular_series_finite_pos_evenPair_ninetyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.singular_series_finite_pos_evenPair_ninetyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.singular_series_finite_pos_evenPair_ninetySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.singular_series_finite_pos_evenPair_ninetyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.singular_series_finite_pos_evenPair_oneHundred` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.singular_series_pos_evenPair_ninetyEight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.singular_series_pos_evenPair_ninetyFour` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.singular_series_pos_evenPair_ninetySix` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.singular_series_pos_evenPair_ninetyTwo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.Gaps92100.singular_series_pos_evenPair_oneHundred` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.evenPair_card_eight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.evenPair_card_four` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.evenPair_card_of_ne_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.evenPair_card_six` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.evenPair_card_ten` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.isAdmissible_evenPair_eight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.isAdmissible_evenPair_four` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.isAdmissible_evenPair_six` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.isAdmissible_evenPair_ten` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactorAt_eight_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactorAt_evenPair_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactorAt_four_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactorAt_four_odd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactorAt_four_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactorAt_four_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactorAt_six_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactorAt_six_odd_ne_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactorAt_six_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactorAt_six_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactorAt_ten_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactor_eight_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactor_evenPair_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactor_four_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactor_four_odd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactor_four_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactor_four_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactor_six_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactor_six_odd_ne_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactor_six_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactor_six_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.localFactor_ten_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.nu_p_evenPair` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.nu_p_evenPair_odd_of_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.nu_p_evenPair_odd_of_not_dvd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.nu_p_evenPair_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.nu_p_four` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.nu_p_four_odd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.nu_p_four_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.nu_p_six` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.nu_p_six_odd_ne_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.nu_p_six_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.nu_p_six_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.singular_series_finite_pos_evenPair` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.singular_series_finite_pos_evenPair_eight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.singular_series_finite_pos_evenPair_four` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.singular_series_finite_pos_evenPair_six` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.singular_series_finite_pos_evenPair_ten` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.singular_series_pos_evenPair_eight` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.singular_series_pos_evenPair_four` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.singular_series_pos_evenPair_six` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.SingularSeries.MoreExamples.singular_series_pos_evenPair_ten` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.SingularSeries.Wire.IsAdmissible` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Wire.h_conv_of_admissible` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Wire.isAdmissible_iff` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Wire.isAdmissible_raw` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Wire.singularSeriesFinite_tendsto_pos_of_admissible` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Wire.singular_series_finite_pos_of_admissible` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Wire.singular_series_pos_of_admissible` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Wire.singular_series_pos_supersedes_conditional` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.SingularSeries.Wire.singular_series_pos_unconditional` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Spectral.cos_two_pi_div_five` | ✓ | verified | lean-4.32.0 | run 73 (b666…) — re-proved fresh @ v4.32 via concrete circulant eigenvalues |
| DEFINITION | `Brockian.Spectral.cycleSpectrum` | ✓ | verified | lean-4.32.0 | run 73 (b666…) — re-proved fresh @ v4.32 via concrete circulant eigenvalues |
| PROVED | `Brockian.Spectral.golden_in_cycleSpectrum_five` | ✓ | verified | lean-4.32.0 | run 73 (b666…) — re-proved fresh @ v4.32 via concrete circulant eigenvalues |
| PROVED | `Brockian.Spectral.golden_sub_one_eq_two_cos` | ✓ | verified | lean-4.32.0 | run 73 (b666…) — re-proved fresh @ v4.32 via concrete circulant eigenvalues |
| PROVED | `Brockian.Spectral.golden_unique_to_five` | ✓ | verified | lean-4.32.0 | run 73 (b666…) — re-proved fresh @ v4.32 via concrete circulant eigenvalues |
| PROVED | `Brockian.Spectral.neg_golden_in_C5_spectrum` | ✓ | verified | lean-4.32.0 | run 73 (b666…) — re-proved fresh @ v4.32 via concrete circulant eigenvalues |
| PROVED | `Brockian.Spectral.two_cos_four_pi_div_five` | ✓ | verified | lean-4.32.0 | run 73 (b666…) — re-proved fresh @ v4.32 via concrete circulant eigenvalues |
| PROVED | `Brockian.SpectralGate1.abs_primeGaussian_le_two` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| PROVED | `Brockian.SpectralGate1.coeFn_mulLpCLM` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| PROVED | `Brockian.SpectralGate1.coeFn_mulLpFun` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| PROVED | `Brockian.SpectralGate1.coeFn_primeGaussianMulCLM` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| PROVED | `Brockian.SpectralGate1.continuous_primeBump` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| PROVED | `Brockian.SpectralGate1.continuous_primeGaussian` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| PROVED | `Brockian.SpectralGate1.eLpNorm_mulLpFun_le` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| PROVED | `Brockian.SpectralGate1.isSelfAdjoint_mulLpCLM` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| PROVED | `Brockian.SpectralGate1.isSelfAdjoint_primeGaussianMulCLM` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| DEFINITION | `Brockian.SpectralGate1.mulLpCLM` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| DEFINITION | `Brockian.SpectralGate1.mulLpFun` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| DEFINITION | `Brockian.SpectralGate1.mulLpₗ` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| DEFINITION | `Brockian.SpectralGate1.primeBump` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| PROVED | `Brockian.SpectralGate1.primeBump_le_geom` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| PROVED | `Brockian.SpectralGate1.primeBump_nonneg` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| DEFINITION | `Brockian.SpectralGate1.primeGaussian` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| DEFINITION | `Brockian.SpectralGate1.primeGaussianMulCLM` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| PROVED | `Brockian.SpectralGate1.primeGaussian_le_two` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| PROVED | `Brockian.SpectralGate1.primeGaussian_nonneg` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| DEFINITION | `Brockian.SpectralGate1.primeGaussianℂ` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| PROVED | `Brockian.SpectralGate1.primeGaussianℂ_memLp_top` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| PROVED | `Brockian.SpectralGate1.primeGaussianℂ_norm_le` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| PROVED | `Brockian.SpectralGate1.summable_primeBump` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — bounded-potential multiplication operator (honest Gate-1 piece) |
| DEFINITION | `Brockian.TransitionKernel.admissibleStarts` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.brockian_table_card` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.cousin_pins_mod_three` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.cousin_run_cap` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.forbidden_transition` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.gap10_run_cap` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| DEFINITION | `Brockian.TransitionKernel.kernel` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.kernel_row_sum` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.quadruplet_pins_mod_five` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.sexy_free_mod_three` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.sexy_run_cap` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.totalSum_count` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.totalSum_eq` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.twin_admissible_singleton` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.twin_pins_mod_three` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.twin_table_card` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TwinPrimeConstant.isAdmissible_twinOffsets` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.localFactorAt_twin` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.localFactorAt_twin_eq_tFactor` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.localFactorAt_twin_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.localFactorAt_twin_odd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.localFactorAt_twin_seven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.localFactorAt_twin_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.localFactorAt_twin_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.localFactor_twin_eq_tFactor` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.localFactor_twin_five` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.localFactor_twin_odd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.localFactor_twin_seven` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.localFactor_twin_three` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.localFactor_twin_two` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.nu_p_twin` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.nu_p_twin_odd` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.nu_p_twin_two` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.TwinPrimeConstant.oddPrimesUpTo` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.singularSeriesFinite_twin_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.singularSeriesFinite_twin_of_two_le` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.singularSeriesFinite_twin_pos` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.singularSeries_twin_eq_two_mul_constant` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.singularSeries_twin_pos` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.TwinPrimeConstant.twinOffsets` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.twinOffsets_card` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.twinOffsets_eq` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.TwinPrimeConstant.twinPrimeConstant` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.TwinPrimeConstant.twinPrimeConstantFinite` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.twinPrimeConstantFinite_pos` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.TwinPrimeConstant.twinPrimeConstant_pos` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.green_identity_integral` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Weyl/Green functional-analytic core (base rung) |
| PROVED | `Brockian.Weyl.lagrange_identity` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Weyl/Green functional-analytic core (base rung) |
| DEFINITION | `Brockian.Weyl.sturmL` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Weyl/Green functional-analytic core (base rung) |
| DEFINITION | `Brockian.Weyl.wronskian` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Weyl/Green functional-analytic core (base rung) |
| PROVED | `Brockian.Weyl.wronskian_const_one_witness` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Weyl/Green functional-analytic core (base rung) |
| PROVED | `Brockian.Weyl.wronskian_hasDerivAt` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Weyl/Green functional-analytic core (base rung) |
| PROVED | `Brockian.Weyl.wronskian_isConst` | ✓ | verified | lean-4.32.0 | swarm 2026-08-01 — Weyl/Green functional-analytic core (base rung) |
| DEFINITION | `Brockian.Weyl.Bridge.IsL2Solution` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.coeff_ne_zero` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.continuous_y` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.continuous_y'` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.global_boundary_identity` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.hasDerivAt_wronskianConj` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.integrable_normSq` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.integrable_normSq_add` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.integrable_wronskianConj_deriv` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.integrable_y'_normSq` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.integrable_y_normSq` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.integral_wronskianConj_eq` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.integral_wronskianConj_eq_mul` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.limUnder_wronskianConj_atBot_eq_zero` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.limUnder_wronskianConj_atTop_eq_zero` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.no_nonzero_L2_solution` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.norm_wronskianConj_le` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.not_integrableOn_const_pos_Ici` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.not_integrableOn_const_pos_Iic` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.tendsto_wronskianConj_atBot` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.tendsto_wronskianConj_atBot_zero` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.tendsto_wronskianConj_atTop` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.tendsto_wronskianConj_atTop_zero` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| DEFINITION | `Brockian.Weyl.Bridge.wronskianConj` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Bridge.wronskianConj_eq_two_I_im` | ✓ | verified | lean-4.32.0 | 2026-08-01 — no_nonzero_L2_solution (Wronskian energy identity) |
| PROVED | `Brockian.Weyl.Cayley.apply_ne_I_smul` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — abstract von Neumann ess-self-adjointness criterion |
| PROVED | `Brockian.Weyl.Cayley.apply_ne_neg_I_smul` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — abstract von Neumann ess-self-adjointness criterion |
| PROVED | `Brockian.Weyl.Cayley.deficiencySpace_eq_bot_iff` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — abstract von Neumann ess-self-adjointness criterion |
| PROVED | `Brockian.Weyl.Cayley.essentiallySelfAdjoint_iff` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — abstract von Neumann ess-self-adjointness criterion |
| PROVED | `Brockian.Weyl.Cayley.mem_orthogonal_rangeSMulSub_iff` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — abstract von Neumann ess-self-adjointness criterion |
| PROVED | `Brockian.Weyl.Cayley.mem_rangeSMulSub` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — abstract von Neumann ess-self-adjointness criterion |
| PROVED | `Brockian.Weyl.Cayley.norm_add_I_smul_eq` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — abstract von Neumann ess-self-adjointness criterion |
| DEFINITION | `Brockian.Weyl.Cayley.rangeAddI` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — abstract von Neumann ess-self-adjointness criterion |
| DEFINITION | `Brockian.Weyl.Cayley.rangeSMulSub` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — abstract von Neumann ess-self-adjointness criterion |
| DEFINITION | `Brockian.Weyl.Cayley.rangeSubI` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — abstract von Neumann ess-self-adjointness criterion |
| PROVED | `Brockian.Weyl.Chain.essSelfAdjoint_of_dense_ranges` | ✓ | verified | lean-4.32.0 | Weyl chain 2026-08-01 — closure modulo the range-density bridge |
| PROVED | `Brockian.Weyl.ClosedRange.eq_univ_of_dense_isClosed` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — dense+closed⇒univ; smulPMap closed |
| PROVED | `Brockian.Weyl.ClosedRange.range_eq_top_of_essentiallySelfAdjoint_of_isClosed_ranges` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — dense+closed⇒univ; smulPMap closed |
| PROVED | `Brockian.Weyl.ClosedRange.smulPMap_isClosed` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — dense+closed⇒univ; smulPMap closed |
| PROVED | `Brockian.Weyl.ClosedRange.smulPMap_isClosed_and_symmetric` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — dense+closed⇒univ; smulPMap closed |
| PROVED | `Brockian.Weyl.ClosedRangeClosure.dense_rangeSMulSub_of_le` | ✓ | verified | lean-4.32.0 | Gate-1 closed-range upgrade — closed symmetric op has closed non-real shifted range; AXLE @4.32 |
| PROVED | `Brockian.Weyl.ClosedRangeClosure.isClosed_rangeAddI_and_rangeSubI` | ✓ | verified | lean-4.32.0 | Gate-1 closed-range upgrade — closed symmetric op has closed non-real shifted range; AXLE @4.32 |
| PROVED | `Brockian.Weyl.ClosedRangeClosure.isClosed_rangeSMulSub_of_isClosed_of_isSymmetric` | ✓ | verified | lean-4.32.0 | Gate-1 closed-range upgrade — closed symmetric op has closed non-real shifted range; AXLE @4.32 |
| PROVED | `Brockian.Weyl.ClosedRangeClosure.rangeSMulSub_mono` | ✓ | verified | lean-4.32.0 | Gate-1 closed-range upgrade — closed symmetric op has closed non-real shifted range; AXLE @4.32 |
| PROVED | `Brockian.Weyl.ClosedShiftedRanges.adjoint_domain_le_closure_domain_of_essentiallySelfAdjoint_of_rangeAddI` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.ClosedShiftedRanges.closureResolventAtIOfEssentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.ClosedShiftedRanges.closureResolventAtIOfEssentiallySelfAdjointOfIsClosedRanges` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ClosedShiftedRanges.closure_eq_adjoint_of_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ClosedShiftedRanges.closure_eq_adjoint_of_essentiallySelfAdjoint_of_isClosed_ranges` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ClosedShiftedRanges.closure_isSelfAdjoint_of_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ClosedShiftedRanges.closure_isSelfAdjoint_of_essentiallySelfAdjoint_of_isClosed_ranges` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ClosedShiftedRanges.closure_shifted_ranges_eq_univ_of_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ClosedShiftedRanges.closure_shifted_ranges_eq_univ_of_essentiallySelfAdjoint_of_isClosed` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ClosedShiftedRanges.dense_closure_shifted_ranges_of_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ClosedShiftedRanges.isClosed_closure_shifted_ranges` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ClosedShiftedRanges.rangeAddI_le_closure` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ClosedShiftedRanges.rangeSubI_le_closure` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.Closure.adjoint_isClosed'` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.closure_eq_self_of_isClosed` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| DEFINITION | `Brockian.Weyl.Closure.deficiencySet` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.inner_adjoint_left` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.isClosed_deficiencySet` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.mem_deficiencySet_iff_mem_deficiencySpace` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.smulPMap_adjoint_isClosed` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.smulPMap_dense` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.smulPMap_isClosable` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.symmetric_adjoint_eq` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.symmetric_closure_le_adjoint` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.symmetric_domain_le_adjoint_domain` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.symmetric_isClosable` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.symmetric_le_adjoint` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Confining.ConfiningPotentialCandidate.isConfining` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.Confining.ConfiningPotentialCandidate.of_isConfining` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.Confining.IsConfining` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.Confining.UnboundedMultiplierShape` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.bound_C_blocks_zeros_outside_ball` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.brockian_realizer_admits_no_finite_bound` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.confiningCandidate_not_bddAbove` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.decaying_not_isConfining` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.gate1_vs_confining_shape` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.isConfining_iff_tendsto` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.isConfining_not_bddAbove` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.isConfining_unbounded` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.isConfining_unboundedMultiplierShape` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.no_brockian_eigenvector_outside_bound` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.not_both_decaying_and_confining` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.not_isConfining_of_abs_le` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.primeGaussian_blocks_zeros_outside_two` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.primeGaussian_is_decaying` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.primeGaussian_not_isConfining` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.primeGaussian_not_unboundedMultiplierShape` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.Confining.quadraticCandidate` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.quadraticCandidate_V` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.quadratic_isConfining` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Confining.quadratic_unboundedMultiplierShape` | ✓ | verified | lean-4.32.0 | roadmap #5 (A5 honesty step) — confining vs decaying dichotomy; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.ConfiningShape.CompactResolventShape` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| DEFINITION | `Brockian.Weyl.ConfiningShape.DiscreteSpectrumCandidate` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| DEFINITION | `Brockian.Weyl.ConfiningShape.EigenvalueCountingAsymptotic` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| DEFINITION | `Brockian.Weyl.ConfiningShape.EigenvalueCountingMatchesNT` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.brockian_eigenvalue_real_of_candidate` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.clm_bound_blocks_zeros_outside_ball` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.clm_bound_no_brockian_eigenvector` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.compactResolventShape_of_candidate` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.compactResolventShape_of_isConfining` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.confining_needed_for_shape_and_unbounded_spectrum` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.eigenvalueCountingAsymptotic_of_matches` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.eigenvalueCountingMatchesNT_comm` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.gate1_vs_confining_shape_package` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.not_compactResolventShape_of_abs_le` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.not_discreteSpectrumCandidate_of_bound` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.not_point_spectrum_unbounded_of_bound` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.primeGaussian_clm_blocks_large_zeros` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.primeGaussian_not_compactResolventShape` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| DEFINITION | `Brockian.Weyl.ConfiningShape.quadraticCandidate_reexport` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.quadratic_compactResolventShape` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.quadratic_isConfining_reexport` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.realizer_admits_no_finite_bound` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConfiningShape.spectrum_real_of_symm` | ✓ | verified | lean-4.32.0 | parallel-tool (Codex/Grok) module; AXLE @4.32; integrated by Claude for tip coherence |
| PROVED | `Brockian.Weyl.ConstMass.continuous_growing_exp_normSq` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — growing-mode mass diverges + radius→0 |
| PROVED | `Brockian.Weyl.ConstMass.exists_growing_mode_limitPointRadius` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — growing-mode mass diverges + radius→0 |
| PROVED | `Brockian.Weyl.ConstMass.growing_exp_IsLimitPointRadius` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — growing-mode mass diverges + radius→0 |
| PROVED | `Brockian.Weyl.ConstMass.growing_exp_mass_monotone` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — growing-mode mass diverges + radius→0 |
| PROVED | `Brockian.Weyl.ConstMass.growing_exp_mass_tendsto_atTop` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — growing-mode mass diverges + radius→0 |
| PROVED | `Brockian.Weyl.ConstMass.growing_exp_radius_tendsto_zero` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — growing-mode mass diverges + radius→0 |
| PROVED | `Brockian.Weyl.ConstMass.integral_exp_mul_tendsto_atTop` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — growing-mode mass diverges + radius→0 |
| PROVED | `Brockian.Weyl.ConstMass.integral_nonneg_mono` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — growing-mode mass diverges + radius→0 |
| PROVED | `Brockian.Weyl.ConstMass.normSq_cexp_eq` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — growing-mode mass diverges + radius→0 |
| DEFINITION | `Brockian.Weyl.DeficiencyODE.H2` | ✓ | verified | lean-4.32.0 | roadmap #1 — Gate-1 linchpin reduced to one classical regularity fact; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.DeficiencyODE.ReducedGate1Status` | ✓ | verified | lean-4.32.0 | roadmap #1 — Gate-1 linchpin reduced to one classical regularity fact; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.DeficiencyODE.WeakSolutionRegularity` | ✓ | verified | lean-4.32.0 | roadmap #1 — Gate-1 linchpin reduced to one classical regularity fact; AXLE @4.32 |
| PROVED | `Brockian.Weyl.DeficiencyODE.coeFn_potentialMul` | ✓ | verified | lean-4.32.0 | roadmap #1 — Gate-1 linchpin reduced to one classical regularity fact; AXLE @4.32 |
| CONDITIONAL | `Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity` | ✓ | verified | lean-4.32.0 | roadmap #1 — Gate-1 linchpin reduced to one classical regularity fact; AXLE @4.32 |
| PROVED | `Brockian.Weyl.DeficiencyODE.inner_g_potential` | ✓ | verified | lean-4.32.0 | roadmap #1 — Gate-1 linchpin reduced to one classical regularity fact; AXLE @4.32 |
| PROVED | `Brockian.Weyl.DeficiencyODE.inner_g_schwartz` | ✓ | verified | lean-4.32.0 | roadmap #1 — Gate-1 linchpin reduced to one classical regularity fact; AXLE @4.32 |
| PROVED | `Brockian.Weyl.DeficiencyODE.inner_g_schwartz_D2` | ✓ | verified | lean-4.32.0 | roadmap #1 — Gate-1 linchpin reduced to one classical regularity fact; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.DeficiencyODE.reduced_gate1_status` | ✓ | verified | lean-4.32.0 | roadmap #1 — Gate-1 linchpin reduced to one classical regularity fact; AXLE @4.32 |
| CONDITIONAL | `Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity` | ✓ | verified | lean-4.32.0 | roadmap #1 — Gate-1 linchpin reduced to one classical regularity fact; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.Dichotomy.IsLimitCircleRadius` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — b→∞ radius dichotomy (pure analysis) |
| DEFINITION | `Brockian.Weyl.Dichotomy.IsLimitPointRadius` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — b→∞ radius dichotomy (pure analysis) |
| PROVED | `Brockian.Weyl.Dichotomy.atTop_of_radius_tendsto_zero` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — b→∞ radius dichotomy (pure analysis) |
| PROVED | `Brockian.Weyl.Dichotomy.limitPointRadius_radius_tendsto_zero` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — b→∞ radius dichotomy (pure analysis) |
| PROVED | `Brockian.Weyl.Dichotomy.limitPoint_or_limitCircle_radius` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — b→∞ radius dichotomy (pure analysis) |
| PROVED | `Brockian.Weyl.Dichotomy.radius_tendsto_zero_iff` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — b→∞ radius dichotomy (pure analysis) |
| PROVED | `Brockian.Weyl.Dichotomy.radius_tendsto_zero_of_atTop` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — b→∞ radius dichotomy (pure analysis) |
| PROVED | `Brockian.Weyl.Dichotomy.tendsto_atTop_of_monotone_not_bddAbove` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — b→∞ radius dichotomy (pure analysis) |
| DEFINITION | `Brockian.Weyl.Dichotomy.weylRadius` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — b→∞ radius dichotomy (pure analysis) |
| DEFINITION | `Brockian.Weyl.Disk.Acoef` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| DEFINITION | `Brockian.Weyl.Disk.Pcoef` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.boundary_L2_identity` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| DEFINITION | `Brockian.Weyl.Disk.circleEq` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.circle_key` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| DEFINITION | `Brockian.Weyl.Disk.diskCenter` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.green_identity_integral` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.integral_normSq_mono` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.lagrange_identity` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.radius_formula` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| DEFINITION | `Brockian.Weyl.Disk.sturmL` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.weyl_disk_circle` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.weyl_nested_circle` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.weyl_radius_antitone` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| DEFINITION | `Brockian.Weyl.Disk.wronskian` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.wronskian_hasDerivAt` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.wronskian_isConst` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| DEFINITION | `Brockian.Weyl.DiskBridge.diskRadius` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — Disk radius = Dichotomy weylRadius + mass⇒r→0 |
| PROVED | `Brockian.Weyl.DiskBridge.diskRadius_eq_weylRadius` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — Disk radius = Dichotomy weylRadius + mass⇒r→0 |
| PROVED | `Brockian.Weyl.DiskBridge.diskRadius_tendsto_zero_of_limitPointRadius` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — Disk radius = Dichotomy weylRadius + mass⇒r→0 |
| PROVED | `Brockian.Weyl.DiskBridge.diskRadius_tendsto_zero_of_mass_atTop` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — Disk radius = Dichotomy weylRadius + mass⇒r→0 |
| PROVED | `Brockian.Weyl.DiskBridge.mass_monotone` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — Disk radius = Dichotomy weylRadius + mass⇒r→0 |
| PROVED | `Brockian.Weyl.ESA.clm_deficiency_eq_bot` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — EssentiallySelfAdjoint genuinely inhabited |
| PROVED | `Brockian.Weyl.ESA.clm_dense` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — EssentiallySelfAdjoint genuinely inhabited |
| PROVED | `Brockian.Weyl.ESA.clm_domain` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — EssentiallySelfAdjoint genuinely inhabited |
| PROVED | `Brockian.Weyl.ESA.clm_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — EssentiallySelfAdjoint genuinely inhabited |
| PROVED | `Brockian.Weyl.ESA.clm_isSymmetric` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — EssentiallySelfAdjoint genuinely inhabited |
| PROVED | `Brockian.Weyl.ESA.id_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — EssentiallySelfAdjoint genuinely inhabited |
| PROVED | `Brockian.Weyl.ESA.vec_eq_zero_of_inner` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — EssentiallySelfAdjoint genuinely inhabited |
| PROVED | `Brockian.Weyl.Extension.adjoint_closure` | ✓ | verified | lean-4.32.0 | roadmap #4 — closure/adjoint/uniqueness/real-spectrum; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Extension.adjoint_eigen_I_eq_zero_of_essSA` | ✓ | verified | lean-4.32.0 | roadmap #4 — closure/adjoint/uniqueness/real-spectrum; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Extension.adjoint_eigen_neg_I_eq_zero_of_essSA` | ✓ | verified | lean-4.32.0 | roadmap #4 — closure/adjoint/uniqueness/real-spectrum; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Extension.adjoint_graph_topologicalClosure_eq` | ✓ | verified | lean-4.32.0 | roadmap #4 — closure/adjoint/uniqueness/real-spectrum; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Extension.closure_eigenvalue_im_zero` | ✓ | verified | lean-4.32.0 | roadmap #4 — closure/adjoint/uniqueness/real-spectrum; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Extension.closure_isSymmetric` | ✓ | verified | lean-4.32.0 | roadmap #4 — closure/adjoint/uniqueness/real-spectrum; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Extension.closure_le_of_isClosed_extension` | ✓ | verified | lean-4.32.0 | roadmap #4 — closure/adjoint/uniqueness/real-spectrum; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Extension.closure_le_of_isSelfAdjoint_extension` | ✓ | verified | lean-4.32.0 | roadmap #4 — closure/adjoint/uniqueness/real-spectrum; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Extension.eigenvalue_im_zero` | ✓ | verified | lean-4.32.0 | roadmap #4 — closure/adjoint/uniqueness/real-spectrum; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Extension.essentiallySelfAdjoint_iff'` | ✓ | verified | lean-4.32.0 | roadmap #4 — closure/adjoint/uniqueness/real-spectrum; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Extension.isSelfAdjoint_closure_iff_eq_adjoint` | ✓ | verified | lean-4.32.0 | roadmap #4 — closure/adjoint/uniqueness/real-spectrum; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Extension.isSymmetric_of_le_adjoint` | ✓ | verified | lean-4.32.0 | roadmap #4 — closure/adjoint/uniqueness/real-spectrum; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Extension.le_closure_le_adjoint` | ✓ | verified | lean-4.32.0 | roadmap #4 — closure/adjoint/uniqueness/real-spectrum; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Extension.smulPMap_closure_eigenvalue_im_zero` | ✓ | verified | lean-4.32.0 | roadmap #4 — closure/adjoint/uniqueness/real-spectrum; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Extension.smulPMap_closure_isSymmetric` | ✓ | verified | lean-4.32.0 | roadmap #4 — closure/adjoint/uniqueness/real-spectrum; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.FourierMultiplier.FourierMultiplierInput` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FourierMultiplier.FourierMultiplierInput.dense_domain_position` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FourierMultiplier.FourierMultiplierInput.essentiallySelfAdjoint_position` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FourierMultiplier.dense_domain_transfer` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FourierMultiplier.dense_rangeAddI_transfer_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FourierMultiplier.dense_rangeSMulSub_transfer_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FourierMultiplier.dense_rangeSubI_transfer_iff` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FourierMultiplier.essentiallySelfAdjoint_of_multiplier_dense_ranges` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FourierMultiplier.essentiallySelfAdjoint_of_multiplier_esa` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FourierMultiplier.essentiallySelfAdjoint_of_multiplier_shift_dense` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FreeLaplacian.FreeLaplacianModel` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.FreeLaplacian.conjCLM` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FreeLaplacian.dense_domain_vadd_clm` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FreeLaplacian.essentiallySelfAdjoint_conjCLM` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FreeLaplacian.essentiallySelfAdjoint_conj_id` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FreeLaplacian.id_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.FreeLaplacian.identityFreeModel` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FreeLaplacian.inner_map_symm` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FreeLaplacian.inner_symm_map` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FreeLaplacian.isSelfAdjoint_conjCLM` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FreeLaplacian.isSymmetric_vadd_clm` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FreeLaplacian.vadd_clm_domain` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.FreeLaplacian2.conjCLM_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | roadmap #1 — ESA transfer across unitary + ξ² mult model; AXLE @4.32 |
| PROVED | `Brockian.Weyl.FreeLaplacian2.conjCLM_toPMap_essentiallySelfAdjoint_iff` | ✓ | verified | lean-4.32.0 | roadmap #1 — ESA transfer across unitary + ξ² mult model; AXLE @4.32 |
| PROVED | `Brockian.Weyl.FreeLaplacian2.dense_map_iff` | ✓ | verified | lean-4.32.0 | roadmap #1 — ESA transfer across unitary + ξ² mult model; AXLE @4.32 |
| PROVED | `Brockian.Weyl.FreeLaplacian2.essentiallySelfAdjoint_transfer` | ✓ | verified | lean-4.32.0 | roadmap #1 — ESA transfer across unitary + ξ² mult model; AXLE @4.32 |
| CONDITIONAL | `Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier` | ✓ | verified | lean-4.32.0 | roadmap #1 — ESA transfer across unitary + ξ² mult model; AXLE @4.32 |
| PROVED | `Brockian.Weyl.FreeLaplacian2.isSelfAdjoint_diagonal` | ✓ | verified | lean-4.32.0 | roadmap #1 — ESA transfer across unitary + ξ² mult model; AXLE @4.32 |
| PROVED | `Brockian.Weyl.FreeLaplacian2.isSelfAdjoint_multCLM` | ✓ | verified | lean-4.32.0 | roadmap #1 — ESA transfer across unitary + ξ² mult model; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.FreeLaplacian2.multCLM` | ✓ | verified | lean-4.32.0 | roadmap #1 — ESA transfer across unitary + ξ² mult model; AXLE @4.32 |
| PROVED | `Brockian.Weyl.FreeLaplacian2.multCLM_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | roadmap #1 — ESA transfer across unitary + ξ² mult model; AXLE @4.32 |
| PROVED | `Brockian.Weyl.FreeLaplacian2.rangeSMulSub_image` | ✓ | verified | lean-4.32.0 | roadmap #1 — ESA transfer across unitary + ξ² mult model; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.FreeLaplacian2.sqMultCLM` | ✓ | verified | lean-4.32.0 | roadmap #1 — ESA transfer across unitary + ξ² mult model; AXLE @4.32 |
| PROVED | `Brockian.Weyl.FreeLaplacian2.sqMult_conj_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | roadmap #1 — ESA transfer across unitary + ξ² mult model; AXLE @4.32 |
| PROVED | `Brockian.Weyl.FreeLaplacian2.sqMult_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | roadmap #1 — ESA transfer across unitary + ξ² mult model; AXLE @4.32 |
| PROVED | `Brockian.Weyl.Gate1Bounded.add_primeGaussian_dense_range_sub` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — Gate 1 potential ESA + Kato dense range on L2 |
| PROVED | `Brockian.Weyl.Gate1Bounded.add_primeGaussian_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — Gate 1 potential ESA + Kato dense range on L2 |
| PROVED | `Brockian.Weyl.Gate1Bounded.add_primeGaussian_isSelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — Gate 1 potential ESA + Kato dense range on L2 |
| PROVED | `Brockian.Weyl.Gate1Bounded.primeGaussianMul_dense_range_sub` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — Gate 1 potential ESA + Kato dense range on L2 |
| PROVED | `Brockian.Weyl.Gate1Bounded.primeGaussianMul_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — Gate 1 potential ESA + Kato dense range on L2 |
| PROVED | `Brockian.Weyl.Kato.dense_range_add_sub_of_selfAdjoint` | ✓ | verified | lean-4.32.0 | Aristotle proj c595862c — bounded Kato-Rellich; independently AXLE-verified @ 4.32 |
| PROVED | `Brockian.Weyl.Kato.isSelfAdjoint_add` | ✓ | verified | lean-4.32.0 | Aristotle proj c595862c — bounded Kato-Rellich; independently AXLE-verified @ 4.32 |
| PROVED | `Brockian.Weyl.KatoNeumann.boundedPerturbationTransfer_of_resolvent_norm_lt_one` | ✓ | verified | lean-4.32.0 | parallel-tool; AXLE @4.32; committed by Claude for coherence |
| DEFINITION | `Brockian.Weyl.KatoNeumann.katoFactorInverseOfNormLtOne` | ✓ | verified | lean-4.32.0 | parallel-tool; AXLE @4.32; committed by Claude for coherence |
| PROVED | `Brockian.Weyl.KatoNeumann.katoFactor_rightInverse_of_norm_lt_one` | ✓ | verified | lean-4.32.0 | parallel-tool; AXLE @4.32; committed by Claude for coherence |
| PROVED | `Brockian.Weyl.KatoNeumann.rangeAddI_perturb_eq_univ_of_resolvent_norm_lt_one` | ✓ | verified | lean-4.32.0 | parallel-tool; AXLE @4.32; committed by Claude for coherence |
| PROVED | `Brockian.Weyl.KatoNeumann.rangeSubI_perturb_eq_univ_of_resolvent_norm_lt_one` | ✓ | verified | lean-4.32.0 | parallel-tool; AXLE @4.32; committed by Claude for coherence |
| PROVED | `Brockian.Weyl.KatoNeumann.rightResolvent_perturb_of_norm_lt_one` | ✓ | verified | lean-4.32.0 | parallel-tool; AXLE @4.32; committed by Claude for coherence |
| PROVED | `Brockian.Weyl.KatoNeumannEstimates.boundedPerturbationTransfer_of_resolvent_norm_mul_lt_one` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoNeumannEstimates.katoFactor_rightInverse_of_norm_mul_lt_one` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoNeumannEstimates.norm_comp_lt_one_of_norm_mul_lt_one` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoNeumannEstimates.rangeAddI_perturb_eq_univ_of_resolvent_norm_mul_lt_one` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoNeumannEstimates.rangeSubI_perturb_eq_univ_of_resolvent_norm_mul_lt_one` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoNeumannEstimates.rightResolvent_perturb_of_norm_mul_lt_one` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRangeDensity.boundedPerturbationTransfer_iff_dense_ranges` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRangeDensity.boundedPerturbationTransfer_of_essentiallySelfAdjoint_perturb` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRangeDensity.boundedPerturbationTransfer_zero_of_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRangeDensity.boundedSelfAdjoint_perturb_dense_ranges` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRangeDensity.boundedSelfAdjoint_perturb_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRangeDensity.dense_rangeAddI_perturb_of_transfer` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRangeDensity.dense_rangeSubI_perturb_of_transfer` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRangeDensity.essentiallySelfAdjoint_perturb_iff_transfer` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRangeDensity.perturb_zero_eq` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRangeDensity.perturbed_ranges_eq_univ_of_transfer_of_isClosed` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRangeDensity.rangeAddI_perturb_eq_univ_of_transfer_of_isClosed` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRangeDensity.rangeSubI_perturb_eq_univ_of_transfer_of_isClosed` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.KatoRellichScaffold.CLMRightInverse` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.KatoRellichScaffold.RightResolvent` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRellichScaffold.boundedPerturbationTransfer_of_resolvent_factors` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRellichScaffold.boundedPerturbationTransfer_zero_of_rightResolvents` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRellichScaffold.dense_rangeSMulSub_of_rightResolvent` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRellichScaffold.factorRightInverse_zero` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.KatoRellichScaffold.katoFactor` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRellichScaffold.rangeAddI_perturb_eq_univ_of_resolvent_factor` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRellichScaffold.rangeSMulSub_eq_univ_of_rightResolvent` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRellichScaffold.rangeSubI_perturb_eq_univ_of_resolvent_factor` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRellichScaffold.rightResolvent_perturb_of_factor_rightInverse` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoRellichTransfer.boundedPerturbationTransfer_of_ranges_eq_univ` | ✓ | verified | lean-4.32.0 | roadmap A4 — Kato/Rellich Neumann transfer; AXLE @4.32 |
| PROVED | `Brockian.Weyl.KatoRellichTransfer.boundedPerturbationTransfer_of_resolvent_comp_norm_lt_one` | ✓ | verified | lean-4.32.0 | roadmap A4 — Kato/Rellich Neumann transfer; AXLE @4.32 |
| PROVED | `Brockian.Weyl.KatoRellichTransfer.boundedPerturbationTransfer_of_resolvent_product_norm_lt_one` | ✓ | verified | lean-4.32.0 | roadmap A4 — Kato/Rellich Neumann transfer; AXLE @4.32 |
| PROVED | `Brockian.Weyl.KatoRellichTransfer.essentiallySelfAdjoint_perturb_of_ranges_eq_univ` | ✓ | verified | lean-4.32.0 | roadmap A4 — Kato/Rellich Neumann transfer; AXLE @4.32 |
| PROVED | `Brockian.Weyl.KatoRellichTransfer.essentiallySelfAdjoint_perturb_of_resolvent_norm_lt_one` | ✓ | verified | lean-4.32.0 | roadmap A4 — Kato/Rellich Neumann transfer; AXLE @4.32 |
| PROVED | `Brockian.Weyl.KatoRellichTransfer.essentiallySelfAdjoint_perturb_of_resolvent_norm_mul_lt_one` | ✓ | verified | lean-4.32.0 | roadmap A4 — Kato/Rellich Neumann transfer; AXLE @4.32 |
| PROVED | `Brockian.Weyl.KatoRellichTransfer.essentiallySelfAdjoint_perturb_of_resolvent_norm_mul_lt_one_via_chain` | ✓ | verified | lean-4.32.0 | roadmap A4 — Kato/Rellich Neumann transfer; AXLE @4.32 |
| PROVED | `Brockian.Weyl.KatoRellichTransfer.perturbed_ranges_eq_univ_of_resolvent_norm_lt_one` | ✓ | verified | lean-4.32.0 | roadmap A4 — Kato/Rellich Neumann transfer; AXLE @4.32 |
| PROVED | `Brockian.Weyl.KatoRellichTransfer.perturbed_ranges_eq_univ_of_resolvent_norm_mul_lt_one` | ✓ | verified | lean-4.32.0 | roadmap A4 — Kato/Rellich Neumann transfer; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.KatoResolventConstruction.UnitShiftRightResolvents` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoResolventConstruction.boundedPerturbationTransfer_of_unitShiftRightResolvents_norm_lt_one` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoResolventConstruction.essentiallySelfAdjoint_perturb_of_unitShiftRightResolvents_norm_lt_one` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoResolventConstruction.essentiallySelfAdjoint_perturb_of_unitShiftRightResolvents_norm_lt_one_via_chain` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoResolventConstruction.norm_mul_Radd_lt_one_of_unitShiftRightResolvents` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoResolventConstruction.norm_mul_Rsub_lt_one_of_unitShiftRightResolvents` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.KatoResolventPackage.ResolventAtI` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoResolventPackage.ResolventAtI.boundedPerturbationTransfer` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoResolventPackage.ResolventAtI.norm_mul_add_lt_one` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoResolventPackage.ResolventAtI.norm_mul_sub_lt_one` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoResolventPackage.ResolventAtI.perturbed_ranges_eq_univ` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoResolventPackage.essentiallySelfAdjoint_perturb_of_resolventAtI` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoResolventPackage.essentiallySelfAdjoint_perturb_of_resolventAtI_via_chain` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.KatoTarget.dense_range_add_sub_of_selfAdjoint` | ✓ | verified | lean-4.32.0 | Aristotle/Harmonic close; AXLE @4.32 |
| PROVED | `Brockian.Weyl.KatoTarget.isSelfAdjoint_add` | ✓ | verified | lean-4.32.0 | Aristotle/Harmonic close; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.KatoUnbounded.BoundedPerturbationTransfer` | ✓ | verified | lean-4.32.0 | roadmap #2 — bounded self-adjoint perturbation of ESA operator; AXLE-verified @4.32 |
| PROVED | `Brockian.Weyl.KatoUnbounded.boundedPerturbationTransfer_clm` | ✓ | verified | lean-4.32.0 | roadmap #2 — bounded self-adjoint perturbation of ESA operator; AXLE-verified @4.32 |
| CONDITIONAL | `Brockian.Weyl.KatoUnbounded.essentiallySelfAdjoint_perturb` | ✓ | verified | lean-4.32.0 | roadmap #2 — bounded self-adjoint perturbation of ESA operator; AXLE-verified @4.32 |
| PROVED | `Brockian.Weyl.KatoUnbounded.essentiallySelfAdjoint_perturb_iff` | ✓ | verified | lean-4.32.0 | roadmap #2 — bounded self-adjoint perturbation of ESA operator; AXLE-verified @4.32 |
| DEFINITION | `Brockian.Weyl.KatoUnbounded.perturb` | ✓ | verified | lean-4.32.0 | roadmap #2 — bounded self-adjoint perturbation of ESA operator; AXLE-verified @4.32 |
| PROVED | `Brockian.Weyl.KatoUnbounded.perturb_apply` | ✓ | verified | lean-4.32.0 | roadmap #2 — bounded self-adjoint perturbation of ESA operator; AXLE-verified @4.32 |
| PROVED | `Brockian.Weyl.KatoUnbounded.perturb_apply_ne_I_smul` | ✓ | verified | lean-4.32.0 | roadmap #2 — bounded self-adjoint perturbation of ESA operator; AXLE-verified @4.32 |
| PROVED | `Brockian.Weyl.KatoUnbounded.perturb_apply_ne_neg_I_smul` | ✓ | verified | lean-4.32.0 | roadmap #2 — bounded self-adjoint perturbation of ESA operator; AXLE-verified @4.32 |
| PROVED | `Brockian.Weyl.KatoUnbounded.perturb_clm_eq` | ✓ | verified | lean-4.32.0 | roadmap #2 — bounded self-adjoint perturbation of ESA operator; AXLE-verified @4.32 |
| PROVED | `Brockian.Weyl.KatoUnbounded.perturb_clm_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | roadmap #2 — bounded self-adjoint perturbation of ESA operator; AXLE-verified @4.32 |
| PROVED | `Brockian.Weyl.KatoUnbounded.perturb_dense_domain` | ✓ | verified | lean-4.32.0 | roadmap #2 — bounded self-adjoint perturbation of ESA operator; AXLE-verified @4.32 |
| PROVED | `Brockian.Weyl.KatoUnbounded.perturb_domain` | ✓ | verified | lean-4.32.0 | roadmap #2 — bounded self-adjoint perturbation of ESA operator; AXLE-verified @4.32 |
| PROVED | `Brockian.Weyl.KatoUnbounded.perturb_isSymmetric` | ✓ | verified | lean-4.32.0 | roadmap #2 — bounded self-adjoint perturbation of ESA operator; AXLE-verified @4.32 |
| PROVED | `Brockian.Weyl.KatoUnbounded.perturb_norm_add_I_smul_eq` | ✓ | verified | lean-4.32.0 | roadmap #2 — bounded self-adjoint perturbation of ESA operator; AXLE-verified @4.32 |
| PROVED | `Brockian.Weyl.KatoUnbounded.perturb_norm_sub_smul_ge` | ✓ | verified | lean-4.32.0 | roadmap #2 — bounded self-adjoint perturbation of ESA operator; AXLE-verified @4.32 |
| DEFINITION | `Brockian.Weyl.LP.IsLimitPointAtInfty` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — limit-point for constant potential |
| DEFINITION | `Brockian.Weyl.LP.IsSolutionOn` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — limit-point for constant potential |
| DEFINITION | `Brockian.Weyl.LP.L2NearInfty` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — limit-point for constant potential |
| PROVED | `Brockian.Weyl.LP.const_potential_isLimitPoint` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — limit-point for constant potential |
| PROVED | `Brockian.Weyl.LP.exists_sqrt_pos_re` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — limit-point for constant potential |
| PROVED | `Brockian.Weyl.LP.indep_of_wronskian_ne_zero` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — limit-point for constant potential |
| PROVED | `Brockian.Weyl.LP.not_integrableOn_exp_mul_Ioi` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — limit-point for constant potential |
| DEFINITION | `Brockian.Weyl.LP.wronskian` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — limit-point for constant potential |
| PROVED | `Brockian.Weyl.LP.wronskian_hasDerivAt` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — limit-point for constant potential |
| PROVED | `Brockian.Weyl.LP.wronskian_isConst` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — limit-point for constant potential |
| DEFINITION | `Brockian.Weyl.LimitPointContinuous.FundSystemLimitPointObligation` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.LimitPointContinuous.HasFundamentalSystem` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.LimitPointContinuous.IsLimitPointAtInfty` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.LimitPointContinuous.IsSolution` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.LimitPointContinuous.L2NearInfty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.L2NearInfty_of_strong` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.LimitPointContinuous.StrongL2NearInfty` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.abs_le_const_potential` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.const_continuous_isLimitPoint` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.contBounded_const_isLimitPoint` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.contBounded_isLimitPoint_of_FS_obligation` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.continuous_const_potential` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.continuous_deriv_of_isSolution` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.continuous_of_isSolution` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.isLimitPoint_of_LP_const` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.isLimitPoint_of_fundSystem_member_not_L2` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.isLimitPoint_of_fundSystem_not_both_L2` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.isLimitPoint_of_non_L2_solution` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.isSolution_iff_isSolutionOn` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.no_nonzero_global_L2_of_contBounded` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.normSq_y''_le_of_bounded` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.norm_y''_le_of_bounded` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.LimitPointContinuous.wronskian` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.wronskian_const_of_solutions` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.wronskian_hasDerivAt` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.LimitPointContinuous.wronskian_isConst` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.MulReal.FreeMulModel` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.FreeMulModel.essentiallySelfAdjoint_mulOp` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.FreeMulModel.isSelfAdjoint_mulOp` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.MulReal.FreeMulModel.mulOp` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.MulReal.H2` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.add_clm_mul_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.add_constMul_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.add_mulLpCLM_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.add_mulLpCLM_isSelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.MulReal.constFreeMulModel` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.constFreeMulModel_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.MulReal.constFun` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.constFun_memLp_top` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.constFun_norm_le` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.constFun_real` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.MulReal.constMulCLM` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.constMul_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.isSelfAdjoint_constMulCLM` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.isSelfAdjoint_oneMulCLM` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.mulLpCLM_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.MulReal.oneFreeMulModel` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.MulReal.oneMulCLM` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.oneMul_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.MulReal.primeGaussianFreeMulModel` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.primeGaussianFreeMulModel_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| PROVED | `Brockian.Weyl.MulReal.primeGaussianMul_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl free-model rung — real L-infinity multiplication ESA; AXLE @4.32 |
| DEFINITION | `Brockian.Weyl.Operator.EssentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — symmetric unbounded-operator framework |
| PROVED | `Brockian.Weyl.Operator.IsSymmetric` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — symmetric unbounded-operator framework |
| PROVED | `Brockian.Weyl.Operator.IsSymmetric.eq_zero_of_apply_eq_smul` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — symmetric unbounded-operator framework |
| PROVED | `Brockian.Weyl.Operator.IsSymmetric.im_eq_zero_of_apply_eq_smul` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — symmetric unbounded-operator framework |
| PROVED | `Brockian.Weyl.Operator.IsSymmetric.inner_apply` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — symmetric unbounded-operator framework |
| PROVED | `Brockian.Weyl.Operator.IsSymmetric.inner_self_im` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — symmetric unbounded-operator framework |
| PROVED | `Brockian.Weyl.Operator.IsSymmetric.norm_sub_smul_ge` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — symmetric unbounded-operator framework |
| DEFINITION | `Brockian.Weyl.Operator.deficiencySpace` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — symmetric unbounded-operator framework |
| PROVED | `Brockian.Weyl.Operator.mem_deficiencySpace_iff` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — symmetric unbounded-operator framework |
| DEFINITION | `Brockian.Weyl.Operator.smulPMap` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — symmetric unbounded-operator framework |
| PROVED | `Brockian.Weyl.Operator.smulPMap_domain` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — symmetric unbounded-operator framework |
| PROVED | `Brockian.Weyl.Operator.smulPMap_isSymmetric` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — symmetric unbounded-operator framework |
| DEFINITION | `Brockian.Weyl.OperatorChoice.ConfiningPotentialCandidate` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.OperatorChoice.DecayingPotentialCandidate` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.OperatorChoice.brockian_eigenvalue_norm` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.OperatorChoice.norm_eigenvalue_le_of_bound` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.OperatorChoice.norm_eigenvalue_le_opNorm` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.OperatorChoice.norm_primeGaussianMulCLM_le` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.OperatorChoice.not_eigenvalue_of_bound_lt` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.OperatorChoice.not_realize_zero_of_bound_lt` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.OperatorChoice.not_realize_zero_of_toPMap` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.OperatorChoice.primeGaussianMulCLM_opNorm_le_two` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.OperatorChoice.primeGaussian_decaying` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.OperatorChoice.primeGaussian_not_realize_large_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.OperatorChoice.rh_operator_needs_unbounded_spectrum` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.RadiusDichotomy.radius_pos_limit_of_mass_finite` | ✓ | verified | lean-4.32.0 | Aristotle proj 50ca67ca — radius dichotomy; AXLE-verified @4.32 (1-line port from 4.28) |
| PROVED | `Brockian.Weyl.RadiusDichotomy.radius_tendsto_zero_iff_counterexample` | ✓ | verified | lean-4.32.0 | Aristotle proj 50ca67ca — radius dichotomy; AXLE-verified @4.32 (1-line port from 4.28) |
| PROVED | `Brockian.Weyl.RadiusDichotomy.radius_tendsto_zero_iff_of_pos` | ✓ | verified | lean-4.32.0 | Aristotle proj 50ca67ca — radius dichotomy; AXLE-verified @4.32 (1-line port from 4.28) |
| PROVED | `Brockian.Weyl.RadiusDichotomy.radius_to_zero_of_mass_infinite` | ✓ | verified | lean-4.32.0 | Aristotle proj 50ca67ca — radius dichotomy; AXLE-verified @4.32 (1-line port from 4.28) |
| PROVED | `Brockian.Weyl.ResolventFromESA.essentiallySelfAdjoint_perturb_of_essentiallySelfAdjoint_of_isClosed_ranges` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ResolventFromESA.exists_rightResolvent_of_range_eq_univ` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ResolventFromESA.norm_le_inv_im_mul_norm_shifted` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ResolventFromESA.norm_rightResolventOfRangeEqUniv_le` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.ResolventFromESA.resolventAtIOfEssentiallySelfAdjointOfIsClosedRanges` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.ResolventFromESA.resolventAtIOfSurjectiveShiftedRanges` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.ResolventFromESA.rightResolventOfRangeEqUniv` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ResolventFromESA.rightResolventOfRangeEqUniv_maps_domain` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ResolventFromESA.rightResolventOfRangeEqUniv_right_inverse` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ResolventFromESA.rightResolvents_of_essentiallySelfAdjoint_of_isClosed_ranges` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ResolventFromESA.rightResolvents_of_surjective_shifted_ranges` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.ResolventFromESA.shiftedMap` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ResolventFromESA.shiftedMap_surjective_of_range_eq_univ` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.ResolventFromESA.shiftedResolventLinearMap` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ResolventFromESA.shiftedResolventLinearMap_bound` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ResolventFromESA.shiftedResolventLinearMap_maps_domain` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ResolventFromESA.shiftedResolventLinearMap_right_inverse` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.ResolventFromESA.shiftedRightInverseLinearMap` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.ResolventFromESA.shiftedRightInverseLinearMap_spec` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.SchrodingerESA.DeficiencyRepresentsODE` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| DEFINITION | `Brockian.Weyl.SchrodingerESA.Gate1ChainStatus` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| PROVED | `Brockian.Weyl.SchrodingerESA.deficiencySpace_eq_bot_of_ode_bridge` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| PROVED | `Brockian.Weyl.SchrodingerESA.dense_ranges_of_ode_bridge` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| PROVED | `Brockian.Weyl.SchrodingerESA.essSelfAdjoint_of_ode_bridge_via_chain` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| PROVED | `Brockian.Weyl.SchrodingerESA.essentiallySelfAdjoint_of_ode_bridge` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| PROVED | `Brockian.Weyl.SchrodingerESA.free_plus_primeGaussian_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| DEFINITION | `Brockian.Weyl.SchrodingerESA.gate1_chain_status` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| PROVED | `Brockian.Weyl.SchrodingerESA.primeGaussian_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| DEFINITION | `Brockian.Weyl.SchrodingerGate1Closed.L2R` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.SchrodingerGate1Closed.schrodinger_closureResolventAtI` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SchrodingerGate1Closed.schrodinger_closure_eq_adjoint` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SchrodingerGate1Closed.schrodinger_closure_isSelfAdjoint` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SchrodingerGate1Closed.schrodinger_closure_shifted_ranges_eq_univ` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SchrodingerGate1Closed.schrodinger_core_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.SchrodingerGate1Final.L2R` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.SchrodingerGate1Final.freeCoreMap` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SchrodingerGate1Final.freeCoreMap_apply` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.SchrodingerGate1Final.freeSchrodingerPMap` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SchrodingerGate1Final.freeSchrodingerPMap_dense` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SchrodingerGate1Final.freeSchrodingerPMap_domain` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SchrodingerGate1Final.freeSchrodingerPMap_isSymmetric` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SchrodingerGate1Final.freeSchrodingerPMap_toFun_ofInjective` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SchrodingerGate1Final.schrodingerPMap_eq_perturb_free` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SchrodingerGate1Final.schrodinger_essentiallySelfAdjoint_iff_katoTransfer` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SchrodingerGate1Final.schrodinger_essentiallySelfAdjoint_of_distributionalPrimitiveIdentity` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SchrodingerGate1Final.schrodinger_essentiallySelfAdjoint_of_katoTransfer` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SchrodingerGate1Final.schrodinger_essentiallySelfAdjoint_of_weakSolutionVanishing` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.SchrodingerMinimal.D2` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.D2_apply` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| DEFINITION | `Brockian.Weyl.SchrodingerMinimal.H2` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| DEFINITION | `Brockian.Weyl.SchrodingerMinimal.Lconj` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.Lconj_apply` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| DEFINITION | `Brockian.Weyl.SchrodingerMinimal.MinimalGate1Status` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.coeFn_schwartzToL2` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| DEFINITION | `Brockian.Weyl.SchrodingerMinimal.coreMap` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.coreMap_apply` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.coreMap_symm` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| DEFINITION | `Brockian.Weyl.SchrodingerMinimal.deficiencyRepresentsODE_of_adjoint_eigenvector` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.inner_toLp` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.isSelfAdjoint_potentialMulCLM` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.kinetic_symm` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| DEFINITION | `Brockian.Weyl.SchrodingerMinimal.minimal_gate1_status` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| DEFINITION | `Brockian.Weyl.SchrodingerMinimal.potentialMulCLM` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.potential_symm` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| DEFINITION | `Brockian.Weyl.SchrodingerMinimal.schrodingerPMap` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.schrodingerPMap_dense` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.schrodingerPMap_domain` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.schrodingerPMap_isSymmetric` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.schrodingerPMap_toFun_ofInjective` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| CONDITIONAL | `Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| DEFINITION | `Brockian.Weyl.SchrodingerMinimal.schwartzToL2` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.schwartzToL2_apply` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.schwartzToL2_injective` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.schwartz_ibp1` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| PROVED | `Brockian.Weyl.SchrodingerMinimal.schwartz_ibp2` | ✓ | verified | lean-4.32.0 | roadmap #3 — concrete T=-d²/dx²+V on L²(ℝ); AXLE @4.32 AND @4.28 |
| DEFINITION | `Brockian.Weyl.SymmetryPackage.SymmetricRealSpectrum` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SymmetryPackage.eigenvalue_im_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SymmetryPackage.injective_of_im_ne_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SymmetryPackage.norm_sub_smul_ge` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SymmetryPackage.not_eigenvalue_of_im_ne_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SymmetryPackage.quadratic_form_im_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SymmetryPackage.smulPMap_isSymmetric` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SymmetryPackage.smulPMap_not_eigenvalue_of_im_ne_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.Weyl.SymmetryPackage.smulPMap_quadratic_form_im_zero` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.SymmetryPackage.symmetricRealSpectrum` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.Weyl.WeylLawTarget.MatchesRiemannVonMangoldt` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| DEFINITION | `Brockian.Weyl.WeylLawTarget.N_model` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| DEFINITION | `Brockian.Weyl.WeylLawTarget.N_op` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| PROVED | `Brockian.Weyl.WeylLawTarget.N_op_tendsto_atTop_of_WeylLawMatch` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| PROVED | `Brockian.Weyl.WeylLawTarget.N_op_tendsto_atTop_of_matches_rvm` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| DEFINITION | `Brockian.Weyl.WeylLawTarget.WeylLawCandidate` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| DEFINITION | `Brockian.Weyl.WeylLawTarget.WeylLawCandidateExists` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| DEFINITION | `Brockian.Weyl.WeylLawTarget.WeylLawMatch` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| DEFINITION | `Brockian.Weyl.WeylLawTarget.WeylLawMatchDiff` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| PROVED | `Brockian.Weyl.WeylLawTarget.WeylLawMatchDiff_iff_eigenvalueCountingMatchesNT` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| PROVED | `Brockian.Weyl.WeylLawTarget.WeylLawMatch_iff_eigenvalueCountingAsymptotic` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| PROVED | `Brockian.Weyl.WeylLawTarget.WeylLawMatch_of_diff` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| PROVED | `Brockian.Weyl.WeylLawTarget.WeylLawMatch_of_eigenvalueCountingMatchesNT` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| CONDITIONAL | `Brockian.Weyl.WeylLawTarget.counting_diverges_of_candidate` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| CONDITIONAL | `Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| CONDITIONAL | `Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| CONDITIONAL | `Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| PROVED | `Brockian.Weyl.WeylLawTarget.point_spectrum_unbounded_of_candidate` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| DEFINITION | `Brockian.Weyl.WeylLawTarget.riemannVonMangoldtMain` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| PROVED | `Brockian.Weyl.WeylLawTarget.riemannVonMangoldtMain_tendsto_atTop` | ✓ | verified | lean-4.32.0 | Grok swarm 2026-08-01 Lane E#25 — N(T)~(T/2π)log conditional schema (CONDITIONAL) |
| DEFINITION | `Brockian.WeylPlancherelScaffold.IsPlancherelUnitary` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylPlancherelScaffold.PlancherelFreeLaplacianInput` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylPlancherelScaffold.PlancherelFreeLaplacianInput.dense_domain_position` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylPlancherelScaffold.PlancherelFreeLaplacianInput.dense_range_addI_position` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylPlancherelScaffold.PlancherelFreeLaplacianInput.dense_range_subI_position` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylPlancherelScaffold.PlancherelFreeLaplacianInput.essentiallySelfAdjoint_position` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylPlancherelScaffold.PlancherelFreeLaplacianInput.essentiallySelfAdjoint_position_of_multiplier_esa` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylPlancherelScaffold.PlancherelFreeLaplacianInput.isPlancherel` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylPlancherelScaffold.PlancherelFreeLaplacianInput.toFourierMultiplierInput` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylPlancherelScaffold.essentiallySelfAdjoint_of_plancherel_multiplier_dense_ranges` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylPlancherelScaffold.isPlancherelUnitary` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakEnergy.L2R` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakEnergy.conjugateLp_eq_star` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakEnergy.conjugateRHSLp_eq_potential_sub` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakEnergy.continuous_laplacianSymbol` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakEnergy.fourier_laplacian_ae` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakEnergy.im_inner_conjugateRHSLp` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakEnergy.im_inner_laplacian_eq_zero` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakEnergy.laplacianSymbol` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakEnergy.laplacianSymbol_mul_locallyIntegrable` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakEnergy.potentialMulCLM_coeFn` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakEnergy.schrodinger_essentiallySelfAdjoint_of_continuous_bounded` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakEnergy.weakSolutionVanishing_of_continuous_bounded` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakPrimitiveClassical.DistributionalPrimitiveData` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakPrimitiveClassical.DistributionalPrimitiveIdentity` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakPrimitiveClassical.WeakPrimitiveClassicalStatus` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakPrimitiveClassical.WeakSolutionVanishing` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakPrimitiveClassical.integral_identity_of_hasDerivAt` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakPrimitiveClassical.memLp_of_l2_representative` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakPrimitiveClassical.primitiveModel_of_distributionalPrimitiveData` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakPrimitiveClassical.primitiveModel_zero` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakPrimitiveClassical.rhs_integral_identity_of_hasDerivAt` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakPrimitiveClassical.weakPrimitiveClassicalStatus` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakPrimitiveClassical.weakToPrimitiveRegularity_of_continuous_bounded_of_distributionalPrimitiveIdentity` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakPrimitiveClassical.weakToPrimitiveRegularity_of_continuous_bounded_of_weakSolutionVanishing` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakPrimitiveClassical.weakToPrimitiveRegularity_of_distributionalPrimitiveIdentity` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakPrimitiveClassical.weakToPrimitiveRegularity_of_weakSolutionVanishing` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakPrimitiveLocal.DistributionalPrimitiveHypothesis` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakPrimitiveLocal.DistributionalPrimitiveIdentity` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakPrimitiveLocal.primitiveModel_of_distributionalPrimitiveIdentity` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakPrimitiveLocal.primitiveModel_y_eq_coe_of_canonical_continuous` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakPrimitiveLocal.schrodinger_essentiallySelfAdjoint_of_distributional_primitives` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakPrimitiveLocal.weakToIntegralRegularity_of_distributional_primitives` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakPrimitiveLocal.weakToPrimitiveRegularity_of_distributional_primitives` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakRegularityClosed.L2R` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakRegularityClosed.conjugateLp` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityClosed.conjugateLp_coeFn` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityClosed.conjugateLp_toTemperedDistribution_apply` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakRegularityClosed.conjugateRHS` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakRegularityClosed.conjugateRHSLp` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityClosed.conjugateRHSLp_coeFn` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityClosed.conjugateRHSLp_toTemperedDistribution_apply` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityClosed.conjugateRHS_memLp` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakRegularityClosed.conjugateRepresentative` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityClosed.conjugateRepresentative_memLp` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityClosed.laplacian_eq_secondDeriv` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityClosed.lineDeriv_one_eq_deriv` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityClosed.secondDeriv_conjugateLp_eq_conjugateRHSLp` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakRegularityCore.IntegralSchrodingerModel` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakRegularityCore.WeakRegularityCoreStatus` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakRegularityCore.WeakToIntegralRegularity` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityCore.classicalL2Representative_of_integralModel` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityCore.continuous_representatives_eq_of_ae` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityCore.continuous_schrodingerRHS` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityCore.integralModel_hasDerivAt_y` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityCore.integralModel_hasDerivAt_yPrime` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityCore.integralModel_isL2Solution` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityCore.integralModel_representative_unique` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakRegularityCore.schrodingerRHS` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityCore.schrodinger_essentiallySelfAdjoint_of_weakToIntegral` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakRegularityCore.weakRegularityCoreStatus` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityCore.weakToClassicalRegularity_of_weakToIntegral` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakRegularityDischarge.PrimitiveSchrodingerModel` | ✓ | verified | lean-4.32.0 | roadmap A1 — weak regularity discharge layer; AXLE @4.32 |
| DEFINITION | `Brockian.WeylWeakRegularityDischarge.WeakRegularityDischargeStatus` | ✓ | verified | lean-4.32.0 | roadmap A1 — weak regularity discharge layer; AXLE @4.32 |
| DEFINITION | `Brockian.WeylWeakRegularityDischarge.WeakToPrimitiveRegularity` | ✓ | verified | lean-4.32.0 | roadmap A1 — weak regularity discharge layer; AXLE @4.32 |
| PROVED | `Brockian.WeylWeakRegularityDischarge.coeFn_integrableOn_Icc` | ✓ | verified | lean-4.32.0 | roadmap A1 — weak regularity discharge layer; AXLE @4.32 |
| PROVED | `Brockian.WeylWeakRegularityDischarge.coeFn_locallyIntegrable` | ✓ | verified | lean-4.32.0 | roadmap A1 — weak regularity discharge layer; AXLE @4.32 |
| PROVED | `Brockian.WeylWeakRegularityDischarge.continuous_rhs_primitive_of_coeFn` | ✓ | verified | lean-4.32.0 | roadmap A1 — weak regularity discharge layer; AXLE @4.32 |
| PROVED | `Brockian.WeylWeakRegularityDischarge.integralModel_of_primitiveModel` | ✓ | verified | lean-4.32.0 | roadmap A1 — weak regularity discharge layer; AXLE @4.32 |
| PROVED | `Brockian.WeylWeakRegularityDischarge.locallyIntegrable_continuous_primitive` | ✓ | verified | lean-4.32.0 | roadmap A1 — weak regularity discharge layer; AXLE @4.32 |
| PROVED | `Brockian.WeylWeakRegularityDischarge.locallyIntegrable_intervalIntegrable` | ✓ | verified | lean-4.32.0 | roadmap A1 — weak regularity discharge layer; AXLE @4.32 |
| PROVED | `Brockian.WeylWeakRegularityDischarge.schrodingerRHS_coeFn_locallyIntegrable` | ✓ | verified | lean-4.32.0 | roadmap A1 — weak regularity discharge layer; AXLE @4.32 |
| PROVED | `Brockian.WeylWeakRegularityDischarge.schrodinger_essentiallySelfAdjoint_of_weakToPrimitive` | ✓ | verified | lean-4.32.0 | roadmap A1 — weak regularity discharge layer; AXLE @4.32 |
| DEFINITION | `Brockian.WeylWeakRegularityDischarge.weakRegularityDischargeStatus` | ✓ | verified | lean-4.32.0 | roadmap A1 — weak regularity discharge layer; AXLE @4.32 |
| PROVED | `Brockian.WeylWeakRegularityDischarge.weakToClassicalRegularity_of_weakToPrimitive` | ✓ | verified | lean-4.32.0 | roadmap A1 — weak regularity discharge layer; AXLE @4.32 |
| PROVED | `Brockian.WeylWeakRegularityDischarge.weakToIntegralRegularity_of_weakToPrimitive` | ✓ | verified | lean-4.32.0 | roadmap A1 — weak regularity discharge layer; AXLE @4.32 |
| DEFINITION | `Brockian.WeylWeakRegularityScaffold.ClassicalL2Representative` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakRegularityScaffold.H2` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakRegularityScaffold.WeakRegularityPipelineStatus` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakRegularityScaffold.WeakSchrodingerEquation` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakRegularityScaffold.WeakToClassicalRegularity` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityScaffold.classicalL2Representative_eq_zero_of_bounded_nonreal` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityScaffold.deficiencyRepresentsODE_of_weakToClassical` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityScaffold.deficiencyVector_weakSchrodingerEquation` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityScaffold.existingWeakRegularity_of_weakToClassical` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityScaffold.schrodinger_essentiallySelfAdjoint_of_weakToClassical` | ✓ | verified | lean-4.32.0 |  |
| DEFINITION | `Brockian.WeylWeakRegularityScaffold.weakRegularityPipelineStatus` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityScaffold.weakToClassicalRegularity_iff_existing` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.WeylWeakRegularityScaffold.weakToClassicalRegularity_of_existing` | ✓ | verified | lean-4.32.0 |  |
| PROVED | `Brockian.XiFunctionalEquation.completedRiemannZeta_functional_equation` | ✓ | verified | lean-4.32.0 | roadmap #28 — xi functional equation + zeta<->xi zero correspondence; AXLE @4.32 |
| PROVED | `Brockian.XiFunctionalEquation.riemannXi_apply` | ✓ | verified | lean-4.32.0 | roadmap #28 — xi functional equation + zeta<->xi zero correspondence; AXLE @4.32 |
| PROVED | `Brockian.XiFunctionalEquation.riemannXi_eq_zero_iff_zeta_zero_of_mem_critical_strip` | ✓ | verified | lean-4.32.0 | roadmap #28 — xi functional equation + zeta<->xi zero correspondence; AXLE @4.32 |
| PROVED | `Brockian.XiFunctionalEquation.riemannXi_functional_equation` | ✓ | verified | lean-4.32.0 | roadmap #28 — xi functional equation + zeta<->xi zero correspondence; AXLE @4.32 |
| PROVED | `Brockian.XiFunctionalEquation.zeta_zero_of_riemannXi_zero` | ✓ | verified | lean-4.32.0 | roadmap #28 — xi functional equation + zeta<->xi zero correspondence; AXLE @4.32 |
| PROVED | `Brockian.XiFunctionalEquation.zeta_zero_one_sub_of_mem_critical_strip` | ✓ | verified | lean-4.32.0 | roadmap #28 — xi functional equation + zeta<->xi zero correspondence; AXLE @4.32 |
