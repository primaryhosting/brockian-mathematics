# Brockian Verified-Theorem Registry

> Generated from AXLE independent verification attestations. `register` is derived from axioms + AXLE verdict, never hand-asserted (spec §5).

> **PROVED** includes theorems closed by the kernel-checked `decide` tactic (finite `ZMod`/`Finset` checks — genuinely verified, ledger-consistent). `native_decide` (compiler-trusted, adds `Lean.ofReduceBool`) is excluded from PROVED by the axiom gate. `DEFINITION` = a supporting `def`; `CONJECTURE` = a named Prop container (never a claim).

## Summary

- **CONDITIONAL**: 15
- **CONJECTURE**: 1
- **DEFINITION**: 217
- **PROVED**: 921

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
| PROVED | `Brockian.CyclotomicRealDegree.pentagon_quadratic` | ✓ | verified | lean-4.32.0 | roadmap #6+#8 — composite-n real cyclotomic degree + quadratic classification; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicRealDegree.quadratic_iff_mem` | ✓ | verified | lean-4.32.0 | roadmap #6+#8 — composite-n real cyclotomic degree + quadratic classification; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicRealDegree.quadratic_iff_totient_four` | ✓ | verified | lean-4.32.0 | roadmap #6+#8 — composite-n real cyclotomic degree + quadratic classification; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicRealDegree.spectral_degree_general` | ✓ | verified | lean-4.32.0 | roadmap #6+#8 — composite-n real cyclotomic degree + quadratic classification; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicRealDegree.spectral_natDegree_two_mul` | ✓ | verified | lean-4.32.0 | roadmap #6+#8 — composite-n real cyclotomic degree + quadratic classification; AXLE @4.32 |
| PROVED | `Brockian.CyclotomicRealDegree.totient_eq_four_iff` | ✓ | verified | lean-4.32.0 | roadmap #6+#8 — composite-n real cyclotomic degree + quadratic classification; AXLE @4.32 |
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
| DEFINITION | `Brockian.FranklinInvolution.FranklinData` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| CONDITIONAL | `Brockian.FranklinInvolution.franklin_of_franklinData` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinInvolution.largestPart` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.largestPart_mem` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.le_largestPart` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.mem_of_lt_tDiag` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.one_le_tDiag` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| CONDITIONAL | `Brockian.FranklinInvolution.pentagonalNumberTheorem_of_franklinData` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinInvolution.sPart` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.sPart_le` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.sPart_mem` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinInvolution.signOf` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.signOf_ne_zero` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.signedSum_eq_fixed_of_involution` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| CONDITIONAL | `Brockian.FranklinInvolution.signedSum_eq_pentCoeff_of_franklinData` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| DEFINITION | `Brockian.FranklinInvolution.tDiag` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.tDiag_gap_exists` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
| PROVED | `Brockian.FranklinInvolution.tDiag_notMem` | ✓ | verified | lean-4.32.0 | roadmap #1 — Franklin cancellation heart proved; PST reduced to explicit involution data; AXLE @4.32 |
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
| CONDITIONAL | `Brockian.PentagonalTheoremFranklin.pentagonalNumberTheorem_of_franklin` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler PST reduced to Franklin involution; AXLE @4.32 |
| CONDITIONAL | `Brockian.PentagonalTheoremFranklin.pentagonalProduct_coeff_of_franklin` | ✓ | verified | lean-4.32.0 | roadmap harvest — Euler PST reduced to Franklin involution; AXLE @4.32 |
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
| DEFINITION | `Brockian.Weyl.SchrodingerESA.DeficiencyRepresentsODE` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| DEFINITION | `Brockian.Weyl.SchrodingerESA.Gate1ChainStatus` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| PROVED | `Brockian.Weyl.SchrodingerESA.deficiencySpace_eq_bot_of_ode_bridge` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| PROVED | `Brockian.Weyl.SchrodingerESA.dense_ranges_of_ode_bridge` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| PROVED | `Brockian.Weyl.SchrodingerESA.essSelfAdjoint_of_ode_bridge_via_chain` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| PROVED | `Brockian.Weyl.SchrodingerESA.essentiallySelfAdjoint_of_ode_bridge` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| PROVED | `Brockian.Weyl.SchrodingerESA.free_plus_primeGaussian_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| DEFINITION | `Brockian.Weyl.SchrodingerESA.gate1_chain_status` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
| PROVED | `Brockian.Weyl.SchrodingerESA.primeGaussian_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | 2026-08-01 — Gate-1 end-to-end assembly under ODE identification |
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
