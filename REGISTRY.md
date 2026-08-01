# Brockian Verified-Theorem Registry

> Generated from AXLE independent verification attestations. `register` is derived from axioms + AXLE verdict, never hand-asserted (spec §5).

> **PROVED** includes theorems closed by the kernel-checked `decide` tactic (finite `ZMod`/`Finset` checks — genuinely verified, ledger-consistent). `native_decide` (compiler-trusted, adds `Lean.ofReduceBool`) is excluded from PROVED by the axiom gate. `DEFINITION` = a supporting `def`; `CONJECTURE` = a named Prop container (never a claim).

## Summary

- **CONDITIONAL**: 4
- **CONJECTURE**: 2
- **DEFINITION**: 63
- **PROVED**: 200

## Theorems

| Register | Name | Axioms clean | AXLE | Env | Ledger |
|---|---|---|---|---|---|
| PROVED | `Brockian.Admissibility.admissibility_count_five` | ✓ | verified | lean-4.32.0 | 74 (a0ce…) / 49 / 105 (independent replications) / 119 module 2 |
| PROVED | `Brockian.Admissibility.admissibility_count_three` | ✓ | verified | lean-4.32.0 | 74 (a0ce…) / 49 / 105 (independent replications) / 119 module 2 |
| DEFINITION | `Brockian.Admissibility.admissibleResidues` | ✓ | verified | lean-4.32.0 | 74 (a0ce…) / 49 / 105 (independent replications) / 119 module 2 |
| PROVED | `Brockian.Admissibility.universal_admissibility_count` | ✓ | verified | lean-4.32.0 | 74 (a0ce…) / 49 / 105 (independent replications) / 119 module 2 |
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
| PROVED | `Brockian.Connectivity.cos_2pi_5` | ✓ | verified | lean-4.32.0 | run 88 (1d2a…) — re-proved fresh @ v4.32 via concrete Laplacian eigenvalues |
| PROVED | `Brockian.Connectivity.lambda2_eq` | ✓ | verified | lean-4.32.0 | run 88 (1d2a…) — re-proved fresh @ v4.32 via concrete Laplacian eigenvalues |
| DEFINITION | `Brockian.Connectivity.laplacianEigs5` | ✓ | verified | lean-4.32.0 | run 88 (1d2a…) — re-proved fresh @ v4.32 via concrete Laplacian eigenvalues |
| PROVED | `Brockian.Connectivity.one_div_phi` | ✓ | verified | lean-4.32.0 | run 88 (1d2a…) — re-proved fresh @ v4.32 via concrete Laplacian eigenvalues |
| PROVED | `Brockian.Connectivity.pentagon_lambda2_phi` | ✓ | verified | lean-4.32.0 | run 88 (1d2a…) — re-proved fresh @ v4.32 via concrete Laplacian eigenvalues |
| PROVED | `Brockian.Connectivity.pentagon_ratio` | ✓ | verified | lean-4.32.0 | run 88 (1d2a…) — re-proved fresh @ v4.32 via concrete Laplacian eigenvalues |
| PROVED | `Brockian.Connectivity.two_cos_4pi_5` | ✓ | verified | lean-4.32.0 | run 88 (1d2a…) — re-proved fresh @ v4.32 via concrete Laplacian eigenvalues |
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
| PROVED | `Brockian.Geometry.d5_card` | ✓ | verified | lean-4.32.0 | runs 16 / 54 / 70 / 73 — pentagon golden diagonal, two-distance, C₅ spectrum |
| PROVED | `Brockian.Geometry.golden_ratio_in_C5_spectrum` | ✓ | verified | lean-4.32.0 | runs 16 / 54 / 70 / 73 — pentagon golden diagonal, two-distance, C₅ spectrum |
| PROVED | `Brockian.Geometry.pentagon_golden_diagonal` | ✓ | verified | lean-4.32.0 | runs 16 / 54 / 70 / 73 — pentagon golden diagonal, two-distance, C₅ spectrum |
| PROVED | `Brockian.Geometry.pentagon_two_distances` | ✓ | verified | lean-4.32.0 | runs 16 / 54 / 70 / 73 — pentagon golden diagonal, two-distance, C₅ spectrum |
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
| CONJECTURE | `Brockian.Sieve.SilverGapRigidityTarget` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
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
| CONDITIONAL | `Brockian.SingularSeries.singular_series_pos` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
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
| PROVED | `Brockian.Weyl.Closure.adjoint_isClosed'` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.adjoint_isClosed'` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.closure_eq_self_of_isClosed` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.closure_eq_self_of_isClosed` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| DEFINITION | `Brockian.Weyl.Closure.deficiencySet` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| DEFINITION | `Brockian.Weyl.Closure.deficiencySet` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.inner_adjoint_left` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.inner_adjoint_left` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.isClosed_deficiencySet` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.isClosed_deficiencySet` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.mem_deficiencySet_iff_mem_deficiencySpace` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.mem_deficiencySet_iff_mem_deficiencySpace` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.smulPMap_adjoint_isClosed` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.smulPMap_adjoint_isClosed` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.smulPMap_dense` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.smulPMap_dense` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.smulPMap_isClosable` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.smulPMap_isClosable` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.symmetric_adjoint_eq` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.symmetric_adjoint_eq` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.symmetric_closure_le_adjoint` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.symmetric_closure_le_adjoint` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.symmetric_domain_le_adjoint_domain` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.symmetric_domain_le_adjoint_domain` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.symmetric_isClosable` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.symmetric_isClosable` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.symmetric_le_adjoint` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| PROVED | `Brockian.Weyl.Closure.symmetric_le_adjoint` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — closure/adjoint/deficiency (von Neumann inclusion chain) |
| DEFINITION | `Brockian.Weyl.Disk.Acoef` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| DEFINITION | `Brockian.Weyl.Disk.Pcoef` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.boundary_L2_identity` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.boundary_L2_identity` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| DEFINITION | `Brockian.Weyl.Disk.circleEq` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.circle_key` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.circle_key` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| DEFINITION | `Brockian.Weyl.Disk.diskCenter` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.green_identity_integral` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.green_identity_integral` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.integral_normSq_mono` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.integral_normSq_mono` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.lagrange_identity` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.radius_formula` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.radius_formula` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| DEFINITION | `Brockian.Weyl.Disk.sturmL` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.weyl_disk_circle` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.weyl_disk_circle` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.weyl_nested_circle` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.weyl_nested_circle` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.weyl_radius_antitone` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.weyl_radius_antitone` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| DEFINITION | `Brockian.Weyl.Disk.wronskian` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.wronskian_hasDerivAt` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.wronskian_isConst` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.Disk.wronskian_isConst` | ✓ | verified | lean-4.32.0 | Weyl campaign 2026-08-01 — finite-b nested-circle geometry (COMPLETE) |
| PROVED | `Brockian.Weyl.ESA.clm_deficiency_eq_bot` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — EssentiallySelfAdjoint genuinely inhabited |
| PROVED | `Brockian.Weyl.ESA.clm_dense` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — EssentiallySelfAdjoint genuinely inhabited |
| PROVED | `Brockian.Weyl.ESA.clm_domain` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — EssentiallySelfAdjoint genuinely inhabited |
| PROVED | `Brockian.Weyl.ESA.clm_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — EssentiallySelfAdjoint genuinely inhabited |
| PROVED | `Brockian.Weyl.ESA.clm_isSymmetric` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — EssentiallySelfAdjoint genuinely inhabited |
| PROVED | `Brockian.Weyl.ESA.id_essentiallySelfAdjoint` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — EssentiallySelfAdjoint genuinely inhabited |
| PROVED | `Brockian.Weyl.ESA.vec_eq_zero_of_inner` | ✓ | verified | lean-4.32.0 | Weyl capstone 2026-08-01 — EssentiallySelfAdjoint genuinely inhabited |
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
