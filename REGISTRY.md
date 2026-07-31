# Brockian Verified-Theorem Registry

> Generated from AXLE independent verification attestations. `register` is derived from axioms + AXLE verdict, never hand-asserted (spec §5).

> **PROVED** includes theorems closed by the kernel-checked `decide` tactic (finite `ZMod`/`Finset` checks — genuinely verified, ledger-consistent). `native_decide` (compiler-trusted, adds `Lean.ofReduceBool`) is excluded from PROVED by the axiom gate. `DEFINITION` = a supporting `def`; `CONJECTURE` = a named Prop container (never a claim).

## Summary

- **CONDITIONAL**: 1
- **CONJECTURE**: 1
- **DEFINITION**: 14
- **PROVED**: 84

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
| PROVED | `Brockian.Core.binet_formula` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.cos_2pi_5` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.cos_pi_div_five_eq_phi_div_two` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.each_ray_has_infinitely_many_primes` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.fib_five_dvd` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.fifth_root_of_unity` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
| PROVED | `Brockian.Core.one_lt_phi` | ✓ | verified | lean-4.32.0 | runs 97 / 103 / 112 (consolidation anchors) — φ stack, ray ring, Dirichlet-on-rays |
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
| PROVED | `Brockian.Sieve.H3_det` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.H3_ground` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.H3_middle` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.H3_top` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.H3_trace` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.compatible_closure` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.no_adjacent_admissible` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.run3_signature` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.run_cap` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.silver_gap_rigidity_finite` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.tau_injective_on_period` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.tau_minimal_period` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.tau_period` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.twin_admissible_card` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.Sieve.twin_pins_mod_three` | ✓ | verified | lean-4.32.0 | intake 18 (dd6a6bd3 / bdfa6014) — silver eigensystem, no-go, run-cap, torus |
| PROVED | `Brockian.SingularSeries.localFactorAt_eq` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.localFactorAt_of_not_prime` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.localFactorAt_pos` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.local_factor_asymptotic` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.local_factor_denom_ne_zero` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.local_factor_of_nu_p_eq_p` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.local_factor_of_nu_p_eq_zero` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.local_factor_pos` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.nu_p_eq_image_card` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.nu_p_lt_p_of_admissible` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.SingularSeries.singular_series_finite_pos` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| CONDITIONAL | `Brockian.SingularSeries.singular_series_pos` | ✓ | verified | lean-4.32.0 | intake run 63 (a0ce…) — largest clean analytic run; singular series |
| PROVED | `Brockian.Spectral.cos_two_pi_div_five` | ✓ | verified | lean-4.32.0 | run 73 (b666…) — re-proved fresh @ v4.32 via concrete circulant eigenvalues |
| DEFINITION | `Brockian.Spectral.cycleSpectrum` | ✓ | verified | lean-4.32.0 | run 73 (b666…) — re-proved fresh @ v4.32 via concrete circulant eigenvalues |
| PROVED | `Brockian.Spectral.golden_in_cycleSpectrum_five` | ✓ | verified | lean-4.32.0 | run 73 (b666…) — re-proved fresh @ v4.32 via concrete circulant eigenvalues |
| PROVED | `Brockian.Spectral.golden_sub_one_eq_two_cos` | ✓ | verified | lean-4.32.0 | run 73 (b666…) — re-proved fresh @ v4.32 via concrete circulant eigenvalues |
| PROVED | `Brockian.Spectral.golden_unique_to_five` | ✓ | verified | lean-4.32.0 | run 73 (b666…) — re-proved fresh @ v4.32 via concrete circulant eigenvalues |
| PROVED | `Brockian.Spectral.neg_golden_in_C5_spectrum` | ✓ | verified | lean-4.32.0 | run 73 (b666…) — re-proved fresh @ v4.32 via concrete circulant eigenvalues |
| PROVED | `Brockian.Spectral.two_cos_four_pi_div_five` | ✓ | verified | lean-4.32.0 | run 73 (b666…) — re-proved fresh @ v4.32 via concrete circulant eigenvalues |
| DEFINITION | `Brockian.TransitionKernel.admissibleStarts` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.brockian_table_card` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.cousin_pins_mod_three` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.cousin_run_cap` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.forbidden_transition` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.gap10_run_cap` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| DEFINITION | `Brockian.TransitionKernel.kernel` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.kernel_row_sum` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.mem_admissibleStarts` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.quadruplet_pins_mod_five` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.sexy_free_mod_three` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.sexy_run_cap` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.totalSum_count` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.totalSum_eq` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.twin_admissible_singleton` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.twin_pins_mod_three` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
| PROVED | `Brockian.TransitionKernel.twin_table_card` | ✓ | verified | lean-4.32.0 | runs 7 / 31 / 117 — kernel double-count, constellation classification, twin exclusion |
