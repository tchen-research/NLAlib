# Local integration validation

Both complete builds, the default-import and experimental axiom audits, linters, downstream examples, focused audits, all 17 Python regression tests, layer/naming/import-surface checks, atlas and audit consistency, book coverage and site build passed. Final atlas tag repairs changed metadata only and were rebuilt and reindexed.

## Complete axiom audit

```text
audited 16247 declarations (8561 public theorems) in [NLAlib]; 23 theorems depend on sorry: [NLAlib.cgRecurrence_r_eq_zero_of_krylovGrade_le,
 NLAlib.cgRecurrence_x_eq_of_krylovGrade_le,
 NLAlib.dotProduct_cgRecurrence_p_mulVec_eq_zero,
 NLAlib.dotProduct_cgRecurrence_r_eq_zero,
 NLAlib.dotProduct_cgRecurrence_r_eq_zero_of_mem,
 NLAlib.dotProduct_golubKahan_eq,
 NLAlib.golubKahanSucceeds_iff,
 NLAlib.isCGIterate_cgRecurrence,
 NLAlib.isGradedKrylovBasis_golubKahanU_V,
 NLAlib.isGradedKrylovBasis_lanczosRecurrence,
 NLAlib.lanczosAlpha_eq_alpha,
 NLAlib.lanczosBeta_eq_beta,
 NLAlib.lanczosBeta_eq_zero_iff,
 NLAlib.lanczosBeta_eq_zero_of_krylovGrade_le,
 NLAlib.lanczosBeta_pos,
 NLAlib.lanczosBeta_succ_eq_dotProduct,
 NLAlib.lanczosRecurrence_eq_arnoldiBasis,
 NLAlib.lanczosRecurrence_eq_zero_of_krylovGrade_le,
 NLAlib.partialCholeskyFactor_mul_transpose_eq_nystrom,
 NLAlib.partialCholeskyResidual_eq_sub_nystrom,
 NLAlib.range_qrAlgorithmQ_castLE_eq_subspaceIterate,
 NLAlib.span_cgRecurrence_p,
 NLAlib.span_cgRecurrence_r]
OK: no axioms beyond propext / Classical.choice / Quot.sound (and sorryAx in scaffolds)
```

## Default-import axiom audit

```text
audited 15956 declarations reachable through import NLAlib
```

## Source and whole-library audit traceability

```text
Source ledger: 30/30 active mathematical scopes complete, 1 deferred; 372 checked, sorry-free theorem anchors.
354/354 cards reviewed in 361 traceable records; 6 overbroad proof-status claims reopened.
```

## Atlas consistency

```text
experimental proof inventory: 23 sorry-dependent declarations indexed and excluded from the default import
atlas OK: 354 results, 17129 declarations scanned; atlas in sync
```

