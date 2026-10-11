/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.ExactConditionalMatrixTransfer

set_option autoImplicit false

/-!
# Exact-s convex and trace-moment transfer

Conditional barycenters imply convex order and the exact even trace-moment comparison.
Ported from `SparseFockFormal.UniformExactSTransfer` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators InnerProductSpace Matrix

namespace NLAlib.SparseFock.UniformExactS

open ParsevalFrame SparseIIDCoupling SparseIIDTransfer
open SparseIIDUnconditional ProductFock VacuumMoment

noncomputable section

variable {b s n d : ℕ}

/-! ## Column-first iid presentation and exact reindexing -/

/-- The actual exact-`s` Gram error as an element of the real vector space of
symmetric matrices.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def exactSymmetricError (F : Frame n d) (X : ExactSample (s * b) s n) :
    SymmetricMatrix d :=
  ⟨gramError F X,
    Matrix.isHermitian_iff_isSymm.mp (gramError_isHermitian F X)⟩

/-- The scaled iid comparison error in the same vector space.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def exactScaledIIDSymmetricError (hb : 0 < b) (F : Frame n d)
    (Y : IidColumnSample b s n) : SymmetricMatrix d :=
  ⟨exactScaledIIDError hb F Y, exactScaledIIDError_symmetric hb F Y⟩

/-- The subtype barycenter is the entrywise matrix expectation.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem coe_barycenter_exactScaledIID
    (hb : 0 < b) (hs : 0 < s) (F : Frame n d)
    (X : ExactSample (s * b) s n) :
    ((barycenter (conditionalSampleLaw hb hs X)
        (exactScaledIIDSymmetricError hb F) : SymmetricMatrix d) :
      Matrix (Fin d) (Fin d) ℝ) =
      matrixExpectation (conditionalSampleLaw hb hs X)
        (exactScaledIIDError hb F) := by
  ext a c
  simp only [barycenter, matrixExpectation, Submodule.coe_sum,
    Submodule.coe_smul_of_tower, Matrix.sum_apply, Matrix.smul_apply,
    exactScaledIIDSymmetricError, FiniteLaw.expect, smul_eq_mul]

/-- The conditional symmetric-matrix barycenter is the actual exact-`s`
error.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem barycenter_exactScaledIID_eq_exact
    (hb : 0 < b) (hs : 0 < s) (F : Frame n d)
    (X : ExactSample (s * b) s n) :
    barycenter (conditionalSampleLaw hb hs X)
        (exactScaledIIDSymmetricError hb F) = exactSymmetricError F X := by
  apply Subtype.ext
  rw [coe_barycenter_exactScaledIID hb hs F X]
  exact conditional_matrix_transfer_gramError hb hs F X

/-- Pointwise conditional Jensen on the genuine vector space of symmetric
matrices.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditional_convex_order
    (hb : 0 < b) (hs : 0 < s) (F : Frame n d)
    (X : ExactSample (s * b) s n)
    (Phi : SymmetricMatrix d → ℝ) (hPhi : ConvexOn ℝ Set.univ Phi) :
    Phi (exactSymmetricError F X) ≤
      (conditionalSampleLaw hb hs X).expect
        (fun Y => Phi (exactScaledIIDSymmetricError hb F Y)) := by
  rw [← barycenter_exactScaledIID_eq_exact hb hs F X]
  exact finite_jensen (conditionalSampleLaw hb hs X)
    (exactScaledIIDSymmetricError hb F) Phi hPhi

/-- Unconditional convex order from independent uniform signed exact-`s`
columns to independent iid ternary columns.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem unconditional_convex_order
    (hb : 0 < b) (hs : 0 < s) (F : Frame n d)
    (Phi : SymmetricMatrix d → ℝ) (hPhi : ConvexOn ℝ Set.univ Phi) :
    (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).expect
        (fun X => Phi (exactSymmetricError F X)) ≤
      (iidColumnSampleLaw hb s n).expect
        (fun Y => Phi (exactScaledIIDSymmetricError hb F Y)) := by
  calc
    (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).expect
        (fun X => Phi (exactSymmetricError F X)) ≤
        (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).expect
          (fun X => (conditionalSampleLaw hb hs X).expect
            (fun Y => Phi (exactScaledIIDSymmetricError hb F Y))) := by
      apply FiniteLaw.expect_mono
      intro X
      exact conditional_convex_order hb hs F X Phi hPhi
    _ = (conditionalSampleMixtureLaw (n := n) hb hs).expect
        (fun Y => Phi (exactScaledIIDSymmetricError hb F Y)) :=
      (conditionalSampleMixtureLaw_expect_eq_iterated hb hs
        (fun Y => Phi (exactScaledIIDSymmetricError hb F Y))).symm
    _ = (iidColumnSampleLaw hb s n).expect
        (fun Y => Phi (exactScaledIIDSymmetricError hb F Y)) :=
      conditionalSampleMixtureLaw_expect_eq_iidColumnSampleLaw_expect
        hb hs (fun Y => Phi (exactScaledIIDSymmetricError hb F Y))

/-! ## Exact trace-moment bridge to the finite-Fock iid law -/

/-- Scaling both iid columns by `exactScale` contributes
`exactScale^(4q)` to the `2q` trace power.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem exactScaledIIDError_trace_even (hb : 0 < b) (F : Frame n d)
    (Y : IidColumnSample b s n) (q : ℕ) :
    ((exactScaledIIDError hb F Y) ^ (2 * q)).trace =
      exactScale (s := s) hb ^ (4 * q) *
        ((iidVectorError F (toYArray Y)) ^ (2 * q)).trace := by
  rw [exactScaledIIDError_eq_smul, MomentTransfer.trace_pow_smul]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

/-- The unscaled column-first iid trace moment is exactly the existing
product-Fock trace moment.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem iidColumn_trace_moment_eq_product
    (hs : 0 < s) (hb : 1 < b) (F : Frame n d) (q : ℕ) :
    (iidColumnSampleLaw (lt_trans Nat.zero_lt_one hb) s n).expect
        (fun Y => ((iidVectorError F (toYArray Y)) ^ (2 * q)).trace) =
      (iidLaw b hb (s * b) n).expect
        (fun omega => ((iidGramError b F omega) ^ (2 * q)).trace) := by
  calc
    (iidColumnSampleLaw (lt_trans Nat.zero_lt_one hb) s n).expect
        (fun Y => ((iidVectorError F (toYArray Y)) ^ (2 * q)).trace) =
        (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
          (fun y => ((iidVectorError F y) ^ (2 * q)).trace) :=
      iidColumnSampleLaw_expect_toYArray_eq_iidArrayLaw_expect
        (lt_trans Nat.zero_lt_one hb)
        (fun y => ((iidVectorError F y) ^ (2 * q)).trace)
    _ = (iidLaw b hb (s * b) n).expect
        (fun omega => ((iidGramError b F omega) ^ (2 * q)).trace) :=
      MomentTransfer.iid_trace_moment_eq_product hs hb F q

/-- The scaled iid trace moment is exactly the product-Fock moment times the
genuine fill/thin coefficient.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem exactScaledIID_trace_moment_eq_product
    (hs : 0 < s) (hb : 1 < b) (F : Frame n d) (q : ℕ) :
    (iidColumnSampleLaw (lt_trans Nat.zero_lt_one hb) s n).expect
        (fun Y => ((exactScaledIIDError (lt_trans Nat.zero_lt_one hb) F Y) ^
          (2 * q)).trace) =
      exactScale (s := s) (lt_trans Nat.zero_lt_one hb) ^ (4 * q) *
        (iidLaw b hb (s * b) n).expect
          (fun omega => ((iidGramError b F omega) ^ (2 * q)).trace) := by
  calc
    (iidColumnSampleLaw (lt_trans Nat.zero_lt_one hb) s n).expect
        (fun Y => ((exactScaledIIDError (lt_trans Nat.zero_lt_one hb) F Y) ^
          (2 * q)).trace) =
        (iidColumnSampleLaw (lt_trans Nat.zero_lt_one hb) s n).expect
          (fun Y => exactScale (s := s) (lt_trans Nat.zero_lt_one hb) ^
            (4 * q) * ((iidVectorError F (toYArray Y)) ^ (2 * q)).trace) := by
      apply (iidColumnSampleLaw (lt_trans Nat.zero_lt_one hb) s n).expect_congr
      intro Y
      exact exactScaledIIDError_trace_even
        (lt_trans Nat.zero_lt_one hb) F Y q
    _ = exactScale (s := s) (lt_trans Nat.zero_lt_one hb) ^ (4 * q) *
        (iidColumnSampleLaw (lt_trans Nat.zero_lt_one hb) s n).expect
          (fun Y => ((iidVectorError F (toYArray Y)) ^ (2 * q)).trace) := by
      exact FiniteLaw.expect_smul _ _ _
    _ = exactScale (s := s) (lt_trans Nat.zero_lt_one hb) ^ (4 * q) *
        (iidLaw b hb (s * b) n).expect
          (fun omega => ((iidGramError b F omega) ^ (2 * q)).trace) := by
      rw [iidColumn_trace_moment_eq_product hs hb F q]

/-- Convexity of the even trace power instantiates the unconditional exact-s
convex order.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem unconditional_trace_moment_order
    (hb : 0 < b) (hs : 0 < s) (F : Frame n d) (q : ℕ) :
    (exactSampleLaw (n := n) (exactS_le_rows (s := s) hb)).expect
        (fun X => ((gramError F X) ^ (2 * q)).trace) ≤
      (iidColumnSampleLaw hb s n).expect
        (fun Y => ((exactScaledIIDError hb F Y) ^ (2 * q)).trace) := by
  simpa [TracePowerConvexity.traceEvenPower, exactSymmetricError,
    exactScaledIIDSymmetricError] using
      (unconditional_convex_order hb hs F
        (TracePowerConvexity.traceEvenPower (d := d) q)
        (TracePowerConvexity.convexOn_traceEvenPower d q))

/-- Distribution-level exact-s trace-moment bridge to the product-Fock iid
law.  The premise is only `s>0`, `b>1`; all laws and independence are explicit.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem exactS_trace_moment_le_scaled_product
    (hs : 0 < s) (hb : 1 < b) (F : Frame n d) (q : ℕ) :
    (exactSampleLaw (n := n)
        (exactS_le_rows (s := s) (lt_trans Nat.zero_lt_one hb))).expect
        (fun X => ((gramError F X) ^ (2 * q)).trace) ≤
      exactScale (s := s) (lt_trans Nat.zero_lt_one hb) ^ (4 * q) *
        (iidLaw b hb (s * b) n).expect
          (fun omega => ((iidGramError b F omega) ^ (2 * q)).trace) := by
  calc
    _ ≤ (iidColumnSampleLaw (lt_trans Nat.zero_lt_one hb) s n).expect
        (fun Y => ((exactScaledIIDError (lt_trans Nat.zero_lt_one hb) F Y) ^
          (2 * q)).trace) :=
      unconditional_trace_moment_order
        (lt_trans Nat.zero_lt_one hb) hs F q
    _ = _ := exactScaledIID_trace_moment_eq_product hs hb F q

end

end NLAlib.SparseFock.UniformExactS
