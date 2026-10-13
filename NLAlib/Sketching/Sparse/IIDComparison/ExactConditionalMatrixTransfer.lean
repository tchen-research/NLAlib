/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.IIDComparison.ExactIIDMatrixError
set_option autoImplicit false

/-!
# Exact-s conditional matrix transfer

Product conditional kernels, their true mixture law, and matrix barycenter transfer.
Ported from `SparseFockFormal.UniformExactSTransfer` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators InnerProductSpace Matrix

namespace NLAlib.SparseSketch.UniformSparse

noncomputable section

variable {b s n d : ℕ}

/-! ## Column-first iid presentation and exact reindexing -/

/-- Given the exact columns, the coupled iid columns are conditionally
independent.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def conditionalSampleLaw (hb : 0 < b) (hs : 0 < s)
    (X : UniformSparseSample (s * b) s n) : FiniteLaw (IidColumnSample b s n) :=
  FiniteLaw.independentProduct (fun i => UniformSparse.conditionalYLaw hb hs (X i))

/-- The iid sample law conditional on an exact sample is the product of conditional column weights.
Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem conditionalSampleLaw_weight (hb : 0 < b) (hs : 0 < s)
    (X : UniformSparseSample (s * b) s n) (Y : IidColumnSample b s n) :
    (conditionalSampleLaw hb hs X).weight Y =
      ∏ i, (UniformSparse.conditionalYLaw hb hs (X i)).weight (Y i) := rfl

/-- First draw independent uniform exact-`s` columns and then their
conditionally independent iid partners.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def conditionalSampleMixtureLaw (hb : 0 < b) (hs : 0 < s) :
    FiniteLaw (IidColumnSample b s n) where
  weight Y := ∑ X,
    (uniformSparseSampleLaw (n := n) (le_rows (s := s) hb)).weight X *
      (conditionalSampleLaw hb hs X).weight Y
  weight_nonneg Y := Finset.sum_nonneg fun X _ =>
    mul_nonneg
      ((uniformSparseSampleLaw (n := n) (le_rows (s := s) hb)).weight_nonneg X)
      ((conditionalSampleLaw hb hs X).weight_nonneg Y)
  sum_weight := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (conditionalSampleLaw hb hs _).sum_weight,
      mul_one]
    exact (uniformSparseSampleLaw (n := n) (le_rows (s := s) hb)).sum_weight

/-- The conditional iid sample mixture has its explicit exact-sample weighted mass.
Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem conditionalSampleMixtureLaw_weight
    (hb : 0 < b) (hs : 0 < s) (Y : IidColumnSample b s n) :
    (conditionalSampleMixtureLaw (n := n) hb hs).weight Y =
      ∑ X, (uniformSparseSampleLaw (n := n) (le_rows (s := s) hb)).weight X *
        (conditionalSampleLaw hb hs X).weight Y := rfl

/-- The independent-column conditional mixture is pointwise exactly the iid
column law.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditionalSampleMixtureLaw_weight_eq_iidColumnSampleLaw_weight
    (hb : 0 < b) (hs : 0 < s) (Y : IidColumnSample b s n) :
    (conditionalSampleMixtureLaw (n := n) hb hs).weight Y =
      (iidColumnSampleLaw hb s n).weight Y := by
  simp only [conditionalSampleMixtureLaw_weight,
    uniformSparseSampleLaw, FiniteLaw.independentProduct_weight,
    conditionalSampleLaw_weight, iidColumnSampleLaw_weight]
  simp_rw [← Finset.prod_mul_distrib]
  calc
    (∑ X : UniformSparseSample (s * b) s n,
        ∏ i : Fin n,
          (uniformSparseColumnLaw (le_rows (s := s) hb)).weight (X i) *
            (UniformSparse.conditionalYLaw hb hs (X i)).weight (Y i)) =
        ∏ i : Fin n, ∑ x : UniformSparseColumn (s * b) s,
          (uniformSparseColumnLaw (le_rows (s := s) hb)).weight x *
            (UniformSparse.conditionalYLaw hb hs x).weight (Y i) := by
      exact (Fintype.prod_sum (fun i (x : UniformSparseColumn (s * b) s) =>
        (uniformSparseColumnLaw (le_rows (s := s) hb)).weight x *
          (UniformSparse.conditionalYLaw hb hs x).weight (Y i))).symm
    _ = ∏ i : Fin n, (nestedYLaw hb s).weight (Y i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact conditionalYLaw_mixture hb hs (Y i)

/-- Expectation under the mixture is iterated expectation over exact columns
and then their conditional iid partners.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditionalSampleMixtureLaw_expect_eq_iterated
    (hb : 0 < b) (hs : 0 < s) (f : IidColumnSample b s n → ℝ) :
    (conditionalSampleMixtureLaw (n := n) hb hs).expect f =
      (uniformSparseSampleLaw (n := n) (le_rows (s := s) hb)).expect
        (fun X => (conditionalSampleLaw hb hs X).expect f) := by
  simp only [FiniteLaw.expect, conditionalSampleMixtureLaw_weight]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro X _
  apply Finset.sum_congr rfl
  intro Y _
  ring

/-- Every observable has its iid expectation under the explicit conditional
mixture.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditionalSampleMixtureLaw_expect_eq_iidColumnSampleLaw_expect
    (hb : 0 < b) (hs : 0 < s) (f : IidColumnSample b s n → ℝ) :
    (conditionalSampleMixtureLaw (n := n) hb hs).expect f =
      (iidColumnSampleLaw hb s n).expect f := by
  rw [FiniteLaw.expect, FiniteLaw.expect]
  apply Finset.sum_congr rfl
  intro Y _
  rw [conditionalSampleMixtureLaw_weight_eq_iidColumnSampleLaw_weight hb hs Y]

/-! ## Conditional matrix barycenter -/

/-- At two distinct columns, conditional independence and the one-column
barycenter identity recover the exact blockwise cross inner product.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditional_cross_inner_block
    (hb : 0 < b) (hs : 0 < s) (X : UniformSparseSample (s * b) s n)
    {i j : Fin n} (hij : i ≠ j) (g : Fin s) :
    (conditionalSampleLaw hb hs X).expect (fun Y =>
      exactScale (s := s) hb ^ 2 *
        inner ℝ (unscaledYVector (Y i g)) (unscaledYVector (Y j g))) =
      ∑ a : Fin b,
        UniformSparseColumn.value (X i) (finProdFinEquiv (g, a)) *
          UniformSparseColumn.value (X j) (finProdFinEquiv (g, a)) := by
  let scale := exactScale (s := s) hb
  calc
    (conditionalSampleLaw hb hs X).expect (fun Y =>
        scale ^ 2 *
          inner ℝ (unscaledYVector (Y i g)) (unscaledYVector (Y j g))) =
        (conditionalSampleLaw hb hs X).expect (fun Y =>
          ∑ a : Fin b,
            (scale * flatYValue (Y i) (finProdFinEquiv (g, a))) *
              (scale * flatYValue (Y j) (finProdFinEquiv (g, a)))) := by
      apply (conditionalSampleLaw hb hs X).expect_congr
      intro Y
      simp only [PiLp.inner_apply, Real.inner_apply,
        unscaledYVector_apply, flatYValue, flatOutcome_pair]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      dsimp [scale]
      ring
    _ = ∑ a : Fin b,
        (conditionalSampleLaw hb hs X).expect (fun Y =>
          (scale * flatYValue (Y i) (finProdFinEquiv (g, a))) *
            (scale * flatYValue (Y j) (finProdFinEquiv (g, a)))) := by
      exact FiniteLaw.expect_sum (conditionalSampleLaw hb hs X) _
    _ = ∑ a : Fin b,
        (UniformSparse.conditionalYLaw hb hs (X i)).expect (fun y =>
          scale * flatYValue y (finProdFinEquiv (g, a))) *
        (UniformSparse.conditionalYLaw hb hs (X j)).expect (fun y =>
          scale * flatYValue y (finProdFinEquiv (g, a))) := by
      apply Finset.sum_congr rfl
      intro a _
      exact expect_two_coordinates
        (mu := fun k : Fin n => UniformSparse.conditionalYLaw hb hs (X k)) hij
        (fun y => scale * flatYValue y (finProdFinEquiv (g, a)))
        (fun y => scale * flatYValue y (finProdFinEquiv (g, a)))
    _ = ∑ a : Fin b,
        UniformSparseColumn.value (X i) (finProdFinEquiv (g, a)) *
          UniformSparseColumn.value (X j) (finProdFinEquiv (g, a)) := by
      apply Finset.sum_congr rfl
      intro a _
      dsimp [scale]
      rw [conditional_scaled_barycenter_coordinate hb hs,
        conditional_scaled_barycenter_coordinate hb hs]

/-- The conditional entrywise matrix expectation of the scaled iid error is
the grouped exact hollow error.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditional_matrix_transfer
    (hb : 0 < b) (hs : 0 < s) (F : Frame n d)
    (X : UniformSparseSample (s * b) s n) :
    FiniteLaw.barycenter (conditionalSampleLaw hb hs X)
        (exactScaledIIDError hb F) = groupedExactError F X := by
  ext a c
  simp only [FiniteLaw.barycenter_apply, groupedExactError]
  simp_rw [exactScaledIIDError_apply_grouped hb F]
  rw [FiniteLaw.expect_smul]
  congr 1
  rw [FiniteLaw.expect_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [FiniteLaw.expect_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [FiniteLaw.expect_mul_const]
  rw [FiniteLaw.expect_mul_const]
  rw [FiniteLaw.expect_sum]
  apply congrArg (fun z : ℝ => z * F.u i a * F.u j c)
  apply Finset.sum_congr rfl
  intro g _
  exact conditional_cross_inner_block hb hs X
    (Ne.symm (Finset.mem_erase.mp hj).1) g

/-- Therefore the scaled iid conditional barycenter is the actual exact-`s`
Gram error, using pointwise hollowness of the exact-s sketch.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditional_matrix_transfer_gramError
    (hb : 0 < b) (hs : 0 < s) (F : Frame n d)
    (X : UniformSparseSample (s * b) s n) :
    FiniteLaw.barycenter (conditionalSampleLaw hb hs X)
        (exactScaledIIDError hb F) = gramError F (uniformSparseMatrix X) := by
  rw [UniformSparse.conditional_matrix_transfer hb hs F X,
    groupedExactError_eq_hollow F X, UniformSparse.gramError_eq_hollow F X hs]

/-! ## Symmetric-matrix wrappers for Jensen -/

end

end NLAlib.SparseSketch.UniformSparse
