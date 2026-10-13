/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.Bands.Light.PatternWords
import NLAlib.Matrix.Basic.QuadForm
/-!
# Normalized hard-core symmetrization and compression bounds

Partition of the literal shared-leg proof from sparse-Fock commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`.
The original `LightSectorConcrete` import re-exports this unchanged namespace.
Supports the `sparse-ose` moment proof.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
namespace NLAlib.SparseSketch.Light
variable {d m n ell : ℕ}

/-- The unnormalized symmetrization matrix: a block basis vector is sent to
the sum of all labelled orderings of its exact light support.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def hardCoreLift (T : Finset (Site m n)) (ell : ℕ) :
    Matrix (LabelledIndex d m n ell) (BlockIndex d T ell) ℝ :=
  fun out x ↦ ∑ pi : Equiv.Perm (Fin ell),
    coordinateDelta out (blockLabel T ell x pi)

/-- Distinct block vectors have disjoint labelled orbits, and every orbit has
exactly `permutationCount ell` elements.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem hardCoreLift_transpose_mul (T : Finset (Site m n)) (ell : ℕ) :
    (hardCoreLift (d := d) T ell).transpose * hardCoreLift T ell =
      (permutationCount ell : ℝ) •
        (1 : Matrix (BlockIndex d T ell) (BlockIndex d T ell) ℝ) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hardCoreLift]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    (∑ out, ∑ pi, ∑ sigma,
        coordinateDelta out (blockLabel T ell x pi) *
          coordinateDelta out (blockLabel T ell y sigma)) =
      ∑ pi, ∑ sigma, ∑ out,
        coordinateDelta out (blockLabel T ell x pi) *
          coordinateDelta out (blockLabel T ell y sigma) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro pi _hpi
        rw [Finset.sum_comm]
    _ = ∑ pi, ∑ sigma,
        coordinateDelta (blockLabel T ell x pi)
          (blockLabel T ell y sigma) := by
      simp_rw [sum_coordinateDelta_mul_coordinateDelta]
    _ = ((permutationCount ell : ℝ) •
        (1 : Matrix (BlockIndex d T ell) (BlockIndex d T ell) ℝ)) x y := by
      by_cases hxy : x = y
      · subst y
        simp [coordinateDelta, blockLabel_eq_iff, permutationCount]
      · simp [coordinateDelta, blockLabel_eq_iff, hxy,
          permutationCount]

/-- Four finite sums can be reordered by exchanging the first and second pairs of indices.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem sum_comm_four
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → B → C → D → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
        ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := by
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _hc
      calc
        (∑ a, ∑ b, ∑ d, f a b c d) =
            ∑ a, ∑ d, ∑ b, f a b c d := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.sum_comm]
        _ = ∑ d, ∑ a, ∑ b, f a b c d := by
          rw [Finset.sum_comm]

/-- A hard-core compression entry is the sum over its two labelled orbits.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem hardCoreLift_compression_apply
    (T : Finset (Site m n)) (ell : ℕ)
    (A : Matrix (LabelledIndex d m n ell) (LabelledIndex d m n ell) ℝ)
    (x y : BlockIndex d T ell) :
    ((hardCoreLift (d := d) T ell).transpose * A *
      hardCoreLift (d := d) T ell) x y =
      ∑ pi, ∑ sigma, A (blockLabel T ell x pi) (blockLabel T ell y sigma) := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hardCoreLift]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [sum_comm_four]
  apply Finset.sum_congr rfl
  intro pi _hpi
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  simp [coordinateDelta]

/-- The normalized hard-core symmetrization from the exact Fock block into
the distinct-site symmetric subspace of the labelled tensor space.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def hardCoreEmbedding (T : Finset (Site m n)) (ell : ℕ) :
    Matrix (LabelledIndex d m n ell) (BlockIndex d T ell) ℝ :=
  (1 / Real.sqrt (permutationCount ell : ℝ)) • hardCoreLift T ell

/-- The normalization is exact: the hard-core embedding is an isometry.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem hardCoreEmbedding_transpose_mul
    (T : Finset (Site m n)) (ell : ℕ) :
    (hardCoreEmbedding (d := d) T ell).transpose *
        hardCoreEmbedding (d := d) T ell =
      (1 : Matrix (BlockIndex d T ell) (BlockIndex d T ell) ℝ) := by
  classical
  have hNnat : 0 < permutationCount ell := permutationCount_pos ell
  have hN : (0 : ℝ) < (permutationCount ell : ℝ) := by exact_mod_cast hNnat
  have hsqrt : Real.sqrt (permutationCount ell : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hN)
  have hscalar :
      (1 / Real.sqrt (permutationCount ell : ℝ)) *
          (1 / Real.sqrt (permutationCount ell : ℝ)) *
            (permutationCount ell : ℝ) = 1 := by
    field_simp [hsqrt]
    nlinarith [Real.sq_sqrt hN.le]
  rw [hardCoreEmbedding, Matrix.transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, hardCoreLift_transpose_mul]
  rw [smul_smul, smul_smul, hscalar, one_smul]

/-- The normalized hard-core embedding preserves coordinate energy.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem hardCoreEmbedding_energy (T : Finset (Site m n)) (ell : ℕ)
    (x : BlockIndex d T ell → ℝ) :
    sumSq ((hardCoreEmbedding (d := d) T ell).mulVec x) =
      sumSq x := by
  rw [coordinateEnergy_mulVec_eq_gram,
    hardCoreEmbedding_transpose_mul]
  simp [quadForm, sumSq, Matrix.mulVec,
    dotProduct, Matrix.one_apply, pow_two]

/-- The literal normalized hard-core compression of the labelled shared-leg
matrix.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def hardCoreCompressedG (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) :
    Matrix (BlockIndex d T ell) (BlockIndex d T ell) ℝ :=
  (hardCoreEmbedding (d := d) T ell).transpose * labelledG F ell *
    hardCoreEmbedding T ell

/-- The normalized hard-core compression is symmetric.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem hardCoreCompressedG_transpose
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) :
    (hardCoreCompressedG F T ell).transpose = hardCoreCompressedG F T ell := by
  simp [hardCoreCompressedG, Matrix.transpose_mul, Matrix.mul_assoc]

/-- The normalized hard-core compression has nonnegative coordinate quadratic form.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem hardCoreCompressedG_coordinateQuadratic_nonneg
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ)
    (x : BlockIndex d T ell → ℝ) :
    0 ≤ quadForm (hardCoreCompressedG F T ell) x := by
  rw [hardCoreCompressedG, quadForm_transpose_mul_mul]
  exact labelledG_coordinateQuadratic_nonneg F ell _

/-- Sharp concrete bound on the explicitly normalized hard-core
compression.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem hardCoreCompressedG_coordinateQuadratic_le
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ)
    (x : BlockIndex d T ell → ℝ) (hell : 1 ≤ ell) :
    quadForm (hardCoreCompressedG F T ell) x ≤
      ((d : ℝ) + (ell : ℝ) - 1) * sumSq x := by
  rw [hardCoreCompressedG, quadForm_transpose_mul_mul,
    ← hardCoreEmbedding_energy T ell x]
  exact labelledG_coordinateQuadratic_le F ell _ hell

/-- The normalized hard-core compression is Hermitian.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem hardCoreCompressedG_isHermitian
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) :
    (hardCoreCompressedG F T ell).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact hardCoreCompressedG_transpose F T ell

/-- L2 operator-norm form of the sharp concrete hard-core compression bound.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem hardCoreCompressedG_norm_le
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) (hell : 1 ≤ ell) :
    ‖hardCoreCompressedG F T ell‖ ≤ (d : ℝ) + (ell : ℝ) - 1 := by
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hc : 0 ≤ (d : ℝ) + (ell : ℝ) - 1 := by linarith
  apply (specNorm_le_iff_abs_dotProduct_mulVec_le
    (hardCoreCompressedG F T ell)
    (hardCoreCompressedG_isHermitian F T ell)
    ((d : ℝ) + (ell : ℝ) - 1) hc).2
  intro x
  have hupper := hardCoreCompressedG_coordinateQuadratic_le F T ell x hell
  rw [sumSq_eq_dotProduct] at hupper
  exact (abs_of_nonneg
    (hardCoreCompressedG_coordinateQuadratic_nonneg F T ell x)).trans_le hupper

/-- The hard-core compression norm is bounded by dimension plus a dominating grade.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem hardCoreCompressedG_norm_le_grade
    (F : Frame n d) (T : Finset (Site m n)) (ell nu : ℕ)
    (hell : 1 ≤ ell) (hle : ell ≤ nu) :
    ‖hardCoreCompressedG F T ell‖ ≤ (d : ℝ) + (nu : ℝ) := by
  calc
    ‖hardCoreCompressedG F T ell‖ ≤ (d : ℝ) + (ell : ℝ) - 1 :=
      hardCoreCompressedG_norm_le F T ell hell
    _ ≤ (d : ℝ) + (nu : ℝ) := by
      have hleR : (ell : ℝ) ≤ (nu : ℝ) := by exact_mod_cast hle
      linarith

end NLAlib.SparseSketch.Light
