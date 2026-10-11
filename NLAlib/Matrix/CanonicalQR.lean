import NLAlib.Matrix.Stiefel
import NLAlib.Matrix.Spectral
import NLAlib.ForMathlib.Analysis.InnerProductSpace.GramSchmidt
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Canonical positive-diagonal thin QR

The frame is the normalized Gram–Schmidt map on full-column-rank arrays,
with the coordinate frame on the rank-deficient set. This gives an actual
Borel map into Stiefel space. Source: operator re-derivation `sh:gaussian-qr`.
Supports atlas `haar-orthogonal`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator
open scoped Classical
namespace NLAlib

/-- The Euclidean columns of an array, with the standard matrix column order.
Source: operator re-derivation `sh:qr-equiv`. -/
def qrColumnFamily {n k : ℕ} (A : Fin n → Fin k → ℝ) :
    Fin k → EuclideanSpace ℝ (Fin n) := fun j => WithLp.toLp 2 (fun i => A i j)

/-- The literal positive normalized Gram–Schmidt array.
Source: operator re-derivation `sh:qr-equiv`; zero residuals are totalized to zero. -/
def qrNormalizedArray {n k : ℕ} (A : Fin n → Fin k → ℝ) : Fin n → Fin k → ℝ :=
  fun i j => gramSchmidtNormed ℝ (qrColumnFamily A) j i

/-- Full-column-rank normalized Gram–Schmidt has orthonormal columns.
Source: operator re-derivation `sh:gaussian-qr`. -/
theorem hasOrthonormalCols_qrNormalizedArray {n k : ℕ} (A : Fin n → Fin k → ℝ)
    (hA : LinearIndependent ℝ (qrColumnFamily A)) :
    HasOrthonormalCols (Matrix.of (qrNormalizedArray A)) := by
  have ho := orthonormal_iff_ite.mp (gramSchmidtNormed_orthonormal hA)
  ext a b
  have hh := ho b a
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply,
    qrNormalizedArray, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, eq_comm] using hh

/-- The actual canonical QR frame, using the coordinate frame on the
rank-deficient set. On full rank its diagonal normalizations are positive.
Source: operator re-derivation `sh:gaussian-qr`. -/
def canonicalQRFrame (n k : ℕ) (hkn : k ≤ n) (A : Fin n → Fin k → ℝ) : Stiefel n k :=
  if hA : LinearIndependent ℝ (qrColumnFamily A) then
    ⟨qrNormalizedArray A, hasOrthonormalCols_qrNormalizedArray A hA⟩
  else coordinateStiefel n k hkn

/-- The canonical frame is literal normalized Gram–Schmidt on full rank.
Source: operator re-derivation `sh:gaussian-qr`. -/
theorem canonicalQRFrame_val_of_linearIndependent {n k : ℕ} (hkn : k ≤ n)
    (A : Fin n → Fin k → ℝ) (hA : LinearIndependent ℝ (qrColumnFamily A)) :
    (canonicalQRFrame n k hkn A).val = qrNormalizedArray A := by
  simp only [canonicalQRFrame, dif_pos hA]

/-- The Euclidean column Gram matrix is the ordinary matrix Gram matrix.
Source: operator re-derivation `sh:gaussian-qr`. -/
theorem gram_qrColumnFamily {n k : ℕ} (A : Fin n → Fin k → ℝ) :
    Matrix.gram ℝ (qrColumnFamily A) = (Matrix.of A)ᵀ * Matrix.of A := by
  ext a b
  simp only [Matrix.gram_apply, qrColumnFamily, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, mul_comm]

/-- The full-column-rank set is open, since its Gram determinant is nonzero.
Source: operator re-derivation `sh:gaussian-qr`. -/
theorem isOpen_linearIndependent_qrColumnFamily (n k : ℕ) :
    IsOpen {A : Fin n → Fin k → ℝ | LinearIndependent ℝ (qrColumnFamily A)} := by
  have hcont : Continuous (fun A : Fin n → Fin k → ℝ =>
      ((Matrix.of A)ᵀ * Matrix.of A).det) := by
    simp only [Matrix.det_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    fun_prop
  have heq : {A : Fin n → Fin k → ℝ | LinearIndependent ℝ (qrColumnFamily A)} =
      {A | ((Matrix.of A)ᵀ * Matrix.of A).det ≠ 0} := by
    ext A
    simp only [Set.mem_ofPred_eq]
    rw [← Matrix.det_gram_ne_zero_iff_linearIndependent, gram_qrColumnFamily]
  rw [heq]
  exact (isClosed_eq hcont continuous_const).isOpen_compl

/-- The literal normalized Gram–Schmidt array is measurable everywhere,
including rank-deficient inputs. Source: operator re-derivation `sh:gaussian-qr`. -/
theorem measurable_qrNormalizedArray (n k : ℕ) :
    Measurable (qrNormalizedArray (n := n) (k := k)) := by
  have hc : ∀ j : Fin k, Measurable (fun A : Fin n → Fin k → ℝ => qrColumnFamily A j) := by
    intro j
    dsimp only [qrColumnFamily]
    fun_prop
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.measurable.comp
    (measurable_gramSchmidtNormed qrColumnFamily hc j)

/-- The canonical QR frame is an actual measurable Stiefel-valued map, with
its rank-deficient fallback explicitly specified.
Source: operator re-derivation `sh:gaussian-qr`. -/
theorem measurable_canonicalQRFrame (n k : ℕ) (hkn : k ≤ n) :
    Measurable (canonicalQRFrame n k hkn) := by
  apply Measurable.subtype_mk
  change Measurable (fun A => (canonicalQRFrame n k hkn A).val)
  have heq : (fun A => (canonicalQRFrame n k hkn A).val) =
      (fun A => if LinearIndependent ℝ (qrColumnFamily A) then qrNormalizedArray A
        else (coordinateStiefel n k hkn).val) := by
    funext A
    unfold canonicalQRFrame
    split_ifs <;> rfl
  rw [heq]
  exact Measurable.ite (isOpen_linearIndependent_qrColumnFamily n k).measurableSet
    (measurable_qrNormalizedArray n k) measurable_const

/-- The upper factor consists of inner products between canonical frame
columns and original columns. Source: operator re-derivation `sh:qr-equiv`. -/
def canonicalQRUpper {n k : ℕ} (hkn : k ≤ n) (A : Fin n → Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ := fun i j =>
  inner ℝ (qrColumnFamily (canonicalQRFrame n k hkn A).val i) (qrColumnFamily A j)

/-- The canonical upper factor has zero entries strictly below its diagonal
on full-column-rank inputs. Source: operator re-derivation `sh:qr-equiv`. -/
theorem canonicalQRUpper_apply_eq_zero_of_lt {n k : ℕ} (hkn : k ≤ n)
    (A : Fin n → Fin k → ℝ) (hA : LinearIndependent ℝ (qrColumnFamily A))
    {i j : Fin k} (hij : j < i) : canonicalQRUpper hkn A i j = 0 := by
  change inner ℝ (qrColumnFamily (canonicalQRFrame n k hkn A).val i) (qrColumnFamily A j) = 0
  rw [canonicalQRFrame_val_of_linearIndependent hkn A hA]
  exact inner_gramSchmidtNormed_eq_zero_of_lt (qrColumnFamily A) hij

/-- Every canonical QR diagonal entry is the strictly positive residual norm
on full-column-rank inputs. Source: operator re-derivation `sh:qr-equiv`. -/
theorem canonicalQRUpper_apply_self_pos {n k : ℕ} (hkn : k ≤ n)
    (A : Fin n → Fin k → ℝ) (hA : LinearIndependent ℝ (qrColumnFamily A)) (i : Fin k) :
    0 < canonicalQRUpper hkn A i i := by
  change 0 < inner ℝ (qrColumnFamily (canonicalQRFrame n k hkn A).val i) (qrColumnFamily A i)
  rw [canonicalQRFrame_val_of_linearIndependent hkn A hA]
  change 0 < inner ℝ (gramSchmidtNormed ℝ (qrColumnFamily A) i) (qrColumnFamily A i)
  rw [inner_gramSchmidtNormed_self_eq_norm_gramSchmidt]
  exact norm_pos_iff.mpr (gramSchmidt_ne_zero i hA)

/-- An actual real orthogonal matrix defines a Euclidean linear isometry.
Source: operator re-derivation `sh:qr-equiv`. -/
def orthogonalToEuclideanIsometry {n : ℕ} (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) where
  toLinearMap := Matrix.toEuclideanLin O.val
  norm_map' x := by
    rw [norm_eq_sqrt_dotProduct, norm_eq_sqrt_dotProduct]
    change Real.sqrt ((O.val *ᵥ x.ofLp) ⬝ᵥ (O.val *ᵥ x.ofLp)) = Real.sqrt (x.ofLp ⬝ᵥ x.ofLp)
    rw [mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols
      (transpose_mul_self_orthogonalGroup O)]

/-- Orthogonal left multiplication carries each input column through its
Euclidean isometry. Source: operator re-derivation `sh:qr-equiv`. -/
theorem qrColumnFamily_orthogonal_mul {n k : ℕ}
    (O : Matrix.orthogonalGroup (Fin n) ℝ) (A : Fin n → Fin k → ℝ) :
    qrColumnFamily (Matrix.of.symm (O.val * Matrix.of A)) =
      fun j => orthogonalToEuclideanIsometry O (qrColumnFamily A j) := by
  rfl

/-- The canonical positive normalized Gram–Schmidt array is equivariant
under orthogonal multiplication, including zero residuals.
Source: operator re-derivation `sh:qr-equiv`. -/
theorem qrNormalizedArray_orthogonal_mul {n k : ℕ}
    (O : Matrix.orthogonalGroup (Fin n) ℝ) (A : Fin n → Fin k → ℝ) :
    qrNormalizedArray (Matrix.of.symm (O.val * Matrix.of A)) =
      Matrix.of.symm (O.val * Matrix.of (qrNormalizedArray A)) := by
  funext i j
  change (gramSchmidtNormed ℝ (qrColumnFamily (Matrix.of.symm (O.val * Matrix.of A))) j) i = _
  rw [qrColumnFamily_orthogonal_mul, gramSchmidtNormed_map_linearIsometry]
  rfl

/-- Canonical positive-diagonal QR frame equivariance on the full-rank set.
Source: operator re-derivation `sh:qr-equiv`; signs are fixed by positive
Gram–Schmidt normalization rather than chosen from the data. -/
theorem canonicalQRFrame_orthogonal_mul {n k : ℕ} (hkn : k ≤ n)
    (O : Matrix.orthogonalGroup (Fin n) ℝ) (A : Fin n → Fin k → ℝ)
    (hA : LinearIndependent ℝ (qrColumnFamily A)) :
    canonicalQRFrame n k hkn (Matrix.of.symm (O.val * Matrix.of A)) =
      O • canonicalQRFrame n k hkn A := by
  have hOA : LinearIndependent ℝ
      (qrColumnFamily (Matrix.of.symm (O.val * Matrix.of A))) := by
    rw [qrColumnFamily_orthogonal_mul]
    exact hA.map' (orthogonalToEuclideanIsometry O).toLinearMap
      ((LinearMap.ker_eq_bot).mpr (orthogonalToEuclideanIsometry O).injective)
  apply Subtype.ext
  change (canonicalQRFrame n k hkn (Matrix.of.symm (O.val * Matrix.of A))).val =
    Matrix.of.symm (O.val * Matrix.of (canonicalQRFrame n k hkn A).val)
  rw [canonicalQRFrame_val_of_linearIndependent hkn _ hOA,
    canonicalQRFrame_val_of_linearIndependent hkn A hA,
    qrNormalizedArray_orthogonal_mul]

/-- The canonical upper factor is unchanged by orthogonal left multiplication.
Source: operator re-derivation `sh:qr-equiv`. -/
theorem canonicalQRUpper_orthogonal_mul {n k : ℕ} (hkn : k ≤ n)
    (O : Matrix.orthogonalGroup (Fin n) ℝ) (A : Fin n → Fin k → ℝ)
    (hA : LinearIndependent ℝ (qrColumnFamily A)) :
    canonicalQRUpper hkn (Matrix.of.symm (O.val * Matrix.of A)) = canonicalQRUpper hkn A := by
  ext i j
  change inner ℝ
    (qrColumnFamily (canonicalQRFrame n k hkn (Matrix.of.symm (O.val * Matrix.of A))).val i)
    (qrColumnFamily (Matrix.of.symm (O.val * Matrix.of A)) j) = _
  rw [canonicalQRFrame_orthogonal_mul hkn O A hA]
  change inner ℝ
    (qrColumnFamily (Matrix.of.symm (O.val * Matrix.of (canonicalQRFrame n k hkn A).val)) i)
    (qrColumnFamily (Matrix.of.symm (O.val * Matrix.of A)) j) = _
  rw [qrColumnFamily_orthogonal_mul, qrColumnFamily_orthogonal_mul]
  exact (orthogonalToEuclideanIsometry O).inner_map_map _ _

/-- The literal canonical factors multiply to the original full-column-rank
input. Together with triangularity and positive diagonal, this is an actual
canonical thin QR decomposition. Source: operator re-derivation `sh:qr-equiv`. -/
theorem canonicalQRFrame_mul_canonicalQRUpper {n k : ℕ} (hkn : k ≤ n)
    (A : Fin n → Fin k → ℝ) (hA : LinearIndependent ℝ (qrColumnFamily A)) :
    Matrix.of (canonicalQRFrame n k hkn A).val * canonicalQRUpper hkn A = Matrix.of A := by
  have hspan : Submodule.span ℝ (Set.range (gramSchmidtNormed ℝ (qrColumnFamily A))) =
      Submodule.span ℝ (Set.range (qrColumnFamily A)) := by
    calc
      _ = Submodule.span ℝ (Set.range (gramSchmidt ℝ (qrColumnFamily A))) := by
        simpa only [Set.image_univ] using
          (span_gramSchmidtNormed (𝕜 := ℝ) (qrColumnFamily A) Set.univ)
      _ = _ := span_gramSchmidt ℝ (qrColumnFamily A)
  have hsum : ∀ j : Fin k, qrColumnFamily A j =
      ∑ i, (inner ℝ (gramSchmidtNormed ℝ (qrColumnFamily A) i) (qrColumnFamily A j)) •
        gramSchmidtNormed ℝ (qrColumnFamily A) i := by
    intro j
    apply eq_sum_inner_smul_of_mem_span_orthonormal _ (gramSchmidtNormed_orthonormal hA)
    rw [hspan]
    exact Submodule.subset_span ⟨j, rfl⟩
  ext i j
  have hh := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) (hsum j)
  simp only [canonicalQRUpper, canonicalQRFrame_val_of_linearIndependent hkn A hA,
    Matrix.mul_apply, Matrix.of_apply, qrColumnFamily, qrNormalizedArray,
    WithLp.toLp_ofLp]
  have hentry : (∑ a,
      (inner ℝ (gramSchmidtNormed ℝ (qrColumnFamily A) a) (qrColumnFamily A j)) •
        gramSchmidtNormed ℝ (qrColumnFamily A) a) i =
      ∑ a, (inner ℝ (gramSchmidtNormed ℝ (qrColumnFamily A) a) (qrColumnFamily A j)) *
        gramSchmidtNormed ℝ (qrColumnFamily A) a i := by
    simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
      smul_eq_mul]
  rw [hentry] at hh
  simpa only [qrColumnFamily, PiLp.toLp_apply, mul_comm] using hh.symm

/-- The canonical upper factor has exactly the original column Gram matrix,
so it preserves the singular-value data. Source: operator re-derivation `sh:qr-equiv`. -/
theorem transpose_canonicalQRUpper_mul_self {n k : ℕ} (hkn : k ≤ n)
    (A : Fin n → Fin k → ℝ) (hA : LinearIndependent ℝ (qrColumnFamily A)) :
    (canonicalQRUpper hkn A)ᵀ * canonicalQRUpper hkn A =
      (Matrix.of A)ᵀ * Matrix.of A := by
  let Q := Matrix.of (canonicalQRFrame n k hkn A).val
  let R := canonicalQRUpper hkn A
  have hQ : Qᵀ * Q = 1 := (canonicalQRFrame n k hkn A).property
  have hQR : Q * R = Matrix.of A := canonicalQRFrame_mul_canonicalQRUpper hkn A hA
  calc
    Rᵀ * R = Rᵀ * (Qᵀ * Q) * R := by rw [hQ, Matrix.mul_one]
    _ = (Q * R)ᵀ * (Q * R) := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hQR]

end NLAlib
