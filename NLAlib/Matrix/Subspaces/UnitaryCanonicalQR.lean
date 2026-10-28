import NLAlib.Matrix.Subspaces.UnitaryStiefel
import NLAlib.ForMathlib.Analysis.InnerProductSpace.GramSchmidtRCLike
import NLAlib.Matrix.Subspaces.OrthogonalProducts
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# The actual measurable canonical thin QR frame over both scalar fields

Normalized Hermitian Gram--Schmidt defines the frame on full rank. The explicit
coordinate fallback on the null rank-deficient set makes this a genuine
measurable map. Its frame is unitary-equivariant, and its upper factor has the
original Hermitian Gram matrix.
-/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped Matrix Classical
namespace NLAlib
variable (𝕜 : Type*) [RCLike 𝕜]

/-- Euclidean columns of a real/complex matrix. -/
def unitaryQRColumnFamily {n k : ℕ} (A : Matrix (Fin n) (Fin k) 𝕜) :
    Fin k → EuclideanSpace 𝕜 (Fin n) := fun j => WithLp.toLp 2 (fun i => A i j)

/-- The actual normalized Hermitian Gram--Schmidt array. -/
def unitaryQRNormalizedArray {n k : ℕ} (A : Matrix (Fin n) (Fin k) 𝕜) :
    Matrix (Fin n) (Fin k) 𝕜 :=
  fun i j => gramSchmidtNormed 𝕜 (unitaryQRColumnFamily 𝕜 A) j i

/-- The Euclidean column Gram matrix is exactly the Hermitian matrix Gram. -/
theorem gram_unitaryQRColumnFamily {n k : ℕ} (A : Matrix (Fin n) (Fin k) 𝕜) :
    Matrix.gram 𝕜 (unitaryQRColumnFamily 𝕜 A) = Aᴴ*A := by
  ext i j
  simp only [Matrix.gram_apply,unitaryQRColumnFamily,PiLp.inner_apply,RCLike.inner_apply,
    Matrix.mul_apply,Matrix.conjTranspose_apply,starRingEnd_apply,mul_comm]

/-- On full rank, the normalized array has orthonormal columns. -/
theorem hasOrthonormalCols_unitaryQRNormalizedArray {n k : ℕ}
    (A : Matrix (Fin n) (Fin k) 𝕜) (hA : LinearIndependent 𝕜 (unitaryQRColumnFamily 𝕜 A)) :
    HasOrthonormalCols (unitaryQRNormalizedArray 𝕜 A) := by
  have ho := orthonormal_iff_ite.mp (gramSchmidtNormed_orthonormal hA)
  ext a b
  have hh := ho a b
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,
    unitaryQRNormalizedArray,PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,mul_comm] using hh

/-- The actual canonical frame, with coordinate fallback on rank-deficient data. -/
def unitaryQRFrame (n k : ℕ) (hkn : k ≤ n) (A : Matrix (Fin n) (Fin k) 𝕜) :
    UnitaryStiefel 𝕜 n k :=
  if hA : LinearIndependent 𝕜 (unitaryQRColumnFamily 𝕜 A) then
    ⟨unitaryQRNormalizedArray 𝕜 A,hasOrthonormalCols_unitaryQRNormalizedArray 𝕜 A hA⟩
  else coordinateUnitaryStiefel 𝕜 n k hkn

/-- Full-rank inputs use the literal normalized Gram--Schmidt frame. -/
theorem unitaryQRFrame_val_of_linearIndependent {n k : ℕ} (hkn : k ≤ n)
    (A : Matrix (Fin n) (Fin k) 𝕜) (hA : LinearIndependent 𝕜 (unitaryQRColumnFamily 𝕜 A)) :
    (unitaryQRFrame 𝕜 n k hkn A).val = unitaryQRNormalizedArray 𝕜 A := by
  simp only [unitaryQRFrame,dif_pos hA]

/-- Full column rank is an open condition. -/
theorem isOpen_linearIndependent_unitaryQRColumnFamily (n k : ℕ) :
    IsOpen {A : Matrix (Fin n) (Fin k) 𝕜 | LinearIndependent 𝕜 (unitaryQRColumnFamily 𝕜 A)} := by
  have hcont : Continuous (fun A : Matrix (Fin n) (Fin k) 𝕜 => (Aᴴ*A).det) := by
    simp only [Matrix.det_apply,Matrix.mul_apply,Matrix.conjTranspose_apply]
    fun_prop
  have heq : {A : Matrix (Fin n) (Fin k) 𝕜 | LinearIndependent 𝕜 (unitaryQRColumnFamily 𝕜 A)} =
      {A | (Aᴴ*A).det ≠ 0} := by
    ext A
    simp only [Set.mem_ofPred_eq]
    rw [← Matrix.det_gram_ne_zero_iff_linearIndependent,gram_unitaryQRColumnFamily]
  rw [heq]
  exact (isClosed_eq hcont continuous_const).isOpen_compl

/-- Every normalized Gram--Schmidt entry is measurable, including at breakdown. -/
theorem measurable_unitaryQRNormalizedArray (n k : ℕ) :
    Measurable (unitaryQRNormalizedArray 𝕜 (n := n) (k := k)) := by
  have hc (j : Fin k) : Measurable (fun A : Matrix (Fin n) (Fin k) 𝕜 => unitaryQRColumnFamily 𝕜 A j) := by
    dsimp only [unitaryQRColumnFamily]
    fun_prop
  apply Matrix.measurable_iff_entries.mpr
  intro i j
  exact (EuclideanSpace.proj i : EuclideanSpace 𝕜 (Fin n) →L[𝕜] 𝕜).continuous.measurable.comp
    (measurable_gramSchmidtNormed_rclike 𝕜 (unitaryQRColumnFamily 𝕜) hc j)

/-- The canonical real/complex QR frame is an actual measurable Stiefel map. -/
theorem measurable_unitaryQRFrame (n k : ℕ) (hkn : k ≤ n) :
    Measurable (unitaryQRFrame 𝕜 n k hkn) := by
  apply Measurable.subtype_mk
  change Measurable (fun A => (unitaryQRFrame 𝕜 n k hkn A).val)
  have heq : (fun A => (unitaryQRFrame 𝕜 n k hkn A).val) =
      (fun A => if LinearIndependent 𝕜 (unitaryQRColumnFamily 𝕜 A) then unitaryQRNormalizedArray 𝕜 A
        else (coordinateUnitaryStiefel 𝕜 n k hkn).val) := by
    funext A
    unfold unitaryQRFrame
    split_ifs <;> rfl
  rw [heq]
  exact Measurable.ite (isOpen_linearIndependent_unitaryQRColumnFamily 𝕜 n k).measurableSet
    (measurable_unitaryQRNormalizedArray 𝕜 n k) measurable_const

/-- Left unitary action transports every original Euclidean column. -/
theorem unitaryQRColumnFamily_unitary_mul {n k : ℕ}
    (O : Matrix.unitaryGroup (Fin n) 𝕜) (A : Matrix (Fin n) (Fin k) 𝕜) :
    unitaryQRColumnFamily 𝕜 (O.val*A) = fun j =>
      HasOrthonormalCols.toLinearIsometry (conjTranspose_mul_self_unitaryGroup 𝕜 O)
        (unitaryQRColumnFamily 𝕜 A j) := rfl

/-- The literal normalized array is unitary-equivariant, even at zero residuals. -/
theorem unitaryQRNormalizedArray_unitary_mul {n k : ℕ}
    (O : Matrix.unitaryGroup (Fin n) 𝕜) (A : Matrix (Fin n) (Fin k) 𝕜) :
    unitaryQRNormalizedArray 𝕜 (O.val*A) = O.val*unitaryQRNormalizedArray 𝕜 A := by
  funext i j
  change (gramSchmidtNormed 𝕜 (unitaryQRColumnFamily 𝕜 (O.val*A)) j) i = _
  rw [unitaryQRColumnFamily_unitary_mul,gramSchmidtNormed_map_linearIsometry_rclike]
  rfl

/-- The canonical frame is unitary-equivariant on the full-rank set. -/
theorem unitaryQRFrame_unitary_mul {n k : ℕ} (hkn : k ≤ n)
    (O : Matrix.unitaryGroup (Fin n) 𝕜) (A : Matrix (Fin n) (Fin k) 𝕜)
    (hA : LinearIndependent 𝕜 (unitaryQRColumnFamily 𝕜 A)) :
    unitaryQRFrame 𝕜 n k hkn (O.val*A) = O • unitaryQRFrame 𝕜 n k hkn A := by
  have hOA : LinearIndependent 𝕜 (unitaryQRColumnFamily 𝕜 (O.val*A)) := by
    rw [unitaryQRColumnFamily_unitary_mul]
    let L := HasOrthonormalCols.toLinearIsometry (conjTranspose_mul_self_unitaryGroup 𝕜 O)
    exact hA.map' L.toLinearMap (LinearMap.ker_eq_bot.mpr L.injective)
  apply Subtype.ext
  change (unitaryQRFrame 𝕜 n k hkn (O.val*A)).val = O.val*(unitaryQRFrame 𝕜 n k hkn A).val
  rw [unitaryQRFrame_val_of_linearIndependent 𝕜 hkn _ hOA,
    unitaryQRFrame_val_of_linearIndependent 𝕜 hkn _ hA,unitaryQRNormalizedArray_unitary_mul]

/-- The canonical upper factor consists of the Hermitian column coordinates. -/
def unitaryQRUpper {n k : ℕ} (hkn : k ≤ n) (A : Matrix (Fin n) (Fin k) 𝕜) :
    Matrix (Fin k) (Fin k) 𝕜 := (unitaryQRFrame 𝕜 n k hkn A).valᴴ*A

/-- The actual canonical QR factors multiply to the original full-rank input. -/
theorem unitaryQRFrame_mul_unitaryQRUpper {n k : ℕ} (hkn : k ≤ n)
    (A : Matrix (Fin n) (Fin k) 𝕜) (hA : LinearIndependent 𝕜 (unitaryQRColumnFamily 𝕜 A)) :
    (unitaryQRFrame 𝕜 n k hkn A).val*unitaryQRUpper 𝕜 hkn A = A := by
  have hspan : Submodule.span 𝕜 (Set.range (gramSchmidtNormed 𝕜 (unitaryQRColumnFamily 𝕜 A))) =
      Submodule.span 𝕜 (Set.range (unitaryQRColumnFamily 𝕜 A)) := by
    calc
      _ = Submodule.span 𝕜 (Set.range (gramSchmidt 𝕜 (unitaryQRColumnFamily 𝕜 A))) := by
        simpa only [Set.image_univ] using
          span_gramSchmidtNormed (𝕜 := 𝕜) (unitaryQRColumnFamily 𝕜 A) Set.univ
      _ = _ := span_gramSchmidt 𝕜 (unitaryQRColumnFamily 𝕜 A)
  have hsum (j : Fin k) : unitaryQRColumnFamily 𝕜 A j =
      ∑ i, inner 𝕜 (gramSchmidtNormed 𝕜 (unitaryQRColumnFamily 𝕜 A) i)
        (unitaryQRColumnFamily 𝕜 A j) • gramSchmidtNormed 𝕜 (unitaryQRColumnFamily 𝕜 A) i := by
    apply eq_sum_inner_smul_of_mem_span_orthonormal_rclike 𝕜 _ (gramSchmidtNormed_orthonormal hA)
    rw [hspan]
    exact Submodule.subset_span ⟨j,rfl⟩
  ext i j
  have hh := congrArg (fun x : EuclideanSpace 𝕜 (Fin n) => x i) (hsum j)
  simp only [unitaryQRColumnFamily,WithLp.ofLp_sum,WithLp.ofLp_smul,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hh
  simpa only [unitaryQRUpper,unitaryQRFrame_val_of_linearIndependent 𝕜 hkn A hA,
    Matrix.mul_apply,Matrix.conjTranspose_apply,unitaryQRNormalizedArray,
    unitaryQRColumnFamily,PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,mul_comm] using hh.symm

/-- The upper factor has exactly the original Hermitian column Gram matrix. -/
theorem conjTranspose_unitaryQRUpper_mul_self {n k : ℕ} (hkn : k ≤ n)
    (A : Matrix (Fin n) (Fin k) 𝕜) (hA : LinearIndependent 𝕜 (unitaryQRColumnFamily 𝕜 A)) :
    (unitaryQRUpper 𝕜 hkn A)ᴴ*unitaryQRUpper 𝕜 hkn A = Aᴴ*A := by
  let Q := (unitaryQRFrame 𝕜 n k hkn A).val
  let R := unitaryQRUpper 𝕜 hkn A
  have hQ : Qᴴ*Q=1 := (unitaryQRFrame 𝕜 n k hkn A).property
  have hQR : Q*R=A := unitaryQRFrame_mul_unitaryQRUpper 𝕜 hkn A hA
  calc
    Rᴴ*R = Rᴴ*(Qᴴ*Q)*R := by rw [hQ,Matrix.mul_one]
    _ = (Q*R)ᴴ*(Q*R) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hQR]

/-- The actual canonical upper factor is invertible on full column rank. -/
theorem isUnit_unitaryQRUpper {n k : ℕ} (hkn : k ≤ n)
    (A : Matrix (Fin n) (Fin k) 𝕜) (hA : LinearIndependent 𝕜 (unitaryQRColumnFamily 𝕜 A)) :
    IsUnit (unitaryQRUpper 𝕜 hkn A) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  intro hd
  have hdet := (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := 𝕜)).mpr hA
  rw [gram_unitaryQRColumnFamily,← conjTranspose_unitaryQRUpper_mul_self 𝕜 hkn A hA,
    Matrix.det_mul,hd,mul_zero] at hdet
  exact hdet rfl

end NLAlib
