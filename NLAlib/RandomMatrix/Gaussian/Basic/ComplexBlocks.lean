import NLAlib.RandomMatrix.Gaussian.Basic.ComplexGaussianMatrix
import Mathlib.Probability.HasLaw
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Joint laws and independence of native complex Gaussian matrix blocks

The row split is a measure-preserving split of the actual finite product law.
A rectangular coisometry then gives joint laws for any two mutually orthogonal
fixed frames. No entrywise-marginal replacement of the matrix law is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

variable {m k n t : Type*} [Fintype m] [Fintype k] [Fintype n] [Fintype t]

/-- Splitting disjoint complex Gaussian row blocks gives their exact independent
matrix product law, including empty row blocks. -/
theorem hasLaw_circularComplexGaussianMatrix_rowSplit :
    HasLaw (fun G : Matrix (m ⊕ k) t ℂ =>
      (G.submatrix Sum.inl id,G.submatrix Sum.inr id))
      ((circularComplexGaussianMatrix m t).prod (circularComplexGaussianMatrix k t))
      (circularComplexGaussianMatrix (m ⊕ k) t) := by
  have hsum := measurePreserving_sumPiEquivProdPi
    (fun _ : m ⊕ k => circularComplexGaussianVector t)
  have hp := (measurePreserving_ofMeasurableEquiv_circularComplexGaussianMatrix (m := m) (n := t)).prod
    (measurePreserving_ofMeasurableEquiv_circularComplexGaussianMatrix (m := k) (n := t))
  have hflat := (measurePreserving_ofMeasurableEquiv_circularComplexGaussianMatrix
    (m := m ⊕ k) (n := t)).symm
  exact (hp.comp (hsum.comp hflat)).hasLaw

/-- Any two mutually orthogonal fixed frames give independent native complex
Gaussian matrix blocks, with their full joint product law. -/
theorem hasLaw_circularComplexGaussianMatrix_blocks [DecidableEq n] [DecidableEq m]
    [DecidableEq k] [DecidableEq t]
    (U : Matrix n m ℂ) (V : Matrix n k ℂ) (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) (hUV : Uᴴ*V=0) :
    HasLaw (fun G : Matrix n t ℂ => (Uᴴ*G,Vᴴ*G))
      ((circularComplexGaussianMatrix m t).prod (circularComplexGaussianMatrix k t))
      (circularComplexGaussianMatrix n t) := by
  let W := Matrix.fromCols U V
  have hVU : Vᴴ*U=0 := by
    rw [← Matrix.conjTranspose_conjTranspose U,← Matrix.conjTranspose_mul,hUV,
      Matrix.conjTranspose_zero]
  have hW : HasOrthonormalCols W := by
    change Wᴴ*W=1
    have hWC : Wᴴ=Matrix.fromRows Uᴴ Vᴴ := by
      ext i j
      cases i <;> rfl
    rw [hWC]
    simp only [W,Matrix.fromRows_mul_fromCols,
      show Uᴴ*U=1 from hU,show Vᴴ*V=1 from hV,hUV,hVU,Matrix.fromBlocks_one]
  have hG := hasLaw_mul_circularComplexGaussianMatrix_orthonormalRows (t := t) Wᴴ
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hW)
  have h := (hasLaw_circularComplexGaussianMatrix_rowSplit (m := m) (k := k) (t := t)).comp hG
  apply h.congr
  apply Filter.Eventually.of_forall
  intro G
  apply Prod.ext <;> ext i j <;> rfl

/-- Orthogonal complex Gaussian blocks are independent as matrix-valued random
variables under the actual native Gaussian measure. -/
theorem circularComplexGaussianMatrix_indepFun_block [DecidableEq n] [DecidableEq m]
    [DecidableEq k] [DecidableEq t]
    (U : Matrix n m ℂ) (V : Matrix n k ℂ) (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) (hUV : Uᴴ*V=0) :
    IndepFun (fun G : Matrix n t ℂ => Uᴴ*G) (fun G : Matrix n t ℂ => Vᴴ*G)
      (circularComplexGaussianMatrix n t) := by
  have hUl := hasLaw_mul_circularComplexGaussianMatrix_orthonormalRows (t := t) Uᴴ
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hU)
  have hVl := hasLaw_mul_circularComplexGaussianMatrix_orthonormalRows (t := t) Vᴴ
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hV)
  exact (indepFun_iff_hasLaw_prodMk_prod hUl hVl).mpr
    (hasLaw_circularComplexGaussianMatrix_blocks U V hU hV hUV)

/-- The complete independent-block law transports to arbitrary sample spaces. -/
theorem hasLaw_circularComplexGaussianMatrix_blocks_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → Matrix n t ℂ}
    [DecidableEq n] [DecidableEq m] [DecidableEq k] [DecidableEq t]
    (hG : HasLaw G (circularComplexGaussianMatrix n t) μ)
    (U : Matrix n m ℂ) (V : Matrix n k ℂ) (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) (hUV : Uᴴ*V=0) :
    HasLaw (fun ω => (Uᴴ*G ω,Vᴴ*G ω))
      ((circularComplexGaussianMatrix m t).prod (circularComplexGaussianMatrix k t)) μ :=
  (hasLaw_circularComplexGaussianMatrix_blocks U V hU hV hUV).comp hG

end NLAlib
