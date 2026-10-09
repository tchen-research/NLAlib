import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import NLAlib.Matrix.Norms
import NLAlib.Matrix.Projections
import NLAlib.Sketching.Basic

/-!
# Subspace embeddings: equivalent forms and basic properties

Facts about `NLAlib.IsSubspaceEmbedding S U ε` (Woodruff 2014 §2.1; Martinsson–Tropp 2020 §8.7):

* `isSubspaceEmbedding_iff_of_hasOrthonormalCols`: for `Uᵀ U = 1`, the embedding property is
  `(1 - ε)‖x‖² ≤ ‖SUx‖² ≤ (1 + ε)‖x‖²` for all `x`;
* `IsSubspaceEmbedding.mul_right`, `IsSubspaceEmbedding.of_mul_right`,
  `isSubspaceEmbedding_mul_right_iff`: the property depends only on `range U`;
* `IsSubspaceEmbedding.mono`: monotonicity in `ε`;
* `isSubspaceEmbedding_of_specNorm_transpose_mul_self_sub_one_le`: the Gram form
  `‖(SU)ᵀ(SU) − I‖₂ ≤ ε ⇒` embedding, for orthonormal `U`.

The converse of the Gram form and the singular-value form `σ(SU) ⊂ [√(1−ε), √(1+ε)]` are still
to do. The helpers `mulVec_dotProduct_mulVec_self`,
`mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` and `abs_dotProduct_mulVec_le_specNorm`
are matrix facts that belong in `NLAlib.Matrix.Norms`.

Atlas: `ose-def`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {k m d e : Type*} [Fintype k] [Fintype m] [Fintype d] [Fintype e]

/-- `‖Ax‖² = xᵀ (AᵀA) x`. Helper for the Gram forms of `ose-def`. -/
theorem mulVec_dotProduct_mulVec_self {p q : Type*} [Fintype p] [Fintype q]
    (A : Matrix p q ℝ) (x : q → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ ((Aᵀ * A) *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Aᵀ, Matrix.vecMul_transpose]

/-- If `U` has orthonormal columns (`Uᵀ U = 1`) then `‖Ux‖² = ‖x‖²`. Helper for `ose-def`. -/
theorem mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols [DecidableEq d] {U : Matrix m d ℝ}
    (hU : HasOrthonormalCols U) (x : d → ℝ) : (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ x := by
  rw [mulVec_dotProduct_mulVec_self, show Uᵀ * U = 1 from hU, Matrix.one_mulVec]

/-- Orthonormal form of a subspace embedding (Woodruff 2014 §2.1; Martinsson–Tropp 2020 §8.7):
for `U` with orthonormal columns, `S` is an `ε`-subspace embedding for `range U` iff
`(1 - ε)‖x‖² ≤ ‖SUx‖² ≤ (1 + ε)‖x‖²` for every coefficient vector `x`.

Atlas: `ose-def`. -/
theorem isSubspaceEmbedding_iff_of_hasOrthonormalCols [DecidableEq d] {S : Matrix k m ℝ}
    {U : Matrix m d ℝ} (hU : HasOrthonormalCols U) {ε : ℝ} :
    IsSubspaceEmbedding S U ε ↔ ∀ x : d → ℝ,
      (1 - ε) * (x ⬝ᵥ x) ≤ ((S * U) *ᵥ x) ⬝ᵥ ((S * U) *ᵥ x) ∧
      ((S * U) *ᵥ x) ⬝ᵥ ((S * U) *ᵥ x) ≤ (1 + ε) * (x ⬝ᵥ x) := by
  unfold IsSubspaceEmbedding
  simp only [mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hU, Matrix.mulVec_mulVec]

/-- Basis independence, easy direction: an embedding for `range U` is an embedding for
`range (U C)` for any `C` (since `range (U C) ⊆ range U`).

Atlas: `ose-def`. -/
theorem IsSubspaceEmbedding.mul_right {S : Matrix k m ℝ} {U : Matrix m d ℝ} {ε : ℝ}
    (h : IsSubspaceEmbedding S U ε) (C : Matrix d e ℝ) : IsSubspaceEmbedding S (U * C) ε := by
  intro x
  simpa only [← Matrix.mulVec_mulVec] using h (C *ᵥ x)

/-- Basis independence, converse direction: if `C` has a right inverse `D` (`C D = 1`, so
`range (U C) = range U`) then an embedding for `range (U C)` is an embedding for `range U`.

Atlas: `ose-def`. -/
theorem IsSubspaceEmbedding.of_mul_right [DecidableEq d] {S : Matrix k m ℝ} {U : Matrix m d ℝ}
    {ε : ℝ} {C : Matrix d e ℝ} {D : Matrix e d ℝ} (hCD : C * D = 1)
    (h : IsSubspaceEmbedding S (U * C) ε) : IsSubspaceEmbedding S U ε := by
  have := h.mul_right D
  rwa [Matrix.mul_assoc, hCD, Matrix.mul_one] at this

/-- Basis independence (Woodruff 2014 §2.1): for invertible `C`, `S` is an `ε`-subspace
embedding for `range U` iff it is one for `range (U C)`. The property depends on the subspace
only.

Atlas: `ose-def`. -/
theorem isSubspaceEmbedding_mul_right_iff [DecidableEq d] {S : Matrix k m ℝ} {U : Matrix m d ℝ}
    {ε : ℝ} {C : Matrix d d ℝ} (hC : IsUnit C.det) :
    IsSubspaceEmbedding S (U * C) ε ↔ IsSubspaceEmbedding S U ε :=
  ⟨fun h => h.of_mul_right (Matrix.mul_nonsing_inv C hC), fun h => h.mul_right C⟩

/-- Monotonicity in the distortion: an `ε`-embedding is an `ε'`-embedding for `ε ≤ ε'`.

Atlas: `ose-def`. -/
theorem IsSubspaceEmbedding.mono {S : Matrix k m ℝ} {U : Matrix m d ℝ} {ε ε' : ℝ}
    (h : IsSubspaceEmbedding S U ε) (hεε' : ε ≤ ε') : IsSubspaceEmbedding S U ε' := by
  intro x
  have hn : 0 ≤ (U *ᵥ x) ⬝ᵥ (U *ᵥ x) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  obtain ⟨h₁, h₂⟩ := h x
  constructor <;> nlinarith

/-- Quadratic-form bound by the spectral norm: `|xᵀ M x| ≤ ‖M‖₂ ‖x‖²`. Helper for the Gram form
of `ose-def`. -/
theorem abs_dotProduct_mulVec_le_specNorm [DecidableEq d] (M : Matrix d d ℝ) (x : d → ℝ) :
    |x ⬝ᵥ (M *ᵥ x)| ≤ specNorm M * (x ⬝ᵥ x) := by
  rw [specNorm_eq_norm]
  have h := M.l2_opNorm_mulVec (WithLp.toLp 2 x)
  have hx : ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.real_norm_sq_eq]; simp [dotProduct, sq]
  have hcs :=
    abs_real_inner_le_norm (WithLp.toLp 2 x) ((EuclideanSpace.equiv d ℝ).symm (M *ᵥ x))
  have hi : inner ℝ (WithLp.toLp 2 x) ((EuclideanSpace.equiv d ℝ).symm (M *ᵥ x)) =
      x ⬝ᵥ (M *ᵥ x) := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [hi] at hcs
  calc |x ⬝ᵥ (M *ᵥ x)| ≤ _ := hcs
    _ ≤ ‖WithLp.toLp 2 x‖ * (‖M‖ * ‖WithLp.toLp 2 x‖) := by gcongr
    _ = ‖M‖ * (x ⬝ᵥ x) := by rw [← hx]; ring

/-- Gram form of a subspace embedding (Woodruff 2014 §2.1; Martinsson–Tropp 2020 §8.7), the
direction used in practice: for `U` with orthonormal columns, `‖(SU)ᵀ(SU) − I‖₂ ≤ ε` implies
that `S` is an `ε`-subspace embedding for `range U`. (The converse also holds; not yet
formalized.)

Atlas: `ose-def`. -/
theorem isSubspaceEmbedding_of_specNorm_transpose_mul_self_sub_one_le [DecidableEq d]
    {S : Matrix k m ℝ} {U : Matrix m d ℝ} (hU : HasOrthonormalCols U) {ε : ℝ}
    (h : specNorm ((S * U)ᵀ * (S * U) - 1) ≤ ε) : IsSubspaceEmbedding S U ε := by
  rw [isSubspaceEmbedding_iff_of_hasOrthonormalCols hU]
  intro x
  have hb := abs_dotProduct_mulVec_le_specNorm ((S * U)ᵀ * (S * U) - 1) x
  have hq : x ⬝ᵥ (((S * U)ᵀ * (S * U) - 1) *ᵥ x) =
      ((S * U) *ᵥ x) ⬝ᵥ ((S * U) *ᵥ x) - x ⬝ᵥ x := by
    rw [Matrix.sub_mulVec, dotProduct_sub, ← mulVec_dotProduct_mulVec_self, Matrix.one_mulVec]
  rw [hq] at hb
  have hn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have hε : specNorm ((S * U)ᵀ * (S * U) - 1) * (x ⬝ᵥ x) ≤ ε * (x ⬝ᵥ x) :=
    mul_le_mul_of_nonneg_right h hn
  obtain ⟨h₁, h₂⟩ := abs_le.mp (hb.trans hε)
  constructor <;> nlinarith

end NLAlib
