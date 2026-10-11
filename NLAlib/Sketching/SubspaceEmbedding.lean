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

The converse of the Gram form is in `NLAlib.Sketching.Gram`; the singular-value
form is in `NLAlib.Sketching.SingularValueEmbedding` and its finite-index transport.
The matrix facts used here (`mulVec_dotProduct_mulVec_self`,
`abs_dotProduct_mulVec_le_specNorm`, `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols`) are
in `NLAlib.Matrix.Norms` and `NLAlib.Matrix.Projections`.

Atlas: `ose-def`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {k m d e : Type*} [Fintype k] [Fintype m] [Fintype d] [Fintype e]

/-- Orthonormal form of a subspace embedding (Woodruff 2014 §2.1; Martinsson–Tropp 2020 §8.7):
for `U` with orthonormal columns, `S` is an `ε`-subspace embedding for `range U` iff
`(1 - ε)‖x‖² ≤ ‖SUx‖² ≤ (1 + ε)‖x‖²` for every coefficient vector `x`.

Atlas: `ose-def`.
atlas: ose-def -/
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

Atlas: `ose-def`.
atlas: ose-def -/
theorem isSubspaceEmbedding_mul_right_iff [DecidableEq d] {S : Matrix k m ℝ} {U : Matrix m d ℝ}
    {ε : ℝ} {C : Matrix d d ℝ} (hC : IsUnit C.det) :
    IsSubspaceEmbedding S (U * C) ε ↔ IsSubspaceEmbedding S U ε :=
  ⟨fun h => h.of_mul_right (Matrix.mul_nonsing_inv C hC), fun h => h.mul_right C⟩

/-- Monotonicity in the distortion: an `ε`-embedding is an `ε'`-embedding for `ε ≤ ε'`.

Atlas: `ose-def`.
atlas: ose-def -/
theorem IsSubspaceEmbedding.mono {S : Matrix k m ℝ} {U : Matrix m d ℝ} {ε ε' : ℝ}
    (h : IsSubspaceEmbedding S U ε) (hεε' : ε ≤ ε') : IsSubspaceEmbedding S U ε' := by
  intro x
  have hn : 0 ≤ (U *ᵥ x) ⬝ᵥ (U *ᵥ x) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  obtain ⟨h₁, h₂⟩ := h x
  constructor <;> nlinarith

/-- Gram form of a subspace embedding (Woodruff 2014 §2.1; Martinsson–Tropp 2020 §8.7), the
direction used in practice: for `U` with orthonormal columns, `‖(SU)ᵀ(SU) − I‖₂ ≤ ε` implies
that `S` is an `ε`-subspace embedding for `range U`. The converse is proved in
`NLAlib.Sketching.Gram`.

Atlas: `ose-def`.
atlas: ose-def -/
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
