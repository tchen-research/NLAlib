import NLAlib.Matrix.Subspaces.Projections
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Basic
import NLAlib.ForMathlib.MeasureTheory.Matrix

/-!
# The compact orthogonal group and Stiefel frame space

Frames are matrices with orthonormal columns; their Borel structure is the subtype of the
global product structure on `Matrix` (`Matrix.instBorelSpace`). The orthogonal group is
Mathlib's actual group.
Source: operator re-derivation `sh:haar`.
Supports atlas `haar-orthogonal`.
-/

noncomputable section
open MeasureTheory Metric
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

/-- The real orthogonal group is compact, including dimension zero.
Source: closed unitary equations and the bounded operator norm;
operator re-derivation `sh:haar`. -/
instance orthogonalGroupCompactSpace (n : ℕ) :
    CompactSpace (Matrix.orthogonalGroup (Fin n) ℝ) := by
  apply isCompact_iff_compactSpace.mp
  apply isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_unitary, isBounded_iff_forall_norm_le.mpr ⟨1, ?_⟩⟩
  intro O hO
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · have hzero : O = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]
    norm_num
  · exact (CStarRing.norm_coe_unitary ⟨O, hO⟩).le

/-- The Stiefel space of real orthonormal `k`-frames, as a subtype of `Matrix (Fin n) (Fin k) ℝ`.
Source: operator re-derivation `sh:haar`; equivalent to `QᵀQ = I`. -/
abbrev Stiefel (n k : ℕ) := {Q : Matrix (Fin n) (Fin k) ℝ // HasOrthonormalCols Q}

/-- The orthonormality equations make the frame space a closed subset of the ambient
matrix space. Source: operator re-derivation `sh:haar`. -/
theorem isClosed_stiefel (n k : ℕ) :
    IsClosed {Q : Matrix (Fin n) (Fin k) ℝ | HasOrthonormalCols Q} := by
  change IsClosed {Q : Matrix (Fin n) (Fin k) ℝ | Qᴴ * Q = 1}
  exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)
    continuous_const

/-- An orthonormal frame has `L2` operator norm at most one.
Source: operator re-derivation `sh:haar`; the C⋆-identity `‖QᴴQ‖ = ‖Q‖²` with `QᴴQ = 1`. -/
theorem norm_array_le_one_of_hasOrthonormalCols {n k : ℕ}
    {Q : Matrix (Fin n) (Fin k) ℝ} (hQ : HasOrthonormalCols Q) : ‖Q‖ ≤ 1 := by
  have h1 : ‖(1 : Matrix (Fin k) (Fin k) ℝ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by simp
  have h2 : ‖Q‖ * ‖Q‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, show Qᴴ * Q = 1 from hQ]
    exact h1
  nlinarith [norm_nonneg Q]

/-- The Stiefel frame space is compact, including empty frames.
Source: operator re-derivation `sh:haar`. -/
instance stiefelCompactSpace (n k : ℕ) : CompactSpace (Stiefel n k) := by
  apply isCompact_iff_compactSpace.mp
  exact isCompact_iff_isClosed_bounded.mpr ⟨isClosed_stiefel n k,
    isBounded_iff_forall_norm_le.mpr ⟨1, fun Q hQ => norm_array_le_one_of_hasOrthonormalCols hQ⟩⟩

/-- The coordinate frame embeds the first `k` standard basis vectors.
Source: operator re-derivation `sh:haar`, requiring `k ≤ n`. -/
def coordinateStiefel (n k : ℕ) (hkn : k ≤ n) : Stiefel n k :=
  ⟨Matrix.of fun i j => if i = Fin.castLE hkn j then 1 else 0, by
    ext a b
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply,
      Fin.castLE_inj, eq_comm]⟩

/-- Matrix entries are continuous in the finite-dimensional operator topology.
Source: finite-dimensional linear maps; supports `haar-orthogonal`. -/
theorem continuous_matrix_apply {n k : ℕ} (i : Fin n) (j : Fin k) :
    Continuous (fun A : Matrix (Fin n) (Fin k) ℝ => A i j) := by
  let L : Matrix (Fin n) (Fin k) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact L.continuous_of_finiteDimensional

/-- An element of the actual orthogonal group has orthonormal columns.
Source: Mathlib's unitary equations; supports `haar-orthogonal`. -/
theorem transpose_mul_self_orthogonalGroup {n : ℕ}
    (O : Matrix.orthogonalGroup (Fin n) ℝ) : O.valᵀ * O.val = 1 := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    using O.property.1

/-- Orthogonal left multiplication acts on the Stiefel frame space.
Source: operator re-derivation `sh:haar`. -/
def stiefelAction {n k : ℕ} (O : Matrix.orthogonalGroup (Fin n) ℝ)
    (Q : Stiefel n k) : Stiefel n k :=
  ⟨O.val * Q.val, by
    change (O.val * Q.val)ᵀ * (O.val * Q.val) = 1
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc O.valᵀ, transpose_mul_self_orthogonalGroup,
      Matrix.one_mul]
    exact Q.property⟩

/-- The orthogonal matrix action is a group action on frames.
Source: operator re-derivation `sh:haar`. -/
instance stiefelMulAction (n k : ℕ) :
    MulAction (Matrix.orthogonalGroup (Fin n) ℝ) (Stiefel n k) where
  smul := stiefelAction
  one_smul Q := by
    apply Subtype.ext
    change 1 * Q.val = Q.val
    rw [Matrix.one_mul]
  mul_smul O P Q := by
    apply Subtype.ext
    change (O.val * P.val) * Q.val = O.val * (P.val * Q.val)
    rw [Matrix.mul_assoc]

/-- The group action on frames is jointly continuous.
Source: operator re-derivation `sh:haar`, finite matrix multiplication. -/
instance stiefelContinuousSMul (n k : ℕ) :
    ContinuousSMul (Matrix.orthogonalGroup (Fin n) ℝ) (Stiefel n k) where
  continuous_smul :=
    ((continuous_subtype_val.comp continuous_fst).matrix_mul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- The action of the real orthogonal group on `k`-frames is transitive whenever
`k ≤ n`, including zero-dimensional frames. Source: operator re-derivation
`sh:haar`, extending both frames to full orthogonal bases. -/
theorem exists_orthogonalGroup_smul_eq {n k : ℕ} (hkn : k ≤ n)
    (Q Q' : Stiefel n k) :
    ∃ O : Matrix.orthogonalGroup (Fin n) ℝ, O • Q = Q' := by
  let e := Fin.castLEEmb hkn
  obtain ⟨W, hW, hWQ⟩ := exists_unitary_completion Q.val Q.property e
  obtain ⟨V, hV, hVQ⟩ := exists_unitary_completion Q'.val Q'.property e
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hW hV
  have hWt : W * Wᵀ = 1 := mul_eq_one_comm.mp hW
  let O := V * Wᵀ
  have hO : O ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    dsimp only [O]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul, hWt]
  refine ⟨⟨O, hO⟩, ?_⟩
  have heqOW : O * W = V := by
    dsimp only [O]
    rw [Matrix.mul_assoc, hW, Matrix.mul_one]
  apply Subtype.ext
  funext i j
  change (O * Q.val) i j = Q'.val i j
  calc
    _ = (O * W) i (e j) := by simp only [Matrix.mul_apply, hWQ]
    _ = V i (e j) := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i (e j)) heqOW
    _ = Q'.val i j := hVQ i j

end NLAlib
