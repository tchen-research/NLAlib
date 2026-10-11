import NLAlib.Matrix.Projections
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# The compact orthogonal group and Stiefel frame space

Frames use the array view of matrices, so their Borel structure is the
established product structure. The orthogonal group is Mathlib's actual group.
Source: operator re-derivation `sh:haar`.
Supports atlas `haar-orthogonal`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Metric
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

/-- The Borel structure of the actual orthogonal group, inherited from its
finite-dimensional matrix topology. Source: operator re-derivation `sh:haar`. -/
instance orthogonalGroupMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix.orthogonalGroup (Fin n) ℝ) := borel _

/-- The orthogonal group carries its Borel sigma algebra.
Source: operator re-derivation `sh:haar`. -/
instance orthogonalGroupBorelSpace (n : ℕ) :
    BorelSpace (Matrix.orthogonalGroup (Fin n) ℝ) := ⟨rfl⟩

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

/-- The Stiefel space of real orthonormal `k`-frames, in the array view.
Source: operator re-derivation `sh:haar`; equivalent to `QᵀQ = I`. -/
abbrev Stiefel (n k : ℕ) := {Q : Fin n → Fin k → ℝ // HasOrthonormalCols (Matrix.of Q)}

/-- Coordinate equations make the frame space a closed subset of the ambient
array space. Source: operator re-derivation `sh:haar`. -/
theorem isClosed_stiefel (n k : ℕ) :
    IsClosed {Q : Fin n → Fin k → ℝ | HasOrthonormalCols (Matrix.of Q)} := by
  let f : (Fin n → Fin k → ℝ) → Fin k → Fin k → ℝ :=
    fun Q a b => ∑ i, Q i a * Q i b
  have hf : Continuous f := by dsimp [f]; fun_prop
  have heq : {Q : Fin n → Fin k → ℝ | HasOrthonormalCols (Matrix.of Q)} =
      f ⁻¹' {Matrix.of.symm (1 : Matrix (Fin k) (Fin k) ℝ)} := by
    ext Q
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    change (Matrix.of Q)ᵀ * Matrix.of Q = 1 ↔ _
    rw [← Matrix.ext_iff (M := (Matrix.of Q)ᵀ * Matrix.of Q) (N := 1)]
    simp only [funext_iff, f, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.of_symm_apply]
  rw [heq]
  exact isClosed_singleton.preimage hf

/-- An orthonormal frame has ambient coordinate norm at most one.
Source: operator re-derivation `sh:haar`; every squared entry is at most
the unit squared norm of its column. -/
theorem norm_array_le_one_of_hasOrthonormalCols {n k : ℕ}
    {Q : Fin n → Fin k → ℝ} (hQ : HasOrthonormalCols (Matrix.of Q)) : ‖Q‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro j
  have hc : ∑ a, Q a j ^ 2 = 1 := by
    have hh := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M j j) hQ
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.one_apply_eq, ← sq] using hh
  have he : Q i j ^ 2 ≤ 1 := by
    rw [← hc]
    exact Finset.single_le_sum (fun a _ => sq_nonneg (Q a j)) (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs (Q i j), abs_nonneg (Q i j)]

/-- The Stiefel frame space is compact, including empty frames.
Source: operator re-derivation `sh:haar`. -/
instance stiefelCompactSpace (n k : ℕ) : CompactSpace (Stiefel n k) := by
  apply isCompact_iff_compactSpace.mp
  exact isCompact_iff_isClosed_bounded.mpr ⟨isClosed_stiefel n k,
    isBounded_iff_forall_norm_le.mpr ⟨1, fun Q hQ => norm_array_le_one_of_hasOrthonormalCols hQ⟩⟩

/-- The coordinate frame embeds the first `k` standard basis vectors.
Source: operator re-derivation `sh:haar`, requiring `k ≤ n`. -/
def coordinateStiefel (n k : ℕ) (hkn : k ≤ n) : Stiefel n k :=
  ⟨fun i j => if i = Fin.castLE hkn j then 1 else 0, by
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
  ⟨Matrix.of.symm (O.val * Matrix.of Q.val), by
    change (O.val * Matrix.of Q.val)ᵀ * (O.val * Matrix.of Q.val) = 1
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
    change Matrix.of.symm (1 * Matrix.of Q.val) = Q.val
    rw [Matrix.one_mul, Equiv.symm_apply_apply]
  mul_smul O P Q := by
    apply Subtype.ext
    change Matrix.of.symm ((O.val * P.val) * Matrix.of Q.val) =
      Matrix.of.symm (O.val * Matrix.of (Matrix.of.symm (P.val * Matrix.of Q.val)))
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc]

/-- The group action on frames is jointly continuous.
Source: operator re-derivation `sh:haar`, finite matrix multiplication. -/
instance stiefelContinuousSMul (n k : ℕ) :
    ContinuousSMul (Matrix.orthogonalGroup (Fin n) ℝ) (Stiefel n k) where
  continuous_smul := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun p : Matrix.orthogonalGroup (Fin n) ℝ × Stiefel n k =>
      ∑ a, p.1.val i a * p.2.val a j)
    apply continuous_finsetSum
    intro a _
    exact ((continuous_matrix_apply i a).comp
      (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply j).comp ((continuous_apply a).comp
        (continuous_subtype_val.comp continuous_snd)))

/-- The action of the real orthogonal group on `k`-frames is transitive whenever
`k ≤ n`, including zero-dimensional frames. Source: operator re-derivation
`sh:haar`, extending both frames to full orthogonal bases. -/
theorem exists_orthogonalGroup_smul_eq {n k : ℕ} (hkn : k ≤ n)
    (Q Q' : Stiefel n k) :
    ∃ O : Matrix.orthogonalGroup (Fin n) ℝ, O • Q = Q' := by
  let e := Fin.castLEEmb hkn
  obtain ⟨W, hW, hWQ⟩ := exists_orthogonal_completion (Matrix.of Q.val) Q.property e
  obtain ⟨V, hV, hVQ⟩ := exists_orthogonal_completion (Matrix.of Q'.val) Q'.property e
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
  change (O * Matrix.of Q.val) i j = Q'.val i j
  calc
    _ = (O * W) i (e j) := by simp only [Matrix.mul_apply, hWQ, Matrix.of_apply]
    _ = V i (e j) := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i (e j)) heqOW
    _ = Q'.val i j := hVQ i j

end NLAlib
