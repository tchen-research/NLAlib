import NLAlib.Matrix.Subspaces.Stiefel

/-!
# Real and complex unitary Stiefel spaces

The actual compact unitary group acts transitively on rectangular orthonormal
frames over either scalar field. The real specialization is the existing
orthogonal Stiefel space; complex frames use the Hermitian equations.
-/

noncomputable section
open MeasureTheory Metric
open scoped Matrix
namespace NLAlib
variable (𝕜 : Type*) [RCLike 𝕜]

/-- The actual orthonormal-column frame space over either scalar field. -/
abbrev UnitaryStiefel (n k : ℕ) :=
  {Q : Matrix (Fin n) (Fin k) 𝕜 // HasOrthonormalCols Q}

open scoped Matrix.Norms.L2Operator in
/-- The actual finite-dimensional unitary group is compact. -/
instance (priority := 100) unitaryGroupCompactSpace (n : ℕ) :
    CompactSpace (Matrix.unitaryGroup (Fin n) 𝕜) := by
  let : ProperSpace (Matrix (Fin n) (Fin n) 𝕜) := FiniteDimensional.proper_rclike 𝕜 _
  apply isCompact_iff_compactSpace.mp
  apply isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_unitary,isBounded_iff_forall_norm_le.mpr ⟨1,?_⟩⟩
  intro O hO
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · have hzero : O = 0 := Subsingleton.elim _ _
    rw [hzero,norm_zero]
    norm_num
  · exact (CStarRing.norm_coe_unitary ⟨O,hO⟩).le

/-- The Hermitian frame equations define a closed set. -/
theorem isClosed_unitaryStiefel (n k : ℕ) :
    IsClosed {Q : Matrix (Fin n) (Fin k) 𝕜 | HasOrthonormalCols Q} := by
  exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const

open scoped Matrix.Norms.L2Operator in
/-- Every unitary frame has Euclidean operator norm at most one. -/
theorem norm_le_one_of_unitaryStiefel {n k : ℕ}
    {Q : Matrix (Fin n) (Fin k) 𝕜} (hQ : HasOrthonormalCols Q) : specNorm Q ≤ 1 := by
  change ‖Q‖ ≤ 1
  have h1 : ‖(1 : Matrix (Fin k) (Fin k) 𝕜)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one,Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by simp
  have h2 : ‖Q‖*‖Q‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self,show Qᴴ*Q=1 from hQ]
    exact h1
  nlinarith [norm_nonneg Q]

open scoped Matrix.Norms.L2Operator in
/-- Rectangular real/complex frame spaces are compact, including empty frames. -/
instance (priority := 100) unitaryStiefelCompactSpace (n k : ℕ) :
    CompactSpace (UnitaryStiefel 𝕜 n k) := by
  let : ProperSpace (Matrix (Fin n) (Fin k) 𝕜) := FiniteDimensional.proper_rclike 𝕜 _
  apply isCompact_iff_compactSpace.mp
  exact isCompact_iff_isClosed_bounded.mpr ⟨isClosed_unitaryStiefel 𝕜 n k,
    isBounded_iff_forall_norm_le.mpr ⟨1,fun Q hQ => by
      change specNorm Q ≤ 1
      exact norm_le_one_of_unitaryStiefel 𝕜 hQ⟩⟩

/-- The initial coordinate frame over the chosen scalar field. -/
def coordinateUnitaryStiefel (n k : ℕ) (hkn : k ≤ n) : UnitaryStiefel 𝕜 n k :=
  ⟨Matrix.of fun i j => if i=Fin.castLE hkn j then 1 else 0,by
    ext a b
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,Fin.castLE_inj,eq_comm]⟩

/-- An actual unitary matrix has orthonormal columns. -/
theorem conjTranspose_mul_self_unitaryGroup {n : ℕ}
    (O : Matrix.unitaryGroup (Fin n) 𝕜) : O.valᴴ*O.val=1 := by
  simpa only [Matrix.star_eq_conjTranspose] using O.property.1

/-- The unitary action on actual rectangular frames. -/
def unitaryStiefelAction {n k : ℕ} (O : Matrix.unitaryGroup (Fin n) 𝕜)
    (Q : UnitaryStiefel 𝕜 n k) : UnitaryStiefel 𝕜 n k :=
  ⟨O.val*Q.val,by
    rw [HasOrthonormalCols,Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc O.valᴴ,conjTranspose_mul_self_unitaryGroup,Matrix.one_mul]
    exact Q.property⟩

/-- Unitarians act as a group on real/complex frames. -/
instance (priority := 100) unitaryStiefelMulAction (n k : ℕ) :
    MulAction (Matrix.unitaryGroup (Fin n) 𝕜) (UnitaryStiefel 𝕜 n k) where
  smul := unitaryStiefelAction 𝕜
  one_smul Q := by
    apply Subtype.ext
    exact Matrix.one_mul Q.val
  mul_smul O P Q := by
    apply Subtype.ext
    exact Matrix.mul_assoc O.val P.val Q.val

/-- The unitary action is jointly continuous. -/
instance (priority := 100) unitaryStiefelContinuousSMul (n k : ℕ) :
    ContinuousSMul (Matrix.unitaryGroup (Fin n) 𝕜) (UnitaryStiefel 𝕜 n k) where
  continuous_smul :=
    ((continuous_subtype_val.comp continuous_fst).matrix_mul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- The actual unitary action is transitive, by extending both frames to full
unitary bases. No scalar-field or nonempty-frame restriction is imposed. -/
theorem exists_unitaryGroup_smul_eq {n k : ℕ} (hkn : k ≤ n)
    (Q Q' : UnitaryStiefel 𝕜 n k) :
    ∃ O : Matrix.unitaryGroup (Fin n) 𝕜, O • Q = Q' := by
  let e := Fin.castLEEmb hkn
  obtain ⟨W,hW,hWQ⟩ := exists_unitary_completion Q.val Q.property e
  obtain ⟨V,hV,hVQ⟩ := exists_unitary_completion Q'.val Q'.property e
  have hWt : W*Wᴴ=1 := mul_eq_one_comm.mp hW
  let O := V*Wᴴ
  have hO : O ∈ Matrix.unitaryGroup (Fin n) 𝕜 := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    simp only [Matrix.star_eq_conjTranspose]
    dsimp only [O]
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ,hV,Matrix.one_mul,hWt]
  refine ⟨⟨O,hO⟩,?_⟩
  have heqOW : O*W=V := by
    dsimp only [O]
    rw [Matrix.mul_assoc,hW,Matrix.mul_one]
  apply Subtype.ext
  funext i j
  change (O*Q.val) i j=Q'.val i j
  calc
    _ = (O*W) i (e j) := by simp only [Matrix.mul_apply,hWQ]
    _ = V i (e j) := congrArg (fun M : Matrix (Fin n) (Fin n) 𝕜 => M i (e j)) heqOW
    _ = Q'.val i j := hVQ i j

end NLAlib
