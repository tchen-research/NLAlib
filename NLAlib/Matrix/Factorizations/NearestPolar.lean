import NLAlib.Matrix.Factorizations.PolarDecomposition
import NLAlib.Matrix.Norms.FanDominance
import NLAlib.Matrix.Spectral.GramSingularValues
/-!
# Polar isometries minimize every invariant norm distance

The exact distance to a polar factor is the invariant norm of the rectangular
diagonal of singular-value distances from one. Mirsky supplies the lower bound
for every competing isometry. Atlas `polar-decomposition`.
-/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- The rectangular diagonal of ones is a coordinate isometry in a tall shape.
Horn–Johnson 2013, Theorem 7.3.1; polar-decomposition helper. -/
theorem hasOrthonormalCols_rectDiag_one {m n : ℕ} (hCard : n ≤ m) :
    HasOrthonormalCols (rectDiag (fun _ => 1) : Matrix (Fin m) (Fin n) ℝ) := by
  rw [hasOrthonormalCols_iff_conjTranspose_mul_self, conjTranspose_rectDiag_mul_rectDiag]
  ext i j
  simp only [one_pow]
  have hi : (i : ℕ) < m := i.isLt.trans_le hCard
  simp [Matrix.diagonal_apply, Matrix.one_apply, hi]

/-- A real isometry has singular value one at every thin index, including
the zero-dimensional case as an empty assertion. Horn–Johnson §7.3.1. -/
theorem singularValues_eq_one_of_hasOrthonormalCols {m n : ℕ}
    {U : Matrix (Fin m) (Fin n) ℝ} (hU : HasOrthonormalCols U)
    (hCard : n ≤ m) {k : ℕ} (hk : k < n) : singularValues U k = 1 := by
  let J : Matrix (Fin m) (Fin n) ℝ := rectDiag (fun _ => 1)
  have hJ := hasOrthonormalCols_rectDiag_one hCard
  have hGram : Uᴴ * U = Jᴴ * J := by
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [(show Uᵀ * U = 1 from hU), (show Jᵀ * J = 1 from hJ)]
  have h := singularValues_eq_of_gram_eq U J hGram k
  change singularValues U k = singularValues J k at h
  rw [h]
  exact singularValues_eq_of_eq_mul_rectDiag_mul
    (U := (1 : Matrix (Fin m) (Fin m) ℝ)) (V := (1 : Matrix (Fin n) (Fin n) ℝ))
    (τ := fun _ => 1) (by simp) (by simp) (fun _ => zero_le_one) (fun _ _ _ => le_rfl)
    (by simp [J]) (by simpa only [min_eq_right hCard] using hk)

private theorem exists_svd_polar_with_distance {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hCard : n ≤ m) (ν : OrthogonallyInvariantNorm (Fin m) (Fin n)) :
    ∃ U : Matrix (Fin m) (Fin n) ℝ, HasOrthonormalCols U ∧
      U * CFC.sqrt (Aᵀ * A) = A ∧
      ν.seminorm (A - U) = ν.seminorm (rectangularDiagonal
        (fun i : Fin (min m n) => singularValues A i - 1)) := by
  obtain ⟨L, R, hSVD⟩ := exists_isSVD A
  let J : Matrix (Fin m) (Fin n) ℝ := rectDiag (fun _ => 1)
  let U := L * J * Rᵀ
  let Q := R * Matrix.diagonal (fun i : Fin n => singularValues A i) * Rᵀ
  have hJ := hasOrthonormalCols_rectDiag_one hCard
  have hL : HasOrthonormalCols L := hSVD.transpose_mul_left
  have hRt : HasOrthonormalCols Rᵀ := by
    change Rᵀᵀ * Rᵀ = 1
    rw [Matrix.transpose_transpose]
    exact hSVD.mul_transpose_right
  have hU : HasOrthonormalCols U := by
    change (L * J * Rᵀ)ᵀ * (L * J * Rᵀ) = 1
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Lᵀ L (J * Rᵀ), (show Lᵀ * L = 1 from hL), Matrix.one_mul,
      ← Matrix.mul_assoc Jᵀ J Rᵀ, (show Jᵀ * J = 1 from hJ), Matrix.one_mul,
      show R * Rᵀ = 1 from hSVD.mul_conjTranspose_right]
  have hQ : Q.PosSemidef := by
    have hD : (Matrix.diagonal (fun i : Fin n => singularValues A i)).PosSemidef :=
      Matrix.posSemidef_diagonal_iff.mpr (fun i => singularValues_nonneg A i)
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hD.mul_mul_conjTranspose_same R
  have hJD : J * Matrix.diagonal (fun i : Fin n => singularValues A i) =
      rectDiag (singularValues A) := by
    ext i j
    simp only [Matrix.mul_diagonal, J, rectDiag_apply]
    split_ifs with hij <;> simp_all
  have hA : U * Q = A := by
    dsimp [U, Q]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Rᵀ R (Matrix.diagonal _ * Rᵀ),
      show Rᵀ * R = 1 from hSVD.conjTranspose_mul_right,
      Matrix.one_mul, ← Matrix.mul_assoc J _ Rᵀ, hJD]
    simpa only [Matrix.mul_assoc] using
      (show A = L * (rectDiag (singularValues A) : Matrix (Fin m) (Fin n) ℝ) * Rᵀ from hSVD.eq).symm
  have hRoot := eq_sqrt_gram_of_isometry_mul_eq hU hQ hA
  refine ⟨U, hU, ?_, ?_⟩
  · rwa [← hRoot]
  · have hDiag : rectDiag (singularValues A) - J = rectangularDiagonal
        (fun i : Fin (min m n) => singularValues A i - 1) := by
      ext i j
      simp only [rectangularDiagonal, J, rectDiag_apply, Matrix.sub_apply]
      by_cases hij : (i : ℕ) = (j : ℕ)
      · have hi : (i : ℕ) < min m n := by omega
        have hj : (j : ℕ) < min m n := by omega
        simp [hij, hj]
      · simp [hij]
    have hDiff : A - U = L * (rectDiag (singularValues A) - J) * Rᵀ := by
      rw [Matrix.mul_sub, Matrix.sub_mul,
        ← show A = L * (rectDiag (singularValues A) : Matrix (Fin m) (Fin n) ℝ) * Rᵀ from hSVD.eq]
    rw [hDiff, ν.right_invariant _ Rᵀ hRt, ν.left_invariant _ L hL, hDiag]

/-- Every polar isometry minimizes the distance to a tall real matrix in
every orthogonally invariant norm, including empty and deficient-rank shapes.
Horn–Johnson 2013, Theorem 7.3.1; uses the full rectangular Mirsky inequality.
atlas: polar-decomposition (partial) -/
theorem invariantNorm_sub_polar_le_sub_isometry_fin {m n : ℕ}
    (ν : OrthogonallyInvariantNorm (Fin m) (Fin n)) (A U V : Matrix (Fin m) (Fin n) ℝ)
    (hCard : n ≤ m) (hU : HasOrthonormalCols U)
    (hA : U * CFC.sqrt (Aᵀ * A) = A) (hV : HasOrthonormalCols V) :
    ν.seminorm (A - U) ≤ ν.seminorm (A - V) := by
  obtain ⟨U₀, hU₀, hA₀, hDistance⟩ := exists_svd_polar_with_distance A hCard ν
  have hGram : (A - U)ᵀ * (A - U) = (A - U₀)ᵀ * (A - U₀) := by
    have hDiff : A - U = U * (CFC.sqrt (Aᵀ * A) - 1) := by
      rw [Matrix.mul_sub, hA, Matrix.mul_one]
    have hDiff₀ : A - U₀ = U₀ * (CFC.sqrt (Aᵀ * A) - 1) := by
      rw [Matrix.mul_sub, hA₀, Matrix.mul_one]
    rw [hDiff, hDiff₀, Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U _, (show Uᵀ * U = 1 from hU), Matrix.one_mul,
      ← Matrix.mul_assoc U₀ᵀ U₀ _, (show U₀ᵀ * U₀ = 1 from hU₀), Matrix.one_mul]
  obtain ⟨O, hO, hEq⟩ := exists_orthogonal_mul_eq_of_gram_eq (A - U) (A - U₀) hGram
  have hNorm : ν.seminorm (A - U) = ν.seminorm (A - U₀) := by
    rw [← hEq, ν.left_invariant _ O hO]
  rw [hNorm, hDistance]
  have hWeak := weaklyMajorized_abs_singularValues_add_sub V (A - V)
  rw [Fintype.card_fin, Fintype.card_fin] at hWeak
  rw [show V + (A - V) = A by abel] at hWeak
  have hσ : (fun i : Fin (min m n) => singularValues V i) = fun _ => (1 : ℝ) := by
    funext i
    exact singularValues_eq_one_of_hasOrthonormalCols hV hCard
      (i.isLt.trans_le (min_le_right _ _))
  change WeaklyMajorized (fun i : Fin (min m n) =>
    |singularValues A i - (fun j : Fin (min m n) => singularValues V j) i|) _ at hWeak
  rw [hσ] at hWeak
  have h := ν.toSymmetricGaugeFin.value_le_of_weaklyMajorized
    (fun i => abs_nonneg (singularValues A i - 1)) hWeak
  rw [SymmetricGauge.value_abs, ν.value_toSymmetricGaugeFin,
    ← ν.seminorm_eq_toSymmetricGaugeFin_singularValues] at h
  exact h

/-- Every polar isometry is a nearest isometry in every invariant norm on
arbitrary finite real matrix indices. Horn–Johnson 2013, Theorem 7.3.1.
atlas: polar-decomposition (partial) -/
theorem invariantNorm_sub_polar_le_sub_isometry {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (ν : OrthogonallyInvariantNorm m n) (A U V : Matrix m n ℝ)
    (hCard : Fintype.card n ≤ Fintype.card m) (hU : HasOrthonormalCols U)
    (hA : U * CFC.sqrt (Aᵀ * A) = A) (hV : HasOrthonormalCols V) :
    ν.seminorm (A - U) ≤ ν.seminorm (A - V) := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  let AF := A.reindex em en
  let UF := U.reindex em en
  let VF := V.reindex em en
  let QF := (CFC.sqrt (Aᵀ * A)).reindex en en
  have hUF : HasOrthonormalCols UF := hU.reindex em en
  have hVF : HasOrthonormalCols VF := hV.reindex em en
  have hQF : QF.PosSemidef := by
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᵀ * A))).submatrix en.symm
  have hAF : UF * QF = AF := by
    rw [← mul_reindex, hA]
  have hRoot := eq_sqrt_gram_of_isometry_mul_eq hUF hQF hAF
  have h := invariantNorm_sub_polar_le_sub_isometry_fin (ν.reindex em en) AF UF VF
    hCard hUF (by rwa [← hRoot]) hVF
  have hBack (M N : Matrix m n ℝ) :
      ((M.reindex em en - N.reindex em en).reindex em.symm en.symm) = M - N := by
    ext i j
    simp [Matrix.reindex_apply]
  simpa only [OrthogonallyInvariantNorm.reindex_seminorm_apply, AF, UF, VF,
    hBack] using h

/-- Transposition transports an invariant norm to the transposed matrix
space. Horn–Johnson §7.4; supports the wide polar minimization theorem. -/
def OrthogonallyInvariantNorm.transpose {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (ν : OrthogonallyInvariantNorm m n) :
    OrthogonallyInvariantNorm n m where
  seminorm := ν.seminorm.comp (Matrix.transposeLinearEquiv n m ℝ ℝ).toLinearMap
  eq_zero_of_map_eq_zero A hA := by
    have h := ν.eq_zero_of_map_eq_zero Aᵀ hA
    apply Matrix.transpose_injective
    exact h
  left_invariant A V hV := by
    change ν.seminorm (V * A)ᵀ = ν.seminorm Aᵀ
    have hVt : HasOrthonormalCols Vᵀ := by
      change Vᵀᵀ * Vᵀ = 1
      rw [Matrix.transpose_transpose]
      exact mul_eq_one_comm.mp hV
    rw [Matrix.transpose_mul, ν.right_invariant _ _ hVt]
  right_invariant A U hU := by
    change ν.seminorm (A * U)ᵀ = ν.seminorm Aᵀ
    have hUt : HasOrthonormalCols Uᵀ := by
      change Uᵀᵀ * Uᵀ = 1
      rw [Matrix.transpose_transpose]
      exact mul_eq_one_comm.mp hU
    rw [Matrix.transpose_mul, ν.left_invariant _ _ hUt]

/-- Every wide polar coisometry is a nearest coisometry in every invariant
norm on arbitrary finite real matrix indices. Horn–Johnson 2013, Thm 7.3.1.
atlas: polar-decomposition (partial) -/
theorem invariantNorm_sub_polar_le_sub_coisometry {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (ν : OrthogonallyInvariantNorm m n) (A U V : Matrix m n ℝ)
    (hCard : Fintype.card m ≤ Fintype.card n) (hU : U * Uᵀ = 1)
    (hA : CFC.sqrt (A * Aᵀ) * U = A) (hV : V * Vᵀ = 1) :
    ν.seminorm (A - U) ≤ ν.seminorm (A - V) := by
  have hUt : HasOrthonormalCols Uᵀ := by
    simpa only [hasOrthonormalCols_iff_conjTranspose_mul_self,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using hU
  have hVt : HasOrthonormalCols Vᵀ := by
    simpa only [hasOrthonormalCols_iff_conjTranspose_mul_self,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using hV
  have hSym : (CFC.sqrt (A * Aᵀ))ᵀ = CFC.sqrt (A * Aᵀ) := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg (A * Aᵀ)).star_eq
  have hAt : Uᵀ * CFC.sqrt (Aᵀᵀ * Aᵀ) = Aᵀ := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hSym] using
      congrArg Matrix.transpose hA
  have h := invariantNorm_sub_polar_le_sub_isometry ν.transpose Aᵀ Uᵀ Vᵀ hCard hUt hAt hVt
  change ν.seminorm (Aᵀ - Uᵀ)ᵀ ≤ ν.seminorm (Aᵀ - Vᵀ)ᵀ at h
  simpa only [Matrix.transpose_sub, Matrix.transpose_transpose] using h

end NLAlib
