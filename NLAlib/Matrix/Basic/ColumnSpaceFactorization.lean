import NLAlib.Matrix.Basic.RankFactorization
import NLAlib.Matrix.Basic.MoorePenrose

/-! # Range-preserving padded matrix generators -/
noncomputable section
open scoped Matrix
namespace NLAlib
variable {K m n p q : Type*} [RCLike K] [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

omit [Fintype m] [DecidableEq m] in
/-- A rank bound admits padded generators with exactly the original column
space; the extra coordinates do not introduce spurious directions. -/
theorem exists_mul_range_eq_of_rank_le (A : Matrix m n K) (k : ℕ) (hk : A.rank ≤ k) :
    ∃ U : Matrix m (Fin k) K, ∃ T : Matrix (Fin k) n K,
      A = U * T ∧ LinearMap.range U.mulVecLin = LinearMap.range A.mulVecLin := by
  classical
  have hdim : Module.finrank K (LinearMap.range A.mulVecLin) ≤ Module.finrank K (Fin k → K) := by
    simpa [Matrix.rank] using hk
  obtain ⟨e, he⟩ := finrank_le_iff_exists_linearMap.mp hdim
  obtain ⟨l, hl⟩ := e.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr he)
  let f := (LinearMap.range A.mulVecLin).subtype.comp l
  let g := e.comp A.mulVecLin.rangeRestrict
  let U := LinearMap.toMatrix' f
  let T := LinearMap.toMatrix' g
  have hA : A = U * T := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro x
    funext i
    exact (congrArg (fun z : LinearMap.range A.mulVecLin => z.val i)
      (DFunLike.congr_fun hl (A.mulVecLin.rangeRestrict x))).symm
  refine ⟨U,T,hA,le_antisymm ?_ ?_⟩
  · rintro x ⟨v,rfl⟩
    have hv : U *ᵥ v = f v := by
      change Matrix.toLin' (LinearMap.toMatrix' f) v = f v
      rw [Matrix.toLin'_toMatrix']
    rw [Matrix.mulVecLin_apply, hv]
    exact (l v).property
  · rintro x ⟨v,rfl⟩
    refine ⟨T *ᵥ v, ?_⟩
    change U *ᵥ (T *ᵥ v) = A *ᵥ v
    rw [Matrix.mulVec_mulVec, ← hA]

omit [Fintype m] [DecidableEq m] [DecidableEq p] in
/-- A column-space inclusion is equivalent to a right factorization. -/
theorem exists_mul_of_range_le (U : Matrix m p K) (X : Matrix m n K)
    (h : LinearMap.range X.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    ∃ E : Matrix p n K, X = U * E := by
  classical
  have hx (j : n) : ∃ v : p → K, U *ᵥ v = X.col j := by
    apply h
    exact ⟨Pi.single j 1, by ext i; simp [Matrix.mulVec_single]⟩
  choose E hE using hx
  refine ⟨fun i j => E j i, ?_⟩
  ext i j
  exact (congrFun (hE j) i).symm

/-- The actual Moore–Penrose range projector fixes every matrix whose columns
belong to the projected range. -/
theorem mul_moorePenroseInverse_mul_eq_of_range_le (U : Matrix m p K) (X : Matrix m n K)
    (h : LinearMap.range X.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    U * moorePenroseInverse U * X = X := by
  obtain ⟨E,rfl⟩ := exists_mul_of_range_le U X h
  rw [← Matrix.mul_assoc, (isMoorePenroseInverse U).mul_mul_eq]

/-- Simultaneous row/column space inclusions yield an actual two-sided
coupling through the chosen padded bases. -/
theorem exists_mul_mul_conjTranspose_of_ranges (U : Matrix m p K) (V : Matrix n q K)
    (X : Matrix m n K) (hU : LinearMap.range X.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hV : LinearMap.range Xᴴ.mulVecLin ≤ LinearMap.range V.mulVecLin) :
    ∃ C : Matrix p q K, X = U * C * Vᴴ := by
  have hL := mul_moorePenroseInverse_mul_eq_of_range_le U X hU
  have hR := congrArg Matrix.conjTranspose (mul_moorePenroseInverse_mul_eq_of_range_le V Xᴴ hV)
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at hR
  refine ⟨moorePenroseInverse U * X * (moorePenroseInverse V)ᴴ, ?_⟩
  calc
    X = X * (moorePenroseInverse V)ᴴ * Vᴴ := by simpa only [Matrix.mul_assoc] using hR.symm
    _ = (U * moorePenroseInverse U * X) * (moorePenroseInverse V)ᴴ * Vᴴ := by rw [hL]
    _ = _ := by simp only [Matrix.mul_assoc]

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
/-- Multiplication cannot enlarge the left factor's column space. -/
theorem range_mulVecLin_mul_le (A : Matrix m p K) (B : Matrix p n K) :
    LinearMap.range (A * B).mulVecLin ≤ LinearMap.range A.mulVecLin := by
  rw [Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
/-- Selecting or repeating columns can only shrink the column space. -/
theorem range_submatrix_cols_le (A : Matrix m n K) (f : p → n) :
    LinearMap.range (A.submatrix id f).mulVecLin ≤ LinearMap.range A.mulVecLin := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  exact Submodule.subset_span ⟨f j,rfl⟩

/-- Row restriction preserves an inclusion of column spaces. -/
theorem range_submatrix_rows_le_of_range_le (X : Matrix m n K) (U : Matrix m p K)
    (f : q → m) (h : LinearMap.range X.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    LinearMap.range (X.submatrix f id).mulVecLin ≤ LinearMap.range (U.submatrix f id).mulVecLin := by
  obtain ⟨E,rfl⟩ := exists_mul_of_range_le U X h
  have he : (U * E).submatrix f id = (U.submatrix f id) * E := by ext i j; rfl
  rw [he]
  exact range_mulVecLin_mul_le _ _

end NLAlib
