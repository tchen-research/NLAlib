import NLAlib.Matrix.Basic.MoorePenrose
import NLAlib.Matrix.Subspaces.OrthogonalProducts
/-!
# Thin singular factorizations

The full positive singular block factors a matrix as `U diag σ Vᴴ` with
orthonormal columns. Its Moore–Penrose inverse is obtained by reciprocating
the diagonal, with no square or full-column-rank assumption on the matrix.
Source: Horn–Johnson, §7.3. Supports DMD, ERA, and Gramian balancing.
-/
noncomputable section
open scoped Matrix
open Matrix
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- A thin singular value factorization retains exactly the positive singular
directions. An ordering of the singular directions is unnecessary here. -/
structure IsThinSVD (A : Matrix m n 𝕜) (U : Matrix m r 𝕜) (V : Matrix n r 𝕜)
    (σ : r → ℝ) : Prop where
  /-- The left singular directions are orthonormal. -/
  left_orth : HasOrthonormalCols U
  /-- The right singular directions are orthonormal. -/
  right_orth : HasOrthonormalCols V
  /-- All retained singular values are positive. -/
  pos : ∀ i, 0 < σ i
  /-- The factorization contains the entire matrix. -/
  eq : A = U * diagonal (fun i => (σ i : 𝕜)) * Vᴴ

/-- A family of positive singular triplets, possibly retaining only some
singular directions. Both triplet equations are required for a truncation. -/
structure IsSingularTripletFamily (A : Matrix m n 𝕜) (U : Matrix m r 𝕜)
    (V : Matrix n r 𝕜) (σ : r → ℝ) : Prop where
  /-- The left singular vectors are orthonormal. -/
  left_orth : HasOrthonormalCols U
  /-- The right singular vectors are orthonormal. -/
  right_orth : HasOrthonormalCols V
  /-- The retained singular values are positive. -/
  pos : ∀ i, 0 < σ i
  /-- The right singular-vector equation. -/
  mul_right : A * V = U * diagonal (fun i => (σ i : 𝕜))
  /-- The adjoint singular-vector equation. -/
  adjoint_mul_left : Aᴴ * U = V * diagonal (fun i => (σ i : 𝕜))

/-- A full thin SVD is, in particular, a positive singular-triplet family. -/
theorem IsThinSVD.isSingularTripletFamily {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsThinSVD A U V σ) :
    IsSingularTripletFamily A U V σ := by
  refine ⟨h.left_orth, h.right_orth, h.pos, ?_, ?_⟩
  · rw [h.eq, Matrix.mul_assoc, h.right_orth.conjTranspose_mul_self, Matrix.mul_one]
  · rw [h.eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      Matrix.mul_assoc,
      h.left_orth.conjTranspose_mul_self, Matrix.mul_one]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j; simp [Matrix.conjTranspose_apply]
    · simp [Matrix.conjTranspose_apply, hij, Ne.symm hij]

/-- Selecting distinct triplets preserves both singular-vector equations. -/
theorem IsSingularTripletFamily.submatrix_cols {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSingularTripletFamily A U V σ)
    {s : Type*} [Fintype s] [DecidableEq s] (e : s ↪ r) :
    IsSingularTripletFamily A (U.submatrix id e) (V.submatrix id e) (fun i => σ (e i)) := by
  refine ⟨h.left_orth.submatrix_cols e, h.right_orth.submatrix_cols e, fun i => h.pos (e i), ?_, ?_⟩
  · have he : A * V.submatrix id e = (A * V).submatrix id e := rfl
    rw [he, h.mul_right]
    ext i j
    simp [Matrix.submatrix_apply, Matrix.mul_diagonal]
  · have he : Aᴴ * U.submatrix id e = (Aᴴ * U).submatrix id e := rfl
    rw [he, h.adjoint_mul_left]
    ext i j
    simp [Matrix.submatrix_apply, Matrix.mul_diagonal]

/-- The pseudoinverse of a real diagonal, also allowing zero diagonal entries. -/
theorem isMoorePenroseInverse_diagonal_ofReal (σ : r → ℝ) :
    IsMoorePenroseInverse (diagonal (fun i => (σ i : 𝕜)))
      (diagonal (fun i => ((σ i)⁻¹ : 𝕜))) := by
  constructor
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    norm_cast
    by_cases h : σ i = 0 <;> simp [h]
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    norm_cast
    by_cases h : σ i = 0 <;> simp [h]
  · ext i j
    by_cases h : i = j
    · subst j; simp [Matrix.diagonal_mul_diagonal, Matrix.conjTranspose_apply]
    · simp [Matrix.diagonal_mul_diagonal, Matrix.conjTranspose_apply, h, Ne.symm h]
  · ext i j
    by_cases h : i = j
    · subst j; simp [Matrix.diagonal_mul_diagonal, Matrix.conjTranspose_apply]
    · simp [Matrix.diagonal_mul_diagonal, Matrix.conjTranspose_apply, h, Ne.symm h]

/-- Reciprocating a thin singular factorization gives the full Moore–Penrose
inverse, at any matrix rank. Horn–Johnson, §7.3. -/
theorem IsThinSVD.moorePenroseInverse_eq {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsThinSVD A U V σ) :
    moorePenroseInverse A = V * diagonal (fun i => ((σ i)⁻¹ : 𝕜)) * Uᴴ := by
  have hp := (isMoorePenroseInverse_diagonal_ofReal (𝕜 := 𝕜) σ).unitary_transform
    U V h.left_orth h.right_orth
  rw [← h.eq] at hp
  exact (isMoorePenroseInverse A).unique hp

/-- The number of columns in a thin SVD is the matrix rank. -/
theorem IsThinSVD.rank_eq_card {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsThinSVD A U V σ) :
    A.rank = Fintype.card r := by
  classical
  have hD : IsUnit (diagonal fun i => (σ i : 𝕜)) := by
    rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
    intro i
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast (h.pos i).ne')
  have hcomp : Uᴴ * A * V = diagonal (fun i => (σ i : 𝕜)) := by
    rw [h.eq, Matrix.mul_assoc, Matrix.mul_assoc,
      h.right_orth.conjTranspose_mul_self, Matrix.mul_one,
      ← Matrix.mul_assoc, h.left_orth.conjTranspose_mul_self, Matrix.one_mul]
  apply le_antisymm
  · rw [h.eq]
    exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_left _ _).trans U.rank_le_card_width)
  · calc
      Fintype.card r = (diagonal fun i => (σ i : 𝕜)).rank :=
        (Matrix.rank_of_isUnit _ hD).symm
      _ = (Uᴴ * A * V).rank := congrArg Matrix.rank hcomp.symm
      _ ≤ (Uᴴ * A).rank := Matrix.rank_mul_le_left _ _
      _ ≤ A.rank := Matrix.rank_mul_le_right _ _

/-- The row-space projector from a thin SVD. -/
theorem IsThinSVD.moorePenroseInverse_mul_eq {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsThinSVD A U V σ) :
    moorePenroseInverse A * A = V * Vᴴ := by
  have hD : (diagonal fun i => ((σ i)⁻¹ : 𝕜)) * diagonal (fun i => (σ i : 𝕜)) =
      (1 : Matrix r r 𝕜) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j; simp [(h.pos i).ne']
    · simp [hij]
  rw [h.moorePenroseInverse_eq, h.eq]
  calc
    _ = V * ((diagonal fun i => ((σ i)⁻¹ : 𝕜)) * (Uᴴ * U) *
        diagonal (fun i => (σ i : 𝕜))) * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h.left_orth.conjTranspose_mul_self, Matrix.mul_one, hD, Matrix.mul_one]

/-- The column-space projector from a thin SVD. -/
theorem IsThinSVD.mul_moorePenroseInverse_eq {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsThinSVD A U V σ) :
    A * moorePenroseInverse A = U * Uᴴ := by
  have hD : (diagonal fun i => (σ i : 𝕜)) * diagonal (fun i => ((σ i)⁻¹ : 𝕜)) =
      (1 : Matrix r r 𝕜) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j; simp [(h.pos i).ne']
    · simp [hij]
  rw [h.moorePenroseInverse_eq, h.eq]
  calc
    _ = U * ((diagonal fun i => (σ i : 𝕜)) * (Vᴴ * V) *
        diagonal (fun i => ((σ i)⁻¹ : 𝕜))) * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h.right_orth.conjTranspose_mul_self, Matrix.mul_one, hD, Matrix.mul_one]

/-- Every finite matrix has a full positive thin SVD, including rank zero.
The retained values are the library's actual ordered singular values. -/
theorem exists_isThinSVD [DecidableEq n] (A : Matrix m n 𝕜) :
    ∃ (U : Matrix m (Fin A.rank) 𝕜) (V : Matrix n (Fin A.rank) 𝕜),
      IsThinSVD A U V (fun i => singularValues A i) := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD A
  let em := Fin.castLEEmb A.rank_le_card_height
  let en := Fin.castLEEmb A.rank_le_card_width
  refine ⟨U.submatrix id em, V.submatrix id en,
    HasOrthonormalCols.submatrix_cols h.conjTranspose_mul_left em,
    HasOrthonormalCols.submatrix_cols h.conjTranspose_mul_right en,
    fun i => (singularValues_pos_iff A i).mpr i.isLt, ?_⟩
  ext i j
  rw [h.apply i j]
  let e := Fin.castLEEmb (le_min A.rank_le_card_height A.rank_le_card_width)
  let g : Fin (min (Fintype.card m) (Fintype.card n)) → 𝕜 := fun k =>
    (singularValues A k : 𝕜) *
      U i (Fin.castLE (min_le_left _ _) k) * star (V j (Fin.castLE (min_le_right _ _) k))
  have hs : ((U.submatrix id em * diagonal (fun i : Fin A.rank => (singularValues A i : 𝕜))) *
      (V.submatrix id en)ᴴ) i j = ∑ k ∈ Finset.univ.map e, g k := by
    rw [Finset.sum_map]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      Matrix.submatrix_apply, id_eq]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [g, e, em, en]
    have hem : Fin.castLE (min_le_left (Fintype.card m) (Fintype.card n))
        (Fin.castLE (le_min A.rank_le_card_height A.rank_le_card_width) k) =
        Fin.castLE A.rank_le_card_height k := Fin.ext rfl
    have hen : Fin.castLE (min_le_right (Fintype.card m) (Fintype.card n))
        (Fin.castLE (le_min A.rank_le_card_height A.rank_le_card_width) k) =
        Fin.castLE A.rank_le_card_width k := Fin.ext rfl
    rw [hem, hen]
    ring
  rw [hs]
  change (∑ k, g k) = _
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k hk hnot
  have hkr : A.rank ≤ k.val := by
    by_contra hlt
    apply hnot
    exact Finset.mem_map.mpr ⟨⟨k, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
  dsimp [g]
  rw [singularValues_eq_zero_of_rank_le A hkr]
  simp

/-- Every positive leading singular block is realized by actual orthonormal
singular vectors, without assumptions about repeated singular values. -/
theorem exists_isSingularTripletFamily [DecidableEq n] (A : Matrix m n 𝕜)
    (k : ℕ) (hk : k ≤ A.rank) :
    ∃ (U : Matrix m (Fin k) 𝕜) (V : Matrix n (Fin k) 𝕜),
      IsSingularTripletFamily A U V (fun i => singularValues A i) := by
  obtain ⟨U, V, h⟩ := exists_isThinSVD A
  exact ⟨_, _, h.isSingularTripletFamily.submatrix_cols (Fin.castLEEmb hk)⟩

end NLAlib
