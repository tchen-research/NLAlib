import NLAlib.Matrix.Basic.MoorePenroseTransformations
import Mathlib.Tactic.Abel

/-!
# Generalized Schur complements (Albert's criterion)

* `schurComplement A B C = C − Bᵀ A⁺ B`, the Schur complement of the block `A` in
  `M = [[A, B], [Bᵀ, C]]` with the Moore–Penrose inverse `A⁺` (no invertibility needed).
* Albert's criterion `M ⪰ 0 ⟺ A ⪰ 0, (I − AA⁺)B = 0, M / A ⪰ 0` (`posSemidef_fromBlocks_iff`),
  proved from the Moore–Penrose square completion
  (`dotProduct_fromBlocks_eq_generalized_schur_square`).
* The attained variational characterisation: `xᵀ (M / A) x` is the least value of
  `(y, x)ᵀ M (y, x)` over `y` (`isLeast_generalized_schur_quadratic`,
  `dotProduct_schurComplement_mulVec_le`), attained at `y = −A⁺Bx`
  (`dotProduct_schurComplement_mulVec_eq`).
* The order bounds `0 ⪯ M / A ⪯ C` (`generalized_schur_nonneg_and_le`,
  `posSemidef_sub_schurComplement`), and the bundle `generalized_schur_complement`.

All index types are arbitrary finite types, including empty blocks. The leading-pivot
complement used by Gaussian elimination and Cholesky is `pivotSchur`
(`Matrix/Basic/SchurComplement.lean`).

Source: Albert 1969, Theorem 1; cf. Horn–Johnson 2013, §7.7 for related results.
Atlas: `generalized-schur-complement-psd`.
-/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib

set_option backward.isDefEq.respectTransparency false

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-- The **generalized Schur complement** `M / A = C − Bᵀ A⁺ B` of the block `A` in
`M = [[A, B], [Bᵀ, C]]`, with the Moore–Penrose inverse `A⁺` (`moorePenroseInverse`), so no
invertibility is needed. Albert 1969, §1; Horn–Johnson 2013, §7.7. For invertible `A` this is
the classical Schur complement `C − Bᵀ A⁻¹ B` (`moorePenroseInverse` of an invertible matrix is
its inverse). -/
def schurComplement (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ) :
    Matrix n n ℝ :=
  C - Bᵀ * moorePenroseInverse A * B

omit [DecidableEq m] in
/-- A PSD block matrix kills every cross-block vector coming from the kernel
of its leading block. Albert 1969, Theorem 1; supports
`generalized-schur-complement-psd`. -/
theorem transpose_mulVec_eq_zero_of_fromBlocks_posSemidef
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hM : (Matrix.fromBlocks A B Bᵀ C).PosSemidef) (z : m → ℝ)
    (hz : A *ᵥ z = 0) : Bᵀ *ᵥ z = 0 := by
  have hq : (Sum.elim z (0 : n → ℝ)) ⬝ᵥ
      Matrix.fromBlocks A B Bᵀ C *ᵥ Sum.elim z (0 : n → ℝ) = 0 := by
    simp [Matrix.fromBlocks_mulVec, hz, sumElim_dotProduct_sumElim]
  have hv := (hM.dotProduct_mulVec_zero_iff (Sum.elim z (0 : n → ℝ))).mp
    (by simpa only [star_trivial] using hq)
  have h := congrArg (fun v : m ⊕ n → ℝ => v ∘ Sum.inr) hv
  simpa [Matrix.fromBlocks_mulVec] using h

/-- Positive semidefiniteness forces the exact range compatibility for a
singular leading block. Albert 1969, Theorem 1; supports
`generalized-schur-complement-psd`. -/
theorem one_sub_mul_moorePenroseInverse_mul_eq_zero_of_fromBlocks_posSemidef
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hM : (Matrix.fromBlocks A B Bᵀ C).PosSemidef) :
    (1 - A * moorePenroseInverse A) * B = 0 := by
  have hA : A.PosSemidef := by
    exact hM.submatrix (Sum.inl : m → m ⊕ n)
  have hAt : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have hAd := Matrix.IsHermitian.moorePenroseInverse (A := A) hA.isHermitian
  have hAdt : (moorePenroseInverse A)ᵀ = moorePenroseInverse A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hAd.eq
  have hRowCol : moorePenroseInverse A * A = A * moorePenroseInverse A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, hAt,
      hAdt] using (mul_moorePenroseInverse_isHermitian A).eq
  let F : Matrix m m ℝ := 1 - moorePenroseInverse A * A
  have hFs : Fᵀ = F := by
    dsimp [F]
    rw [Matrix.transpose_sub, Matrix.transpose_one, ← Matrix.conjTranspose_eq_transpose_of_trivial,
      (moorePenroseInverse_mul_isHermitian A).eq]
  have hAF : A * F = 0 := by
    dsimp [F]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, mul_moorePenroseInverse_mul, sub_self]
  have hFid : F * F = F := by
    dsimp [F]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, show (moorePenroseInverse A * A) * (moorePenroseInverse A * A) =
        moorePenroseInverse A * A from moorePenroseInverse_mul_isIdempotentElem A]
    abel
  have hFB : F * B = 0 := by
    apply Matrix.ext
    intro i j
    let z : m → ℝ := F *ᵥ B.col j
    have hz : A *ᵥ z = 0 := by
      dsimp [z]
      rw [Matrix.mulVec_mulVec, hAF, Matrix.zero_mulVec]
    have hBz := transpose_mulVec_eq_zero_of_fromBlocks_posSemidef hM z hz
    have hDot : B.col j ⬝ᵥ z = 0 := by
      simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.col,
        Pi.zero_apply] using congrFun hBz j
    have hFz : F *ᵥ z = z := by
      dsimp [z]
      rw [Matrix.mulVec_mulVec, hFid]
    have hzz : z ⬝ᵥ z = 0 := by
      calc
        z ⬝ᵥ z = B.col j ⬝ᵥ Fᵀ *ᵥ z :=
          (Matrix.dotProduct_transpose_mulVec F (B.col j) z).symm
        _ = B.col j ⬝ᵥ z := by rw [hFs, hFz]
        _ = 0 := hDot
    have hz0 : z = 0 := dotProduct_self_eq_zero.mp hzz
    simpa [z, Matrix.mul_apply, Matrix.mulVec, Matrix.col, dotProduct] using congrFun hz0 i
  simpa only [F, hRowCol] using hFB

omit [DecidableEq m] in
/-- The completed square for a singular leading block uses its actual
Moore--Penrose inverse. Albert 1969, Theorem 1; supports
`generalized-schur-complement-psd`. -/
theorem dotProduct_fromBlocks_eq_generalized_schur_square
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hA : A.IsSymm) (hRange : A * moorePenroseInverse A * B = B)
    (y : m → ℝ) (x : n → ℝ) :
    Sum.elim y x ⬝ᵥ Matrix.fromBlocks A B Bᵀ C *ᵥ Sum.elim y x =
      (y + moorePenroseInverse A *ᵥ (B *ᵥ x)) ⬝ᵥ
        A *ᵥ (y + moorePenroseInverse A *ᵥ (B *ᵥ x)) +
      x ⬝ᵥ schurComplement A B C *ᵥ x := by
  rw [schurComplement]
  have hAx : A *ᵥ (moorePenroseInverse A *ᵥ (B *ᵥ x)) = B *ᵥ x := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hRange]
  have hCross : (moorePenroseInverse A *ᵥ (B *ᵥ x)) ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := by
    simpa only [hA.eq, hAx] using
      (Matrix.dotProduct_transpose_mulVec A (moorePenroseInverse A *ᵥ (B *ᵥ x)) y)
  have hTail : (moorePenroseInverse A *ᵥ (B *ᵥ x)) ⬝ᵥ (B *ᵥ x) =
      x ⬝ᵥ (Bᵀ * moorePenroseInverse A * B) *ᵥ x := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
  simp only [Matrix.fromBlocks_mulVec, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    sumElim_dotProduct_sumElim, Matrix.mulVec_add, Matrix.sub_mulVec,
    add_dotProduct, dotProduct_add, dotProduct_sub, hAx, hCross, hTail,
    Matrix.dotProduct_transpose_mulVec]
  ring

/-- **Albert's criterion**: `[[A, B], [Bᵀ, C]] ⪰ 0` iff `A ⪰ 0`, `(I − AA⁺) B = 0` (range of `B`
inside range of `A`) and `M / A = C − Bᵀ A⁺ B ⪰ 0`, with the actual Moore–Penrose inverse and its
exact range condition. No symmetry hypotheses are needed: each side forces `A` and `C`
symmetric. Albert 1969, Thm 1; cf. Horn–Johnson 2013, Theorems 7.7.7 and 7.7.9 for related
matrix-order results.
Proof: (⇒) `A ⪰ 0` and `C ⪰ 0` are principal submatrices; for `z ∈ ker A`,
`(z, 0)ᵀ M (z, 0) = 0` forces `Bᵀ z = 0`, i.e. `range B ⊆ range A`, which is `(I − AA⁺)B = 0`;
then with `y = −A⁺Bx` the quadratic form is `xᵀ(M/A)x ≥ 0`. (⇐) the square completion
`dotProduct_fromBlocks_eq_generalized_schur_square`.
atlas: generalized-schur-complement-psd (partial) -/
theorem posSemidef_fromBlocks_iff
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ) :
    (Matrix.fromBlocks A B Bᵀ C).PosSemidef ↔
      A.PosSemidef ∧ (1 - A * moorePenroseInverse A) * B = 0 ∧
        (schurComplement A B C).PosSemidef := by
  constructor
  · intro hM
    have hA : A.PosSemidef := by
      exact hM.submatrix (Sum.inl : m → m ⊕ n)
    have hC : C.PosSemidef := by
      exact hM.submatrix (Sum.inr : n → m ⊕ n)
    have hCompat := one_sub_mul_moorePenroseInverse_mul_eq_zero_of_fromBlocks_posSemidef hM
    have hRange : A * moorePenroseInverse A * B = B := by
      rw [Matrix.sub_mul, Matrix.one_mul] at hCompat
      exact (sub_eq_zero.mp hCompat).symm
    refine ⟨hA, hCompat, ?_⟩
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hC.isHermitian.sub
      ((Matrix.PosSemidef.moorePenroseInverse hA).conjTranspose_mul_mul_same B).isHermitian, ?_⟩
    intro x
    have h := hM.dotProduct_mulVec_nonneg (Sum.elim (-(moorePenroseInverse A *ᵥ (B *ᵥ x))) x)
    simp only [star_trivial] at h ⊢
    rw [dotProduct_fromBlocks_eq_generalized_schur_square A B C hA.isHermitian hRange] at h
    simpa only [neg_add_cancel, Matrix.zero_mulVec, zero_dotProduct, zero_add] using h
  · rintro ⟨hA, hCompat, hS⟩
    have hRange : A * moorePenroseInverse A * B = B := by
      rw [Matrix.sub_mul, Matrix.one_mul] at hCompat
      exact (sub_eq_zero.mp hCompat).symm
    have hCorr := (Matrix.PosSemidef.moorePenroseInverse hA).conjTranspose_mul_mul_same B
    have hC : C.IsHermitian := by
      simpa only [schurComplement, Matrix.conjTranspose_eq_transpose_of_trivial,
        sub_add_cancel] using hS.isHermitian.add hCorr.isHermitian
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hA.isHermitian.fromBlocks (by simp) hC, ?_⟩
    intro z
    have hz : z = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) := by ext i; cases i <;> rfl
    rw [hz]
    simp only [star_trivial]
    rw [dotProduct_fromBlocks_eq_generalized_schur_square A B C hA.isHermitian hRange]
    exact add_nonneg (by simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg _)
      (by simpa only [star_trivial] using hS.dotProduct_mulVec_nonneg _)

/-- The generalized Schur quadratic form is the attained minimum over the
leading block variable: `xᵀ (M / A) x = min_y (y, x)ᵀ M (y, x)` for `M ⪰ 0`.
Albert 1969, Theorem 1.
atlas: generalized-schur-complement-psd (partial) -/
theorem isLeast_generalized_schur_quadratic
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hM : (Matrix.fromBlocks A B Bᵀ C).PosSemidef) (x : n → ℝ) :
    IsLeast (Set.range (fun y : m → ℝ =>
      Sum.elim y x ⬝ᵥ Matrix.fromBlocks A B Bᵀ C *ᵥ Sum.elim y x))
      (x ⬝ᵥ schurComplement A B C *ᵥ x) := by
  obtain ⟨hA, hCompat, _⟩ := (posSemidef_fromBlocks_iff A B C).mp hM
  have hRange : A * moorePenroseInverse A * B = B := by
    rw [Matrix.sub_mul, Matrix.one_mul] at hCompat
    exact (sub_eq_zero.mp hCompat).symm
  constructor
  · refine ⟨-(moorePenroseInverse A *ᵥ (B *ᵥ x)), ?_⟩
    dsimp only
    rw [dotProduct_fromBlocks_eq_generalized_schur_square A B C hA.isHermitian hRange]
    simp
  · rintro _ ⟨y, rfl⟩
    dsimp only
    rw [dotProduct_fromBlocks_eq_generalized_schur_square A B C hA.isHermitian hRange]
    exact le_add_of_nonneg_left (by simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg _)

/-- **Variational characterisation, lower bound**: for `M = [[A, B], [Bᵀ, C]] ⪰ 0`,
`xᵀ (M / A) x ≤ (y, x)ᵀ M (y, x)` for every `y`. Albert 1969, Thm 1; cf. Horn–Johnson 2013, §7.7
for related results. The lower-bound half of `isLeast_generalized_schur_quadratic`.
atlas: generalized-schur-complement-psd (partial) -/
theorem dotProduct_schurComplement_mulVec_le {A : Matrix m m ℝ} {B : Matrix m n ℝ}
    {C : Matrix n n ℝ} (hM : (Matrix.fromBlocks A B Bᵀ C).PosSemidef) (x : n → ℝ) (y : m → ℝ) :
    x ⬝ᵥ (schurComplement A B C *ᵥ x) ≤
      Sum.elim y x ⬝ᵥ (Matrix.fromBlocks A B Bᵀ C *ᵥ Sum.elim y x) :=
  (isLeast_generalized_schur_quadratic A B C hM x).2 ⟨y, rfl⟩

/-- **Variational characterisation, attainment**: for `M = [[A, B], [Bᵀ, C]] ⪰ 0` the minimum over
`y` of `(y, x)ᵀ M (y, x)` is attained at `y = −A⁺Bx` and equals `xᵀ (M / A) x`.
Albert 1969, Thm 1; cf. Horn–Johnson 2013, §7.7 for related results.
Proof: the square completion `dotProduct_fromBlocks_eq_generalized_schur_square` with
`y + A⁺Bx = 0`.
atlas: generalized-schur-complement-psd (partial) -/
theorem dotProduct_schurComplement_mulVec_eq {A : Matrix m m ℝ} {B : Matrix m n ℝ}
    {C : Matrix n n ℝ} (hM : (Matrix.fromBlocks A B Bᵀ C).PosSemidef) (x : n → ℝ) :
    x ⬝ᵥ (schurComplement A B C *ᵥ x) =
      Sum.elim (-(moorePenroseInverse A * B) *ᵥ x) x ⬝ᵥ
        (Matrix.fromBlocks A B Bᵀ C *ᵥ Sum.elim (-(moorePenroseInverse A * B) *ᵥ x) x) := by
  obtain ⟨hA, hCompat, _⟩ := (posSemidef_fromBlocks_iff A B C).mp hM
  have hRange : A * moorePenroseInverse A * B = B := by
    rw [Matrix.sub_mul, Matrix.one_mul] at hCompat
    exact (sub_eq_zero.mp hCompat).symm
  rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_fromBlocks_eq_generalized_schur_square A B C hA.isHermitian hRange]
  simp

/-- Generalized Schur complements lie between zero and the trailing block:
`0 ⪯ M / A ⪯ C` for `M ⪰ 0`. Albert 1969, Theorem 1.
atlas: generalized-schur-complement-psd (partial) -/
theorem generalized_schur_nonneg_and_le
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hM : (Matrix.fromBlocks A B Bᵀ C).PosSemidef) :
    0 ≤ schurComplement A B C ∧ schurComplement A B C ≤ C := by
  obtain ⟨hA, _, hS⟩ := (posSemidef_fromBlocks_iff A B C).mp hM
  refine ⟨hS.nonneg, ?_⟩
  rw [Matrix.le_iff, schurComplement, sub_sub_cancel]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.PosSemidef.moorePenroseInverse hA).conjTranspose_mul_mul_same B

omit [DecidableEq m] in
/-- **Schur complement below the trailing block**: for `A ⪰ 0`, `C − M / A = Bᵀ A⁺ B ⪰ 0`
(the upper half of `0 ⪯ M / A ⪯ C`, needing only `A ⪰ 0`; the lower half is part of
`posSemidef_fromBlocks_iff`).
Proof: `A⁺` is symmetric and `A⁺ = A⁺ A A⁺`, so `Bᵀ A⁺ B = (A⁺B)ᵀ A (A⁺B)`.
Albert 1969, Thm 1; cf. Horn–Johnson 2013, §7.7 for related results.
atlas: generalized-schur-complement-psd (partial) -/
theorem posSemidef_sub_schurComplement {A : Matrix m m ℝ} {B : Matrix m n ℝ}
    {C : Matrix n n ℝ} (hA : A.PosSemidef) :
    (C - schurComplement A B C).PosSemidef := by
  have hAs : Aᵀ = A := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  have hP : (moorePenroseInverse A)ᵀ = moorePenroseInverse A := by
    rw [← moorePenroseInverse_transpose, hAs]
  have h : C - schurComplement A B C =
      (moorePenroseInverse A * B)ᴴ * A * (moorePenroseInverse A * B) := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, hP, schurComplement,
      sub_sub_cancel]
    conv_lhs => rw [← moorePenroseInverse_mul_moorePenroseInverse A]
    simp only [Matrix.mul_assoc]
  rw [h]
  exact hA.conjTranspose_mul_mul_same _

/-- Complete singular-pivot Schur contract: Albert's positive-semidefinite criterion,
attained quadratic minimum at the explicit Moore--Penrose minimizer `y = −A⁺Bx`, and both
order bounds `0 ⪯ M / A ⪯ C`. Arbitrary finite block sizes, including empty blocks, are covered.
Albert 1969, Theorem 1; cf. Horn--Johnson 2013, Theorems 7.7.7 and 7.7.9
(related Schur complement results; Albert's pseudoinverse criterion is not stated there).
atlas: generalized-schur-complement-psd -/
theorem generalized_schur_complement (A : Matrix m m ℝ) (B : Matrix m n ℝ)
    (C : Matrix n n ℝ) :
    ((Matrix.fromBlocks A B Bᵀ C).PosSemidef ↔
      A.PosSemidef ∧ (1 - A * moorePenroseInverse A) * B = 0 ∧
        (schurComplement A B C).PosSemidef) ∧
    ((Matrix.fromBlocks A B Bᵀ C).PosSemidef →
      (∀ x : n → ℝ,
        IsLeast (Set.range (fun y : m → ℝ =>
          Sum.elim y x ⬝ᵥ Matrix.fromBlocks A B Bᵀ C *ᵥ Sum.elim y x))
          (x ⬝ᵥ schurComplement A B C *ᵥ x) ∧
        x ⬝ᵥ schurComplement A B C *ᵥ x =
          Sum.elim (-(moorePenroseInverse A * B) *ᵥ x) x ⬝ᵥ
            Matrix.fromBlocks A B Bᵀ C *ᵥ Sum.elim (-(moorePenroseInverse A * B) *ᵥ x) x) ∧
      (0 ≤ schurComplement A B C ∧ schurComplement A B C ≤ C)) := by
  refine ⟨posSemidef_fromBlocks_iff A B C, ?_⟩
  intro hM
  exact ⟨fun x => ⟨isLeast_generalized_schur_quadratic A B C hM x,
    dotProduct_schurComplement_mulVec_eq hM x⟩,
    generalized_schur_nonneg_and_le A B C hM⟩

end NLAlib
