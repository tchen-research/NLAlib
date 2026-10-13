import NLAlib.Matrix.Basic.MoorePenroseTransformations
import Mathlib.Tactic.Abel

/-!
# Generalized Schur complements (Albert's criterion)

* `generalizedSchurComplement A B C = C − Bᴴ A⁺ B`, the Schur complement of the block `A` in
  `M = [[A, B], [Bᴴ, C]]` with the Moore–Penrose inverse `A⁺` (no invertibility needed), over
  `[RCLike 𝕜]`.
* Albert's criterion `M ⪰ 0 ⟺ A ⪰ 0, (I − AA⁺)B = 0, M / A ⪰ 0` (`posSemidef_fromBlocks_iff`),
  proved from the Moore–Penrose square completion
  (`dotProduct_fromBlocks_eq_generalizedSchurComplement_square`).
* The attained variational characterisation: `x̄ᵀ (M / A) x` is the least value of
  `(y, x)ᴴ M (y, x)` over `y` (`isLeast_generalizedSchurComplement_quadratic`,
  `dotProduct_generalizedSchurComplement_mulVec_le`), attained at `y = −A⁺Bx`
  (`dotProduct_generalizedSchurComplement_mulVec_eq`).
* The order bounds `0 ⪯ M / A ⪯ C` (`generalizedSchurComplement_nonneg`,
  `generalizedSchurComplement_le`).

All index types are arbitrary finite types, including empty blocks. The leading-pivot
complement used by Gaussian elimination and Cholesky is `pivotSchur`
(`Matrix/Basic/SchurComplement.lean`).

Source: Albert 1969, Theorem 1; cf. Horn–Johnson 2013, §7.7 for related results.
Atlas: `generalized-schur-complement-psd`.
-/

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

omit [DecidableEq m] in
/-- The **generalized Schur complement** `M / A = C − Bᴴ A⁺ B` of the block `A` in
`M = [[A, B], [Bᴴ, C]]`, with the Moore–Penrose inverse `A⁺` (`moorePenroseInverse`), so no
invertibility is needed. Albert 1969, §1; Horn–Johnson 2013, §7.7. For invertible `A` this is
the classical Schur complement `C − Bᴴ A⁻¹ B` (`moorePenroseInverse` of an invertible matrix is
its inverse). -/
def generalizedSchurComplement (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) (C : Matrix n n 𝕜) :
    Matrix n n 𝕜 :=
  C - Bᴴ * moorePenroseInverse A * B

omit [DecidableEq m] in
/-- `star (M v) ⬝ w = star v ⬝ (Mᴴ w)` (proof helper). -/
private theorem star_mulVec_dotProduct {p q : Type*} [Fintype p] [Fintype q]
    (M : Matrix p q 𝕜) (v : q → 𝕜) (w : p → 𝕜) :
    star (M *ᵥ v) ⬝ᵥ w = star v ⬝ᵥ (Mᴴ *ᵥ w) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]

omit [Fintype m] [Fintype n] [DecidableEq m] in
private theorem star_sumElim (y : m → 𝕜) (x : n → 𝕜) :
    star (Sum.elim y x) = Sum.elim (star y) (star x) := by
  ext i; cases i <;> rfl

omit [DecidableEq m] in
/-- A PSD block matrix kills every cross-block vector coming from the kernel of its leading
block: `A z = 0 ⟹ Bᴴ z = 0`. Albert 1969, Theorem 1; supports
`generalized-schur-complement-psd`. -/
theorem conjTranspose_mulVec_eq_zero_of_fromBlocks_posSemidef
    {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (hM : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) (z : m → 𝕜)
    (hz : A *ᵥ z = 0) : Bᴴ *ᵥ z = 0 := by
  have hq : star (Sum.elim z (0 : n → 𝕜)) ⬝ᵥ
      Matrix.fromBlocks A B Bᴴ C *ᵥ Sum.elim z (0 : n → 𝕜) = 0 := by
    simp [Matrix.fromBlocks_mulVec, hz, star_sumElim, sumElim_dotProduct_sumElim]
  have hv := (hM.dotProduct_mulVec_zero_iff (Sum.elim z (0 : n → 𝕜))).mp hq
  have h := congrArg (fun v : m ⊕ n → 𝕜 => v ∘ Sum.inr) hv
  simpa [Matrix.fromBlocks_mulVec] using h

/-- Positive semidefiniteness forces the range compatibility `(I − A A⁺) B = 0` for a singular
leading block. Albert 1969, Theorem 1; supports `generalized-schur-complement-psd`. -/
theorem one_sub_mul_moorePenroseInverse_mul_eq_zero_of_fromBlocks_posSemidef
    {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (hM : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    (1 - A * moorePenroseInverse A) * B = 0 := by
  have hA : A.PosSemidef := hM.submatrix (Sum.inl : m → m ⊕ n)
  have hAh : Aᴴ = A := hA.isHermitian.eq
  have hAdh : (moorePenroseInverse A)ᴴ = moorePenroseInverse A :=
    (Matrix.IsHermitian.moorePenroseInverse hA.isHermitian).eq
  have hRowCol : moorePenroseInverse A * A = A * moorePenroseInverse A := by
    have h := (mul_moorePenroseInverse_isHermitian A).eq
    rwa [Matrix.conjTranspose_mul, hAh, hAdh] at h
  let F : Matrix m m 𝕜 := 1 - moorePenroseInverse A * A
  have hFh : Fᴴ = F := by
    simp only [F, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      (moorePenroseInverse_mul_isHermitian A).eq]
  have hAF : A * F = 0 := by
    simp only [F]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, mul_moorePenroseInverse_mul, sub_self]
  have hFid : F * F = F := by
    simp only [F]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, show (moorePenroseInverse A * A) * (moorePenroseInverse A * A) =
        moorePenroseInverse A * A from moorePenroseInverse_mul_isIdempotentElem A]
    abel
  have hFB : F * B = 0 := by
    apply Matrix.ext
    intro i j
    let z : m → 𝕜 := F *ᵥ B.col j
    have hz : A *ᵥ z = 0 := by
      simp only [z]
      rw [Matrix.mulVec_mulVec, hAF, Matrix.zero_mulVec]
    have hBz := conjTranspose_mulVec_eq_zero_of_fromBlocks_posSemidef hM z hz
    have hDot : star (B.col j) ⬝ᵥ z = 0 := by
      simpa only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.col,
        Matrix.transpose_apply, Pi.zero_apply, Pi.star_apply] using congrFun hBz j
    have hFz : F *ᵥ z = z := by
      simp only [z]
      rw [Matrix.mulVec_mulVec, hFid]
    have hzz : star z ⬝ᵥ z = 0 := by
      calc
        star z ⬝ᵥ z = star (B.col j) ⬝ᵥ (Fᴴ *ᵥ z) := star_mulVec_dotProduct F (B.col j) z
        _ = star (B.col j) ⬝ᵥ z := by rw [hFh, hFz]
        _ = 0 := hDot
    have hz0 : z = 0 := dotProduct_star_self_eq_zero.mp hzz
    simpa [z, Matrix.mul_apply, Matrix.mulVec, Matrix.col, dotProduct] using congrFun hz0 i
  simpa only [F, hRowCol] using hFB

omit [DecidableEq m] in
/-- **Square completion** with the Moore–Penrose inverse: for Hermitian `A` with
`A A⁺ B = B`,
`(y, x)ᴴ M (y, x) = (y + A⁺Bx)ᴴ A (y + A⁺Bx) + xᴴ (M / A) x`. Albert 1969, Theorem 1; supports
`generalized-schur-complement-psd`. -/
theorem dotProduct_fromBlocks_eq_generalizedSchurComplement_square
    (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) (C : Matrix n n 𝕜)
    (hA : A.IsHermitian) (hRange : A * moorePenroseInverse A * B = B)
    (y : m → 𝕜) (x : n → 𝕜) :
    star (Sum.elim y x) ⬝ᵥ Matrix.fromBlocks A B Bᴴ C *ᵥ Sum.elim y x =
      star (y + moorePenroseInverse A *ᵥ (B *ᵥ x)) ⬝ᵥ
        A *ᵥ (y + moorePenroseInverse A *ᵥ (B *ᵥ x)) +
      star x ⬝ᵥ generalizedSchurComplement A B C *ᵥ x := by
  rw [generalizedSchurComplement]
  set w := moorePenroseInverse A *ᵥ (B *ᵥ x) with hw
  have hAdh : (moorePenroseInverse A)ᴴ = moorePenroseInverse A :=
    (Matrix.IsHermitian.moorePenroseInverse hA).eq
  have hAw : A *ᵥ w = B *ᵥ x := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hRange]
  have hRange' : Bᴴ * moorePenroseInverse A * A = Bᴴ := by
    have h := congrArg Matrix.conjTranspose hRange
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hAdh, hA.eq, ← Matrix.mul_assoc] at h
  have hCross : star w ⬝ᵥ (A *ᵥ y) = star x ⬝ᵥ (Bᴴ *ᵥ y) := by
    rw [hw, star_mulVec_dotProduct, hAdh, star_mulVec_dotProduct, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hRange']
  have hTail : star w ⬝ᵥ (B *ᵥ x) = star x ⬝ᵥ (Bᴴ * moorePenroseInverse A * B) *ᵥ x := by
    rw [hw, star_mulVec_dotProduct, hAdh, star_mulVec_dotProduct, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  simp only [Matrix.fromBlocks_mulVec, star_sumElim, sumElim_dotProduct_sumElim,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    Matrix.mulVec_add, Matrix.sub_mulVec, star_add, add_dotProduct, dotProduct_add,
    dotProduct_sub, hAw, hCross, hTail]
  ring

/-- **Albert's criterion**: `[[A, B], [Bᴴ, C]] ⪰ 0` iff `A ⪰ 0`, `(I − AA⁺) B = 0` (range of `B`
inside range of `A`) and `M / A = C − Bᴴ A⁺ B ⪰ 0`. No Hermitian hypotheses are needed: each
side forces `A` and `C` Hermitian. Albert 1969, Thm 1; cf. Horn–Johnson 2013, Theorems 7.7.7
and 7.7.9 for the invertible case.
Proof: (⇒) `A ⪰ 0` and `C ⪰ 0` are principal submatrices; for `z ∈ ker A`,
`(z, 0)ᴴ M (z, 0) = 0` forces `Bᴴ z = 0`, i.e. `range B ⊆ range A`, which is `(I − AA⁺)B = 0`;
then with `y = −A⁺Bx` the quadratic form is `xᴴ(M/A)x ≥ 0`. (⇐) the square completion
`dotProduct_fromBlocks_eq_generalizedSchurComplement_square`.
atlas: generalized-schur-complement-psd -/
theorem posSemidef_fromBlocks_iff
    (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) (C : Matrix n n 𝕜) :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef ↔
      A.PosSemidef ∧ (1 - A * moorePenroseInverse A) * B = 0 ∧
        (generalizedSchurComplement A B C).PosSemidef := by
  constructor
  · intro hM
    have hA : A.PosSemidef := hM.submatrix (Sum.inl : m → m ⊕ n)
    have hC : C.PosSemidef := hM.submatrix (Sum.inr : n → m ⊕ n)
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
    rw [dotProduct_fromBlocks_eq_generalizedSchurComplement_square A B C hA.isHermitian hRange]
      at h
    simpa only [neg_add_cancel, Matrix.zero_mulVec, star_zero, zero_dotProduct, zero_add] using h
  · rintro ⟨hA, hCompat, hS⟩
    have hRange : A * moorePenroseInverse A * B = B := by
      rw [Matrix.sub_mul, Matrix.one_mul] at hCompat
      exact (sub_eq_zero.mp hCompat).symm
    have hCorr := (Matrix.PosSemidef.moorePenroseInverse hA).conjTranspose_mul_mul_same B
    have hC : C.IsHermitian := by
      simpa only [generalizedSchurComplement, sub_add_cancel] using
        hS.isHermitian.add hCorr.isHermitian
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hA.isHermitian.fromBlocks (by simp) hC, ?_⟩
    intro z
    have hz : z = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) := by ext i; cases i <;> rfl
    rw [hz, dotProduct_fromBlocks_eq_generalizedSchurComplement_square A B C hA.isHermitian hRange]
    exact add_nonneg (hA.dotProduct_mulVec_nonneg _) (hS.dotProduct_mulVec_nonneg _)

/-- The generalized Schur quadratic form is the attained minimum over the leading block
variable: `xᴴ (M / A) x = min_y (y, x)ᴴ M (y, x)` for `M ⪰ 0`. Albert 1969, Theorem 1.
atlas: generalized-schur-complement-psd (partial) -/
theorem isLeast_generalizedSchurComplement_quadratic
    (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) (C : Matrix n n 𝕜)
    (hM : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) (x : n → 𝕜) :
    IsLeast (Set.range (fun y : m → 𝕜 =>
      star (Sum.elim y x) ⬝ᵥ Matrix.fromBlocks A B Bᴴ C *ᵥ Sum.elim y x))
      (star x ⬝ᵥ generalizedSchurComplement A B C *ᵥ x) := by
  obtain ⟨hA, hCompat, _⟩ := (posSemidef_fromBlocks_iff A B C).mp hM
  have hRange : A * moorePenroseInverse A * B = B := by
    rw [Matrix.sub_mul, Matrix.one_mul] at hCompat
    exact (sub_eq_zero.mp hCompat).symm
  constructor
  · refine ⟨-(moorePenroseInverse A *ᵥ (B *ᵥ x)), ?_⟩
    dsimp only
    rw [dotProduct_fromBlocks_eq_generalizedSchurComplement_square A B C hA.isHermitian hRange]
    simp
  · rintro _ ⟨y, rfl⟩
    dsimp only
    rw [dotProduct_fromBlocks_eq_generalizedSchurComplement_square A B C hA.isHermitian hRange]
    exact le_add_of_nonneg_left (hA.dotProduct_mulVec_nonneg _)

/-- **Variational characterisation, lower bound**: for `M = [[A, B], [Bᴴ, C]] ⪰ 0`,
`xᴴ (M / A) x ≤ (y, x)ᴴ M (y, x)` for every `y`. Albert 1969, Thm 1; cf. Horn–Johnson 2013,
§7.7. The lower-bound half of `isLeast_generalizedSchurComplement_quadratic`.
atlas: generalized-schur-complement-psd (partial) -/
theorem dotProduct_generalizedSchurComplement_mulVec_le {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (hM : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) (x : n → 𝕜) (y : m → 𝕜) :
    star x ⬝ᵥ (generalizedSchurComplement A B C *ᵥ x) ≤
      star (Sum.elim y x) ⬝ᵥ (Matrix.fromBlocks A B Bᴴ C *ᵥ Sum.elim y x) :=
  (isLeast_generalizedSchurComplement_quadratic A B C hM x).2 ⟨y, rfl⟩

/-- **Variational characterisation, attainment**: for `M = [[A, B], [Bᴴ, C]] ⪰ 0` the minimum
over `y` of `(y, x)ᴴ M (y, x)` is attained at `y = −A⁺Bx` and equals `xᴴ (M / A) x`.
Albert 1969, Thm 1; cf. Horn–Johnson 2013, §7.7.
Proof: the square completion `dotProduct_fromBlocks_eq_generalizedSchurComplement_square` with
`y + A⁺Bx = 0`.
atlas: generalized-schur-complement-psd (partial) -/
theorem dotProduct_generalizedSchurComplement_mulVec_eq {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (hM : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) (x : n → 𝕜) :
    star x ⬝ᵥ (generalizedSchurComplement A B C *ᵥ x) =
      star (Sum.elim (-(moorePenroseInverse A * B) *ᵥ x) x) ⬝ᵥ
        (Matrix.fromBlocks A B Bᴴ C *ᵥ Sum.elim (-(moorePenroseInverse A * B) *ᵥ x) x) := by
  obtain ⟨hA, hCompat, _⟩ := (posSemidef_fromBlocks_iff A B C).mp hM
  have hRange : A * moorePenroseInverse A * B = B := by
    rw [Matrix.sub_mul, Matrix.one_mul] at hCompat
    exact (sub_eq_zero.mp hCompat).symm
  rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_fromBlocks_eq_generalizedSchurComplement_square A B C hA.isHermitian hRange]
  simp

/-- The generalized Schur complement of a PSD block matrix is PSD: `0 ⪯ M / A` for `M ⪰ 0`
(Loewner order). Albert 1969, Theorem 1.
atlas: generalized-schur-complement-psd (partial) -/
theorem generalizedSchurComplement_nonneg
    {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (hM : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    0 ≤ generalizedSchurComplement A B C :=
  ((posSemidef_fromBlocks_iff A B C).mp hM).2.2.nonneg

omit [DecidableEq m] in
/-- **Schur complement below the trailing block**: for `A ⪰ 0`, `M / A ⪯ C` (Loewner order),
since `C − M / A = Bᴴ A⁺ B = (A⁺B)ᴴ A (A⁺B) ⪰ 0`; only `A ⪰ 0` is needed.
Albert 1969, Thm 1; cf. Horn–Johnson 2013, §7.7.
atlas: generalized-schur-complement-psd (partial) -/
theorem generalizedSchurComplement_le {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (hA : A.PosSemidef) :
    generalizedSchurComplement A B C ≤ C := by
  rw [Matrix.le_iff]
  have hP : (moorePenroseInverse A)ᴴ = moorePenroseInverse A :=
    (Matrix.IsHermitian.moorePenroseInverse hA.isHermitian).eq
  have h : C - generalizedSchurComplement A B C =
      (moorePenroseInverse A * B)ᴴ * A * (moorePenroseInverse A * B) := by
    rw [Matrix.conjTranspose_mul, hP, generalizedSchurComplement, sub_sub_cancel]
    conv_lhs => rw [← moorePenroseInverse_mul_moorePenroseInverse A]
    simp only [Matrix.mul_assoc]
  rw [h]
  exact hA.conjTranspose_mul_mul_same _

end NLAlib
