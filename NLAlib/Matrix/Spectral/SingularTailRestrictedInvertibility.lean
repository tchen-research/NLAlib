import NLAlib.Matrix.Spectral.SingularTailInverseTrace
import NLAlib.Matrix.Spectral.PrincipalDeletionSelection
import NLAlib.Matrix.Basic.InverseOnRange

/-!
# Singular-tail restricted invertibility

The maximum-volume inverse-trace bound and the principal-coordinate lower
barrier yield the singular-tail restricted-invertibility theorem. The inverse
is the actual Euclidean inverse on the selected range. Source: Naor--Youssef
(2016), Theorem 6, with the explicit universal constant `2`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib
namespace RestrictedInvertibility

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The one-based singular-tail scale of the Naor--Youssef bound. The
zero-based library tail `bestRankFrobSq A (r-1)` equals the source sum from
singular value `r` onward. This expression is total; a vanishing denominator
gives zero and is excluded in the selection theorems. -/
def singularTailInverseScale (A : Matrix m n ℝ) (k r : ℕ) : ℝ :=
  Real.sqrt ((Fintype.card n : ℝ) * r /
    ((r - k : ℕ) * bestRankFrobSq A (r - 1)))

/-- For every admissible tail index, an exact `k`-column selection has a
strict positive lower Gram barrier of half the squared reciprocal tail
scale. The proof uses maximum-volume selection at size `r-1`, followed by
principal-coordinate deletion. -/
theorem exists_embedding_posDef_gram_sub_singularTail
    (A : Matrix m n ℝ) {k r : ℕ} (hk : 1 ≤ k) (hkr : k < r) (hr : r ≤ A.rank) :
    ∃ e : Fin k ↪ n,
      ((A.submatrix id e)ᵀ * A.submatrix id e -
        (((r - k : ℕ) : ℝ) * bestRankFrobSq A (r - 1) /
          (2 * (Fintype.card n : ℝ) * r)) • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef := by
  have hrl : r - 1 < A.rank := by omega
  have hkl : k ≤ r - 1 := by omega
  have hrpos : 0 < r := by omega
  have hnpos : 0 < Fintype.card n := hrpos.trans_le (hr.trans A.rank_le_card_width)
  have hE : 0 < bestRankFrobSq A (r - 1) := bestRankFrobSq_pos_of_lt_rank A hrl
  let T : ℝ := (Fintype.card n : ℝ) * r / bestRankFrobSq A (r - 1)
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨e, hePos, heTrace⟩ := exists_column_embedding_posDef_gram_trace_inv_le_tail A (r - 1) hrl
  let C := A.submatrix id e
  let G := Cᵀ * C
  have hTrace : G⁻¹.trace ≤ T := by
    apply heTrace.trans
    dsimp [T]
    apply div_le_div_of_nonneg_right _ hE.le
    have hleft : (r - 1 : ℕ) ≤ r := Nat.sub_le _ _
    have hright : (Fintype.card n : ℝ) - (r - 1 : ℕ) ≤ Fintype.card n := by
      linarith [Nat.cast_nonneg (r - 1) (α := ℝ)]
    have hright0 : 0 ≤ (Fintype.card n : ℝ) - (r - 1 : ℕ) := by
      exact sub_nonneg.mpr (Nat.cast_le.mpr ((Nat.sub_le r 1).trans (hr.trans A.rank_le_card_width)))
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hleft) hright0).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hright (Nat.cast_nonneg r)])
  obtain ⟨f, hf⟩ := exists_embedding_posDef_sub_smul_one_of_trace_inv_le G hePos hkl hT hTrace
  let s : Fin k ↪ n := ⟨fun i => e (f i), e.injective.comp f.injective⟩
  have hGram : G.submatrix f f = (A.submatrix id s)ᵀ * A.submatrix id s := by
    ext i j
    simp only [G, C, s, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Function.Embedding.coeFn_mk, id_eq]
  have hNat : r - 1 - k + 1 = r - k := by omega
  have hscale : ((r - 1 - k + 1 : ℕ) : ℝ) / (2 * T) =
      ((r - k : ℕ) : ℝ) * bestRankFrobSq A (r - 1) /
        (2 * (Fintype.card n : ℝ) * r) := by
    rw [hNat]
    dsimp [T]
    field_simp
  refine ⟨s, ?_⟩
  rwa [hGram, hscale] at hf

omit [Fintype n] [DecidableEq m] in
private theorem column_embedding_posDef_to_finset
    {k : ℕ} (A : Matrix m n ℝ) (e : Fin k ↪ n) (b : ℝ)
    (hPos : ((A.submatrix id e)ᵀ * A.submatrix id e -
      b • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef) :
    ∃ S : Finset n, S.card = k ∧
      ((A.submatrix id (fun i : S => (i : n)))ᵀ * A.submatrix id (fun i : S => (i : n)) -
        b • (1 : Matrix S S ℝ)).PosDef := by
  classical
  let S := Finset.univ.image e
  let f₀ : Fin k → S := fun j => ⟨e j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
  have hf : Function.Bijective f₀ := by
    constructor
    · intro i j hij
      exact e.injective (congrArg Subtype.val hij)
    · intro i
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp i.property
      exact ⟨j, Subtype.ext hj⟩
  let f := Equiv.ofBijective f₀ hf
  have hval (i : S) : e (f.symm i) = (i : n) :=
    congrArg Subtype.val (f.apply_symm_apply i)
  have heq :
      (((A.submatrix id e)ᵀ * A.submatrix id e - b • (1 : Matrix (Fin k) (Fin k) ℝ)).submatrix
        f.symm f.symm) =
      (A.submatrix id (fun i : S => (i : n)))ᵀ * A.submatrix id (fun i : S => (i : n)) -
        b • (1 : Matrix S S ℝ) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply]
    have hId := congrArg (fun P : Matrix S S ℝ => P i j)
      (Matrix.submatrix_one f.symm f.symm.injective (α := ℝ))
    simp only [Matrix.submatrix_apply] at hId
    rw [hId]
    congr 1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, hval]
  refine ⟨S, ?_, ?_⟩
  · dsimp [S]
    rw [Finset.card_image_of_injective _ e.injective, Finset.card_univ, Fintype.card_fin]
  · exact heq ▸ hPos.submatrix f.symm.injective

/-- For one admissible tail index, an exact `k`-element subset has inverse
norm at most twice the tail scale. The inverse is defined on the selected
range, and the selected Euclidean matrix map is injective. -/
theorem exists_finset_card_eq_and_norm_inverseOnRange_le_tail
    (A : Matrix m n ℝ) {k r : ℕ} (hk : 1 ≤ k) (hkr : k < r) (hr : r ≤ A.rank) :
    ∃ S : Finset n, S.card = k ∧
      ∃ hA : Function.Injective (Matrix.toEuclideanLin (A.submatrix id (fun i : S => (i : n)))),
        ‖inverseOnRange (A.submatrix id (fun i : S => (i : n))) hA‖ ≤
          2 * singularTailInverseScale A k r := by
  let b : ℝ := ((r - k : ℕ) : ℝ) * bestRankFrobSq A (r - 1) /
    (2 * (Fintype.card n : ℝ) * r)
  have hrpos : 0 < r := by omega
  have hnpos : 0 < Fintype.card n := hrpos.trans_le (hr.trans A.rank_le_card_width)
  have hE : 0 < bestRankFrobSq A (r - 1) := bestRankFrobSq_pos_of_lt_rank A (by omega)
  have hdiff : 0 < r - k := Nat.sub_pos_of_lt hkr
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨e, he⟩ := exists_embedding_posDef_gram_sub_singularTail A hk hkr hr
  obtain ⟨S, hS, hPos⟩ := column_embedding_posDef_to_finset A e b he
  let C := A.submatrix id (fun i : S => (i : n))
  have hGram : (Cᵀ * C).PosDef := by
    have hh := hPos.add (Matrix.PosDef.one.smul hb)
    simpa only [sub_add_cancel] using hh
  let hC := injective_toEuclideanLin_of_posDef_gram C hGram
  refine ⟨S, hS, hC, (norm_inverseOnRange_le_of_posDef_gram_sub C hC hb hPos).trans ?_⟩
  have hscale : 1 / b = 2 * ((Fintype.card n : ℝ) * r /
      ((r - k : ℕ) * bestRankFrobSq A (r - 1))) := by
    dsimp [b]
    field_simp
  have hnon : 0 ≤ (Fintype.card n : ℝ) * r /
      ((r - k : ℕ) * bestRankFrobSq A (r - 1)) := by positivity
  calc
    1 / Real.sqrt b = Real.sqrt (1 / b) := by
      symm
      simpa only [Real.sqrt_one] using Real.sqrt_div (show (0 : ℝ) ≤ 1 by norm_num) b
    _ = Real.sqrt 2 * singularTailInverseScale A k r := by
      rw [hscale, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rfl
    _ ≤ 2 * singularTailInverseScale A k r :=
      mul_le_mul_of_nonneg_right
        (by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)])
        (Real.sqrt_nonneg _)

end RestrictedInvertibility

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- An exact `k`-column selection is injective and its actual inverse on the
selected Euclidean range satisfies the singular-tail bound with universal
constant `2`. The same selected subset satisfies the bound for every integer
`k < r ≤ rank A`; this is exactly the minimum over those finitely many
integers in the source statement. The zero-based tail at `r-1` equals the
one-based source sum from `r` onward. Naor--Youssef (2016), Theorem 6, p. 4.
atlas: singular-tail-restricted-invertibility -/
theorem exists_finset_card_eq_and_norm_inverseOnRange_le_singularTail
    (A : Matrix m n ℝ) (k : ℕ) (hk : 1 ≤ k) (hkrank : k < A.rank) :
    ∃ S : Finset n, S.card = k ∧
      ∃ hA : Function.Injective (Matrix.toEuclideanLin (A.submatrix id (fun i : S => (i : n)))),
        ∀ r : ℕ, k < r → r ≤ A.rank →
          ‖inverseOnRange (A.submatrix id (fun i : S => (i : n))) hA‖ ≤
            2 * RestrictedInvertibility.singularTailInverseScale A k r := by
  classical
  let R : Finset ℕ := Finset.Icc (k + 1) A.rank
  have hR : R.Nonempty := ⟨k + 1, Finset.mem_Icc.mpr ⟨le_rfl, hkrank⟩⟩
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image R
    (RestrictedInvertibility.singularTailInverseScale A k) hR
  have hr' := Finset.mem_Icc.mp hr
  obtain ⟨S, hS, hA, hbound⟩ :=
    RestrictedInvertibility.exists_finset_card_eq_and_norm_inverseOnRange_le_tail A hk
      (by omega) hr'.2
  refine ⟨S, hS, hA, ?_⟩
  intro t hkt ht
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (hmin t (Finset.mem_Icc.mpr ⟨hkt, ht⟩)) (by norm_num))

/-- The literal finite-minimum form of singular-tail restricted invertibility.
The minimum ranges over the integers `k+1` through `rank A`, with
the rank endpoint included, and the explicit universal constant is `2`.
Naor--Youssef (2016), Theorem 6, p. 4.
atlas: singular-tail-restricted-invertibility -/
theorem exists_finset_card_eq_and_norm_inverseOnRange_le_min_singularTail
    (A : Matrix m n ℝ) (k : ℕ) (hk : 1 ≤ k) (hkrank : k < A.rank) :
    ∃ S : Finset n, S.card = k ∧
      ∃ hA : Function.Injective (Matrix.toEuclideanLin (A.submatrix id (fun i : S => (i : n)))),
        ‖inverseOnRange (A.submatrix id (fun i : S => (i : n))) hA‖ ≤
          2 * (Finset.Icc (k + 1) A.rank).inf'
            (by exact ⟨k + 1, Finset.mem_Icc.mpr ⟨le_rfl, hkrank⟩⟩)
            (RestrictedInvertibility.singularTailInverseScale A k) := by
  obtain ⟨S, hS, hA, hbound⟩ :=
    exists_finset_card_eq_and_norm_inverseOnRange_le_singularTail A k hk hkrank
  refine ⟨S, hS, hA, ?_⟩
  have hh : ‖inverseOnRange (A.submatrix id (fun i : S => (i : n))) hA‖ / 2 ≤
      (Finset.Icc (k + 1) A.rank).inf'
        (by exact ⟨k + 1, Finset.mem_Icc.mpr ⟨le_rfl, hkrank⟩⟩)
        (RestrictedInvertibility.singularTailInverseScale A k) := by
    apply Finset.le_inf' _ _
    intro r hr
    have hr' := Finset.mem_Icc.mp hr
    have hh := hbound r (by omega) hr'.2
    linarith
  linarith

end NLAlib
