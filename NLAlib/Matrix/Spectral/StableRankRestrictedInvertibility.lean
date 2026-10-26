import NLAlib.Matrix.Spectral.RestrictedInvertibilityGram
import NLAlib.Matrix.Spectral.RestrictedInvertibilityParameters

/-!
# Stable-rank restricted invertibility

An isotropic frame, transformed by an arbitrary nonzero real linear map,
contains an injective selection of exactly the floor of the stable-rank
budget. Every nonzero coefficient vector satisfies the strict lower bound
with the source constant `(1-ε)²`. Source: Spielman--Srivastava (2009),
Theorem 2. Atlas: `stable-rank-restricted-invertibility`.
-/

noncomputable section

open scoped Matrix BigOperators MatrixOrder
open Matrix

namespace NLAlib
namespace RestrictedInvertibility

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- A PSD decomposition with trace `F` and operator bound `Λ` has a linearly
independent selection of exactly `floor(ε² F/Λ)` columns and the strict
Spielman--Srivastava lower bound. Empty selections are included. -/
theorem exists_embedding_norm_sum_sq_gt_of_decomposition
    [Nonempty I] (v : I → n → ℝ) {H : Matrix n n ℝ}
    (hH : H.PosSemidef) (hframe : ∑ i, vecMulVec (v i) (v i) = H)
    (hF : 0 < H.trace) {Λ ε : ℝ} (hΛ : 0 < Λ)
    (hHle : H ≤ Λ • (1 : Matrix n n ℝ)) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ s : Fin ⌊ε ^ 2 * H.trace / Λ⌋₊ ↪ I,
      LinearIndependent ℝ (fun j => v (s j)) ∧
      ∀ a : Fin ⌊ε ^ 2 * H.trace / Λ⌋₊ → ℝ, a ≠ 0 →
        (1 - ε) ^ 2 * H.trace / (Fintype.card I : ℝ) * ‖WithLp.toLp 2 a‖ ^ 2 <
          ‖WithLp.toLp 2 (∑ j, a j • v (s j))‖ ^ 2 := by
  let M : ℝ := Fintype.card I
  have hM : 0 < M := Nat.cast_pos.mpr Fintype.card_pos
  let b₀ : ℝ := (1 - ε) * H.trace / M
  let δ : ℝ := (1 - ε) * Λ / (ε * M)
  let k : ℕ := ⌊ε ^ 2 * H.trace / Λ⌋₊
  have hb₀ : 0 < b₀ := by dsimp [b₀]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hparameters := floor_mul_decrement_lt_and_terminal_barrier_le hF hΛ hM hε hε1
  change (k : ℝ) * δ < b₀ ∧
    (1 - ε) ^ 2 * H.trace / M ≤ b₀ - (k : ℝ) * δ at hparameters
  obtain ⟨s, hRank, hGap, _hPot⟩ :=
    exists_selectedFrameOperator_rank_eq_and_eigenvalues_gap v hH hframe hb₀ hδ hΛ hHle
      (by exact le_of_eq (neg_div_initial_barrier_eq hF hΛ hM hε hε1)) k hparameters.1
  let X : Matrix n (Fin k) ℝ := fun i j => v (s j) i
  have hXX : X * Xᵀ = selectedFrameOperator v s := by
    ext i j
    change (∑ l : Fin k, v (s l) i * v (s l) j) =
      (∑ l : Fin k, vecMulVec (v (s l)) (v (s l))) i j
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
  have hXRank : X.rank = Fintype.card (Fin k) := by
    rw [← Matrix.rank_self_mul_conjTranspose X,
      Matrix.conjTranspose_eq_transpose_of_trivial, hXX, hRank, Fintype.card_fin]
  have hli : LinearIndependent ℝ (fun j => v (s j)) := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    have hh := hXRank
    rw [Matrix.rank_eq_finrank_span_cols] at hh
    exact hh.symm
  have hinj : Function.Injective s := by
    intro i j hij
    apply hli.injective
    exact congrArg v hij
  refine ⟨⟨s, hinj⟩, hli, ?_⟩
  intro a ha
  have hA : (X * Xᵀ).IsHermitian := by
    rw [hXX]
    exact (selectedFrameOperator_posSemidef v s).isHermitian
  have heigen : hA.eigenvalues = (selectedFrameOperator_posSemidef v s).isHermitian.eigenvalues :=
    (hA.eigenvalues_eq_eigenvalues_iff _).mpr (congrArg Matrix.charpoly hXX)
  have hGapX : ∀ i, hA.eigenvalues i = 0 ∨ b₀ - (k : ℝ) * δ < hA.eigenvalues i := by
    rw [heigen]
    exact hGap
  have hstrict := norm_mulVec_sq_gt_of_eigenvalues_gap X hXRank hA
    (b₀ - (k : ℝ) * δ) hGapX a ha
  have hXa : X *ᵥ a = ∑ j, a j • v (s j) := by
    ext i
    change (∑ j : Fin k, v (s j) i * a j) = (∑ j : Fin k, a j • v (s j)) i
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hXa] at hstrict
  exact (mul_le_mul_of_nonneg_right hparameters.2 (sq_nonneg _)).trans_lt hstrict

open scoped Matrix.Norms.L2Operator in
private theorem specNorm_pos_of_ne_zero (L : Matrix n n ℝ) (hL : L ≠ 0) : 0 < specNorm L := by
  rw [specNorm_eq_norm]
  exact norm_pos_iff.mpr hL

end RestrictedInvertibility

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- An identity decomposition contains a stable-rank sized independent
selection after applying any nonzero real linear map. The labels form an
embedding of exactly `floor(ε² ‖L‖F² / ‖L‖₂²)` elements, so in particular the
selected subset has at least the source cardinality. The quadratic inequality
is strict for every nonzero coefficient vector, including the vacuous empty
selection case. Spielman--Srivastava (2009), Theorem 2, p. 2.
atlas: stable-rank-restricted-invertibility -/
theorem exists_embedding_norm_sum_sq_gt_of_isotropic_frame
    [Nonempty I] [Nonempty n] (v : I → n → ℝ)
    (hframe : ∑ i, vecMulVec (v i) (v i) = 1)
    (L : Matrix n n ℝ) (hL : L ≠ 0) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ s : Fin ⌊ε ^ 2 * frobSq L / specNorm L ^ 2⌋₊ ↪ I,
      LinearIndependent ℝ (fun j => L *ᵥ v (s j)) ∧
      ∀ a : Fin ⌊ε ^ 2 * frobSq L / specNorm L ^ 2⌋₊ → ℝ, a ≠ 0 →
        (1 - ε) ^ 2 * frobSq L / (Fintype.card I : ℝ) * ‖WithLp.toLp 2 a‖ ^ 2 <
          ‖WithLp.toLp 2 (∑ j, a j • (L *ᵥ v (s j)))‖ ^ 2 := by
  let H : Matrix n n ℝ := L * Lᵀ
  have hH : H.PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose L
  have htrace : H.trace = frobSq L := by
    rw [frobSq, frobInner_eq_re_trace_mul_conjTranspose]
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.re_to_real, H]
  have hF : 0 < H.trace := by
    rw [htrace]
    exact lt_of_le_of_ne (frobSq_nonneg L) (Ne.symm ((frobSq_eq_zero_iff L).not.mpr hL))
  have hΛ : 0 < specNorm L ^ 2 :=
    sq_pos_of_pos (RestrictedInvertibility.specNorm_pos_of_ne_zero L hL)
  have hHle : H ≤ specNorm L ^ 2 • (1 : Matrix n n ℝ) := by
    apply Matrix.le_iff.mpr
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · apply Matrix.IsHermitian.sub _ hH.isHermitian
      rw [Matrix.smul_one_eq_diagonal]
      exact Matrix.isHermitian_diagonal _
    · intro x
      have hb := (le_abs_self (x ⬝ᵥ (H *ᵥ x))).trans (abs_dotProduct_mulVec_le_specNorm H x)
      have hnorm : specNorm H = specNorm L ^ 2 := by
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using specNorm_mul_conjTranspose_self L
      rw [hnorm] at hb
      simpa only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, sub_nonneg] using hb
  have hdecomp : ∑ i, vecMulVec (L *ᵥ v i) (L *ᵥ v i) = H := by
    calc
      _ = ∑ i, L * vecMulVec (v i) (v i) * Lᵀ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
      _ = L * (∑ i, vecMulVec (v i) (v i)) * Lᵀ := by
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = H := by rw [hframe, Matrix.mul_one]
  have hres := RestrictedInvertibility.exists_embedding_norm_sum_sq_gt_of_decomposition
    (fun i => L *ᵥ v i) hH hdecomp hF hΛ hHle hε hε1
  rw [htrace] at hres
  exact hres

/-- The subset form of stable-rank restricted invertibility, with exactly the
source floor cardinality, independent transformed columns, and the strict
squared Euclidean inequality on all nonzero coefficient vectors indexed by
the selected subset. Spielman--Srivastava (2009), Theorem 2, p. 2.
atlas: stable-rank-restricted-invertibility -/
theorem exists_finset_card_eq_and_norm_sum_sq_gt_of_isotropic_frame
    [Nonempty I] [Nonempty n] (v : I → n → ℝ)
    (hframe : ∑ i, vecMulVec (v i) (v i) = 1)
    (L : Matrix n n ℝ) (hL : L ≠ 0) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ S : Finset I,
      S.card = ⌊ε ^ 2 * frobSq L / specNorm L ^ 2⌋₊ ∧
      LinearIndependent ℝ (fun i : S => L *ᵥ v i) ∧
      ∀ a : S → ℝ, a ≠ 0 →
        (1 - ε) ^ 2 * frobSq L / (Fintype.card I : ℝ) * ‖WithLp.toLp 2 a‖ ^ 2 <
          ‖WithLp.toLp 2 (∑ i : S, a i • (L *ᵥ v i))‖ ^ 2 := by
  classical
  obtain ⟨e, hli, hbound⟩ :=
    exists_embedding_norm_sum_sq_gt_of_isotropic_frame v hframe L hL hε hε1
  let S : Finset I := Finset.univ.image e
  let f₀ : Fin ⌊ε ^ 2 * frobSq L / specNorm L ^ 2⌋₊ → S :=
    fun j => ⟨e j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
  have hf : Function.Bijective f₀ := by
    constructor
    · intro i j hij
      exact e.injective (congrArg Subtype.val hij)
    · intro i
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp i.property
      exact ⟨j, Subtype.ext hj⟩
  let f := Equiv.ofBijective f₀ hf
  refine ⟨S, ?_, ?_, ?_⟩
  · dsimp [S]
    rw [Finset.card_image_of_injective _ e.injective, Finset.card_univ, Fintype.card_fin]
  · exact (linearIndependent_equiv f).mp hli
  · intro a ha
    have hane : (fun j => a (f j)) ≠ 0 := by
      intro hz
      apply ha
      funext i
      have hh := congrFun hz (f.symm i)
      simpa only [f.apply_symm_apply, Pi.zero_apply] using hh
    have hnorm : ‖WithLp.toLp 2 (fun j => a (f j))‖ ^ 2 = ‖WithLp.toLp 2 a‖ ^ 2 := by
      simp only [norm_toLp_sq_eq_dotProduct_self, dotProduct]
      exact f.sum_comp (fun i => a i * a i)
    have hsum : (∑ j, a (f j) • (L *ᵥ v (e j))) =
        ∑ i : S, a i • (L *ᵥ v i) := by
      exact f.sum_comp (fun i : S => a i • (L *ᵥ v i))
    have hh := hbound (fun j => a (f j)) hane
    rw [hnorm, hsum] at hh
    exact hh

end NLAlib
