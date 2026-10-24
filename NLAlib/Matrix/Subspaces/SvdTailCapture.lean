import NLAlib.Matrix.Subspaces.ProjectorCapture
import NLAlib.ForMathlib.Analysis.MonotoneTailSum

/-! # Captured energy of a leading-SVD tail

A rank-k orthogonal projector captures at most the k largest entries of the discarded
singular-value square sequence. This is the finite Ky Fan step used by fixed-offset
projection-cost sketches. Source: Cohen et al. (2015), Theorem 7.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

private theorem sum_tail_mul_le_sum_shifted {a w : ℕ → ℝ} {N ℓ k : ℕ}
    (hℓ : ℓ ≤ N) (ha0 : ∀ i, 0 ≤ a i) (ha : Antitone a)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hbudget : ∑ i ∈ Finset.range N, w i ≤ (k : ℝ)) :
    (∑ i ∈ Finset.range N, if i < ℓ then 0 else a i * w i) ≤
      ∑ j ∈ Finset.range k, a (ℓ + j) := by
  have hSplit : (∑ i ∈ Finset.range N, w i) =
      (∑ i ∈ Finset.range ℓ, w i) + ∑ j ∈ Finset.range (N - ℓ), w (ℓ + j) := by
    conv_lhs => rw [show N = ℓ + (N - ℓ) by omega]
    exact Finset.sum_range_add w ℓ (N - ℓ)
  have htBudget : ∑ j : Fin (N - ℓ), w (ℓ + j) ≤ (k : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => w (ℓ + j)) (N - ℓ)]
    have h0 : 0 ≤ ∑ i ∈ Finset.range ℓ, w i := Finset.sum_nonneg (fun i _ => hw0 i)
    linarith
  have ht := sum_mul_le_sum_ite_lt_of_antitone
    (fun j : Fin (N - ℓ) => a (ℓ + j)) (fun j => w (ℓ + j))
    (fun j => ha0 _) (fun i j hij => ha (Nat.add_le_add_left hij ℓ))
    (fun j => hw0 _) (fun j => hw1 _) htBudget
  have hL : (∑ i ∈ Finset.range N, if i < ℓ then 0 else a i * w i) =
      ∑ j : Fin (N - ℓ), a (ℓ + j) * w (ℓ + j) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => a (ℓ + j) * w (ℓ + j)) (N - ℓ)]
    conv_lhs => rw [show N = ℓ + (N - ℓ) by omega]
    rw [Finset.sum_range_add]
    have hHead : (∑ i ∈ Finset.range ℓ, if i < ℓ then 0 else a i * w i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [if_pos (Finset.mem_range.mp hi)]
    rw [hHead, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    rw [if_neg (by omega)]
  rw [hL]
  apply ht.trans
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < k then a (ℓ + j) else 0) (N - ℓ),
    ← Finset.sum_filter]
  have hf : (Finset.range (N - ℓ)).filter (fun j => j < k) =
      Finset.range (min (N - ℓ) k) := by ext j; simp
  rw [hf]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.min_le_right _ _))
    (fun j _ _ => ha0 _)

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- The actual ℓ-column leading SVD factor U_ℓ Σ_ℓ. Its column count is ℓ rather
than the original width; the definition is total at every cutoff. -/
def IsSVD.leadingFactor {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (_h : IsSVD A U V) (ℓ : ℕ) :
    Matrix m (Fin ℓ) 𝕜 := U * (rectDiag (singularValues A) : Matrix (Fin p) (Fin ℓ) 𝕜)

/-- The row Gram of the actual leading SVD factor is its finite singular-coordinate
head, without retaining any unused right-factor columns. -/
theorem IsSVD.leadingFactor_mul_conjTranspose {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V) (ℓ : ℕ) :
    h.leadingFactor ℓ * (h.leadingFactor ℓ)ᴴ =
      U * Matrix.diagonal (fun i : Fin p =>
        if (i : ℕ) < ℓ then ((singularValues A i ^ 2 : ℝ) : 𝕜) else 0) * Uᴴ := by
  rw [IsSVD.leadingFactor, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (rectDiag (singularValues A)), rectDiag_mul_conjTranspose_rectDiag]

/-- The native truncated-matrix tail has the discarded singular-coordinate Gram. -/
theorem IsSVD.tail_mul_conjTranspose {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V) (ℓ : ℕ) :
    (A - h.truncatedMatrix ℓ) * (A - h.truncatedMatrix ℓ)ᴴ =
      U * Matrix.diagonal (fun i : Fin p =>
        if (i : ℕ) < ℓ then 0 else ((singularValues A i ^ 2 : ℝ) : 𝕜)) * Uᴴ := by
  let T : Matrix (Fin p) (Fin q) 𝕜 :=
    rectDiag (fun i => if i < ℓ then 0 else singularValues A i)
  have he : A - h.truncatedMatrix ℓ = U * T * Vᴴ := by
    have hd := h.eq_head_add_tail ℓ
    change A = h.truncatedMatrix ℓ + U * T * Vᴴ at hd
    calc
      _ = (h.truncatedMatrix ℓ + U * T * Vᴴ) - h.truncatedMatrix ℓ :=
        congrArg (fun M => M - h.truncatedMatrix ℓ) hd
      _ = _ := by abel
  rw [he, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᴴ V, h.conjTranspose_mul_right, Matrix.one_mul,
    ← Matrix.mul_assoc T, rectDiag_mul_conjTranspose_rectDiag]
  have hD : (Matrix.diagonal (fun i : Fin p => if (i : ℕ) < q then
      ((((if (i : ℕ) < ℓ then 0 else singularValues A i) ^ 2 : ℝ)) : 𝕜) else 0)) =
      Matrix.diagonal (fun i : Fin p => if (i : ℕ) < ℓ then 0 else
        ((singularValues A i ^ 2 : ℝ) : 𝕜)) := by
    congr 1
    funext i
    by_cases hiq : (i : ℕ) < q
    · by_cases hiℓ : (i : ℕ) < ℓ <;> simp [hiq, hiℓ]
    · have hz : singularValues A i = 0 := singularValues_eq_zero_of_width_le A
        (show Fintype.card n ≤ (i : ℕ) by rw [h.card_right]; omega)
      simp [hiq, hz]
  simpa only [Matrix.mul_assoc] using congrArg (fun D => U * D * Uᴴ) hD

/-- Leading factor and discarded tail give the exact orthogonal row-Gram split. -/
theorem IsSVD.sub_leadingFactor_gram_eq_tail_gram {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V) (ℓ : ℕ) :
    A * Aᴴ - h.leadingFactor ℓ * (h.leadingFactor ℓ)ᴴ =
      (A - h.truncatedMatrix ℓ) * (A - h.truncatedMatrix ℓ)ᴴ := by
  rw [h.mul_conjTranspose_self, h.leadingFactor_mul_conjTranspose,
    h.tail_mul_conjTranspose, ← Matrix.sub_mul, ← Matrix.mul_sub,
    Matrix.diagonal_sub]
  have hCoeff : (fun i : Fin p => ((singularValues A i ^ 2 : ℝ) : 𝕜) -
      if (i : ℕ) < ℓ then ((singularValues A i ^ 2 : ℝ) : 𝕜) else 0) =
      (fun i : Fin p => if (i : ℕ) < ℓ then 0 else ((singularValues A i ^ 2 : ℝ) : 𝕜)) := by
    funext i
    by_cases hi : (i : ℕ) < ℓ <;> simp [hi]
  exact congrArg (fun f : Fin p → 𝕜 => U * Matrix.diagonal f * Uᴴ) hCoeff

/-- A rank-at-most-k orthogonal projector captures at most the first k squares of the
discarded singular values. This avoids choosing any SVD of the tail itself. -/
theorem IsSVD.frobSq_projector_tail_le_sum_shifted {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V)
    {ℓ k : ℕ} (hℓp : ℓ ≤ p) {P : Matrix m m 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) (hr : P.rank ≤ k) :
    frobSq (P * (A - h.truncatedMatrix ℓ)) ≤
      ∑ j ∈ Finset.range k, singularValues A (ℓ + j) ^ 2 := by
  let R := Uᴴ * P * U
  have hsR : R.IsHermitian := by
    change (Uᴴ * P * U)ᴴ = Uᴴ * P * U
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hs.eq,
      Matrix.mul_assoc]
  have hpR : IsIdempotentElem R := by
    change (Uᴴ * P * U) * (Uᴴ * P * U) = Uᴴ * P * U
    calc
      _ = Uᴴ * (P * (U * Uᴴ) * P) * U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h.mul_conjTranspose_left, Matrix.mul_one, show P * P = P from hp]
  let w : ℕ → ℝ := fun i => if hi : i < p then RCLike.re (R ⟨i, hi⟩ ⟨i, hi⟩) else 0
  have hw (i : ℕ) : w i ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [w]
    split_ifs with hi
    · exact re_diag_mem_Icc_of_isHermitian_of_isIdempotentElem R hsR hpR _
    · exact ⟨le_rfl, zero_le_one⟩
  have hbudget : ∑ i ∈ Finset.range p, w i ≤ (k : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range w p]
    simp only [w, dif_pos (Fin.isLt _)]
    rw [h.re_trace_conjTranspose_mul_mul P,
      trace_eq_rank_of_isIdempotentElem P hp, RCLike.natCast_re]
    exact_mod_cast hr
  have hCapture : frobSq (P * (A - h.truncatedMatrix ℓ)) =
      ∑ i ∈ Finset.range p, if i < ℓ then 0 else singularValues A i ^ 2 * w i := by
    let T := A - h.truncatedMatrix ℓ
    let D : Matrix (Fin p) (Fin p) 𝕜 := Matrix.diagonal (fun i =>
      if (i : ℕ) < ℓ then 0 else ((singularValues A i ^ 2 : ℝ) : 𝕜))
    have hPT : frobSq (P * T) = RCLike.re (P * (T * Tᴴ)).trace := by
      rw [← frobSq_conjTranspose (P * T), Matrix.conjTranspose_mul, hs.eq,
        frobSq_mul_projector_eq_re_trace_mul hs hp Tᴴ, Matrix.conjTranspose_conjTranspose]
    change frobSq (P * T) = _
    rw [hPT, h.tail_mul_conjTranspose ℓ]
    calc
      _ = RCLike.re ((P * U) * D * Uᴴ).trace := by simp only [Matrix.mul_assoc, D]
      _ = RCLike.re (Uᴴ * ((P * U) * D)).trace := by rw [Matrix.trace_mul_comm]
      _ = RCLike.re (R * D).trace := by simp only [R, Matrix.mul_assoc]
      _ = RCLike.re (D * R).trace := by rw [Matrix.trace_mul_comm]
      _ = ∑ i : Fin p, if (i : ℕ) < ℓ then 0 else singularValues A i ^ 2 * w i := by
        simp only [D, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, map_sum]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : (i : ℕ) < ℓ <;> simp [hi, w, i.isLt]
      _ = _ := Fin.sum_univ_eq_sum_range (fun i =>
        if i < ℓ then 0 else singularValues A i ^ 2 * w i) p
  rw [hCapture]
  exact sum_tail_mul_le_sum_shifted hℓp (fun i => sq_nonneg _) (by
    intro i j hij
    exact pow_le_pow_left₀ (singularValues_nonneg A j) (singularValues_antitone A hij) 2)
    (fun i => (hw i).1) (fun i => (hw i).2) hbudget

/-- Tail averaging gives the sharper k/ℓ captured-energy constant; no spectral gap or
individual tail SVD is required. The zero target rank is included. -/
theorem IsSVD.mul_frobSq_projector_tail_le_mul_bestRankFrobSq {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V)
    {ℓ k : ℕ} (hℓp : ℓ ≤ p) (hkl : k ≤ ℓ) {P : Matrix m m 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) (hr : P.rank ≤ k) :
    (ℓ : ℝ) * frobSq (P * (A - h.truncatedMatrix ℓ)) ≤
      (k : ℝ) * bestRankFrobSq A k := by
  have ha : Antitone (fun i => singularValues A i ^ 2) := by
    intro i j hij
    exact pow_le_pow_left₀ (singularValues_nonneg A j) (singularValues_antitone A hij) 2
  have hCapture := h.frobSq_projector_tail_le_sum_shifted hℓp hs hp hr
  have hAverage := ha.mul_sum_tail_le_mul_sum_block hkl
  have hSplit := frobSq_eq_sum_prefix_sq_add_bestRankFrobSq A k
  have hSum := frobSq_eq_sum_prefix_sq_add_bestRankFrobSq A (k + ℓ)
  rw [Finset.sum_range_add] at hSum
  have hTail0 : 0 ≤ bestRankFrobSq A (k + ℓ) := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> positivity
  have hBlock : (∑ i ∈ Finset.range ℓ, singularValues A (k + i) ^ 2) ≤ bestRankFrobSq A k := by
    linarith
  exact (mul_le_mul_of_nonneg_left hCapture (Nat.cast_nonneg ℓ)).trans
    (hAverage.trans (mul_le_mul_of_nonneg_left hBlock (Nat.cast_nonneg k)))

/-- At a cutoff reaching the ambient singular dimension, the discarded tail is zero. -/
theorem IsSVD.sub_truncatedMatrix_eq_zero_of_min_le {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V)
    {ℓ : ℕ} (hℓ : min (Fintype.card m) (Fintype.card n) ≤ ℓ) :
    A - h.truncatedMatrix ℓ = 0 := by
  apply (frobSq_eq_zero_iff _).mp
  rw [h.frobSq_sub_truncatedMatrix, bestRankFrobSq]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi
  · rw [singularValues_eq_zero_of_min_le A (hℓ.trans hi)]
    simp
  · rfl

end NLAlib
