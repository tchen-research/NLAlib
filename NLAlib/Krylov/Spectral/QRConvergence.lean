import NLAlib.Krylov.Spectral.QRFlags
import NLAlib.Matrix.Subspaces.ColumnAlignment
import NLAlib.Matrix.Spectral.OrderedRatios
import NLAlib.Matrix.Norms.OrthogonalConjugation
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Geometric convergence of unshifted symmetric QR

Convergence of all leading flags gives convergence of the ordered columns after
sign alignment. Only proper leading overlaps are inverted; the last eigenvalue
may be zero. Source: Trefethen--Bau, Theorem 28.4 and its simultaneous-iteration proof.
-/

noncomputable section
open scoped Matrix Topology
open Filter
namespace NLAlib
variable {n : ℕ}

/-- A finite explicit sum of the initial leading-flag tangents. -/
def qrFlagConstant (Q : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ j : Fin (n+1), Real.sqrt (2 * (j.val : ℝ)) *
    overlapTangentNorm (headColumns Q (show j.val ≤ n by omega))
      (headColumns (1 : Matrix (Fin n) (Fin n) ℝ) (show j.val ≤ n by omega))

/-- The leading-flag constant is nonnegative. -/
theorem qrFlagConstant_nonneg (Q : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ qrFlagConstant Q := by
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (overlapTangentNorm_nonneg _ _)

/-- Every initial flag coefficient is bounded by their sum. -/
theorem sqrt_mul_overlapTangentNorm_le_qrFlagConstant (Q : Matrix (Fin n) (Fin n) ℝ)
    {j : ℕ} (hj : j ≤ n) :
    Real.sqrt (2 * (j : ℝ)) * overlapTangentNorm (headColumns Q hj)
      (headColumns (1 : Matrix (Fin n) (Fin n) ℝ) hj) ≤ qrFlagConstant Q := by
  unfold qrFlagConstant
  exact Finset.single_le_sum (f := fun i : Fin (n+1) =>
    Real.sqrt (2 * (i.val : ℝ)) * overlapTangentNorm (headColumns Q (show i.val ≤ n by omega))
      (headColumns (1 : Matrix (Fin n) (Fin n) ℝ) (show i.val ≤ n by omega))) (fun i _ =>
    mul_nonneg (Real.sqrt_nonneg _) (overlapTangentNorm_nonneg _ _))
      (Finset.mem_univ (⟨j, by omega⟩ : Fin (n+1)))

/-- The leading overlap with coordinate vectors is exactly the corresponding
leading principal submatrix of the transposed eigenvector matrix. -/
theorem transpose_headColumns_mul_headColumns_one (Q : Matrix (Fin n) (Fin n) ℝ)
    {j : ℕ} (hj : j ≤ n) :
    (headColumns Q hj)ᵀ * headColumns (1 : Matrix (Fin n) (Fin n) ℝ) hj =
      Qᵀ.submatrix (Fin.castLE hj) (Fin.castLE hj) := by
  rw [mul_headColumns, Matrix.mul_one]
  rfl

/-- Every leading QR projector converges at the maximum consecutive eigenvalue
modulus ratio, including the empty and full flags.
atlas: qr-algorithm-convergence (partial) -/
theorem frobNorm_head_projector_qrAlgorithm_le
    {qr : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ}
    {A Q : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    (hQ : HasOrthonormalCols Q) (hAQ : A * Q = Q * Matrix.diagonal d)
    (hd : StrictAnti fun i => |d i|)
    (hminor : ∀ j (hj : j ≤ n), IsUnit (Qᵀ.submatrix (Fin.castLE hj) (Fin.castLE hj)))
    {k : ℕ} (hqr : QRAlgorithmSucceeds qr (fun _ => 0) A k) {j : ℕ} (hj : j ≤ n) :
    frobNorm (headColumns Q hj * (headColumns Q hj)ᵀ -
      headColumns (qrAlgorithmQ qr (fun _ => 0) A k) hj *
        (headColumns (qrAlgorithmQ qr (fun _ => 0) A k) hj)ᵀ) ≤
      qrFlagConstant Q * maxAdjacentAbsRatio d ^ k := by
  have hr := maxAdjacentAbsRatio_nonneg d
  have hc := qrFlagConstant_nonneg Q
  have hW : HasOrthonormalCols (qrAlgorithmQ qr (fun _ => 0) A k) :=
    transpose_mul_self_qrAlgorithmQ hqr
  by_cases hj0 : j = 0
  · subst j
    simpa [headColumns, Matrix.mul_apply] using mul_nonneg hc (pow_nonneg hr k)
  by_cases hjn : j = n
  · subst j
    have hf (Z : Matrix (Fin n) (Fin n) ℝ) : headColumns Z le_rfl = Z := by ext a b; rfl
    rw [hf, hf]
    change frobNorm (Q * Qᴴ - _ * (qrAlgorithmQ qr (fun _ => 0) A k)ᴴ) ≤ _
    rw [mul_eq_one_comm.mp hQ, mul_eq_one_comm.mp hW, sub_self, frobNorm_zero]
    positivity
  have hjlt : j < n := lt_of_le_of_ne hj hjn
  let a : Fin n := ⟨j-1, by omega⟩
  let b : Fin n := ⟨j, hjlt⟩
  have hab : a < b := by change j-1 < j; omega
  have ha : 0 < |d a| := lt_of_le_of_lt (abs_nonneg _) (hd hab)
  have hlower (i : Fin j) : |d a| ≤ |d (Fin.castLE hj i)| := by
    exact hd.antitone (show Fin.castLE hj i ≤ a by change i.val ≤ j-1; omega)
  have hupper (i : Fin (n-j)) : |d ⟨j+i.val, by omega⟩| ≤ |d b| := by
    exact hd.antitone (show b ≤ (⟨j+i.val, by omega⟩ : Fin n) by change j ≤ j+i.val; omega)
  have ho : IsUnit ((headColumns Q hj)ᵀ * headColumns (1 : Matrix (Fin n) (Fin n) ℝ) hj) := by
    rw [transpose_headColumns_mul_headColumns_one]
    exact hminor j hj
  have hd0 (i : Fin j) : d (Fin.castLE hj i) ≠ 0 := by
    intro hz
    have h := hlower i
    rw [hz, abs_zero] at h
    linarith
  have hi := (qrAlgorithm_head_overlap_isUnit hQ hAQ hj hd0 ho hqr).1
  have hg := frobNorm_sub_frame_projector_le_overlapTangentNorm
    (hasOrthonormalCols_headColumns hQ hj) (hasOrthonormalCols_headColumns hW hj) hi
  have ht := overlapTangentNorm_qrAlgorithm_head_le hQ hAQ hj ha (abs_nonneg _) hlower hupper ho hqr
  have hratio : |d b| / |d a| ≤ maxAdjacentAbsRatio d := by
    simpa only [a, b, show j-1+1=j by omega] using adjacentAbsRatio_le_max d a (by dsimp [a]; omega)
  have hpow := pow_le_pow_left₀ (div_nonneg (abs_nonneg _) (abs_nonneg _)) hratio k
  have hsum := sqrt_mul_overlapTangentNorm_le_qrFlagConstant Q hj
  simp only [Fintype.card_fin] at hg
  calc
    _ ≤ Real.sqrt (2 * (j : ℝ)) * overlapTangentNorm (headColumns Q hj)
        (headColumns (qrAlgorithmQ qr (fun _ => 0) A k) hj) := hg
    _ ≤ Real.sqrt (2 * (j : ℝ)) * ((|d b| / |d a|)^k *
        overlapTangentNorm (headColumns Q hj) (headColumns (1 : Matrix (Fin n) (Fin n) ℝ) hj)) :=
      mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg _)
    _ ≤ (Real.sqrt (2 * (j : ℝ)) * overlapTangentNorm (headColumns Q hj)
        (headColumns (1 : Matrix (Fin n) (Fin n) ℝ) hj)) * maxAdjacentAbsRatio d ^ k := by
      nlinarith [mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (Real.sqrt_nonneg (2 * (j:ℝ)))
          (overlapTangentNorm_nonneg (headColumns Q hj) (headColumns (1 : Matrix (Fin n) (Fin n) ℝ) hj)))]
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum (pow_nonneg hr k)

/-- Both the accumulated QR frame, up to column signs, and the actual matrix
iterate satisfy a geometric bound with the exact consecutive-modulus rate.
The QR routine is arbitrary subject to its native success predicate.
atlas: qr-algorithm-convergence (partial) -/
theorem exists_signs_frobNorm_qrAlgorithm_le
    {qr : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ}
    {A Q : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    (hQ : HasOrthonormalCols Q) (hAQ : A * Q = Q * Matrix.diagonal d)
    (hd : StrictAnti fun i => |d i|)
    (hminor : ∀ j (hj : j ≤ n), IsUnit (Qᵀ.submatrix (Fin.castLE hj) (Fin.castLE hj)))
    {k : ℕ} (hqr : QRAlgorithmSucceeds qr (fun _ => 0) A k) :
    ∃ s : Fin n → ℝ, (∀ i, s i ^ 2 = 1) ∧
      frobNorm (qrAlgorithmQ qr (fun _ => 0) A k - Q * Matrix.diagonal s) ≤
        (2 * Real.sqrt n * qrFlagConstant Q) * maxAdjacentAbsRatio d ^ k ∧
      frobNorm (qrAlgorithm qr (fun _ => 0) A k - Matrix.diagonal d) ≤
        (2 * specNorm A * (2 * Real.sqrt n * qrFlagConstant Q)) * maxAdjacentAbsRatio d ^ k := by
  have hW : HasOrthonormalCols (qrAlgorithmQ qr (fun _ => 0) A k) :=
    transpose_mul_self_qrAlgorithmQ hqr
  obtain ⟨s, hs, hb⟩ := exists_signs_frobNorm_sub_le_of_head_projectors hQ hW
    (mul_nonneg (qrFlagConstant_nonneg Q) (pow_nonneg (maxAdjacentAbsRatio_nonneg d) k))
    (fun j hj => frobNorm_head_projector_qrAlgorithm_le hQ hAQ hd hminor hqr hj)
  have hb' : frobNorm (qrAlgorithmQ qr (fun _ => 0) A k - Q * Matrix.diagonal s) ≤
        (2 * Real.sqrt n * qrFlagConstant Q) * maxAdjacentAbsRatio d ^ k := by
    convert hb using 1; ring
  refine ⟨s, hs, hb', ?_⟩
  have hsdiag : (Matrix.diagonal s)ᵀ * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    nlinarith [hs i]
  have hV : HasOrthonormalCols (Q * Matrix.diagonal s) := by
    change (Q * Matrix.diagonal s)ᴴ * (Q * Matrix.diagonal s) = 1
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ,
      hQ.conjTranspose_mul_self, Matrix.one_mul]
    exact hsdiag
  have hdiag : Qᵀ * A * Q = Matrix.diagonal d := by
    rw [Matrix.mul_assoc, hAQ, ← Matrix.mul_assoc]
    change (Qᴴ * Q) * Matrix.diagonal d = _
    rw [hQ.conjTranspose_mul_self, Matrix.one_mul]
  have hrepr : (Q * Matrix.diagonal s)ᵀ * A * (Q * Matrix.diagonal s) = Matrix.diagonal d := by
    calc
      _ = Matrix.diagonal s * (Qᵀ * A * Q) * Matrix.diagonal s := by
        simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
      _ = Matrix.diagonal s * Matrix.diagonal d * Matrix.diagonal s := by rw [hdiag]
      _ = Matrix.diagonal d := by
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        change (s i * d i) * s i = d i
        calc
          _ = d i * s i ^ 2 := by ring
          _ = d i := by rw [hs i, mul_one]
  rw [qrAlgorithm_eq_transpose_mul_mul hqr, ← hrepr]
  have hp := frobNorm_conjTranspose_mul_mul_sub_le A hW hV
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hp
  calc
    _ ≤ 2 * specNorm A * frobNorm (qrAlgorithmQ qr (fun _ => 0) A k - Q * Matrix.diagonal s) := hp
    _ ≤ 2 * specNorm A * ((2 * Real.sqrt n * qrFlagConstant Q) * maxAdjacentAbsRatio d ^ k) :=
      mul_le_mul_of_nonneg_left hb' (mul_nonneg (by norm_num) (specNorm_nonneg A))
    _ = _ := by ring

/-- Infinite native unshifted QR runs converge to the ordered eigenvalue
diagonal, and admit column signs for convergence to the eigenvector matrix.
The geometric rate is the maximum consecutive eigenvalue modulus ratio.
atlas: qr-algorithm-convergence (partial) -/
theorem tendsto_frobNorm_qrAlgorithm_and_alignedQ
    {qr : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ}
    {A Q : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    (hQ : HasOrthonormalCols Q) (hAQ : A * Q = Q * Matrix.diagonal d)
    (hd : StrictAnti fun i => |d i|)
    (hminor : ∀ j (hj : j ≤ n), IsUnit (Qᵀ.submatrix (Fin.castLE hj) (Fin.castLE hj)))
    (hqr : ∀ k, QRAlgorithmSucceeds qr (fun _ => 0) A k) :
    Tendsto (fun k => frobNorm (qrAlgorithm qr (fun _ => 0) A k - Matrix.diagonal d)) atTop (𝓝 0) ∧
      ∃ s : ℕ → Fin n → ℝ, (∀ k i, s k i ^ 2 = 1) ∧
        Tendsto (fun k => frobNorm (qrAlgorithmQ qr (fun _ => 0) A k - Q * Matrix.diagonal (s k)))
          atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (maxAdjacentAbsRatio_nonneg d)
    (maxAdjacentAbsRatio_lt_one hd)
  choose s hs hframe hiter using fun k => exists_signs_frobNorm_qrAlgorithm_le hQ hAQ hd hminor (hqr k)
  constructor
  · apply squeeze_zero (fun _ => frobNorm_nonneg _) hiter
    simpa only [mul_zero] using hp.const_mul (2 * specNorm A * (2 * Real.sqrt n * qrFlagConstant Q))
  · refine ⟨s, hs, ?_⟩
    apply squeeze_zero (fun _ => frobNorm_nonneg _) hframe
    simpa only [mul_zero] using hp.const_mul (2 * Real.sqrt n * qrFlagConstant Q)

end NLAlib
