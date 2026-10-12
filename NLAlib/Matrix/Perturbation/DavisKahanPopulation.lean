import NLAlib.Matrix.Perturbation.PopulationTraceGap
import NLAlib.Matrix.Inequalities.VonNeumann
import NLAlib.Matrix.Basic.RankBounds
/-!
# Population-gap Davis–Kahan Frobenius bounds

The finite trace deficit bounds genuine top eigenspaces without a smallness
assumption. Frobenius Cauchy–Schwarz gives the sharper `sqrt 2` branch and the
rank trace inequality gives `2 * sqrt k` in spectral perturbation norm.
Source: Yu–Wang–Samworth (2015), Theorem 2; atlas `davis-kahan-sin-theta`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {A E : Matrix n n ℝ}

/-- The Frobenius norm of the difference of equal-width frame projectors
is `sqrt 2` times the sine-angle Frobenius norm. Stewart–Sun §I.5. -/
theorem frobNorm_projector_distance_eq_sqrt_two_mul_sinePrincipalAngles
    {r : Type*} [Fintype r] [DecidableEq r] {P Q : Matrix n r ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    frobNorm (P*Pᵀ-Q*Qᵀ)=Real.sqrt 2*frobNorm (sinePrincipalAngles P Q) := by
  have hh := frobSq_projector_distance_eq_two_mul_sinePrincipalAngles hP hQ
  rw [← frobNorm_sq, ← frobNorm_sq] at hh
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn := frobNorm_nonneg (P*Pᵀ-Q*Qᵀ)
  have hn' := frobNorm_nonneg (sinePrincipalAngles P Q)
  have heq : frobNorm (P*Pᵀ-Q*Qᵀ)^2=(Real.sqrt 2*frobNorm (sinePrincipalAngles P Q))^2 := by
    rw [mul_pow, hs]; exact hh
  exact (sq_eq_sq₀ hn (mul_nonneg (Real.sqrt_nonneg _) hn')).mp heq

omit [DecidableEq n] in
/-- The projector difference of width-`k` frames has rank at most `2*k`.
Stewart–Sun §I.5; no full-width or nonempty-index assumption is needed. -/
theorem rank_sub_frame_projector_le_two_mul {k : ℕ} (P Q : Matrix n (Fin k) ℝ) :
    (P*Pᵀ-Q*Qᵀ).rank ≤ 2*k := by
  have heq : P*Pᵀ-Q*Qᵀ=P*Pᵀ+(-Q)*Qᵀ := by rw [Matrix.neg_mul, sub_eq_add_neg]
  rw [heq]
  have hP : (P*Pᵀ).rank ≤ k :=
    (Matrix.rank_mul_le_left P Pᵀ).trans (by simpa using P.rank_le_card_width)
  have hQ : ((-Q)*Qᵀ).rank ≤ k :=
    (Matrix.rank_mul_le_left (-Q) Qᵀ).trans (by simpa using (-Q).rank_le_card_width)
  exact (rank_add_le _ _).trans (by omega)

/-- The unconditional top-cluster Frobenius bound retains both perturbation
norms and improves the Frobenius branch to `sqrt 2`. Yu–Wang–Samworth (2015),
Theorem 2, via the finite trace deficit. The perturbed frame may be any
orthonormal maximizer of the actual top-`k` compression trace, including
arbitrary choices at repeated eigenvalues.
atlas: davis-kahan-sin-theta (partial) -/
theorem frobNorm_sinePrincipalAngles_le_min_div_population_gap
    (hA : A.IsHermitian) (hE : E.IsHermitian) {k : ℕ}
    (hk0 : 0 < k) (hkN : k < Fintype.card n)
    (hg : 0 < hA.eigenvalues₀ ⟨k-1, by omega⟩-hA.eigenvalues₀ ⟨k, hkN⟩)
    {Q : Matrix n (Fin k) ℝ} (hQ : HasOrthonormalCols Q)
    (htop : (Qᵀ*(A+E)*Q).trace=eigenvaluePrefix (hA.add hE) hkN.le) :
    frobNorm (sinePrincipalAngles (topEigenframe hA hkN.le) Q) ≤
      min (2*Real.sqrt k*specNorm E) (Real.sqrt 2*frobNorm E)/
        (hA.eigenvalues₀ ⟨k-1, by omega⟩-hA.eigenvalues₀ ⟨k, hkN⟩) := by
  let P := topEigenframe hA hkN.le
  let S := frobNorm (sinePrincipalAngles P Q)
  let g := hA.eigenvalues₀ ⟨k-1, by omega⟩-hA.eigenvalues₀ ⟨k, hkN⟩
  have hP : HasOrthonormalCols P := hasOrthonormalCols_topEigenframe hA hkN.le
  have hS0 : 0 ≤ S := frobNorm_nonneg _
  have hdef := mul_frobSq_sinePrincipalAngles_le_frobInner_perturbation hA hE hk0 hkN hQ htop
  rw [← frobNorm_sq] at hdef
  change g*S^2 ≤ frobInner (Q*Qᵀ-P*Pᵀ) E at hdef
  have hnorm : frobNorm (Q*Qᵀ-P*Pᵀ)=Real.sqrt 2*S := by
    rw [show Q*Qᵀ-P*Pᵀ=-(P*Pᵀ-Q*Qᵀ) by abel, frobNorm_neg]
    exact frobNorm_projector_distance_eq_sqrt_two_mul_sinePrincipalAngles hP hQ
  have hF := frobInner_le_frobNorm_mul_frobNorm (Q*Qᵀ-P*Pᵀ) E
  have hO := frobInner_le_sqrt_mul_frobNorm_mul_specNorm_of_rank_le
    (Q*Qᵀ-P*Pᵀ) E (rank_sub_frame_projector_le_two_mul Q P)
  rw [hnorm] at hF hO
  have hroot : Real.sqrt (↑(2*k) : ℝ)=Real.sqrt 2*Real.sqrt k := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hroot] at hO
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply (le_div_iff₀ hg).2
  change S*g ≤ min (2*Real.sqrt k*specNorm E) (Real.sqrt 2*frobNorm E)
  apply le_min
  · by_cases hS : S=0
    · simp only [hS, zero_mul]; exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (specNorm_nonneg _)
    · have hSp : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS)
      have heq : Real.sqrt 2*Real.sqrt k*(Real.sqrt 2*S)*specNorm E =
          (2*Real.sqrt k*specNorm E)*S := by
        calc
          _ = (Real.sqrt 2)^2*(Real.sqrt k*specNorm E*S) := by ring
          _ = _ := by rw [hs]; ring
      rw [heq] at hO
      exact le_of_mul_le_mul_right (by nlinarith [hdef.trans hO]) hSp
  · by_cases hS : S=0
    · simp only [hS, zero_mul]; exact mul_nonneg (Real.sqrt_nonneg _) (frobNorm_nonneg _)
    · have hSp : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS)
      exact le_of_mul_le_mul_right (by nlinarith [hdef.trans hF]) hSp

/-- The advertised constant-two Frobenius minimum follows from the sharper
top-cluster trace bounds. Yu–Wang–Samworth (2015), Theorem 2; no perturbation
smallness hypothesis is imposed.
atlas: davis-kahan-sin-theta (partial) -/
theorem frobNorm_sinePrincipalAngles_le_two_mul_min_div_population_gap
    (hA : A.IsHermitian) (hE : E.IsHermitian) {k : ℕ}
    (hk0 : 0 < k) (hkN : k < Fintype.card n)
    (hg : 0 < hA.eigenvalues₀ ⟨k-1, by omega⟩-hA.eigenvalues₀ ⟨k, hkN⟩)
    {Q : Matrix n (Fin k) ℝ} (hQ : HasOrthonormalCols Q)
    (htop : (Qᵀ*(A+E)*Q).trace=eigenvaluePrefix (hA.add hE) hkN.le) :
    frobNorm (sinePrincipalAngles (topEigenframe hA hkN.le) Q) ≤
      2*min (Real.sqrt k*specNorm E) (frobNorm E)/
        (hA.eigenvalues₀ ⟨k-1, by omega⟩-hA.eigenvalues₀ ⟨k, hkN⟩) := by
  have hh := frobNorm_sinePrincipalAngles_le_min_div_population_gap hA hE hk0 hkN hg hQ htop
  apply hh.trans
  apply div_le_div_of_nonneg_right _ hg.le
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  apply min_le_min
  · ring_nf; exact le_rfl
  · apply mul_le_mul_of_nonneg_right _ (frobNorm_nonneg E)
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]

end NLAlib
