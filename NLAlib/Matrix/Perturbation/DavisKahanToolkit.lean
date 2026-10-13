import NLAlib.Matrix.Perturbation.DavisKahanFrames
/-!
# Complete davis kahan sin theta contract

The clauses below are the actual universally quantified public statements,
assembled so that a full atlas tag certifies the entire family. Individual
clauses remain available in the imported topic modules.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
open scoped ENNReal
namespace NLAlib
universe u_1 u_2 u_3

/-- All clauses of the davis-kahan-sin-theta result, with their original hypotheses,
constants, finite indices and endpoint conventions.
Components: `davis_kahan_bounds`, `davis_kahan_top_frame_bounds`, `frobNorm_sinePrincipalAngles_le_min_div_population_gap_of_frames`, `sinePrincipalAngles_eq_zero_of_empty_or_full_frames`.
Source: dk70, sin θ theorem (§6); bhatia97, Thm VII.3.1; ss90, Thm V.3.6; ywss15, Thm 2.
atlas: davis-kahan-sin-theta -/
theorem davis_kahan_toolkit_properties :
    (∀ {n : Type u_1} {k : Type u_2} {r : Type u_3} [_inst : Fintype n] [_inst_1 : Fintype k]
  [_inst_2 : Fintype r] [_inst_3 : DecidableEq n] [_inst_4 : DecidableEq k] [_inst_5 : DecidableEq r]
  {A E : Matrix n n ℝ} (hA : A.IsHermitian) (hE : E.IsHermitian) {Q Qhat : Matrix n k ℝ}
  {R : Matrix n r ℝ} (hQ : NLAlib.HasOrthonormalCols Q),
  NLAlib.HasOrthonormalCols Qhat →
    ∀ (hR : NLAlib.HasOrthonormalCols R),
      Qhat * Qhat.transpose + R * R.transpose = 1 →
        ∀ {L : Matrix k k ℝ} {M : Matrix r r ℝ} (hAQ : A * Q = Q * L) (hAR : (A + E) * R = R * M),
          (∀ (a b δ : ℝ),
              0 < δ →
                (∀ (j : k),
                    a ≤
                        (NLAlib.isHermitian_of_invariant_orthonormal_frame hA hQ hAQ).eigenvalues
                          j ∧
                      (NLAlib.isHermitian_of_invariant_orthonormal_frame hA hQ hAQ).eigenvalues j ≤
                        b) →
                  (∀ (i : r),
                      (NLAlib.isHermitian_of_invariant_orthonormal_frame
                                (Matrix.IsHermitian.add hA hE) hR hAR).eigenvalues
                            i ≤
                          a - δ ∨
                        b + δ ≤
                          (NLAlib.isHermitian_of_invariant_orthonormal_frame
                                (Matrix.IsHermitian.add hA hE) hR hAR).eigenvalues
                            i) →
                    NLAlib.specNorm (NLAlib.sinePrincipalAngles Q Qhat) ≤
                        NLAlib.specNorm (R.transpose * E * Q) / δ ∧
                      NLAlib.specNorm (R.transpose * E * Q) / δ ≤ NLAlib.specNorm (E * Q) / δ ∧
                        NLAlib.specNorm (E * Q) / δ ≤ NLAlib.specNorm E / δ ∧
                          NLAlib.frobNorm (NLAlib.sinePrincipalAngles Q Qhat) ≤
                              NLAlib.frobNorm (R.transpose * E * Q) / δ ∧
                            NLAlib.frobNorm (R.transpose * E * Q) / δ ≤
                                NLAlib.frobNorm (E * Q) / δ ∧
                              NLAlib.frobNorm (E * Q) / δ ≤ NLAlib.frobNorm E / δ ∧
                                NLAlib.frobNorm (E * Q) / δ ≤
                                  √↑(Fintype.card k) * NLAlib.specNorm E / δ) ∧
            (∀ (j : ℕ) (hj0 : 0 < j) (hjN : j < Fintype.card n),
                0 <
                    hA.eigenvalues₀
                        ⟨j - 1, by omega⟩ -
                      (Matrix.IsHermitian.add hA hE).eigenvalues₀ ⟨j, hjN⟩ →
                  have S :=
                    NLAlib.sinePrincipalAngles (NLAlib.topEigenframe hA (LT.lt.le hjN))
                      (NLAlib.topEigenframe (Matrix.IsHermitian.add hA hE) (LT.lt.le hjN));
                  have δ :=
                    hA.eigenvalues₀
                        ⟨j - 1, by omega⟩ -
                      (Matrix.IsHermitian.add hA hE).eigenvalues₀ ⟨j, hjN⟩;
                  NLAlib.specNorm S ≤ NLAlib.specNorm E / δ ∧
                    NLAlib.frobNorm S ≤ Min.min (√↑j * NLAlib.specNorm E) (NLAlib.frobNorm E) / δ) ∧
              (∀ (j : ℕ) (hj0 : 0 < j) (hjN : j < Fintype.card n),
                  0 <
                      hA.eigenvalues₀
                          ⟨j - 1, by omega⟩ -
                        hA.eigenvalues₀ ⟨j, hjN⟩ →
                    have S :=
                      NLAlib.sinePrincipalAngles (NLAlib.topEigenframe hA (LT.lt.le hjN))
                        (NLAlib.topEigenframe (Matrix.IsHermitian.add hA hE) (LT.lt.le hjN));
                    have g :=
                      hA.eigenvalues₀
                          ⟨j - 1, by omega⟩ -
                        hA.eigenvalues₀ ⟨j, hjN⟩;
                    NLAlib.specNorm S ≤ 2 * NLAlib.specNorm E / g ∧
                      NLAlib.frobNorm S ≤
                        2 * Min.min (√↑j * NLAlib.specNorm E) (NLAlib.frobNorm E) / g) ∧
                ∀ (j : ℕ) (hj : j ≤ Fintype.card n),
                  j = 0 ∨ j = Fintype.card n →
                    NLAlib.sinePrincipalAngles (NLAlib.topEigenframe hA hj)
                        (NLAlib.topEigenframe (Matrix.IsHermitian.add hA hE) hj) =
                      0) ∧
    (∀ {n : Type u_1} {r : Type u_3} [_inst : Fintype n] [_inst_1 : Fintype r] [_inst_2 : DecidableEq n]
  [_inst_3 : DecidableEq r] {A E : Matrix n n ℝ} (hA : A.IsHermitian) (hE : E.IsHermitian) {j : ℕ}
  (hj0 : 0 < j) (hjN : j < Fintype.card n) {Q Qhat : Matrix n (Fin j) ℝ} {R : Matrix n r ℝ}
  (hQ : NLAlib.HasOrthonormalCols Q),
  NLAlib.HasOrthonormalCols Qhat →
    ∀ (hR : NLAlib.HasOrthonormalCols R),
      Qhat * Qhat.transpose + R * R.transpose = 1 →
        ∀ {L : Matrix (Fin j) (Fin j) ℝ} {M : Matrix r r ℝ} (hAQ : A * Q = Q * L)
          (hAR : (A + E) * R = R * M),
          (∀ (t : Fin j),
              hA.eigenvalues₀
                  ⟨j - 1, by omega⟩ ≤
                (NLAlib.isHermitian_of_invariant_orthonormal_frame hA hQ hAQ).eigenvalues t) →
            (∀ (t : r),
                (NLAlib.isHermitian_of_invariant_orthonormal_frame (Matrix.IsHermitian.add hA hE) hR
                        hAR).eigenvalues
                    t ≤
                  (Matrix.IsHermitian.add hA hE).eigenvalues₀ ⟨j, hjN⟩) →
              have S := NLAlib.sinePrincipalAngles Q Qhat;
              have δ :=
                hA.eigenvalues₀
                    ⟨j - 1, by omega⟩ -
                  (Matrix.IsHermitian.add hA hE).eigenvalues₀ ⟨j, hjN⟩;
              have g :=
                hA.eigenvalues₀
                    ⟨j - 1, by omega⟩ -
                  hA.eigenvalues₀ ⟨j, hjN⟩;
              (0 < δ →
                  NLAlib.specNorm S ≤ NLAlib.specNorm (R.transpose * E * Q) / δ ∧
                    NLAlib.specNorm (R.transpose * E * Q) / δ ≤ NLAlib.specNorm (E * Q) / δ ∧
                      NLAlib.specNorm (E * Q) / δ ≤ NLAlib.specNorm E / δ ∧
                        NLAlib.frobNorm S ≤ NLAlib.frobNorm (R.transpose * E * Q) / δ ∧
                          NLAlib.frobNorm (R.transpose * E * Q) / δ ≤ NLAlib.frobNorm (E * Q) / δ ∧
                            NLAlib.frobNorm (E * Q) / δ ≤
                              Min.min (√↑j * NLAlib.specNorm E) (NLAlib.frobNorm E) / δ) ∧
                (0 < g → NLAlib.specNorm S ≤ 2 * NLAlib.specNorm E / g) ∧ (E = 0 → 0 < g → S = 0)) ∧
    (∀ {n : Type u_1} [_inst : Fintype n] [_inst_1 : DecidableEq n] {A E : Matrix n n ℝ}
  (hA : A.IsHermitian) (hE : E.IsHermitian) {j : ℕ} (hj0 : 0 < j) (hjN : j < Fintype.card n),
  0 <
      hA.eigenvalues₀
          ⟨j - 1, by omega⟩ -
        hA.eigenvalues₀ ⟨j, hjN⟩ →
    ∀ {Q Qhat : Matrix n (Fin j) ℝ} (hQ : NLAlib.HasOrthonormalCols Q),
      NLAlib.HasOrthonormalCols Qhat →
        ∀ {L : Matrix (Fin j) (Fin j) ℝ} (hAQ : A * Q = Q * L),
          (∀ (t : Fin j),
              hA.eigenvalues₀
                  ⟨j - 1, by omega⟩ ≤
                (NLAlib.isHermitian_of_invariant_orthonormal_frame hA hQ hAQ).eigenvalues t) →
            (Qhat.transpose * (A + E) * Qhat).trace =
                NLAlib.eigenvaluePrefix (Matrix.IsHermitian.add hA hE) (LT.lt.le hjN) →
              NLAlib.frobNorm (NLAlib.sinePrincipalAngles Q Qhat) ≤
                Min.min (2 * √↑j * NLAlib.specNorm E) (√2 * NLAlib.frobNorm E) /
                  (hA.eigenvalues₀
                      ⟨j - 1, by omega⟩ -
                    hA.eigenvalues₀ ⟨j, hjN⟩)) ∧
    (∀ {n : Type u_1} {k : Type u_2} [_inst : Fintype n] [_inst_1 : Fintype k] [DecidableEq n]
  [_inst_3 : DecidableEq k] {Q Qhat : Matrix n k ℝ},
  NLAlib.HasOrthonormalCols Q →
    NLAlib.HasOrthonormalCols Qhat →
      Fintype.card k = 0 ∨ Fintype.card k = Fintype.card n → NLAlib.sinePrincipalAngles Q Qhat = 0) := by
  exact ⟨@NLAlib.davis_kahan_bounds,
    @NLAlib.davis_kahan_top_frame_bounds,
    @NLAlib.frobNorm_sinePrincipalAngles_le_min_div_population_gap_of_frames,
    @NLAlib.sinePrincipalAngles_eq_zero_of_empty_or_full_frames⟩

end NLAlib
