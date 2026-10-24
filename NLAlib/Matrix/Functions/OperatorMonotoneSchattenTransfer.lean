import NLAlib.ForMathlib.Analysis.ConcavePowerDeficit
import NLAlib.Matrix.Functions.SpectralTruncation
import NLAlib.Matrix.Functions.MonotoneConcavity
import NLAlib.Matrix.Inequalities.PositiveTracePowers

/-!
# Transfer of ordered Schatten trace deficits to operator-monotone functions

The input certificate is the original ordered PSD Schatten trace deficit, at any
finite real exponent at least one. Scalar concavity transfers its head/tail comparison
and McCarthy superadditivity converts the transformed trace deficit to the actual matrix
error. Every ordered orthogonal eigendecomposition is permitted; the canonical basis is
an unconditional corollary. Truncation occurs after applying the function, including when
the function is positive at zero.

Source: Persson–Meyer–Musco 2025, Theorem 2.6; scalar cutoff route in
`sketching_lowrank_routes_2026_10_24/deterministic_lra.tex`.
Atlas: `operator-monotone-schatten-transfer`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Operator monotonicity on the nonnegative half-line preserves order for the
actual real-matrix functional calculus. This transports the complex defining API
through the canonical real matrix embedding, including singular matrices. -/
theorem OperatorMonotoneOn.cfc_le_real {f : ℝ → ℝ}
    (hm : OperatorMonotoneOn (Ici 0) f) {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : A ≤ B) : cfc f A ≤ cfc f B := by
  apply (realMatrixComplexification_le_iff (𝕜 := ℂ) _ _).mp
  rw [realMatrixComplexification_cfc f hA.isHermitian,
    realMatrixComplexification_cfc f hB.isHermitian]
  have hAc := (posSemidef_realMatrixComplexification_iff (𝕜 := ℂ) A).mpr hA
  have hBc := (posSemidef_realMatrixComplexification_iff (𝕜 := ℂ) B).mpr hB
  exact hm.cfc_le hAc.isHermitian hBc.isHermitian
    (fun _ hx => spectrum_nonneg_of_nonneg hAc.nonneg hx)
    (fun _ hx => spectrum_nonneg_of_nonneg hBc.nonneg hx)
    ((realMatrixComplexification_le_iff A B).mpr hAB)

omit [Fintype n] [DecidableEq n] in
/-- Operator monotonicity includes scalar monotonicity, by the one-dimensional
real diagonal instance. No differentiability or zero boundary value is assumed. -/
theorem OperatorMonotoneOn.monotoneOn_nonneg {f : ℝ → ℝ}
    (hm : OperatorMonotoneOn (Ici 0) f) : MonotoneOn f (Ici 0) := by
  intro x hx y hy hxy
  have hX : (Matrix.diagonal (fun _ : Fin 1 => x)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun _ => hx)
  have hY : (Matrix.diagonal (fun _ : Fin 1 => y)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun _ => hy)
  have hXY : Matrix.diagonal (fun _ : Fin 1 => x) ≤ Matrix.diagonal (fun _ : Fin 1 => y) := by
    apply Matrix.le_iff.mpr
    rw [Matrix.diagonal_sub]
    exact Matrix.posSemidef_diagonal_iff.mpr (fun _ => sub_nonneg.mpr hxy)
  have h := hm.cfc_le_real hX hY hXY
  rw [cfc_diagonal, cfc_diagonal] at h
  have hd := (Matrix.le_iff.mp h).diag_nonneg (i := (0 : Fin 1))
  exact sub_nonneg.mp (by simpa only [Matrix.sub_apply, Matrix.diagonal_apply_eq] using hd)

/-- A nonnegative operator-monotone function keeps the decreasing order of a
PSD matrix's eigenvalue list. Its prefix in the original ordered basis is therefore
a spectral truncation after applying the function, including transformed ties. -/
theorem OperatorMonotoneOn.antitone_comp_eigenvalues₀ {f : ℝ → ℝ}
    (hm : OperatorMonotoneOn (Ici 0) f) {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    Antitone (fun i => f (hA.isHermitian.eigenvalues₀ i)) := by
  intro i j hij
  exact hm.monotoneOn_nonneg (eigenvalues₀_nonneg_of_posSemidef hA j)
    (eigenvalues₀_nonneg_of_posSemidef hA i) (hA.isHermitian.eigenvalues₀_antitone hij)

/-- The exact ordered Schatten trace-deficit certificate transfers to a continuous
nonnegative operator-monotone function, for every finite real exponent `p ≥ 1` and
every supplied ordered orthogonal eigenbasis, including choices within ties.

The premise is a trace deficit. At `p = 2` it is stronger than an ordinary Frobenius
residual certificate. The approximation on the conclusion is formed by applying `f`
before truncating, so no condition `f 0 = 0` is imposed.
Source: Persson–Meyer–Musco 2025, Theorem 2.6.
atlas: operator-monotone-schatten-transfer -/
theorem schattenNormReal_cfc_sub_spectralFunctionTruncation_rpow_le_of_ordered_eigenbases
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : B ≤ A)
    (U V : Matrix n n ℝ) (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hAU : spectralBasisMatrix U hA.isHermitian.eigenvalues₀ = A)
    (hBV : spectralBasisMatrix V hB.isHermitian.eigenvalues₀ = B)
    {k : ℕ} (hk : k < Fintype.card n) {p ε : ℝ} (hp : 1 ≤ p) (hε : 0 ≤ ε)
    {f : ℝ → ℝ} (hm : OperatorMonotoneOn (Ici 0) f)
    (hf : ContinuousOn f (Ici 0)) (hfn : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hdeficit : schattenNormReal A p ^ p -
        schattenNormReal (spectralFunctionTruncation V hB.isHermitian.eigenvalues₀ id k) p ^ p ≤
      (1 + ε) * schattenNormReal
        (A - spectralFunctionTruncation U hA.isHermitian.eigenvalues₀ id k) p ^ p) :
    schattenNormReal (cfc f A - spectralFunctionTruncation V hB.isHermitian.eigenvalues₀ f k) p ^ p ≤
      (1 + ε) * schattenNormReal
        (cfc f A - spectralFunctionTruncation U hA.isHermitian.eigenvalues₀ f k) p ^ p := by
  let a := hA.isHermitian.eigenvalues₀
  let b := hB.isHermitian.eigenvalues₀
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have ha0 : ∀ i, 0 ≤ a i := eigenvalues₀_nonneg_of_posSemidef hA
  have hb0 : ∀ i, 0 ≤ b i := eigenvalues₀_nonneg_of_posSemidef hB
  have hba : ∀ i, b i ≤ a i :=
    Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_of_le hB.isHermitian hA.isHermitian hAB
  have hApower : schattenNormReal A p ^ p = ∑ i, a i ^ p := by
    calc
      _ = schattenNormReal (spectralBasisMatrix U a) p ^ p :=
        congrArg (fun M : Matrix n n ℝ => schattenNormReal M p ^ p) hAU.symm
      _ = _ := schattenNormReal_spectralBasisMatrix_rpow U hU a ha0 hp0
  have hBhead : schattenNormReal (spectralFunctionTruncation V b id k) p ^ p =
      ∑ i, if i.val < k then b i ^ p else 0 := by
    simpa only [id_eq] using
      schattenNormReal_spectralFunctionTruncation_rpow V hV b id k hb0 hp0
  have hAid : cfc id (spectralBasisMatrix U a) = A :=
    (cfc_id' ℝ _ (posSemidef_spectralBasisMatrix U a ha0).isHermitian).trans hAU
  have hAtail : schattenNormReal (A - spectralFunctionTruncation U a id k) p ^ p =
      ∑ i, if k ≤ i.val then a i ^ p else 0 := by
    have ht := schattenNormReal_cfc_sub_spectralFunctionTruncation_rpow U hU a id k ha0 hp0
    simpa only [hAid, id_eq] using ht
  have hscalar : (∑ i, f (a i) ^ p) - (∑ i, if i.val < k then f (b i) ^ p else 0) ≤
      (1 + ε) * (∑ i, if k ≤ i.val then f (a i) ^ p else 0) := by
    apply (hm.concaveOn_nonneg hf).sum_rpow_sub_prefix_le a b
      hA.isHermitian.eigenvalues₀_antitone ha0 hb0 hba hk hp0 hε hfn
    rwa [hApower, hBhead, hAtail] at hdeficit
  have hAf : cfc f A = spectralBasisMatrix U (f ∘ a) := by
    calc
      _ = cfc f (spectralBasisMatrix U a) := congrArg (cfc f) hAU.symm
      _ = _ := cfc_spectralBasisMatrix U hU a f
  have hAfPower : schattenNormReal (cfc f A) p ^ p = ∑ i, f (a i) ^ p := by
    rw [hAf]
    exact schattenNormReal_spectralBasisMatrix_rpow U hU (f ∘ a)
      (fun i => hfn _ (ha0 i)) hp0
  have hBfHead : schattenNormReal (spectralFunctionTruncation V b f k) p ^ p =
      ∑ i, if i.val < k then f (b i) ^ p else 0 :=
    schattenNormReal_spectralFunctionTruncation_rpow V hV b f k (fun i => hfn _ (hb0 i)) hp0
  have hAfTail : schattenNormReal (cfc f A - spectralFunctionTruncation U a f k) p ^ p =
      ∑ i, if k ≤ i.val then f (a i) ^ p else 0 := by
    have ht := schattenNormReal_cfc_sub_spectralFunctionTruncation_rpow U hU a f k
      (fun i => hfn _ (ha0 i)) hp0
    have he : cfc f (spectralBasisMatrix U a) = cfc f A := congrArg (cfc f) hAU
    rwa [he] at ht
  have hBfPSD : (spectralFunctionTruncation V b f k).PosSemidef :=
    posSemidef_spectralFunctionTruncation V b f k (fun i => hfn _ (hb0 i))
  have hBfLe : spectralFunctionTruncation V b f k ≤ cfc f A := by
    calc
      _ ≤ cfc f (spectralBasisMatrix V b) :=
        spectralFunctionTruncation_le_cfc V hV b f k (fun i => hfn _ (hb0 i))
      _ = cfc f B := congrArg (cfc f) hBV
      _ ≤ cfc f A := hm.cfc_le_real hB hA hAB
  have herr := schattenNormReal_sub_rpow_le hBfPSD hBfLe hp
  rw [hAfPower, hBfHead] at herr
  change schattenNormReal (cfc f A - spectralFunctionTruncation V b f k) p ^ p ≤
    (1 + ε) * schattenNormReal (cfc f A - spectralFunctionTruncation U a f k) p ^ p
  rw [hAfTail]
  exact herr.trans hscalar

/-- The native canonical-basis form of the operator-monotone Schatten transfer
theorem. All truncations use the original matrix's ordered eigenvectors; the
function is evaluated before its prefix is retained. The theorem includes `k = 0`,
zero original tail, singular matrices, positive `f(0)`, and every real `p ≥ 1`.
Source: Persson–Meyer–Musco 2025, Theorem 2.6. -/
theorem schattenNormReal_cfc_sub_spectralFunctionTruncation_rpow_le
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : B ≤ A)
    {k : ℕ} (hk : k < Fintype.card n) {p ε : ℝ} (hp : 1 ≤ p) (hε : 0 ≤ ε)
    {f : ℝ → ℝ} (hm : OperatorMonotoneOn (Ici 0) f)
    (hf : ContinuousOn f (Ici 0)) (hfn : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hdeficit : schattenNormReal A p ^ p -
        schattenNormReal (hB.isHermitian.spectralFunctionTruncation id k) p ^ p ≤
      (1 + ε) * schattenNormReal (A - hA.isHermitian.spectralFunctionTruncation id k) p ^ p) :
    schattenNormReal (cfc f A - hB.isHermitian.spectralFunctionTruncation f k) p ^ p ≤
      (1 + ε) * schattenNormReal (cfc f A - hA.isHermitian.spectralFunctionTruncation f k) p ^ p := by
  exact schattenNormReal_cfc_sub_spectralFunctionTruncation_rpow_le_of_ordered_eigenbases
    hA hB hAB (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)
    (hB.isHermitian.eigenvectorUnitary : Matrix n n ℝ)
    (transpose_eigenvectorUnitary_mul_self hA.isHermitian)
    (transpose_eigenvectorUnitary_mul_self hB.isHermitian)
    (spectralBasisMatrix_eigenvectorUnitary hA.isHermitian)
    (spectralBasisMatrix_eigenvectorUnitary hB.isHermitian)
    hk hp hε hm hf hfn hdeficit

/-- A zero original optimal tail in an ordered Schatten trace-deficit certificate
forces the underlying matrices to be equal. This supplies the singular endpoint
without a regularization limit or a division by a vanishing tail. -/
theorem eq_of_schatten_trace_deficit_of_tail_eq_zero
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : B ≤ A)
    (k : ℕ) {p ε : ℝ} (hp : 1 ≤ p)
    (htail : schattenNormReal (A - hA.isHermitian.spectralFunctionTruncation id k) p ^ p = 0)
    (hdeficit : schattenNormReal A p ^ p -
        schattenNormReal (hB.isHermitian.spectralFunctionTruncation id k) p ^ p ≤
      (1 + ε) * schattenNormReal (A - hA.isHermitian.spectralFunctionTruncation id k) p ^ p) :
    A = B := by
  let V : Matrix n n ℝ := hB.isHermitian.eigenvectorUnitary
  let b := hB.isHermitian.eigenvalues₀
  let BK := hB.isHermitian.spectralFunctionTruncation id k
  have hV : HasOrthonormalCols V := transpose_eigenvectorUnitary_mul_self hB.isHermitian
  have hb0 : ∀ i, 0 ≤ b i := eigenvalues₀_nonneg_of_posSemidef hB
  have hBK : BK.PosSemidef := posSemidef_spectralFunctionTruncation V b id k hb0
  have hId : cfc id (spectralBasisMatrix V b) = B :=
    (cfc_id' ℝ _ (posSemidef_spectralBasisMatrix V b hb0).isHermitian).trans
      (spectralBasisMatrix_eigenvectorUnitary hB.isHermitian)
  have hBKB : BK ≤ B := by
    have h := spectralFunctionTruncation_le_cfc V hV b id k hb0
    rwa [hId] at h
  have herr := schattenNormReal_sub_rpow_le hBK (hBKB.trans hAB) hp
  rw [htail, mul_zero] at hdeficit
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hzero : schattenNormReal (A - BK) p ^ p = 0 :=
    le_antisymm (herr.trans hdeficit)
      (Real.rpow_nonneg (schattenNormReal_nonneg (A - BK) p) p)
  have hn : schattenNormReal (A - BK) p = 0 :=
    (Real.rpow_eq_zero (schattenNormReal_nonneg (A - BK) p) hp0.ne').mp hzero
  have he : A = BK := sub_eq_zero.mp ((schattenNormReal_eq_zero_iff (A - BK) hp0).mp hn)
  exact le_antisymm (he.symm ▸ hBKB) hAB

end NLAlib
