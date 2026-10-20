import NLAlib.Matrix.Norms.SchattenPowers
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Tactic.FieldSimp

/-!
# Mixed powers of a normal matrix in actual Schatten norms

The finite-index singular-value identity includes a=b=0, repeated or zero singular values and empty matrices.
The product identity uses positive arc lengths and a positive total length;
no matrix invertibility is required. All Schatten norms and traces here are
unnormalized. Source: the common-resolvent word estimates underlying
Brailovskaya–van Handel, arXiv:2201.05142v3, Lemma 6.9 and Proposition 5.1.
Supports independent-sum-spectrum-universality (partial).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
private theorem cfcAbs_pow_of_commute_conjTranspose {B : Matrix n n 𝕜}
    (hB : Commute B Bᴴ) (a : ℕ) : CFC.abs (B ^ a) = CFC.abs B ^ a := by
  induction a with
  | zero => simp only [pow_zero, CFC.abs_one]
  | succ a ih =>
    rw [pow_succ, (Commute.pow_self B a).cfcAbs_mul_eq
      (by simpa only [Matrix.star_eq_conjTranspose] using hB.pow_left a), ih, pow_succ]

open scoped Matrix.Norms.L2Operator in
/-- A normal matrix's mixed adjoint power has exactly the modulus power of
its total degree. No nonzero or invertibility assumption is needed. -/
theorem cfcAbs_mul_pow_conjTranspose_pow {B : Matrix n n 𝕜}
    (hB : Commute B Bᴴ) (a b : ℕ) :
    CFC.abs (B ^ a * Bᴴ ^ b) = CFC.abs B ^ (a + b) := by
  have hstar : Commute Bᴴ (Bᴴ)ᴴ := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hB.symm
  have hnormal : IsStarNormal B := ⟨by simpa only [Matrix.star_eq_conjTranspose] using hB.symm⟩
  have hAbsStar : CFC.abs Bᴴ = CFC.abs B := by
    simpa only [Matrix.star_eq_conjTranspose] using CFC.abs_star B hnormal
  have hcross : Commute (B ^ a) (star (Bᴴ ^ b)) := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_pow,
      Matrix.conjTranspose_conjTranspose] using Commute.pow_pow_self B a b
  rw [(hB.pow_pow a b).cfcAbs_mul_eq hcross,
    cfcAbs_pow_of_commute_conjTranspose hB a,
    cfcAbs_pow_of_commute_conjTranspose hstar b, hAbsStar, ← pow_add]

open scoped Matrix.Norms.L2Operator in
/-- Mixed normal-matrix powers raise every in-dimension singular value to
the total degree. The Fin index is essential at degree zero: singular values
outside the matrix dimension are zero, whereas scalar x^0 is one. -/
theorem singularValues_mul_pow_conjTranspose_pow {B : Matrix n n 𝕜}
    (hB : Commute B Bᴴ) (a b : ℕ) (i : Fin (Fintype.card n)) :
    singularValues (B ^ a * Bᴴ ^ b) i = singularValues B i ^ (a + b) := by
  have hP : (CFC.abs B).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg B)
  have hp := singularValues_rpow_of_posSemidef hP
    (s := ((a + b : ℕ) : ℝ)) (Nat.cast_nonneg _) i
  change singularValues ((CFC.abs B) ^ ((a + b : ℕ) : ℝ)) i = _ at hp
  rw [CFC.rpow_natCast (CFC.abs B) (a + b) (CFC.abs_nonneg B)] at hp
  calc
    _ = singularValues (CFC.abs (B ^ a * Bᴴ ^ b)) i :=
      (congrFun (singularValues_cfcAbs (B ^ a * Bᴴ ^ b)) i).symm
    _ = singularValues (CFC.abs B ^ (a + b)) i := by
      rw [cfcAbs_mul_pow_conjTranspose_pow hB]
    _ = _ := by simpa only [singularValues_cfcAbs, Real.rpow_natCast] using hp

open scoped Matrix.Norms.L2Operator in
/-- Exact native finite Schatten formula for a mixed normal-matrix power.
The power-sum definition makes the identity valid at every real exponent;
in particular it applies to every positive Schatten exponent. -/
theorem schattenNormReal_mul_pow_conjTranspose_pow_eq_sum {B : Matrix n n 𝕜}
    (hB : Commute B Bᴴ) (a b : ℕ) (q : ℝ) :
    schattenNormReal (B ^ a * Bᴴ ^ b) q =
      (∑ i : Fin (Fintype.card n),
        singularValues B i ^ (((a + b : ℕ) : ℝ) * q)) ^ (1 / q) := by
  simp only [schattenNormReal, min_self, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [singularValues_mul_pow_conjTranspose_pow hB a b i,
    ← Real.rpow_natCast, ← Real.rpow_mul (singularValues_nonneg B i)]

open scoped Matrix.Norms.L2Operator in
/-- The ordinary trace of a modulus power is its exact finite singular-value
power sum, including degree zero and empty matrix dimensions. -/
theorem re_trace_cfcAbs_pow_eq_sum_singularValues (B : Matrix n n 𝕜) (L : ℕ) :
    RCLike.re (CFC.abs B ^ L).trace =
      ∑ i : Fin (Fintype.card n), singularValues B i ^ L := by
  let P := CFC.abs B
  have hP : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg B)
  have htrace : RCLike.re (P ^ L).trace = ∑ i : n, hP.isHermitian.eigenvalues i ^ L := by
    conv_lhs => rw [hP.isHermitian.spectral_theorem]
    rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
    simp only [map_sum, Pi.pow_apply, Function.comp_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [htrace]
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  rw [← e.sum_comp (fun i : n => hP.isHermitian.eigenvalues i ^ L)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]
  rw [← singularValues_eq_eigenvalues₀_of_posSemidef hP i]
  simp only [P, singularValues_cfcAbs]

open scoped Matrix.Norms.L2Operator in
/-- Choosing each Schatten exponent as total length divided by its positive
arc length collapses the product to a single actual ordinary modulus trace.
No dimension factor or independence premise occurs. -/
theorem prod_schattenNormReal_mixed_powers_eq_re_trace_cfcAbs_pow
    {ι : Type*} [Fintype ι] {B : Matrix n n 𝕜} (hB : Commute B Bᴴ)
    (a b : ι → ℕ) {L : ℕ} (hL : ∑ j, (a j + b j) = L)
    (hLpos : 0 < L) (hArc : ∀ j, 0 < a j + b j) :
    (∏ j, schattenNormReal (B ^ a j * Bᴴ ^ b j)
      ((L : ℝ) / (a j + b j : ℕ))) = RCLike.re (CFC.abs B ^ L).trace := by
  let T : ℝ := ∑ i : Fin (Fintype.card n), singularValues B i ^ (L : ℝ)
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValues_nonneg B i) _
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hs0 (j : ι) : (0 : ℝ) < (a j + b j : ℕ) := by exact_mod_cast hArc j
  have hsSum : ∑ j, ((a j + b j : ℕ) : ℝ) = (L : ℝ) := by exact_mod_cast hL
  have hfactor (j : ι) :
      schattenNormReal (B ^ a j * Bᴴ ^ b j) ((L : ℝ) / (a j + b j : ℕ)) =
        T ^ (((a j + b j : ℕ) : ℝ) / L) := by
    rw [schattenNormReal_mul_pow_conjTranspose_pow_eq_sum hB]
    have hexp : ((a j + b j : ℕ) : ℝ) * ((L : ℝ) / (a j + b j : ℕ)) = L := by
      exact mul_div_cancel₀ (L : ℝ) (hs0 j).ne'
    have hinv : 1 / ((L : ℝ) / (a j + b j : ℕ)) = ((a j + b j : ℕ) : ℝ) / L := by
      rw [one_div_div]
    rw [hexp, hinv]
  have hweights : ∑ j, ((a j + b j : ℕ) : ℝ) / L = 1 := by
    rw [← Finset.sum_div, hsSum, div_self hL0.ne']
  simp_rw [hfactor]
  rw [← Real.rpow_sum_of_nonneg hT (fun j _ => div_nonneg (hs0 j).le hL0.le),
    hweights, Real.rpow_one, re_trace_cfcAbs_pow_eq_sum_singularValues]
  simp only [T, Real.rpow_natCast]

open scoped Matrix.Norms.L2Operator in
/-- The mixed-power product formula in the main extended Schatten interface,
with no dimension factor, including empty matrix dimensions. Source: the
common-resolvent word estimates underlying Brailovskaya--van Handel,
arXiv:2201.05142v3, Proposition 5.1 and Lemma 6.9. -/
theorem prod_schattenNorm_mixed_powers_eq_re_trace_cfcAbs_pow
    {𝕜 n ι : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] [Fintype ι]
    {B : Matrix n n 𝕜} (hB : Commute B Bᴴ) (a b : ι → ℕ) {L : ℕ}
    (hL : ∑ j, (a j + b j) = L) (hLpos : 0 < L)
    (hArc : ∀ j, 0 < a j + b j) :
    (∏ j, schattenNorm (B ^ a j * Bᴴ ^ b j)
      (ENNReal.ofReal ((L : ℝ) / (a j + b j : ℕ)))) =
      RCLike.re (CFC.abs B ^ L).trace := by
  have hp0 (j : ι) : 0 ≤ (L : ℝ) / (a j + b j : ℕ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  simpa only [schattenNorm_ofReal _ (hp0 _)] using
    prod_schattenNormReal_mixed_powers_eq_re_trace_cfcAbs_pow hB a b hL hLpos hArc

end NLAlib
