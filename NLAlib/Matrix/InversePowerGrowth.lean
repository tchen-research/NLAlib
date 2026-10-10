import NLAlib.Matrix.GramSoftMin
import NLAlib.Matrix.QuadraticProbe

/-!
# Growth bounds for inverse-power Gram derivatives

Trace/Frobenius estimates bound the explicit inverse-power Hessian and provide
fixed-regularization polynomial dominators for Gaussian integration by parts.
Source: operator hard-edge derivation, atlas wishart-lambda-min-tail.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A trace power-product with two copies of the same direction is bounded by
spectral powers times the squared Frobenius direction size. Source: Frobenius
Cauchy--Schwarz; atlas wishart-lambda-min-tail (Hessian growth helper). -/
theorem abs_trace_pow_mul_mul_pow_mul_le (R B : Matrix ι ι ℝ) (p q : ℕ) :
    |Matrix.trace (R ^ p * B * R ^ q * B)| ≤
      specNorm R ^ (p + q) * frobSq B := by
  cases isEmpty_or_nonempty ι with
  | inl hι => simp [Matrix.trace, Matrix.diag, frobSq, frobInner]
  | inr hι =>
    have htrace : Matrix.trace (R ^ p * B * R ^ q * B) =
        frobInner (R ^ p * B)ᵀ (R ^ q * B) := by
      rw [frobInner_eq_trace, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
    have hp : specNorm (R ^ p) ≤ specNorm R ^ p := by
      simp only [specNorm_eq_norm]
      exact norm_pow_le R p
    have hq : specNorm (R ^ q) ≤ specNorm R ^ q := by
      simp only [specNorm_eq_norm]
      exact norm_pow_le R q
    have hfp : frobNorm (R ^ p * B) ≤ specNorm R ^ p * frobNorm B :=
      (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans
        (mul_le_mul_of_nonneg_right hp (frobNorm_nonneg B))
    have hfq : frobNorm (R ^ q * B) ≤ specNorm R ^ q * frobNorm B :=
      (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans
        (mul_le_mul_of_nonneg_right hq (frobNorm_nonneg B))
    rw [htrace]
    calc
      _ ≤ frobNorm (R ^ p * B) * frobNorm (R ^ q * B) := by
        simpa only [frobNorm_transpose] using
          abs_frobInner_le_frobNorm_mul_frobNorm (R ^ p * B)ᵀ (R ^ q * B)
      _ ≤ (specNorm R ^ p * frobNorm B) * (specNorm R ^ q * frobNorm B) :=
        mul_le_mul hfp hfq (frobNorm_nonneg _) (mul_nonneg
          (pow_nonneg (specNorm_nonneg R) _) (frobNorm_nonneg B))
      _ = _ := by rw [pow_add, ← frobNorm_sq B]; ring

/-- The inverse-power Hessian kernel has an explicit spectral/Frobenius norm bound.
Source: summing the trace product bound; atlas wishart-lambda-min-tail
(Hessian growth helper). -/
theorem abs_inversePowerHessianKernel_le (R B : Matrix ι ι ℝ) (n : ℕ) :
    |inversePowerHessianKernel R B n| ≤
      ((n : ℝ) + 1) * specNorm R ^ (n + 2) * frobSq B := by
  unfold inversePowerHessianKernel
  calc
    _ ≤ ∑ a ∈ Finset.range (n + 1),
        |Matrix.trace (R ^ (n - a + 1) * B * R ^ (a + 1) * B)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Finset.range (n + 1), specNorm R ^ (n + 2) * frobSq B := by
      apply Finset.sum_le_sum
      intro a ha
      have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      simpa only [show n - a + 1 + (a + 1) = n + 2 by omega] using
        abs_trace_pow_mul_mul_pow_mul_le R B (n - a + 1) (a + 1)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]; ring

/-- Concavity removes the nonnegative trace-square part from the absolute Hessian
bound. Source: inverse-power operator Hessian; atlas wishart-lambda-min-tail
(growth helper). -/
theorem abs_inversePowerSoftMinSecond_le [Nonempty ι] (n : ℕ) (A B : Matrix ι ι ℝ)
    (hA : A.PosDef) (hB : B.IsHermitian) :
    |inversePowerSoftMinSecond n A B| ≤
      Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) *
        (((n : ℝ) + 1) * specNorm A⁻¹ ^ (n + 2) * frobSq B) := by
  have hnonpos := inversePowerSoftMinSecond_nonpos n hA hB
  have hT := trace_pow_pos_of_posDef hA.inv n
  have hsquare : 0 ≤ ((n : ℝ) + 1) *
      Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 2) *
      Matrix.trace (A⁻¹ ^ (n + 1) * B) ^ 2 := by positivity
  have hc : 0 ≤ Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) :=
    Real.rpow_nonneg hT.le _
  have hk := abs_inversePowerHessianKernel_le A⁻¹ B n
  rw [abs_of_nonpos hnonpos]
  unfold inversePowerSoftMinSecond
  calc
    _ ≤ Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) *
        inversePowerHessianKernel A⁻¹ B n := by linarith
    _ ≤ Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) *
        |inversePowerHessianKernel A⁻¹ B n| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hc
    _ ≤ _ := mul_le_mul_of_nonneg_left hk hc

omit [DecidableEq κ] in
/-- Positive Gram regularization bounds the inverse spectral norm by its scalar
regularization reciprocal. Source: a top inverse eigenvector and the regularized
Gram quadratic form; atlas wishart-lambda-min-tail (growth helper). -/
theorem specNorm_inv_regularizedGram_le [Nonempty ι] (ε : ℝ) (hε : 0 < ε)
    (G : Matrix ι κ ℝ) :
    specNorm (regularizedGram ε G)⁻¹ ≤ ε⁻¹ := by
  let A := regularizedGram ε G
  have hA : A.PosDef := regularizedGram_posDef hε G
  obtain ⟨v, hv, heig⟩ := exists_unit_mulVec_eq_specNorm_smul hA.inv.posSemidef
  have hmul : A * A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have heq : specNorm A⁻¹ * (v ⬝ᵥ (A *ᵥ v)) = 1 := by
    have hh : A *ᵥ (A⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
    rw [heig, Matrix.mulVec_smul] at hh
    have h := congrArg (fun w => v ⬝ᵥ w) hh
    simpa only [dotProduct_smul, smul_eq_mul, hv] using h
  have hG : (G * Gᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose G
  have hpos := hG.dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hpos
  have hquad : ε ≤ v ⬝ᵥ (A *ᵥ v) := by
    dsimp [A, regularizedGram]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul, hv, mul_one]
    linarith
  have hεs : ε * specNorm A⁻¹ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hquad (specNorm_nonneg A⁻¹)
    rw [heq] at hh
    simpa only [mul_comm] using hh
  rw [← one_div ε]
  exact (le_div_iff₀ hε).mpr (by simpa only [mul_comm] using hεs)

/-- The inverse-power soft minimum is bounded by the trace of a positive definite
matrix. Source: one top inverse eigenvalue, the inverse norm identity, and PSD trace
domination; atlas wishart-lambda-min-tail (growth helper). -/
theorem inversePowerSoftMin_le_trace [Nonempty ι] (n : ℕ) (hn : 0 < n)
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    inversePowerSoftMin n A ≤ Matrix.trace A := by
  let R : Matrix ι ι ℝ := A⁻¹
  let T : ℝ := Matrix.trace (R ^ n)
  have hR : R.PosDef := hA.inv
  have hT : 0 < T := trace_pow_pos_of_posDef hR n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let ev := hR.isHermitian.eigenvalues
  have hev : ∀ i, 0 ≤ ev i := fun i => (hR.eigenvalues_pos i).le
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm ev).1
  dsimp only at hi
  have hei : ev i = specNorm R := by
    rw [specNorm_eq_norm_eigenvalues hR.isHermitian, ← hi,
      Real.norm_of_nonneg (hev i)]
  have htrace : Matrix.trace (R ^ n) = ∑ j, ev j ^ n := by
    rw [hR.isHermitian.spectral_theorem, ← map_pow, trace_conjStarAlgAut,
      Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  have hsingle : ev i ^ n ≤ T := by
    rw [show T = Matrix.trace (R ^ n) from rfl, htrace]
    exact Finset.single_le_sum (fun j _ => pow_nonneg (hev j) n) (Finset.mem_univ i)
  have hroot : specNorm R ≤ T ^ (n : ℝ)⁻¹ := by
    have hh := Real.rpow_le_rpow (pow_nonneg (hev i) n) hsingle
      (inv_nonneg.mpr (Nat.cast_nonneg n))
    rw [← Real.rpow_natCast (ev i) n, Real.rpow_rpow_inv (hev i) hn0, hei] at hh
    exact hh
  have hmul : R * A = 1 :=
    Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hprod : 1 ≤ specNorm R * specNorm A := by
    rw [specNorm_eq_norm, specNorm_eq_norm]
    have hh := norm_mul_le R A
    rw [hmul, norm_one] at hh
    exact hh
  have hprodroot : 1 ≤ T ^ (n : ℝ)⁻¹ * specNorm A :=
    hprod.trans (mul_le_mul_of_nonneg_right hroot (specNorm_nonneg A))
  have hnorm : inversePowerSoftMin n A ≤ specNorm A := by
    change T ^ (-(n : ℝ)⁻¹) ≤ specNorm A
    rw [Real.rpow_neg hT.le]
    rw [← one_div (T ^ (n : ℝ)⁻¹)]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hT _)).mpr
      (by simpa only [mul_comm] using hprodroot)
  exact hnorm.trans (specNorm_le_trace_of_posSemidef hA.posSemidef)

/-- The inverse-power Hessian coefficient is bounded by a natural power of the
matrix trace. Source: the soft-minimum trace bound; atlas wishart-lambda-min-tail
(growth helper). -/
theorem rpow_trace_inv_pow_coefficient_le_trace_pow [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) ≤ Matrix.trace A ^ (n + 1) := by
  have hT := trace_pow_pos_of_posDef hA.inv n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) =
      inversePowerSoftMin n A ^ (n + 1) := by
    unfold inversePowerSoftMin
    rw [← Real.rpow_natCast _ (n + 1), ← Real.rpow_mul hT.le]
    congr 1
    push_cast
    field_simp
    ring
  rw [heq]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hT.le _)
    (inversePowerSoftMin_le_trace n hn A hA) _

omit [DecidableEq κ] in
/-- The regularized inverse-power Hessian has a fixed-regularization polynomial
growth bound, with no spectral-gap denominator. Source: trace coefficient and
resolvent norm estimates; atlas wishart-lambda-min-tail (growth helper). -/
theorem abs_inversePowerSoftMinSecond_regularizedGram_le [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (G : Matrix ι κ ℝ) (B : Matrix ι ι ℝ) (hB : B.IsHermitian) :
    |inversePowerSoftMinSecond n (regularizedGram ε G) B| ≤
      Matrix.trace (regularizedGram ε G) ^ (n + 1) * ((n : ℝ) + 1) *
        ε⁻¹ ^ (n + 2) * frobSq B := by
  let A := regularizedGram ε G
  have hA : A.PosDef := regularizedGram_posDef hε G
  have hcoef := rpow_trace_inv_pow_coefficient_le_trace_pow n hn A hA
  have htrace : 0 ≤ Matrix.trace A := by
    simpa only [pow_one] using (trace_pow_pos_of_posDef hA 1).le
  have hpow := pow_le_pow_left₀ (specNorm_nonneg A⁻¹)
    (specNorm_inv_regularizedGram_le ε hε G) (n + 2)
  have hkernel :
      ((n : ℝ) + 1) * specNorm A⁻¹ ^ (n + 2) * frobSq B ≤
      ((n : ℝ) + 1) * ε⁻¹ ^ (n + 2) * frobSq B :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity)) (frobSq_nonneg B)
  have hk0 : 0 ≤ ((n : ℝ) + 1) * specNorm A⁻¹ ^ (n + 2) * frobSq B :=
    mul_nonneg (mul_nonneg (by positivity)
      (pow_nonneg (specNorm_nonneg A⁻¹) _)) (frobSq_nonneg B)
  calc
    _ ≤ Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) *
        (((n : ℝ) + 1) * specNorm A⁻¹ ^ (n + 2) * frobSq B) :=
      abs_inversePowerSoftMinSecond_le n A B hA hB
    _ ≤ Matrix.trace A ^ (n + 1) *
        (((n : ℝ) + 1) * ε⁻¹ ^ (n + 2) * frobSq B) :=
      mul_le_mul hcoef hkernel hk0 (pow_nonneg htrace _)
    _ = _ := by ring

/-- A coordinate Gram direction has squared Frobenius size at most four times the
input size. Source: the Frobenius triangle and product inequalities;
atlas wishart-lambda-min-tail (growth helper). -/
theorem frobSq_single_gram_direction_le (G : Matrix ι κ ℝ) (i : ι) (j : κ) :
    let E : Matrix ι κ ℝ := Matrix.single i j 1
    frobSq (E * Gᵀ + G * Eᵀ) ≤ 4 * frobSq G := by
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hEsq : frobSq E = 1 := by
    simp [E, frobSq, frobInner, Matrix.single, ite_and]
  have hE : frobNorm E = 1 := by
    rw [frobNorm, hEsq]
    norm_num
  have h1 : frobNorm (E * Gᵀ) ≤ frobNorm G := by
    simpa only [frobNorm_transpose, hE, one_mul] using frobNorm_mul_le E Gᵀ
  have h2 : frobNorm (G * Eᵀ) ≤ frobNorm G := by
    simpa only [frobNorm_transpose, hE, mul_one] using frobNorm_mul_le G Eᵀ
  have hnorm := (frobNorm_add_le (E * Gᵀ) (G * Eᵀ)).trans (add_le_add h1 h2)
  change frobSq (E * Gᵀ + G * Eᵀ) ≤ _
  nlinarith [frobNorm_nonneg (E * Gᵀ + G * Eᵀ), frobNorm_nonneg G,
    frobNorm_sq (E * Gᵀ + G * Eᵀ), frobNorm_sq G]

/-- Each coordinate second Gram derivative has an explicit polynomial growth
bound at every fixed positive regularization. Source: inverse-power Hessian
growth and the PSD gradient diagonal; atlas wishart-lambda-min-tail (helper). -/
theorem abs_gramSoftMinSecond_single_le [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (G : Matrix ι κ ℝ) (i : ι) (j : κ) :
    |gramSoftMinSecond n ε G (Matrix.single i j 1)| ≤
      2 + 4 * Matrix.trace (regularizedGram ε G) ^ (n + 1) * ((n : ℝ) + 1) *
        ε⁻¹ ^ (n + 2) * frobSq G := by
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  let A := regularizedGram ε G
  let P := inversePowerSoftMinWeight n A
  have hA : A.PosDef := regularizedGram_posDef hε G
  have hP : P.PosSemidef := inversePowerSoftMinWeight_posSemidef n hA.posSemidef
  have hPdiag (k : ι) : 0 ≤ P k k := hP.diag_nonneg
  have hPi : P i i ≤ 1 := by
    have hh : P i i ≤ Matrix.trace P := by
      simpa only [Matrix.trace, Matrix.diag] using
        Finset.single_le_sum (fun k _ => hPdiag k) (Finset.mem_univ i)
    exact hh.trans (trace_inversePowerSoftMinWeight_le_one n hn hA)
  have hEE : E * Eᵀ = Matrix.single i i 1 := by
    simp only [E, Matrix.transpose_single, Matrix.single_mul_single_same, one_mul]
  have hfirst : inversePowerSoftMinFirst n A ((2 : ℝ) • (E * Eᵀ)) = 2 * P i i := by
    rw [inversePowerSoftMinFirst_eq_trace_weight_mul, hEE, mul_smul_comm,
      Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_single]
    simp [P]
  have hfirstabs : |inversePowerSoftMinFirst n A ((2 : ℝ) • (E * Eᵀ))| ≤ 2 := by
    rw [hfirst, abs_of_nonneg (mul_nonneg (by norm_num) (hPdiag i))]
    linarith
  have hdir : (E * Gᵀ + G * Eᵀ).IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    simp only [Matrix.IsSymm, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    exact add_comm _ _
  have hsecond := abs_inversePowerSoftMinSecond_regularizedGram_le n hn ε hε G
    (E * Gᵀ + G * Eᵀ) hdir
  have hB := frobSq_single_gram_direction_le G i j
  have hc0 : 0 ≤ Matrix.trace A ^ (n + 1) * ((n : ℝ) + 1) * ε⁻¹ ^ (n + 2) := by
    have ht : 0 ≤ Matrix.trace A := by
      simpa only [pow_one] using (trace_pow_pos_of_posDef hA 1).le
    positivity
  change |inversePowerSoftMinSecond n A (E * Gᵀ + G * Eᵀ) +
    inversePowerSoftMinFirst n A ((2 : ℝ) • (E * Eᵀ))| ≤ _
  calc
    _ ≤ |inversePowerSoftMinSecond n A (E * Gᵀ + G * Eᵀ)| +
        |inversePowerSoftMinFirst n A ((2 : ℝ) • (E * Eᵀ))| := abs_add_le _ _
    _ ≤ Matrix.trace A ^ (n + 1) * ((n : ℝ) + 1) * ε⁻¹ ^ (n + 2) *
        frobSq (E * Gᵀ + G * Eᵀ) + 2 := add_le_add hsecond hfirstabs
    _ ≤ Matrix.trace A ^ (n + 1) * ((n : ℝ) + 1) * ε⁻¹ ^ (n + 2) *
        (4 * frobSq G) + 2 := add_le_add (mul_le_mul_of_nonneg_left hB hc0) (le_refl _)
    _ = _ := by ring

omit [DecidableEq κ] in
/-- The trace of a regularized Gram matrix is its squared Frobenius size plus
the scalar regularization times the row dimension. Source: trace cyclicity;
atlas wishart-lambda-min-tail (growth helper). -/
theorem trace_regularizedGram_eq (ε : ℝ) (G : Matrix ι κ ℝ) :
    Matrix.trace (regularizedGram ε G) = frobSq G + ε * Fintype.card ι := by
  unfold regularizedGram
  rw [Matrix.trace_add, Matrix.trace_smul]
  simp only [smul_eq_mul, Matrix.trace_one]
  have hh : Matrix.trace (G * Gᵀ) = frobSq G := by
    rw [frobSq, frobInner_eq_trace, Matrix.trace_mul_comm]
  rw [hh]

/-- The second Gram derivative is bounded by a fixed polynomial in the squared
Frobenius size. The coefficient depends only on the degree, dimension, and positive
regularization. Source: the explicit Hessian growth bound;
atlas wishart-lambda-min-tail (Gaussian domination helper). -/
theorem abs_gramSoftMinSecond_single_le_frobSq_polynomial [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (G : Matrix ι κ ℝ) (i : ι) (j : κ) :
    |gramSoftMinSecond n ε G (Matrix.single i j 1)| ≤
      2 + (4 * ((n : ℝ) + 1) * ε⁻¹ ^ (n + 2) *
        (1 + ε * Fintype.card ι) ^ (n + 1)) * (1 + frobSq G) ^ (n + 2) := by
  have hG := frobSq_nonneg G
  have ha : 0 ≤ ε * (Fintype.card ι : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg _)
  have htrace : 0 ≤ Matrix.trace (regularizedGram ε G) := by
    rw [trace_regularizedGram_eq]
    exact add_nonneg hG ha
  have htr : Matrix.trace (regularizedGram ε G) ≤
      (1 + ε * (Fintype.card ι : ℝ)) * (1 + frobSq G) := by
    rw [trace_regularizedGram_eq]
    nlinarith [mul_nonneg ha hG]
  have hprod : Matrix.trace (regularizedGram ε G) ^ (n + 1) * frobSq G ≤
      (1 + ε * (Fintype.card ι : ℝ)) ^ (n + 1) * (1 + frobSq G) ^ (n + 2) := by
    calc
      _ ≤ ((1 + ε * (Fintype.card ι : ℝ)) * (1 + frobSq G)) ^ (n + 1) *
          (1 + frobSq G) :=
        mul_le_mul (pow_le_pow_left₀ htrace htr _) (by linarith) hG (by positivity)
      _ = _ := by
        rw [mul_pow, show n + 2 = (n + 1) + 1 by omega, pow_succ]
        ring
  have hc : 0 ≤ 4 * ((n : ℝ) + 1) * ε⁻¹ ^ (n + 2) := by positivity
  calc
    _ ≤ 2 + (4 * ((n : ℝ) + 1) * ε⁻¹ ^ (n + 2)) *
        (Matrix.trace (regularizedGram ε G) ^ (n + 1) * frobSq G) := by
      convert! abs_gramSoftMinSecond_single_le n hn ε hε G i j using 1
      ring
    _ ≤ 2 + (4 * ((n : ℝ) + 1) * ε⁻¹ ^ (n + 2)) *
        ((1 + ε * (Fintype.card ι : ℝ)) ^ (n + 1) * (1 + frobSq G) ^ (n + 2)) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hprod hc)
    _ = _ := by ring

end NLAlib
