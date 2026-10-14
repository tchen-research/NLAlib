import NLAlib.Matrix.Spectral.DefiniteCongruence
import NLAlib.Matrix.Inequalities.MinkowskiDeterminant
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Determinants of matrices with positive definite Hermitian part

Simultaneous congruence of the positive Hermitian part and the imaginary
Hermitian part reduces the exact determinant formulas to finite scalar
products. Sources: Horn–Johnson (2013), Theorems 7.8.19, 7.8.24 and 7.8.27;
operator derivations, (S13)–(S17). Atlas: `psd-hermitian-part`.
-/

noncomputable section
open Matrix
open scoped Matrix ComplexOrder
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A complex positive-semidefinite determinant is real and its modulus is
its nonnegative real part. -/
theorem norm_det_eq_re_of_posSemidef {H : Matrix n n ℂ} (hH : H.PosSemidef) :
    ‖H.det‖ = H.det.re := by
  have hn := RCLike.norm_of_nonneg' hH.det_nonneg
  have h := congrArg Complex.re hn
  simpa using h

private theorem norm_one_add_I_mul (t : ℝ) :
    ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ = Real.sqrt (1 + t ^ 2) := by
  rw [Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply]
  ring

/-- Positive Hermitian and arbitrary Hermitian parts admit exact determinant
product formulas after simultaneous congruence. The diagonal parameters also
detect whether the imaginary Hermitian part vanishes. Empty dimension is included.
Source: operator derivations, (S13).
atlas: psd-hermitian-part (partial) -/
theorem exists_det_add_I_smul_factors {H K : Matrix n n ℂ}
    (hH : H.PosDef) (hK : K.IsHermitian) :
    ∃ t : n → ℝ,
      ‖(H + Complex.I • K).det‖ = H.det.re * ∏ i, Real.sqrt (1 + t i ^ 2) ∧
      ‖K.det‖ = H.det.re * ∏ i, |t i| ∧ (K = 0 ↔ ∀ i, t i = 0) := by
  obtain ⟨S, t, hS, hHH, hKK, -⟩ := exists_definite_pair_congruence_diagonal hH hK
  have hdetH : H.det.re = ‖S.det‖ ^ 2 := by
    rw [← norm_det_eq_re_of_posSemidef hH.posSemidef, hHH,
      Matrix.det_mul, norm_mul, Matrix.det_conjTranspose, norm_star]
    ring
  have hA : H + Complex.I • K =
      S * diagonal (fun i => (1 : ℂ) + Complex.I * (t i : ℂ)) * Sᴴ := by
    have hd : diagonal (fun i => (1 : ℂ) + Complex.I * (t i : ℂ)) =
        1 + Complex.I • diagonal (fun i => (t i : ℂ)) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
    rw [hHH, hKK, hd]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.mul_smul, Matrix.smul_mul]
    rfl
  refine ⟨t, ?_, ?_, ?_⟩
  · rw [hA, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul,
      Matrix.det_conjTranspose, norm_star, Matrix.det_diagonal,
      norm_prod, hdetH]
    simp only [norm_one_add_I_mul]
    ring
  · rw [hKK, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul,
      Matrix.det_conjTranspose, norm_star, Matrix.det_diagonal,
      norm_prod, hdetH]
    simp only [RCLike.norm_ofReal]
    ring
  · have hSH : IsUnit Sᴴ := (Matrix.isUnit_conjTranspose S).mpr hS
    constructor
    · intro hKzero
      have hd : diagonal (fun i => (t i : ℂ)) = 0 := by
        apply hS.mul_left_cancel
        apply hSH.mul_right_cancel
        rw [Matrix.mul_zero, Matrix.zero_mul]
        exact hKK.symm.trans hKzero
      intro i
      have he := congrArg (fun M : Matrix n n ℂ => M i i) hd
      simpa using he
    · intro ht
      rw [hKK]
      simp [ht]

private theorem one_le_sqrt_one_add_sq (t : ℝ) : 1 ≤ Real.sqrt (1 + t ^ 2) := by
  exact (Real.le_sqrt (by positivity) (by positivity)).mpr (by nlinarith [sq_nonneg t])

/-- Ostrowski–Taussky's determinant lower bound for a matrix with positive
definite Hermitian part, including dimension zero.
Source: Horn–Johnson (2013), Theorem 7.8.19; operator derivations, (S15).
atlas: psd-hermitian-part (partial) -/
theorem re_det_le_norm_det_add_I_smul {H K : Matrix n n ℂ}
    (hH : H.PosDef) (hK : K.IsHermitian) :
    H.det.re ≤ ‖(H + Complex.I • K).det‖ := by
  obtain ⟨t, hdet, -, -⟩ := exists_det_add_I_smul_factors hH hK
  rw [hdet]
  have hp : (1 : ℝ) ≤ ∏ i, Real.sqrt (1 + t i ^ 2) :=
    Finset.one_le_prod (fun i (_ : i ∈ Finset.univ) => one_le_sqrt_one_add_sq (t i))
  have hre : 0 < H.det.re := (RCLike.pos_iff.mp hH.det_pos).1
  nlinarith

/-- Equality in Ostrowski–Taussky holds exactly when the imaginary Hermitian
part vanishes; empty dimension is included.
Source: Horn–Johnson (2013), Theorem 7.8.19; operator derivations, (S15).
atlas: psd-hermitian-part (partial) -/
theorem re_det_eq_norm_det_add_I_smul_iff {H K : Matrix n n ℂ}
    (hH : H.PosDef) (hK : K.IsHermitian) :
    H.det.re = ‖(H + Complex.I • K).det‖ ↔ K = 0 := by
  obtain ⟨t, hdet, -, hzero⟩ := exists_det_add_I_smul_factors hH hK
  rw [hdet, hzero]
  have hre : 0 < H.det.re := (RCLike.pos_iff.mp hH.det_pos).1
  have hp : (∏ i, Real.sqrt (1 + t i ^ 2)) = 1 ↔ ∀ i, t i = 0 := by
    constructor
    · intro h i
      have hi : Real.sqrt (1 + t i ^ 2) ≤ ∏ j, Real.sqrt (1 + t j ^ 2) := by
        have hh := Finset.prod_le_prod_of_subset_of_one_le
          (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
          (fun j (_ : j ∈ ({i} : Finset n)) => Real.sqrt_nonneg (1 + t j ^ 2))
          (fun j (_ : j ∈ (Finset.univ : Finset n)) _ => one_le_sqrt_one_add_sq (t j))
        simpa only [Finset.prod_singleton] using hh
      rw [h] at hi
      have hs := Real.sqrt_eq_one.mp (le_antisymm hi (one_le_sqrt_one_add_sq (t i)))
      nlinarith [sq_nonneg (t i)]
    · intro ht
      simp [ht]
  constructor
  · intro h
    apply hp.mp
    nlinarith
  · intro h
    rw [hp.mpr h, mul_one]

private theorem abs_le_sqrt_one_add_sq (t : ℝ) :
    |t| ≤ Real.sqrt (1 + t ^ 2) := by
  exact (Real.le_sqrt (abs_nonneg t) (by positivity)).mpr (by simp [sq_abs])

private theorem one_add_abs_mul_le_sqrt_mul (a b : ℝ) :
    1 + |a| * |b| ≤ Real.sqrt (1 + a ^ 2) * Real.sqrt (1 + b ^ 2) := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

private theorem one_add_prod_abs_le_prod_sqrt (t : n → ℝ)
    (hN : 2 ≤ Fintype.card n) :
    1 + ∏ i, |t i| ≤ ∏ i, Real.sqrt (1 + t i ^ 2) := by
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card n)
  let s := (Finset.univ.erase i).erase j
  have hprod (f : n → ℝ) : (∏ k, f k) = f i * f j * ∏ k ∈ s, f k := by
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) f
        (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
    simp only [s, mul_assoc]
  have hrest1 : 1 ≤ ∏ k ∈ s, Real.sqrt (1 + t k ^ 2) :=
    Finset.one_le_prod fun k _ => one_le_sqrt_one_add_sq (t k)
  have hrestAbs : (∏ k ∈ s, |t k|) ≤ ∏ k ∈ s, Real.sqrt (1 + t k ^ 2) :=
    Finset.prod_le_prod (fun k _ => abs_nonneg (t k)) (fun k _ => abs_le_sqrt_one_add_sq (t k))
  rw [hprod (fun k => |t k|), hprod (fun k => Real.sqrt (1 + t k ^ 2))]
  calc
    _ ≤ (1 + |t i| * |t j|) * ∏ k ∈ s, Real.sqrt (1 + t k ^ 2) := by
      rw [add_mul, one_mul]
      exact add_le_add hrest1
        (mul_le_mul_of_nonneg_left hrestAbs (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ ≤ _ := mul_le_mul_of_nonneg_right (one_add_abs_mul_le_sqrt_mul (t i) (t j))
      (Finset.prod_nonneg (fun k _ => Real.sqrt_nonneg _))

/-- The determinant-sum bound for positive Hermitian part requires dimension
at least two. Source: Horn–Johnson (2013), Theorem 7.8.24;
operator derivations, (S17).
atlas: psd-hermitian-part (partial) -/
theorem re_det_add_norm_det_le_norm_det_add_I_smul {H K : Matrix n n ℂ}
    (hH : H.PosDef) (hK : K.IsHermitian) (hN : 2 ≤ Fintype.card n) :
    H.det.re + ‖K.det‖ ≤ ‖(H + Complex.I • K).det‖ := by
  obtain ⟨t, hA, hKdet, -⟩ := exists_det_add_I_smul_factors hH hK
  rw [hA, hKdet]
  have hre : 0 < H.det.re := (RCLike.pos_iff.mp hH.det_pos).1
  have h := mul_le_mul_of_nonneg_left (one_add_prod_abs_le_prod_sqrt t hN) hre.le
  nlinarith

private theorem one_add_prod_abs_rpow_le_prod_sqrt_rpow (t : n → ℝ)
    (hN : 0 < Fintype.card n) :
    1 + (∏ i, |t i|) ^ (2 / (Fintype.card n : ℝ)) ≤
      (∏ i, Real.sqrt (1 + t i ^ 2)) ^ (2 / (Fintype.card n : ℝ)) := by
  let D : Matrix n n ℝ := diagonal (fun i => t i ^ 2)
  have hD : D.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr (fun i => sq_nonneg (t i))
  have h := det_rpow_inv_card_add_le_of_posSemidef
    (A := (1 : Matrix n n ℝ)) Matrix.PosSemidef.one hD hN
  have hdiag : 1 + D = diagonal (fun i => 1 + t i ^ 2) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_add]
  rw [Matrix.det_one, hdiag, Matrix.det_diagonal, Matrix.det_diagonal] at h
  simp only [Real.one_rpow] at h
  have habs : (∏ i, |t i|) ^ 2 = ∏ i, t i ^ 2 := by
    rw [← Finset.prod_pow]
    simp only [sq_abs]
  have hsqrt : (∏ i, Real.sqrt (1 + t i ^ 2)) ^ 2 = ∏ i, (1 + t i ^ 2) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    exact Real.sq_sqrt (by positivity)
  have hrpow (a : ℝ) (ha : 0 ≤ a) :
      a ^ (2 / (Fintype.card n : ℝ)) = (a ^ 2) ^ (1 / (Fintype.card n : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    congr 1
    ring
  rw [hrpow _ (Finset.prod_nonneg fun i _ => abs_nonneg (t i)),
    hrpow _ (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _), habs, hsqrt]
  exact h

/-- Fan's determinant-power bound holds for positive definite Hermitian
part in positive dimension. Singular imaginary part and repeated relative
eigenvalues are included. Source: Horn–Johnson (2013), Theorem 7.8.27;
operator derivations, (S16).
atlas: psd-hermitian-part (partial) -/
theorem re_det_rpow_add_norm_det_rpow_le_norm_det_add_I_smul_rpow
    {H K : Matrix n n ℂ} (hH : H.PosDef) (hK : K.IsHermitian)
    (hN : 0 < Fintype.card n) :
    H.det.re ^ (2 / (Fintype.card n : ℝ)) + ‖K.det‖ ^ (2 / (Fintype.card n : ℝ)) ≤
      ‖(H + Complex.I • K).det‖ ^ (2 / (Fintype.card n : ℝ)) := by
  obtain ⟨t, hA, hKdet, -⟩ := exists_det_add_I_smul_factors hH hK
  have hre : 0 < H.det.re := (RCLike.pos_iff.mp hH.det_pos).1
  rw [hA, hKdet, Real.mul_rpow hre.le (Finset.prod_nonneg fun i _ => abs_nonneg (t i)),
    Real.mul_rpow hre.le (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _)]
  have h := mul_le_mul_of_nonneg_left (one_add_prod_abs_rpow_le_prod_sqrt_rpow t hN)
    (Real.rpow_nonneg hre.le (2 / (Fintype.card n : ℝ)))
  nlinarith

end NLAlib
