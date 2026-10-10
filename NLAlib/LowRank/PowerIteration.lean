import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import NLAlib.Matrix.PolynomialCalculus
import NLAlib.Matrix.QuadraticProbe
import NLAlib.Matrix.Projections

/-!
# Power iteration: the deterministic bound

* `dotProduct_mulVec_pow_le_dotProduct_pow_mulVec`: Jensen for a positive semidefinite `M`,
  `(yᵀMy)^s ≤ yᵀM^s y` for `‖y‖ ≤ 1`, `s ≥ 1` (the spectral-decomposition step of HMT 2011,
  proof of Prop 8.6);
* `specNorm_mul_pow_le_specNorm_mul_gram_pow_mul`: **HMT 2011, Prop 8.6.** For an orthogonal
  projector `P` (symmetric idempotent), any real `A` and `q ≥ 0`,
  `‖PA‖^{2q+1} ≤ ‖P(AAᵀ)^q A‖`;
* `specNorm_residual_pow_le` and `specNorm_residual_le_rpow`: **HMT 2011, Thm 9.2**
  (deterministic power-iteration bound) for `P = I − QQᵀ`, any `Q` with orthonormal columns:
  `‖(I − QQᵀ)A‖ ≤ ‖(I − QQᵀ)(AAᵀ)^q A‖^{1/(2q+1)}`.

The source assumes `Q = orth((AAᵀ)^q AΩ)`; Prop 8.6 holds for every orthogonal projector, so
that hypothesis is dropped (audit G2 A2/B1, C-flag 9).

Proof of Prop 8.6: with `M = AAᵀ ⪰ 0` and `s = 2q + 1`, `‖PA‖² = ‖PMP‖` and
`‖PM^qA‖² = ‖PM^sP‖`. A unit top eigenvector `x` of `PMP` gives `‖PMP‖ = yᵀMy` with `y = Px`,
`‖y‖ ≤ 1`, so `‖PMP‖^s = (yᵀMy)^s ≤ yᵀM^s y = xᵀ(PM^sP)x ≤ ‖PM^sP‖`.

Atlas: `power-iteration-deterministic`.
-/

noncomputable section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq n] in
/-- **Jensen for a positive semidefinite quadratic form.** For `M ⪰ 0`, a vector `y` with
`y ⬝ y ≤ 1` and `s ≥ 1`, `(yᵀMy)^s ≤ yᵀM^s y`. With `y = Σᵢ cᵢuᵢ` in an eigenbasis this is
`(Σᵢ cᵢ²λᵢ)^s ≤ Σᵢ cᵢ²λᵢ^s`, convexity of `t ↦ t^s` on `t ≥ 0` with total weight `Σᵢ cᵢ² ≤ 1`.
HMT 2011, proof of Prop 8.6. Atlas `power-iteration-deterministic` (helper; belongs in
`Matrix/PolynomialCalculus.lean`). -/
theorem dotProduct_mulVec_pow_le_dotProduct_pow_mulVec {M : Matrix m m ℝ} (hM : M.PosSemidef)
    {y : m → ℝ} (hy : y ⬝ᵥ y ≤ 1) {s : ℕ} (hs : 1 ≤ s) :
    (y ⬝ᵥ (M *ᵥ y)) ^ s ≤ y ⬝ᵥ ((M ^ s) *ᵥ y) := by
  have hH := hM.isHermitian
  set ev := hH.eigenvalues with hev
  set w : m → ℝ := fun i => (⇑(hH.eigenvectorBasis i) ⬝ᵥ y) ^ 2 with hw
  have hev0 : ∀ i, 0 ≤ ev i := hM.eigenvalues_nonneg
  have hw0 : ∀ i, 0 ≤ w i := fun i => sq_nonneg _
  have h1 : y ⬝ᵥ (M *ᵥ y) = ∑ i, w i * ev i := by
    have h := dotProduct_aeval_mulVec_eq_sum hH X y
    simp only [aeval_X, eval_X] at h
    rw [h]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : y ⬝ᵥ ((M ^ s) *ᵥ y) = ∑ i, w i * ev i ^ s := by
    have h := dotProduct_aeval_mulVec_eq_sum hH (X ^ s) y
    simp only [map_pow, aeval_X, eval_pow, eval_X] at h
    rw [h]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hc : ∑ i, w i = y ⬝ᵥ y := sum_sq_eigenvectorBasis_dotProduct hH y
  have hR0 : 0 ≤ ∑ i, w i * ev i ^ s :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (pow_nonneg (hev0 i) s)
  rw [h1, h2]
  obtain ⟨c, hcdef⟩ : ∃ c, c = ∑ i, w i := ⟨_, rfl⟩
  have hc1 : c ≤ 1 := by rw [hcdef, hc]; exact hy
  rcases (by rw [hcdef]; exact Finset.sum_nonneg fun i _ => hw0 i : (0 : ℝ) ≤ c).eq_or_lt
    with hc0 | hcpos
  · have hwz : ∀ i, w i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hw0 j).1 (hcdef ▸ hc0.symm) i
        (Finset.mem_univ i)
    simp only [hwz, zero_mul, Finset.sum_const_zero]
    rw [zero_pow (by omega)]
  · have hJ := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun i => w i / c) ev
      (fun i _ => div_nonneg (hw0 i) hcpos.le)
      (by rw [← Finset.sum_div, ← hcdef, div_self hcpos.ne']) (fun i _ => hev0 i) s
    have hL : ∑ i, w i * ev i = c * ∑ i, w i / c * ev i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by field_simp
    have hR : ∑ i, w i / c * ev i ^ s = c⁻¹ * ∑ i, w i * ev i ^ s := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by field_simp
    rw [hR] at hJ
    rw [hL, mul_pow]
    calc c ^ s * (∑ i, w i / c * ev i) ^ s ≤ c ^ s * (c⁻¹ * ∑ i, w i * ev i ^ s) :=
          mul_le_mul_of_nonneg_left hJ (pow_nonneg hcpos.le s)
      _ = c ^ (s - 1) * ∑ i, w i * ev i ^ s := by
          rw [← mul_assoc]
          congr 1
          rw [← pow_sub_one_mul (by omega : s ≠ 0)]
          field_simp
      _ ≤ 1 * ∑ i, w i * ev i ^ s :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hcpos.le hc1) hR0
      _ = _ := one_mul _

/-- **HMT 2011, Prop 8.6** (the power-iteration inequality). For an orthogonal projector `P`
(`Pᵀ = P`, `P² = P`), any real `A` and `q ≥ 0`, `‖PA‖^{2q+1} ≤ ‖P(AAᵀ)^q A‖`.
Deviation: none (HMT state it for any orthogonal projector and any `A`; `q = 0` is equality).
Atlas `power-iteration-deterministic` (core lemma; audit G2 A2). -/
theorem specNorm_mul_pow_le_specNorm_mul_gram_pow_mul (P : Matrix m m ℝ) (hPs : Pᵀ = P)
    (hPi : IsIdempotentElem P) (A : Matrix m n ℝ) (q : ℕ) :
    specNorm (P * A) ^ (2 * q + 1) ≤ specNorm (P * (A * Aᵀ) ^ q * A) := by
  set M := A * Aᵀ with hMdef
  set s := 2 * q + 1 with hs
  have hMs : Mᵀ = M := by rw [hMdef, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hMpsd : M.PosSemidef := by
    rw [hMdef, ← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact Matrix.posSemidef_self_mul_conjTranspose A
  -- `‖PA‖² = ‖PMP‖` and `‖PM^qA‖² = ‖PM^sP‖`.
  have hH : (P * A) * (P * A)ᵀ = P * M * P := by
    rw [Matrix.transpose_mul, hPs, hMdef]; simp only [Matrix.mul_assoc]
  have hHs : (P * M ^ q * A) * (P * M ^ q * A)ᵀ = P * M ^ s * P := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hPs, Matrix.transpose_pow, hMs]
    have : M ^ s = M ^ q * M * M ^ q := by
      rw [hs, ← pow_succ, ← pow_add]; ring_nf
    rw [this, hMdef]; simp only [Matrix.mul_assoc]
  have hA2 : specNorm (P * A) ^ 2 = specNorm (P * M * P) := by
    rw [← specNorm_mul_transpose_self, hH]
  have hB2 : specNorm (P * M ^ q * A) ^ 2 = specNorm (P * M ^ s * P) := by
    rw [← specNorm_mul_transpose_self, hHs]
  -- The key inequality `‖PMP‖^s ≤ ‖PM^sP‖`.
  have hkey : specNorm (P * M * P) ^ s ≤ specNorm (P * M ^ s * P) := by
    rcases isEmpty_or_nonempty m with hm | hm
    · have : P * M * P = 0 := Subsingleton.elim _ _
      rw [this, specNorm_zero, zero_pow (by omega)]
      exact specNorm_nonneg _
    · have hHpsd : (P * M * P).PosSemidef := by
        rw [← hH, ← Matrix.conjTranspose_eq_transpose_of_trivial]
        exact Matrix.posSemidef_self_mul_conjTranspose _
      obtain ⟨x, hx, hxe⟩ := exists_unit_mulVec_eq_specNorm_smul hHpsd
      have hval : x ⬝ᵥ ((P * M * P) *ᵥ x) = specNorm (P * M * P) := by
        rw [hxe, dotProduct_smul, hx, smul_eq_mul, mul_one]
      -- `xᵀ(P B P)x = (Px)ᵀ B (Px)` for symmetric `P`.
      have hsand : ∀ B : Matrix m m ℝ, x ⬝ᵥ ((P * B * P) *ᵥ x) = (P *ᵥ x) ⬝ᵥ (B *ᵥ (P *ᵥ x)) := by
        intro B
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          ← Matrix.mulVec_transpose, hPs]
      have hy : (P *ᵥ x) ⬝ᵥ (P *ᵥ x) ≤ 1 := by
        rw [mulVec_dotProduct_mulVec_self, hPs, show P * P = P from hPi]
        have h := abs_dotProduct_mulVec_le_specNorm P x
        rw [hx, mul_one] at h
        exact (le_abs_self _).trans (h.trans
          (specNorm_le_one_of_isSymm_of_isIdempotentElem hPs hPi))
      have hJ := dotProduct_mulVec_pow_le_dotProduct_pow_mulVec hMpsd hy (by omega : 1 ≤ s)
      rw [← hsand, ← hsand, hval] at hJ
      refine hJ.trans ?_
      have h := abs_dotProduct_mulVec_le_specNorm (P * M ^ s * P) x
      rw [hx, mul_one] at h
      exact (le_abs_self _).trans h
  have hfin : (specNorm (P * A) ^ s) ^ 2 ≤ specNorm (P * M ^ q * A) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, hA2, hB2]; exact hkey
  have := (pow_le_pow_iff_left₀ (pow_nonneg (specNorm_nonneg _) s) (specNorm_nonneg _)
    two_ne_zero).1 hfin
  simpa only [Matrix.mul_assoc] using this

/-- **Deterministic power-iteration bound** (HMT 2011, Thm 9.2, power form): for `Q` with
orthonormal columns and `q ≥ 0`, `‖(I − QQᵀ)A‖^{2q+1} ≤ ‖(I − QQᵀ)(AAᵀ)^q A‖`.
Deviation: the source takes `Q = orth((AAᵀ)^q AΩ)`; the inequality holds for every `Q` with
orthonormal columns, so that hypothesis is dropped. Atlas `power-iteration-deterministic`. -/
theorem specNorm_residual_pow_le {q' : Type*} [Fintype q'] [DecidableEq q']
    {Q : Matrix m q' ℝ} (hQ : HasOrthonormalCols Q) (A : Matrix m n ℝ) (q : ℕ) :
    specNorm (residual Q A) ^ (2 * q + 1) ≤ specNorm (residual Q ((A * Aᵀ) ^ q * A)) := by
  have hPs : (1 - Q * Qᵀ)ᵀ = 1 - Q * Qᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, mul_transpose_symm]
  have h := specNorm_mul_pow_le_specNorm_mul_gram_pow_mul (1 - Q * Qᵀ) hPs
    (one_sub_mul_transpose_idem hQ) A q
  rwa [residual_eq_one_sub_mul, residual_eq_one_sub_mul, ← Matrix.mul_assoc]

/-- **Deterministic power-iteration bound** (HMT 2011, Thm 9.2, as printed):
`‖(I − QQᵀ)A‖ ≤ ‖(I − QQᵀ)(AAᵀ)^q A‖^{1/(2q+1)}` for any `Q` with orthonormal columns.
Deviation: no `Q = orth((AAᵀ)^q AΩ)` hypothesis (see `specNorm_residual_pow_le`).
Atlas `power-iteration-deterministic`. -/
theorem specNorm_residual_le_rpow {q' : Type*} [Fintype q'] [DecidableEq q']
    {Q : Matrix m q' ℝ} (hQ : HasOrthonormalCols Q) (A : Matrix m n ℝ) (q : ℕ) :
    specNorm (residual Q A) ≤
      specNorm (residual Q ((A * Aᵀ) ^ q * A)) ^ (1 / (2 * (q : ℝ) + 1)) := by
  have h := specNorm_residual_pow_le hQ A q
  have hne : 2 * q + 1 ≠ 0 := by omega
  have hcast : (1 / (2 * (q : ℝ) + 1)) = ((2 * q + 1 : ℕ) : ℝ)⁻¹ := by push_cast; ring
  rw [hcast, ← Real.pow_rpow_inv_natCast (specNorm_nonneg (residual Q A)) hne]
  exact Real.rpow_le_rpow (pow_nonneg (specNorm_nonneg _) _) h
    (inv_nonneg.2 (Nat.cast_nonneg _))

end NLAlib
