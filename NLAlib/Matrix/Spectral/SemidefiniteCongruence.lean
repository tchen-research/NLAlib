import NLAlib.Matrix.Spectral.SimultaneousOrthogonal
import NLAlib.Matrix.Basic.GramVanishing
/-!
# Simultaneous congruence of singular positive semidefinite pairs

Whiten the positive spectral coordinates of the sum and leave its kernel
unchanged. The two resulting positive semidefinite matrices commute, hence
admit a common orthogonal diagonalization. Source: Horn--Johnson (2013),
Section 7.6; atlas `simultaneous-diagonalization-congruence`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Two PSD summands of a diagonal orthogonal projection commute.
Horn--Johnson (2013), Section 7.6; helper for singular simultaneous congruence. -/
theorem commute_of_posSemidef_add_eq_diagonal_projection {A B : Matrix n n ℝ}
    {p : n → ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : A + B = diagonal p) (hp : ∀ i, p i = 0 ∨ p i = 1) : Commute A B := by
  have hAP : A * diagonal p = A := by
    ext i j
    rw [Matrix.mul_diagonal]
    rcases hp j with hj | hj
    · have he := congrArg (fun M : Matrix n n ℝ => M j j) hAB
      simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, hj] at he
      have hz : A j j = 0 := by linarith [hA.diag_nonneg (i := j), hB.diag_nonneg (i := j)]
      rw [hj, mul_zero, apply_eq_zero_of_posSemidef_of_apply_self_eq_zero hA hz i]
    · rw [hj, mul_one]
  have hPA : diagonal p * A = A := by
    have h := congrArg Matrix.transpose hAP
    have ht : Aᵀ = A := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
    simpa only [Matrix.transpose_mul, Matrix.diagonal_transpose, ht] using h
  change A * B = B * A
  have hleft : A * A + A * B = A := by rw [← Matrix.mul_add, hAB, hAP]
  have hright : A * A + B * A = A := by rw [← Matrix.add_mul, hAB, hPA]
  exact add_left_cancel (hleft.trans hright.symm)

open scoped Matrix.Norms.L2Operator in
/-- A pair of real PSD matrices, including singular pairs with a common
kernel, has an invertible simultaneous diagonal congruence with nonnegative
diagonal entries. Horn--Johnson (2013), Section 7.6.
atlas: simultaneous-diagonalization-congruence (partial) -/
theorem exists_diagonal_congruence_of_posSemidef {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∃ (X : Matrix n n ℝ) (a b : n → ℝ), IsUnit X ∧
      Xᵀ * A * X = diagonal a ∧ Xᵀ * B * X = diagonal b ∧
      (∀ i, 0 ≤ a i) ∧ (∀ i, 0 ≤ b i) := by
  classical
  let hC := (hA.add hB).isHermitian
  let U : Matrix n n ℝ := hC.eigenvectorUnitary
  let c := hC.eigenvalues
  have hc : ∀ i, 0 ≤ c i := (hA.add hB).eigenvalues_nonneg
  have hUt : Uᵀ * U = 1 := transpose_eigenvectorUnitary_mul_self hC
  have hUu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr
    (Matrix.isUnit_det_of_left_inverse hUt)
  have hCU : Uᵀ * (A + B) * U = diagonal c := by
    calc
      Uᵀ * (A + B) * U = Uᵀ * (U * diagonal c * Uᵀ) * U :=
        congrArg (fun M => Uᵀ * M * U) (eq_eigenvectorUnitary_mul_diagonal_mul_transpose hC)
      _ = diagonal c := by
        simp only [Matrix.mul_assoc]
        rw [hUt, Matrix.mul_one, ← Matrix.mul_assoc, hUt, Matrix.one_mul]
  let t : n → ℝ := fun i => if c i = 0 then 1 else (Real.sqrt (c i))⁻¹
  have ht : ∀ i, t i ≠ 0 := by
    intro i
    dsimp [t]
    split_ifs with hi
    · exact one_ne_zero
    · exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hc i) (Ne.symm hi)))
  let R := U * diagonal t
  have hR : IsUnit R := hUu.mul (Matrix.isUnit_diagonal.mpr
    (Pi.isUnit_iff.mpr fun i => isUnit_iff_ne_zero.mpr (ht i)))
  let A' := Rᵀ * A * R
  let B' := Rᵀ * B * R
  have hA' : A'.PosSemidef := by
    simpa only [A', Matrix.conjTranspose_eq_transpose_of_trivial] using
      hA.conjTranspose_mul_mul_same R
  have hB' : B'.PosSemidef := by
    simpa only [B', Matrix.conjTranspose_eq_transpose_of_trivial] using
      hB.conjTranspose_mul_mul_same R
  let p : n → ℝ := fun i => t i * c i * t i
  have hsum : A' + B' = diagonal p := by
    calc
      A' + B' = Rᵀ * (A + B) * R := by simp only [Matrix.mul_add, Matrix.add_mul, A', B']
      _ = diagonal t * (Uᵀ * (A + B) * U) * diagonal t := by
        simp only [R, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
      _ = diagonal p := by rw [hCU, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  have hp : ∀ i, p i = 0 ∨ p i = 1 := by
    intro i
    by_cases hi : c i = 0
    · exact Or.inl (by simp [p, hi])
    · right
      have hs : Real.sqrt (c i) ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hc i) (Ne.symm hi))
      dsimp [p, t]
      rw [if_neg hi]
      field_simp
      exact (Real.sq_sqrt (hc i)).symm
  obtain ⟨V, a, b, hV, hVA, hVB⟩ := exists_orthogonal_congruence_diagonal_of_commute
    hA'.isHermitian hB'.isHermitian
    (commute_of_posSemidef_add_eq_diagonal_projection hA' hB' hsum hp)
  have hVu : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).mpr
    (Matrix.isUnit_det_of_left_inverse hV)
  refine ⟨R * V, a, b, hR.mul hVu, ?_, ?_, ?_, ?_⟩
  · simpa only [A', Matrix.transpose_mul, Matrix.mul_assoc] using hVA
  · simpa only [B', Matrix.transpose_mul, Matrix.mul_assoc] using hVB
  · apply Matrix.posSemidef_diagonal_iff.mp
    rw [← hVA]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA'.conjTranspose_mul_mul_same V
  · apply Matrix.posSemidef_diagonal_iff.mp
    rw [← hVB]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB'.conjTranspose_mul_mul_same V

open scoped Matrix.Norms.L2Operator in
/-- Singular PSD pairs have normalized diagonal congruences: the first
diagonal contains only zero and one; the second is nonnegative and contains
only zero and one wherever the first is zero. These are exactly the three
blocks `(I_r,0_s,0_t)` and `(diag(beta),I_s,0_t)`, without fixing a coordinate
ordering. Horn--Johnson (2013), Section 7.6.
atlas: simultaneous-diagonalization-congruence (partial) -/
theorem exists_normalized_diagonal_congruence_of_posSemidef {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∃ (X : Matrix n n ℝ) (a b : n → ℝ), IsUnit X ∧
      Xᵀ * A * X = diagonal a ∧ Xᵀ * B * X = diagonal b ∧
      (∀ i, a i = 0 ∨ a i = 1) ∧ (∀ i, 0 ≤ b i) ∧
      (∀ i, a i = 0 → b i = 0 ∨ b i = 1) := by
  classical
  obtain ⟨Y, a, b, hY, hYA, hYB, ha, hb⟩ := exists_diagonal_congruence_of_posSemidef hA hB
  let q : n → ℝ := fun i => if a i = 0 then b i else a i
  have hq : ∀ i, 0 ≤ q i := by intro i; dsimp [q]; split_ifs <;> first | exact ha i | exact hb i
  let t : n → ℝ := fun i => if q i = 0 then 1 else (Real.sqrt (q i))⁻¹
  have ht : ∀ i, t i ≠ 0 := by
    intro i
    dsimp [t]
    split_ifs with hi
    · exact one_ne_zero
    · exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hq i) (Ne.symm hi)))
  have htqt : ∀ i, q i ≠ 0 → t i * q i * t i = 1 := by
    intro i hi
    have hs : Real.sqrt (q i) ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hq i) (Ne.symm hi))
    dsimp [t]
    rw [if_neg hi]
    field_simp
    exact (Real.sq_sqrt (hq i)).symm
  let a' : n → ℝ := fun i => t i * a i * t i
  let b' : n → ℝ := fun i => t i * b i * t i
  refine ⟨Y * diagonal t, a', b', hY.mul (Matrix.isUnit_diagonal.mpr
    (Pi.isUnit_iff.mpr fun i => isUnit_iff_ne_zero.mpr (ht i))), ?_, ?_, ?_, ?_, ?_⟩
  · calc
      (Y * diagonal t)ᵀ * A * (Y * diagonal t) =
          diagonal t * (Yᵀ * A * Y) * diagonal t := by
        simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
      _ = diagonal a' := by rw [hYA, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  · calc
      (Y * diagonal t)ᵀ * B * (Y * diagonal t) =
          diagonal t * (Yᵀ * B * Y) * diagonal t := by
        simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
      _ = diagonal b' := by rw [hYB, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  · intro i
    by_cases hai : a i = 0
    · exact Or.inl (by simp [a', hai])
    · right
      have hqi : q i = a i := if_neg hai
      simpa only [a', hqi] using htqt i (hqi ▸ hai)
  · intro i
    change 0 ≤ t i * b i * t i
    nlinarith [sq_nonneg (t i), hb i, mul_nonneg (sq_nonneg (t i)) (hb i)]
  · intro i hai
    have hai0 : a i = 0 := by
      change t i * a i * t i = 0 at hai
      exact (mul_eq_zero.mp (mul_eq_zero.mp hai |>.resolve_right (ht i))).resolve_left (ht i)
    have hqi : q i = b i := if_pos hai0
    by_cases hbi : b i = 0
    · exact Or.inl (by simp [b', hbi])
    · right
      simpa only [b', hqi] using htqt i (hqi ▸ hbi)

/-- Congruence diagonal identities can equivalently be written in factor
form using the inverse transpose. Horn--Johnson (2013), Section 7.6;
helper for simultaneous congruence. -/
theorem eq_inv_transpose_mul_diagonal_mul_inv_of_congruence
    {A X : Matrix n n ℝ} {a : n → ℝ} (hX : IsUnit X)
    (hXA : Xᵀ * A * X = diagonal a) :
    A = Xᵀ⁻¹ * diagonal a * X⁻¹ := by
  have hXd := (Matrix.isUnit_iff_isUnit_det X).mp hX
  have hXtd := (Matrix.isUnit_iff_isUnit_det Xᵀ).mp ((Matrix.isUnit_transpose X).mpr hX)
  rw [← hXA]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul Xᵀ hXtd, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv X hXd, Matrix.mul_one]

omit [DecidableEq n] in
/-- The kernel of the sum of two PSD real matrices is their common kernel.
Horn--Johnson (2013), Section 7.6; helper for singular simultaneous congruence. -/
theorem ker_add_eq_inf_of_posSemidef {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    LinearMap.ker (A + B).mulVecLin = LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_inf, Matrix.mulVecLin_apply, Matrix.add_mulVec]
  constructor
  · intro h
    have hq : x ⬝ᵥ A *ᵥ x + x ⬝ᵥ B *ᵥ x = 0 := by rw [← dotProduct_add, h, dotProduct_zero]
    have ha : 0 ≤ x ⬝ᵥ A *ᵥ x := by simpa using hA.dotProduct_mulVec_nonneg x
    have hb : 0 ≤ x ⬝ᵥ B *ᵥ x := by simpa using hB.dotProduct_mulVec_nonneg x
    exact ⟨(hA.dotProduct_mulVec_zero_iff x).mp (by simpa using (show x ⬝ᵥ A *ᵥ x = 0 by linarith)),
      (hB.dotProduct_mulVec_zero_iff x).mp (by simpa using (show x ⬝ᵥ B *ᵥ x = 0 by linarith))⟩
  · rintro ⟨ha, hb⟩
    rw [ha, hb, add_zero]

/-- The rank of a congruence diagonal equals the number of its nonzero
entries. Horn--Johnson (2013), Section 7.6; helper for PSD-pair block sizes. -/
theorem rank_eq_card_nonzero_of_diagonal_congruence {A X : Matrix n n ℝ} {a : n → ℝ}
    (hX : IsUnit X) (hXA : Xᵀ * A * X = diagonal a) :
    A.rank = Fintype.card {i // a i ≠ 0} := by
  classical
  have hr := congrArg Matrix.rank hXA
  rw [Matrix.rank_mul_eq_left_of_isUnit_det X _ ((Matrix.isUnit_iff_isUnit_det _).mp hX),
    Matrix.rank_mul_eq_right_of_isUnit_det Xᵀ _ ((Matrix.isUnit_iff_isUnit_det _).mp
      ((Matrix.isUnit_transpose _).mpr hX)), Matrix.rank_diagonal] at hr
  exact hr

/-- Full singular PSD-pair normal form with exact three-block dimensions.
The first block is indexed by `a=1`, the second by `a=0,b=1`, and the third
by `a=b=0`; thus coordinate reordering gives `(I_r,0_s,0_t)` and
`(diag(beta),I_s,0_t)`. The identities identify `r=rank A`,
`r+s=rank(A+B)`, and `t=dim(ker A ∩ ker B)`, including all empty blocks.
Horn--Johnson (2013), Section 7.6.
atlas: simultaneous-diagonalization-congruence -/
theorem semidefinite_pair_congruence_normal_form {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∃ (S : Matrix n n ℝ) (a b : n → ℝ), IsUnit S ∧
      A = S * diagonal a * Sᵀ ∧ B = S * diagonal b * Sᵀ ∧
      (∀ i, a i = 0 ∨ a i = 1) ∧ (∀ i, 0 ≤ b i) ∧
      (∀ i, a i = 0 → b i = 0 ∨ b i = 1) ∧
      A.rank = Fintype.card {i // a i = 1} ∧
      (A + B).rank = Fintype.card {i // a i = 1} +
        Fintype.card {i // a i = 0 ∧ b i = 1} ∧
      Module.finrank ℝ ↥(LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin) =
        Fintype.card {i // a i = 0 ∧ b i = 0} := by
  classical
  obtain ⟨X, a, b, hX, hXA, hXB, ha, hb, hab⟩ :=
    exists_normalized_diagonal_congruence_of_posSemidef hA hB
  have ha0 (i : n) : 0 ≤ a i := by rcases ha i with h | h <;> simp [h]
  have hsum0 (i : n) : a i + b i = 0 ↔ a i = 0 ∧ b i = 0 := by
    constructor
    · intro h; constructor <;> linarith [ha0 i, hb i]
    · rintro ⟨h, h'⟩; rw [h, h', add_zero]
  have ha1 (i : n) : a i ≠ 0 ↔ a i = 1 := by rcases ha i with h | h <;> simp [h]
  have hsum1 (i : n) : a i + b i ≠ 0 ↔ a i = 1 ∨ (a i = 0 ∧ b i = 1) := by
    simp only [ne_eq, hsum0]
    rcases ha i with hai | hai
    · rcases hab i hai with hbi | hbi <;> simp [hai, hbi]
    · simp [hai]
  have hXsum : Xᵀ * (A + B) * X = diagonal (fun i => a i + b i) := by
    rw [Matrix.mul_add, Matrix.add_mul, hXA, hXB, ← Matrix.diagonal_add]
  have hrA := rank_eq_card_nonzero_of_diagonal_congruence hX hXA
  have hrC := rank_eq_card_nonzero_of_diagonal_congruence hX hXsum
  have hrA' : A.rank = Fintype.card {i // a i = 1} := by
    simpa only [ha1] using hrA
  have hrC' : (A + B).rank = Fintype.card {i // a i = 1} +
      Fintype.card {i // a i = 0 ∧ b i = 1} := by
    rw [hrC]
    simp only [hsum1, Fintype.card_subtype, Finset.filter_or]
    apply Finset.card_union_of_disjoint
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    exact zero_ne_one (hi'.1.symm.trans hi)
  have hnull : Module.finrank ℝ ↥(LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin) =
      Fintype.card {i // a i = 0 ∧ b i = 0} := by
    rw [← ker_add_eq_inf_of_posSemidef hA hB]
    have hr : (A + B).rank + Module.finrank ℝ (LinearMap.ker (A + B).mulVecLin) =
        Fintype.card n := by
      simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
        LinearMap.finrank_range_add_finrank_ker (A + B).mulVecLin
    have hc := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset n)) (p := fun i => a i + b i = 0)
    simp only [Finset.card_univ, hsum0] at hc
    rw [hrC, Fintype.card_subtype] at hr
    simp only [ne_eq, hsum0] at hr
    rw [Fintype.card_subtype]
    omega
  refine ⟨Xᵀ⁻¹, a, b, Matrix.isUnit_nonsing_inv_iff.mpr ((Matrix.isUnit_transpose X).mpr hX),
    ?_, ?_, ha, hb, hab, hrA', hrC', hnull⟩
  · simpa only [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose] using
      eq_inv_transpose_mul_diagonal_mul_inv_of_congruence hX hXA
  · simpa only [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose] using
      eq_inv_transpose_mul_diagonal_mul_inv_of_congruence hX hXB

end NLAlib
