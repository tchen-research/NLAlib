import NLAlib.Krylov.Processes.BidiagonalizationBasic
import NLAlib.Krylov.Processes.LanczosRecurrence
import NLAlib.Matrix.Basic.Dilation

/-!
# Golub--Kahan as Lanczos on the symmetric dilation

Alternating left and right embedded vectors turns two Lanczos steps on `[0 A; Aᵀ 0]`
into one Golub--Kahan step. The identities use the actual total recurrences, including
zero normalization at breakdown.
Source: Golub--Van Loan (2013), Section 10.4.1; Paige--Saunders (1982), Section 3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n : Type*}

private def left (u : m → ℝ) : m ⊕ n → ℝ := Sum.elim u 0
private def right (v : n → ℝ) : m ⊕ n → ℝ := Sum.elim 0 v

private theorem left_sub (u v : m → ℝ) : left (n := n) (u - v) = left u - left v := by
  ext (i | i) <;> simp [left]

private theorem right_sub (u v : n → ℝ) : right (m := m) (u - v) = right u - right v := by
  ext (i | i) <;> simp [right]

private theorem left_smul (a : ℝ) (u : m → ℝ) : left (n := n) (a • u) = a • left u := by
  ext (i | i) <;> simp [left]

private theorem right_smul (a : ℝ) (v : n → ℝ) : right (m := m) (a • v) = a • right v := by
  ext (i | i) <;> simp [right]

variable [Fintype m] [Fintype n]

private theorem dot_left_right (u : m → ℝ) (v : n → ℝ) : left u ⬝ᵥ right v = 0 := by
  simp [left, right, dotProduct, Fintype.sum_sum_type]

private theorem dot_right_left (v : n → ℝ) (u : m → ℝ) : right v ⬝ᵥ left u = 0 := by
  rw [dotProduct_comm, dot_left_right]

private theorem norm_left (u : m → ℝ) :
    ‖WithLp.toLp 2 (left (n := n) u)‖ = ‖WithLp.toLp 2 u‖ := by
  rw [norm_toLp_eq_sqrt_dotProduct_self, norm_toLp_eq_sqrt_dotProduct_self]
  simp [left, dotProduct, Fintype.sum_sum_type]

private theorem norm_right (v : n → ℝ) :
    ‖WithLp.toLp 2 (right (m := m) v)‖ = ‖WithLp.toLp 2 v‖ := by
  rw [norm_toLp_eq_sqrt_dotProduct_self, norm_toLp_eq_sqrt_dotProduct_self]
  simp [right, dotProduct, Fintype.sum_sum_type]

private theorem dilation_mulVec_left (A : Matrix m n ℝ) (u : m → ℝ) :
    dilation A *ᵥ left u = right (Aᵀ *ᵥ u) := by
  ext (i | i) <;> simp [dilation, left, right, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

private theorem dilation_mulVec_right (A : Matrix m n ℝ) (v : n → ℝ) :
    dilation A *ᵥ right v = left (A *ᵥ v) := by
  ext (i | i) <;> simp [dilation, left, right, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

private theorem lanczosStep_dilation_left (A : Matrix m n ℝ) (u : m → ℝ) (v : n → ℝ)
    (a : ℝ) :
    lanczosStep (dilation A) ⟨right v, left u, a⟩ =
      ⟨left u, right (‖WithLp.toLp 2 (Aᵀ *ᵥ u - a • v)‖⁻¹ • (Aᵀ *ᵥ u - a • v)),
        ‖WithLp.toLp 2 (Aᵀ *ᵥ u - a • v)‖⟩ := by
  simp only [lanczosStep, dilation_mulVec_left, dot_left_right, zero_smul, sub_zero,
    ← right_smul, ← right_sub, norm_right]

private theorem lanczosStep_dilation_right (A : Matrix m n ℝ) (v : n → ℝ) (u : m → ℝ)
    (a : ℝ) :
    lanczosStep (dilation A) ⟨left u, right v, a⟩ =
      ⟨right v, left (‖WithLp.toLp 2 (A *ᵥ v - a • u)‖⁻¹ • (A *ᵥ v - a • u)),
        ‖WithLp.toLp 2 (A *ᵥ v - a • u)‖⟩ := by
  simp only [lanczosStep, dilation_mulVec_right, dot_right_left, zero_smul, sub_zero,
    ← left_smul, ← left_sub, norm_left]

private def pairedState (s : GolubKahanState m n) : LanczosState (m ⊕ n) :=
  ⟨left s.u, right s.v, s.alpha⟩

private theorem lanczosStep_twice_pairedState (A : Matrix m n ℝ) (s : GolubKahanState m n) :
    lanczosStep (dilation A) (lanczosStep (dilation A) (pairedState s)) =
      pairedState (golubKahanStep A s) := by
  rw [pairedState, lanczosStep_dilation_right, lanczosStep_dilation_left]
  simp only [pairedState, golubKahanStep, norm_toLp_eq_sqrt_dotProduct_self]

private theorem lanczosState_one_pairedState (A : Matrix m n ℝ) (b : m → ℝ) :
    lanczosState (dilation A) (left b) 1 = pairedState (golubKahanInit A b) := by
  rw [lanczosState_succ, lanczosState_zero]
  have hi : lanczosInit (left (n := n) b) =
      (⟨right (0 : n → ℝ), left (‖WithLp.toLp 2 b‖⁻¹ • b), 0⟩ : LanczosState (m ⊕ n)) := by
    simp only [lanczosInit, norm_left, ← left_smul]
    congr 1
    ext (i | i) <;> rfl
  rw [hi, lanczosStep_dilation_left]
  simp only [zero_smul, sub_zero, pairedState, golubKahanInit,
    norm_toLp_eq_sqrt_dotProduct_self]

private theorem lanczosState_odd_pairedState (A : Matrix m n ℝ) (b : m → ℝ) (j : ℕ) :
    lanczosState (dilation A) (left b) (2 * j + 1) =
      pairedState (golubKahanRecurrence A b j) := by
  induction j with
  | zero => exact lanczosState_one_pairedState A b
  | succ j ih =>
    have he : 2 * (j + 1) + 1 = (2 * j + 1 + 1) + 1 := by omega
    rw [he, lanczosState_succ, lanczosState_succ, ih, lanczosStep_twice_pairedState]
    simp only [golubKahanRecurrence, Function.iterate_succ_apply']

/-- The odd Lanczos vectors of the dilation are exactly the embedded right
Golub--Kahan vectors, including zeros after breakdown. -/
theorem lanczosRecurrence_dilation_odd (A : Matrix m n ℝ) (b : m → ℝ) (j : ℕ) :
    lanczosRecurrence (dilation A) (Sum.elim b (0 : n → ℝ)) (2 * j + 1) =
      Sum.elim (0 : m → ℝ) (golubKahanRecurrence A b j).v := by
  exact congrArg LanczosState.cur (lanczosState_odd_pairedState A b j)

/-- The even Lanczos vectors of the dilation are exactly the embedded left
Golub--Kahan vectors. -/
theorem lanczosRecurrence_dilation_even (A : Matrix m n ℝ) (b : m → ℝ) (j : ℕ) :
    lanczosRecurrence (dilation A) (Sum.elim b (0 : n → ℝ)) (2 * j) =
      Sum.elim (golubKahanRecurrence A b j).u (0 : n → ℝ) := by
  have h := congrArg LanczosState.prev (lanczosState_odd_pairedState A b j)
  simpa only [lanczosState_succ_prev, lanczosRecurrence, pairedState, left] using h

/-- Each Golub--Kahan diagonal coefficient is the corresponding odd Lanczos link
coefficient of the symmetric dilation. -/
theorem lanczosBeta_dilation_odd (A : Matrix m n ℝ) (b : m → ℝ) (j : ℕ) :
    lanczosBeta (dilation A) (Sum.elim b (0 : n → ℝ)) (2 * j + 1) =
      (golubKahanRecurrence A b j).alpha := by
  exact congrArg LanczosState.beta (lanczosState_odd_pairedState A b j)

/-- After initialization, the even Lanczos link coefficients are the Golub--Kahan
subdiagonal coefficients. The initial Golub--Kahan `beta` is instead the norm of `b`. -/
theorem lanczosBeta_dilation_even_succ (A : Matrix m n ℝ) (b : m → ℝ) (j : ℕ) :
    lanczosBeta (dilation A) (Sum.elim b (0 : n → ℝ)) (2 * (j + 1)) =
      (golubKahanRecurrence A b (j + 1)).beta := by
  have he : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
  change (lanczosState (dilation A) (left b) (2 * (j + 1))).beta = _
  rw [he, lanczosState_succ, lanczosState_odd_pairedState,
    pairedState, lanczosStep_dilation_right]
  simp only [golubKahanRecurrence, Function.iterate_succ_apply', golubKahanStep,
    norm_toLp_eq_sqrt_dotProduct_self]

/-- The diagonal entry of the Golub--Kahan compression is the recurrence's `alpha`,
even for the total recurrence after breakdown. -/
theorem dotProduct_golubKahan_eq_alpha (A : Matrix m n ℝ) (b : m → ℝ) (j : ℕ) :
    (golubKahanRecurrence A b j).u ⬝ᵥ (A *ᵥ (golubKahanRecurrence A b j).v) =
      (golubKahanRecurrence A b j).alpha := by
  classical
  have h := lanczosBeta_succ_eq_dotProduct (isHermitian_dilation A)
    (Sum.elim b (0 : n → ℝ)) (2 * j)
  rw [lanczosBeta_dilation_odd,
    ← lanczosRecurrence_eq_arnoldiBasis (isHermitian_dilation A),
    ← lanczosRecurrence_eq_arnoldiBasis (isHermitian_dilation A),
    lanczosRecurrence_dilation_odd, lanczosRecurrence_dilation_even] at h
  change _ = right (golubKahanRecurrence A b j).v ⬝ᵥ
    (dilation A *ᵥ left (golubKahanRecurrence A b j).u) at h
  rw [dilation_mulVec_left] at h
  simp only [right, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] at h
  change _ = (golubKahanRecurrence A b j).v ⬝ᵥ
    (Aᵀ *ᵥ (golubKahanRecurrence A b j).u) at h
  rw [Matrix.dotProduct_transpose_mulVec] at h
  exact h.symm

/-- The subdiagonal entry of the Golub--Kahan compression is the next `beta`,
even for the total recurrence after breakdown. -/
theorem dotProduct_golubKahan_eq_beta (A : Matrix m n ℝ) (b : m → ℝ) (j : ℕ) :
    (golubKahanRecurrence A b (j + 1)).u ⬝ᵥ (A *ᵥ (golubKahanRecurrence A b j).v) =
      (golubKahanRecurrence A b (j + 1)).beta := by
  classical
  have h := lanczosBeta_succ_eq_dotProduct (isHermitian_dilation A)
    (Sum.elim b (0 : n → ℝ)) (2 * j + 1)
  have he : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
  rw [he, lanczosBeta_dilation_even_succ,
    ← lanczosRecurrence_eq_arnoldiBasis (isHermitian_dilation A),
    ← lanczosRecurrence_eq_arnoldiBasis (isHermitian_dilation A),
    lanczosRecurrence_dilation_even, lanczosRecurrence_dilation_odd] at h
  change _ = left (golubKahanRecurrence A b (j + 1)).u ⬝ᵥ
    (dilation A *ᵥ right (golubKahanRecurrence A b j).v) at h
  rw [dilation_mulVec_right] at h
  simpa only [left, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero] using h.symm

end NLAlib
