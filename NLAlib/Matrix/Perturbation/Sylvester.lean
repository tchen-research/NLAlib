import NLAlib.Matrix.Norms.EuclideanOperatorBounds
import NLAlib.Matrix.Perturbation.ResidualBounds
/-!
# Separation bounds for Hermitian Sylvester equations

Pairwise spectral separation controls the Frobenius norm. The stronger
interval/complement separation controls the spectral norm with constant one.
The operator proof centers the interval and cancels its half-width, avoiding
an improper integral. Source: Bhatia §VII.2; atlas `sylvester-separation-bound`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
open Polynomial

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A pointwise lower spectral distance makes a shifted Hermitian matrix
expand Euclidean lengths. Bhatia §VII.2, by finite spectral expansion. -/
theorem mulVec_shift_sq_ge_of_eigenvalue_abs_sub_ge {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {s c : ℝ} (hs : 0 ≤ s)
    (hsep : ∀ i, s ≤ |hA.eigenvalues i-c|) (x : n → ℝ) :
    s^2*(x ⬝ᵥ x) ≤ ((A-c•1)*ᵥx) ⬝ᵥ ((A-c•1)*ᵥx) := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_shifted_residual_eq_sum hA, ← sum_sq_eigenvectorBasis_dotProduct hA x,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hh : s^2 ≤ (hA.eigenvalues i-c)^2 := by
    nlinarith [hsep i, sq_abs (hA.eigenvalues i-c), abs_nonneg (hA.eigenvalues i-c)]
  exact mul_le_mul_of_nonneg_right hh (sq_nonneg _)

/-- Spectral interval containment bounds the norm of the centered matrix by
the interval half-width. Bhatia §VII.2; empty spectra cause no exception. -/
theorem specNorm_shift_le_half_width {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a b : ℝ} (hab : a ≤ b) (hinterval : ∀ i, a ≤ hA.eigenvalues i ∧ hA.eigenvalues i ≤ b) :
    specNorm (A-((a+b)/2)•1) ≤ (b-a)/2 := by
  have hh := specNorm_aeval_le hA (X-C ((a+b)/2)) (by linarith : 0 ≤ (b-a)/2)
    (by intro i; simp only [eval_sub, eval_X, eval_C]; rw [abs_le];
        have hi := hinterval i; constructor <;> linarith)
  simpa only [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] using hh

/-- Interval/complement separation expands centered left multiplication
in spectral norm. Bhatia §VII.2, including empty row or column spaces. -/
theorem mul_specNorm_le_specNorm_shift_mul {L : Matrix m m ℝ} (hL : L.IsHermitian)
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 ≤ δ)
    (hout : ∀ i, hL.eigenvalues i ≤ a-δ ∨ b+δ ≤ hL.eigenvalues i)
    (X : Matrix m n ℝ) :
    ((b-a)/2+δ)*specNorm X ≤ specNorm ((L-((a+b)/2)•1)*X) := by
  have hs : 0 ≤ (b-a)/2+δ := by linarith
  apply mul_specNorm_le_specNorm_mul_of_mulVec_sq_le hs
  apply mulVec_shift_sq_ge_of_eigenvalue_abs_sub_ge hL hs
  intro i
  rw [le_abs]
  rcases hout i with hi | hi
  · right; linarith
  · left; linarith

/-- Interval/complement spectral separation bounds the Sylvester operator
in spectral norm with constant one. Bhatia §VII.2; interval structure is
essential and arbitrary interlaced spectra are not claimed.
atlas: sylvester-separation-bound (partial) -/
theorem mul_specNorm_le_specNorm_sylvester {L : Matrix m m ℝ} {M : Matrix n n ℝ}
    (hL : L.IsHermitian) (hM : M.IsHermitian) {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hinterval : ∀ j, a ≤ hM.eigenvalues j ∧ hM.eigenvalues j ≤ b)
    (hout : ∀ i, hL.eigenvalues i ≤ a-δ ∨ b+δ ≤ hL.eigenvalues i)
    (X : Matrix m n ℝ) : δ*specNorm X ≤ specNorm (L*X-X*M) := by
  have hl := mul_specNorm_le_specNorm_shift_mul hL hab hδ.le hout X
  have hm := specNorm_shift_le_half_width hM hab hinterval
  have heq : (L-((a+b)/2)•1)*X = (L*X-X*M)+X*(M-((a+b)/2)•1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    abel
  rw [heq] at hl
  have hu := specNorm_add_le (L*X-X*M) (X*(M-((a+b)/2)•1))
  have hp := specNorm_mul_le X (M-((a+b)/2)•1)
  have hmul := mul_le_mul_of_nonneg_left hm (specNorm_nonneg X)
  nlinarith

/-- A positive interval/complement gap yields the usual solution bound
for a Sylvester equation. Bhatia §VII.2; no invertibility assumption is added.
atlas: sylvester-separation-bound (partial) -/
theorem specNorm_le_specNorm_sylvester_div {L : Matrix m m ℝ} {M : Matrix n n ℝ}
    (hL : L.IsHermitian) (hM : M.IsHermitian) {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hinterval : ∀ j, a ≤ hM.eigenvalues j ∧ hM.eigenvalues j ≤ b)
    (hout : ∀ i, hL.eigenvalues i ≤ a-δ ∨ b+δ ≤ hL.eigenvalues i)
    (X : Matrix m n ℝ) : specNorm X ≤ specNorm (L*X-X*M)/δ := by
  apply (le_div_iff₀ hδ).2
  simpa only [mul_comm] using mul_specNorm_le_specNorm_sylvester hL hM hab hδ hinterval hout X

/-- Pairwise spectral separation controls the squared Frobenius norm of
the Sylvester operator. Bhatia §VII.2; both eigenspaces may be empty.
atlas: sylvester-separation-bound (partial) -/
theorem mul_frobSq_le_frobSq_sylvester {L : Matrix m m ℝ} {M : Matrix n n ℝ}
    (hL : L.IsHermitian) (hM : M.IsHermitian) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsep : ∀ i j, δ ≤ |hL.eigenvalues i-hM.eigenvalues j|) (X : Matrix m n ℝ) :
    δ^2*frobSq X ≤ frobSq (L*X-X*M) := by
  let U : Matrix m m ℝ := hL.eigenvectorUnitary
  let V : Matrix n n ℝ := hM.eigenvectorUnitary
  let Z := Uᵀ*X*V
  have hUt : Uᵀ*U=1 := transpose_eigenvectorUnitary_mul_self hL
  have hU : U*Uᵀ=1 := eigenvectorUnitary_mul_transpose_self hL
  have hVt : Vᵀ*V=1 := transpose_eigenvectorUnitary_mul_self hM
  have hV : V*Vᵀ=1 := eigenvectorUnitary_mul_transpose_self hM
  have hLX : Uᵀ*L = Matrix.diagonal hL.eigenvalues*Uᵀ := by
    calc
      _ = Uᵀ*(U*Matrix.diagonal hL.eigenvalues*Uᵀ) :=
        congrArg (fun T => Uᵀ*T) (eq_eigenvectorUnitary_mul_diagonal_mul_transpose hL)
      _ = _ := by simp only [← Matrix.mul_assoc, hUt, Matrix.one_mul]
  have hMV : M*V = V*Matrix.diagonal hM.eigenvalues := by
    calc
      _ = (V*Matrix.diagonal hM.eigenvalues*Vᵀ)*V :=
        congrArg (fun T => T*V) (eq_eigenvectorUnitary_mul_diagonal_mul_transpose hM)
      _ = _ := by rw [Matrix.mul_assoc, hVt, Matrix.mul_one]
  have heq : Uᵀ*(L*X-X*M)*V =
      Matrix.diagonal hL.eigenvalues*Z-Z*Matrix.diagonal hM.eigenvalues := by
    rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc Uᵀ L, hLX,
      ← Matrix.mul_assoc Uᵀ X M, Matrix.mul_assoc (Uᵀ*X) M V, hMV]
    simp only [Z, Matrix.mul_assoc]
  have hnorm (Y : Matrix m n ℝ) : frobSq (Uᵀ*Y*V) = frobSq Y := by
    have hUr : Uᵀᵀ*Uᵀ=1 := by simpa only [Matrix.transpose_transpose] using hU
    have hVr : Vᵀᵀ*Vᵀ=1 := by simpa only [Matrix.transpose_transpose] using hV
    have hh := frobSq_mul_right_of_orthonormal hVr (Uᵀ*Y)
    simpa only [Matrix.transpose_transpose, frobSq_mul_left_of_orthonormal hUr] using hh
  have hb : δ^2*frobSq Z ≤
      frobSq (Matrix.diagonal hL.eigenvalues*Z-Z*Matrix.diagonal hM.eigenvalues) := by
    rw [frobSq_eq_sum_sq, frobSq_eq_sum_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    have hh : δ^2 ≤ (hL.eigenvalues i-hM.eigenvalues j)^2 := by
      nlinarith [hsep i j, sq_abs (hL.eigenvalues i-hM.eigenvalues j),
        abs_nonneg (hL.eigenvalues i-hM.eigenvalues j)]
    have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg (Z i j))
    nlinarith
  rw [← heq] at hb
  simpa only [Z, hnorm] using hb

/-- Pairwise spectral separation controls the Frobenius norm with constant
one. Bhatia §VII.2; unlike the operator bound, arbitrary spectra are allowed.
atlas: sylvester-separation-bound (partial) -/
theorem mul_frobNorm_le_frobNorm_sylvester {L : Matrix m m ℝ} {M : Matrix n n ℝ}
    (hL : L.IsHermitian) (hM : M.IsHermitian) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j, δ ≤ |hL.eigenvalues i-hM.eigenvalues j|) (X : Matrix m n ℝ) :
    δ*frobNorm X ≤ frobNorm (L*X-X*M) := by
  have hh := mul_frobSq_le_frobSq_sylvester hL hM hδ.le hsep X
  rw [← frobNorm_sq X, ← frobNorm_sq (L*X-X*M), ← mul_pow] at hh
  exact le_of_pow_le_pow_left₀ two_ne_zero (frobNorm_nonneg _) hh

/-- The Frobenius solution bound corresponding to pairwise spectral
separation. Bhatia §VII.2, including zero-dimensional matrix spaces.
atlas: sylvester-separation-bound (partial) -/
theorem frobNorm_le_frobNorm_sylvester_div {L : Matrix m m ℝ} {M : Matrix n n ℝ}
    (hL : L.IsHermitian) (hM : M.IsHermitian) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j, δ ≤ |hL.eigenvalues i-hM.eigenvalues j|) (X : Matrix m n ℝ) :
    frobNorm X ≤ frobNorm (L*X-X*M)/δ := by
  apply (le_div_iff₀ hδ).2
  simpa only [mul_comm] using mul_frobNorm_le_frobNorm_sylvester hL hM hδ hsep X

/-- Interval/complement containment implies the pairwise separation used
by the Frobenius bound. Bhatia §VII.2. -/
theorem eigenvalue_separation_of_interval_complement {L : Matrix m m ℝ}
    {M : Matrix n n ℝ} (hL : L.IsHermitian) (hM : M.IsHermitian) {a b δ : ℝ}
    (hinterval : ∀ j, a ≤ hM.eigenvalues j ∧ hM.eigenvalues j ≤ b)
    (hout : ∀ i, hL.eigenvalues i ≤ a-δ ∨ b+δ ≤ hL.eigenvalues i) :
    ∀ i j, δ ≤ |hL.eigenvalues i-hM.eigenvalues j| := by
  intro i j
  have hj := hinterval j
  rw [le_abs]
  rcases hout i with hi | hi
  · right; linarith
  · left; linarith

/-- One-sided spectral separation gives constant-one spectral norm control.
Bhatia §VII.2; an empty right space is discharged before choosing an eigenvalue. -/
theorem mul_specNorm_le_specNorm_sylvester_of_one_sided {L : Matrix m m ℝ}
    {M : Matrix n n ℝ} (hL : L.IsHermitian) (hM : M.IsHermitian)
    {α δ : ℝ} (hδ : 0 < δ) (hmax : ∀ i, hL.eigenvalues i ≤ α-δ)
    (hmin : ∀ j, α ≤ hM.eigenvalues j) (X : Matrix m n ℝ) :
    δ*specNorm X ≤ specNorm (L*X-X*M) := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have hX : X=0 := by ext i j; exact isEmptyElim j
    simp [hX, specNorm_zero]
  | inr hn =>
    have hupper (j : n) : hM.eigenvalues j ≤ ‖hM.eigenvalues‖ := by
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm hM.eigenvalues j)
    have hab : α ≤ ‖hM.eigenvalues‖ := (hmin (Classical.arbitrary n)).trans (hupper _)
    exact mul_specNorm_le_specNorm_sylvester hL hM hab hδ
      (fun j => ⟨hmin j, hupper j⟩) (fun i => Or.inl (hmax i)) X

/-- Interval/complement separation without an extra endpoint-order
assumption: a nonempty interval spectrum forces it, and empty source spaces
have zero matrices. Bhatia §VII.2. -/
theorem mul_specNorm_le_specNorm_sylvester_of_interval {L : Matrix m m ℝ}
    {M : Matrix n n ℝ} (hL : L.IsHermitian) (hM : M.IsHermitian) {a b δ : ℝ}
    (hδ : 0 < δ) (hinterval : ∀ j, a ≤ hM.eigenvalues j ∧ hM.eigenvalues j ≤ b)
    (hout : ∀ i, hL.eigenvalues i ≤ a-δ ∨ b+δ ≤ hL.eigenvalues i)
    (X : Matrix m n ℝ) : δ*specNorm X ≤ specNorm (L*X-X*M) := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have hX : X=0 := by ext i j; exact isEmptyElim j
    simp [hX, specNorm_zero]
  | inr hn =>
    have hi := hinterval (Classical.arbitrary n)
    exact mul_specNorm_le_specNorm_sylvester hL hM (hi.1.trans hi.2) hδ hinterval hout X

/-- All Sylvester separation conclusions: arbitrary pairwise gaps in
Frobenius norm and interval/complement gaps in both norms. Bhatia §VII.2,
Davis–Kahan §5–6. Indices are arbitrary finite types and may be empty.
atlas: sylvester-separation-bound -/
theorem sylvester_separation_bounds {L : Matrix m m ℝ} {M : Matrix n n ℝ}
    (hL : L.IsHermitian) (hM : M.IsHermitian) (X : Matrix m n ℝ) :
    (∀ δ : ℝ, 0 < δ → (∀ i j, δ ≤ |hL.eigenvalues i-hM.eigenvalues j|) →
      δ*frobNorm X ≤ frobNorm (L*X-X*M)) ∧
    (∀ a b δ : ℝ, 0 < δ →
      (∀ j, a ≤ hM.eigenvalues j ∧ hM.eigenvalues j ≤ b) →
      (∀ i, hL.eigenvalues i ≤ a-δ ∨ b+δ ≤ hL.eigenvalues i) →
      δ*specNorm X ≤ specNorm (L*X-X*M) ∧ δ*frobNorm X ≤ frobNorm (L*X-X*M)) ∧
    (∀ α δ : ℝ, 0 < δ → (∀ i, hL.eigenvalues i ≤ α-δ) →
      (∀ j, α ≤ hM.eigenvalues j) → δ*specNorm X ≤ specNorm (L*X-X*M)) := by
  refine ⟨fun δ hδ hsep => mul_frobNorm_le_frobNorm_sylvester hL hM hδ hsep X, ?_, ?_⟩
  · intro a b δ hδ hint hout
    exact ⟨mul_specNorm_le_specNorm_sylvester_of_interval hL hM hδ hint hout X,
      mul_frobNorm_le_frobNorm_sylvester hL hM hδ
        (eigenvalue_separation_of_interval_complement hL hM hint hout) X⟩
  · intro α δ hδ hmax hmin
    exact mul_specNorm_le_specNorm_sylvester_of_one_sided hL hM hδ hmax hmin X

end NLAlib
