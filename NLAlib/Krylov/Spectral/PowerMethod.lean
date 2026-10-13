import NLAlib.Krylov.Spectral.Ritz
import NLAlib.Krylov.Spaces.Block
import NLAlib.Matrix.Subspaces.PrincipalAngles
/-!
# Power iteration and inverse iteration

The power method is the `s = 1` case of subspace iteration (`subspaceIterate`): the iterate is
the direction of `A^k x₀`, and normalisation is bookkeeping.

* `NLAlib.powerIterate A x₀ k = A^k x₀` (unnormalised; `powerIterate_succ`,
  `powerIterate_mem_krylovSpace`, `span_powerIterate_eq_subspaceIterate`);
  `NLAlib.powerStep A x = A x/‖A x‖` is the textbook normalised step and
  `powerStep_iterate_succ` says that `k + 1` normalised steps give `A^{k+1} x₀/‖A^{k+1} x₀‖`;
  angles and Rayleigh quotients are scale invariant (`tanSqAngle_smul`,
  `rayleighQuotient_smul`), so every statement transfers.
* `NLAlib.rayleighQuotient A x = xᵀAx/xᵀx`.
* **Angle bound** (`tanSqAngle_powerIterate_le`): for symmetric `A`, an eigenpair
  `(λ₁, u₁) = (λ_{i₁}, u_{i₁})` and `|λᵢ| ≤ ρ` for `i ≠ i₁`,
  `tan² ∠(u₁, A^k x₀) ≤ (ρ/|λ₁|)^{2k} tan² ∠(u₁, x₀)` (the `p = X^k` case of
  `tanSqAngle_aeval_mulVec_le`); the normalised form `tanSqAngle_powerStep_iterate_le`.
* **Rayleigh quotient** (`abs_rayleighQuotient_sub_le_mul_tanSqAngle`):
  `|ρ(x) − λ₁| ≤ D tan² ∠(u₁, x)` whenever `|λᵢ − λ₁| ≤ D` for all `i`, so the Rayleigh quotient
  of the power iterates converges at the squared rate (`abs_rayleighQuotient_powerIterate_sub_le`).
  For the top eigenvalue the one-sided form with `D = λ₁ − λ_min` is Ritz.lean's
  `eigenvalues_sub_eigenvalues_le_mul_tanSqAngle` (Rayleigh–Ritz on a one-column `Q`).
* **Inverse iteration** (`inverseIterate A μ x₀ k = (A − μI)^{-k} x₀`, power iteration on the
  resolvent): `tan² ∠(u_J, x_k) ≤ (|λ_J − μ|/d)^{2k} tan² ∠(u_J, x₀)` when every other
  eigenvalue is at distance `≥ d > 0` from `μ` (`tanSqAngle_inverseIterate_le`), with the
  Rayleigh-quotient corollary. The resolvent shares the eigenvectors of `A`
  (`eigenvectorBasis_dotProduct_inv_sub_mulVec`).

Source: Trefethen–Bau (1997) [`tb97`], Thm 27.1 (power iteration), Thm 27.2 (inverse iteration);
Golub–Van Loan (2013) [`gvl13`], Thm 8.2.1, §8.2.2; Saad (2011) [`saad11`], §4.1.
Atlas: `power-iteration`, `inverse-iteration`.
-/

noncomputable section

open scoped Matrix
open Matrix Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The iterates -/

/-- The `k`-th (unnormalised) power iterate `A^k x₀`. Normalisation does not change its
direction (`powerStep_iterate_succ`). Source: Trefethen–Bau (1997) [`tb97`], Alg. 27.1 (Lect.
27); Golub–Van Loan (2013) [`gvl13`], §8.2.1. Helper for `power-iteration`. -/
def powerIterate (A : Matrix n n ℝ) (x₀ : n → ℝ) (k : ℕ) : n → ℝ := (A ^ k) *ᵥ x₀

/-- `x_0 = x₀`. Helper for `power-iteration`. -/
@[simp]
theorem powerIterate_zero (A : Matrix n n ℝ) (x₀ : n → ℝ) : powerIterate A x₀ 0 = x₀ := by
  simp [powerIterate]

/-- One power step: `x_{k+1} = A x_k`. Source: Trefethen–Bau (1997) [`tb97`], Alg. 27.1.
Helper for `power-iteration`. -/
theorem powerIterate_succ (A : Matrix n n ℝ) (x₀ : n → ℝ) (k : ℕ) :
    powerIterate A x₀ (k + 1) = A *ᵥ powerIterate A x₀ k := by
  rw [powerIterate, powerIterate, pow_succ', ← Matrix.mulVec_mulVec]

/-- `A^k x₀ ∈ K_{k+1}(A, x₀)`. Source: Saad (2011) [`saad11`], §4.1 and §6.1. Helper for
`power-iteration`. -/
theorem powerIterate_mem_krylovSpace (A : Matrix n n ℝ) (x₀ : n → ℝ) (k : ℕ) :
    powerIterate A x₀ k ∈ krylovSpace A x₀ (k + 1) :=
  pow_mulVec_mem_krylovSpace A x₀ (Nat.lt_succ_self k)

/-- Power iteration is subspace iteration with one column: `span {A^k x₀} = S_k(A, x₀)`.
Source: Saad (2011) [`saad11`], §5.1. Helper for `power-iteration`. -/
theorem span_powerIterate_eq_subspaceIterate (A : Matrix n n ℝ) (x₀ : n → ℝ) (k : ℕ) :
    ℝ ∙ powerIterate A x₀ k = subspaceIterate A (Matrix.replicateCol Unit x₀) k := by
  rw [subspaceIterate, Matrix.range_mulVecLin]
  have h : Set.range (A ^ k * Matrix.replicateCol Unit x₀).col = {powerIterate A x₀ k} := by
    rw [Set.range_unique, col_mul_eq_mulVec_col]
    rfl
  rw [h]

/-- The normalised power step `x ↦ A x/‖A x‖` (junk value `0` when `A x = 0`). Source:
Trefethen–Bau (1997) [`tb97`], Alg. 27.1. Helper for `power-iteration`. -/
def powerStep (A : Matrix n n ℝ) (x : n → ℝ) : n → ℝ :=
  (√((A *ᵥ x) ⬝ᵥ (A *ᵥ x)))⁻¹ • (A *ᵥ x)

omit [Fintype n] [DecidableEq n] in
/-- Scaling does not change an angle: `tan² ∠(u, c x) = tan² ∠(u, x)` for `c ≠ 0`. Helper for
`power-iteration`. -/
theorem tanSqAngle_smul [Fintype n] (u x : n → ℝ) {c : ℝ} (hc : c ≠ 0) :
    tanSqAngle u (c • x) = tanSqAngle u x := by
  simp only [tanSqAngle, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  by_cases hx : u ⬝ᵥ x = 0
  · simp [hx]
  · field_simp

omit [DecidableEq n] in
/-- Scaling does not change the Rayleigh quotient: `ρ(c x) = ρ(x)` for `c ≠ 0`. Helper for
`power-iteration`. -/
theorem rayleighQuotient_smul (A : Matrix n n ℝ) (x : n → ℝ) {c : ℝ} (hc : c ≠ 0) :
    rayleighQuotient A (c • x) = rayleighQuotient A x := by
  simp only [rayleighQuotient_def, RCLike.re_to_real, quadForm_def, star_trivial,
    Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  by_cases hx : x ⬝ᵥ x = 0
  · simp [hx]
  · field_simp

omit [DecidableEq n] in
/-- Normalising a positive multiple: `c w/‖c w‖ = w/‖w‖` for `c > 0`. Helper for
`power-iteration`. -/
theorem inv_sqrt_smul_smul (w : n → ℝ) {c : ℝ} (hc : 0 < c) :
    (√((c • w) ⬝ᵥ (c • w)))⁻¹ • (c • w) = (√(w ⬝ᵥ w))⁻¹ • w := by
  rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    Real.sqrt_mul (by positivity) (w ⬝ᵥ w), Real.sqrt_mul_self hc.le, smul_smul, mul_inv,
    mul_comm c⁻¹ (√(w ⬝ᵥ w))⁻¹, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

/-- Normalisation is bookkeeping: `k + 1` normalised power steps from `x₀` give
`A^{k+1} x₀/‖A^{k+1} x₀‖` (both sides `0` if `A^{k+1} x₀ = 0`). Source: Trefethen–Bau (1997)
[`tb97`], Lect. 27. Helper for `power-iteration`. -/
theorem powerStep_iterate_succ (A : Matrix n n ℝ) (x₀ : n → ℝ) (k : ℕ) :
    (powerStep A)^[k + 1] x₀ =
      (√(powerIterate A x₀ (k + 1) ⬝ᵥ powerIterate A x₀ (k + 1)))⁻¹ •
        powerIterate A x₀ (k + 1) := by
  induction k with
  | zero => simp [powerStep, powerIterate]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    set v := powerIterate A x₀ (k + 1)
    have hv : powerIterate A x₀ (k + 1 + 1) = A *ᵥ v := powerIterate_succ A x₀ (k + 1)
    rw [hv, powerStep, Matrix.mulVec_smul]
    set c := (√(v ⬝ᵥ v))⁻¹
    by_cases hc : c = 0
    · have hv0 : v ⬝ᵥ v = 0 := by
        have h1 : √(v ⬝ᵥ v) = 0 := inv_eq_zero.1 hc
        have h2 := Real.sqrt_eq_zero'.1 h1
        exact le_antisymm h2 (dotProduct_self_nonneg v)
      have : v = 0 := dotProduct_self_eq_zero.1 hv0
      simp [this]
    · exact inv_sqrt_smul_smul _ (lt_of_le_of_ne (inv_nonneg.2 (Real.sqrt_nonneg _)) (Ne.symm hc))

/-! ### A spectral multiplier lemma -/

/-- **Angle contraction under a spectral multiplier.** If `w` has eigen-coordinates
`uᵢ ⬝ w = fᵢ (uᵢ ⬝ v)` (e.g. `w = p(A) v`, `w = (A − μI)⁻¹ v`) and `|fᵢ| ≤ M` for `i ≠ i₁`,
then `tan² ∠(u_{i₁}, w) ≤ (M/f_{i₁})² tan² ∠(u_{i₁}, v)`. The polynomial case is Ritz.lean's
`tanSqAngle_aeval_mulVec_le`. Source: Trefethen–Bau (1997) [`tb97`], proof of Thm 27.1. Helper
for `power-iteration`, `inverse-iteration`. -/
theorem tanSqAngle_le_of_dotProduct_eq_mul {A : Matrix n n ℝ} (hA : A.IsHermitian) (i₁ : n)
    {v w : n → ℝ} {f : n → ℝ}
    (hf : ∀ i, (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ w = f i * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v))
    {M : ℝ} (hM : ∀ i, i ≠ i₁ → |f i| ≤ M) :
    tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) w ≤
      (M / f i₁) ^ 2 * tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) v := by
  set c : n → ℝ := fun i => (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v with hc
  rw [tanSqAngle_eigenvectorBasis_eq, tanSqAngle_eigenvectorBasis_eq]
  simp only [hf]
  set N := ∑ i ∈ Finset.univ.erase i₁, c i ^ 2
  have hN : ∑ i ∈ Finset.univ.erase i₁, (f i * c i) ^ 2 ≤ M ^ 2 * N := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have h := hM i (Finset.ne_of_mem_erase hi)
    have hsq : f i ^ 2 ≤ M ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le (f i)]) ((le_abs_self _).trans h)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  rw [show (M / f i₁) ^ 2 * (N / c i₁ ^ 2) = M ^ 2 * N / (f i₁ * c i₁) ^ 2 by ring]
  exact div_le_div_of_nonneg_right hN (sq_nonneg _)

/-- Eigen-coordinates of powers of a spectral multiplier: if `uᵢ ⬝ (B y) = fᵢ (uᵢ ⬝ y)` for all
`y`, then `uᵢ ⬝ (B^k v) = fᵢ^k (uᵢ ⬝ v)`. Helper for `power-iteration`, `inverse-iteration`. -/
theorem dotProduct_pow_mulVec_eq {A B : Matrix n n ℝ} (hA : A.IsHermitian) {f : n → ℝ}
    (hB : ∀ i y, (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ (B *ᵥ y) =
      f i * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ y)) (k : ℕ) (v : n → ℝ) (i : n) :
    (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ ((B ^ k) *ᵥ v) =
      f i ^ k * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, hB, ih, pow_succ']; ring

/-! ### Power iteration -/

/-- **Power iteration, angle bound.** Let `A` be real symmetric with eigenpair
`(λ₁, u₁) = (λ_{i₁}, u_{i₁})` and `|λᵢ| ≤ ρ` for every `i ≠ i₁`. Then
`tan² ∠(u₁, A^k x₀) ≤ (ρ/|λ₁|)^{2k} tan² ∠(u₁, x₀)`. No hypothesis on `x₀` or on the gap is
needed for the inequality (a right angle has the junk value `0` on both sides); it is
informative when `ρ < |λ₁|` and `u₁ ⬝ x₀ ≠ 0`. Source: Trefethen–Bau (1997) [`tb97`], Thm 27.1;
Golub–Van Loan (2013) [`gvl13`], Thm 8.2.1. Deviations: squared tangents; `ρ` any bound on the
other eigenvalues (T&B: `ρ = |λ₂|`); unnormalised iterates (`tanSqAngle_powerStep_iterate_le`
for the normalised ones).
atlas: power-iteration -/
theorem tanSqAngle_powerIterate_le {A : Matrix n n ℝ} (hA : A.IsHermitian) (i₁ : n) {ρ : ℝ}
    (hρ : ∀ i, i ≠ i₁ → |hA.eigenvalues i| ≤ ρ) (x₀ : n → ℝ) (k : ℕ) :
    tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) (powerIterate A x₀ k) ≤
      (ρ / |hA.eigenvalues i₁|) ^ (2 * k) * tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) x₀ := by
  have hM : ∀ i, i ≠ i₁ → |(X ^ k : ℝ[X]).eval (hA.eigenvalues i)| ≤ ρ ^ k := fun i hi => by
    rw [eval_pow, eval_X, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hρ i hi) k
  have h := tanSqAngle_aeval_mulVec_le hA i₁ hM x₀
  rw [aeval_X_pow, eval_pow, eval_X] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [← div_pow, ← pow_mul, mul_comm k 2, pow_mul, pow_mul, div_pow, div_pow ρ, sq_abs]

/-- **Power iteration, normalised iterates.** Under the hypotheses of
`tanSqAngle_powerIterate_le`, the textbook iterates `x_k = (powerStep A)^[k] x₀` (normalised at
every step) satisfy `tan² ∠(u₁, x_k) ≤ (ρ/|λ₁|)^{2k} tan² ∠(u₁, x₀)`. Source: Trefethen–Bau
(1997) [`tb97`], Thm 27.1.
atlas: power-iteration -/
theorem tanSqAngle_powerStep_iterate_le {A : Matrix n n ℝ} (hA : A.IsHermitian) (i₁ : n)
    {ρ : ℝ} (hρ : ∀ i, i ≠ i₁ → |hA.eigenvalues i| ≤ ρ) (x₀ : n → ℝ) (k : ℕ) :
    tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) ((powerStep A)^[k] x₀) ≤
      (ρ / |hA.eigenvalues i₁|) ^ (2 * k) * tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) x₀ := by
  cases k with
  | zero => simp
  | succ k =>
    rw [powerStep_iterate_succ]
    set v := powerIterate A x₀ (k + 1)
    by_cases hc : (√(v ⬝ᵥ v))⁻¹ = 0
    · rw [hc, zero_smul]
      have h0 : tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) 0 = 0 := by simp [tanSqAngle]
      rw [h0]
      exact mul_nonneg ((even_two_mul _).pow_nonneg _)
        (tanSqAngle_eigenvectorBasis_nonneg hA i₁ x₀)
    · rw [tanSqAngle_smul _ _ hc]
      exact tanSqAngle_powerIterate_le hA i₁ hρ x₀ (k + 1)

/-- **Rayleigh quotient error from the angle.** For real symmetric `A`, an eigenpair
`(λ₁, u₁) = (λ_{i₁}, u_{i₁})`, `D` with `|λᵢ − λ₁| ≤ D` for every `i` (e.g. `D = λ_max − λ_min`),
and `x` with `u₁ ⬝ x ≠ 0`: `|ρ(x) − λ₁| ≤ D tan² ∠(u₁, x)`. Proof: in eigen-coordinates
`cᵢ = uᵢ ⬝ x`, `ρ(x) − λ₁ = ∑_{i ≠ i₁} (λᵢ − λ₁) cᵢ²/‖x‖²` and `‖x‖² ≥ c_{i₁}²`. Source:
Trefethen–Bau (1997) [`tb97`], Thm 27.1 (second bound) and Lect. 27 (`ρ(x) − λ = O(‖x − u‖²)`);
Saad (2011) [`saad11`], §4.1. Deviation: explicit constant `D` instead of `O(·)`; two-sided.
atlas: power-iteration -/
theorem abs_rayleighQuotient_sub_le_mul_tanSqAngle {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (i₁ : n) {D : ℝ} (hD : ∀ i, |hA.eigenvalues i - hA.eigenvalues i₁| ≤ D) {x : n → ℝ}
    (hx : (hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ x ≠ 0) :
    |rayleighQuotient A x - hA.eigenvalues i₁| ≤
      D * tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) x := by
  set c : n → ℝ := fun i => (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ x with hc
  set L := hA.eigenvalues i₁
  set N := ∑ i ∈ Finset.univ.erase i₁, c i ^ 2
  have hxx : x ⬝ᵥ x = c i₁ ^ 2 + N := by
    rw [← sum_sq_eigenvectorBasis_dotProduct hA x,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i₁)]
  have hdiff : quadForm A x - L * (x ⬝ᵥ x) =
      ∑ i ∈ Finset.univ.erase i₁, (hA.eigenvalues i - L) * c i ^ 2 := by
    rw [quadForm_eq_sum_eigenvalues hA x, ← sum_sq_eigenvectorBasis_dotProduct hA x,
      Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₁)]
    simp only [L, sub_self, zero_add, hc]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hbound : |∑ i ∈ Finset.univ.erase i₁, (hA.eigenvalues i - L) * c i ^ 2| ≤ D * N := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg (c i))]
    exact mul_le_mul_of_nonneg_right (hD i) (sq_nonneg _)
  have hc1 : 0 < c i₁ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx))
  have hN : 0 ≤ N := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD i₁)
  have hpos : 0 < x ⬝ᵥ x := by rw [hxx]; exact add_pos_of_pos_of_nonneg hc1 hN
  have hq : rayleighQuotient A x - L = (quadForm A x - L * (x ⬝ᵥ x)) / (x ⬝ᵥ x) := by
    rw [rayleighQuotient_def, RCLike.re_to_real, RCLike.re_to_real, star_trivial, sub_div,
      mul_div_assoc, div_self hpos.ne', mul_one]
  rw [tanSqAngle_eigenvectorBasis_eq, hq, hdiff, abs_div, abs_of_pos hpos]
  calc _ ≤ D * N / (x ⬝ᵥ x) := div_le_div_of_nonneg_right hbound hpos.le
    _ ≤ D * N / c i₁ ^ 2 :=
        div_le_div_of_nonneg_left (mul_nonneg hD0 hN) hc1 (by rw [hxx]; linarith)
    _ = D * (N / c i₁ ^ 2) := mul_div_assoc _ _ _

/-- **Power iteration, Rayleigh quotient.** For real symmetric `A` with eigenpair
`(λ₁, u₁)`, `λ₁ ≠ 0`, `|λᵢ| ≤ ρ` for `i ≠ i₁`, `|λᵢ − λ₁| ≤ D` for all `i`, and
`u₁ ⬝ x₀ ≠ 0`: `|ρ(A^k x₀) − λ₁| ≤ D (ρ/|λ₁|)^{2k} tan² ∠(u₁, x₀)`, the squared rate of the
angle. Source: Trefethen–Bau (1997) [`tb97`], Thm 27.1; Golub–Van Loan (2013) [`gvl13`],
Thm 8.2.1. Deviation: explicit constant `D` (T&B: `O(|λ₂/λ₁|^{2k})`).
atlas: power-iteration -/
theorem abs_rayleighQuotient_powerIterate_sub_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (i₁ : n) (hl : hA.eigenvalues i₁ ≠ 0) {ρ D : ℝ}
    (hρ : ∀ i, i ≠ i₁ → |hA.eigenvalues i| ≤ ρ)
    (hD : ∀ i, |hA.eigenvalues i - hA.eigenvalues i₁| ≤ D) {x₀ : n → ℝ}
    (hx₀ : (hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ x₀ ≠ 0) (k : ℕ) :
    |rayleighQuotient A (powerIterate A x₀ k) - hA.eigenvalues i₁| ≤
      D * ((ρ / |hA.eigenvalues i₁|) ^ (2 * k) *
        tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) x₀) := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD i₁)
  have hxk : (hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ powerIterate A x₀ k ≠ 0 := by
    have h := eigenvectorBasis_dotProduct_aeval_mulVec hA (X ^ k) x₀ i₁
    rw [aeval_X_pow, eval_pow, eval_X] at h
    rw [powerIterate, h]
    exact mul_ne_zero (pow_ne_zero _ hl) hx₀
  exact (abs_rayleighQuotient_sub_le_mul_tanSqAngle hA i₁ hD hxk).trans
    (mul_le_mul_of_nonneg_left (tanSqAngle_powerIterate_le hA i₁ hρ x₀ k) hD0)

/-! ### Inverse iteration -/

/-- The `k`-th (unnormalised) inverse-iteration iterate with shift `μ`: power iteration on the
resolvent, `(A − μI)^{-k} x₀`. Junk (Mathlib's inverse `0`) when `μ` is an eigenvalue.
Source: Trefethen–Bau (1997) [`tb97`], Alg. 27.2; Golub–Van Loan (2013) [`gvl13`], §8.2.2.
Helper for `inverse-iteration`. -/
def inverseIterate (A : Matrix n n ℝ) (μ : ℝ) (x₀ : n → ℝ) (k : ℕ) : n → ℝ :=
  powerIterate (A - μ • (1 : Matrix n n ℝ))⁻¹ x₀ k

/-- The shifted matrix in eigen-coordinates: `uᵢ ⬝ ((A − μI) y) = (λᵢ − μ)(uᵢ ⬝ y)`. Helper for
`inverse-iteration`. -/
theorem eigenvectorBasis_dotProduct_sub_smul_mulVec {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (μ : ℝ) (y : n → ℝ) (i : n) :
    (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ ((A - μ • (1 : Matrix n n ℝ)) *ᵥ y) =
      (hA.eigenvalues i - μ) * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ y) := by
  have h := eigenvectorBasis_dotProduct_aeval_mulVec hA (X - C μ) y i
  simpa [Algebra.algebraMap_eq_smul_one] using h

/-- The resolvent shares the eigenvectors of `A`: if `μ` is not an eigenvalue,
`uᵢ ⬝ ((A − μI)⁻¹ v) = (λᵢ − μ)⁻¹ (uᵢ ⬝ v)`. Source: Trefethen–Bau (1997) [`tb97`], Lect. 27.
Helper for `inverse-iteration`. -/
theorem eigenvectorBasis_dotProduct_inv_sub_mulVec {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {μ : ℝ} (hμ : ∀ i, hA.eigenvalues i ≠ μ) (v : n → ℝ) (i : n) :
    (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ ((A - μ • (1 : Matrix n n ℝ))⁻¹ *ᵥ v) =
      (hA.eigenvalues i - μ)⁻¹ * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v) := by
  set B := A - μ • (1 : Matrix n n ℝ)
  have hker : ∀ y, B *ᵥ y = 0 → y = 0 := fun y hy => by
    have hc : ∀ j, (hA.eigenvectorBasis j : n → ℝ) ⬝ᵥ y = 0 := fun j => by
      have h := eigenvectorBasis_dotProduct_sub_smul_mulVec hA μ y j
      rw [show B *ᵥ y = 0 from hy, dotProduct_zero] at h
      exact (mul_eq_zero.1 h.symm).resolve_left (sub_ne_zero.2 (hμ j))
    have hyy := sum_sq_eigenvectorBasis_dotProduct hA y
    simp only [hc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero] at hyy
    exact dotProduct_self_eq_zero.1 hyy.symm
  have hinj : Function.Injective B.mulVec := fun y z h =>
    sub_eq_zero.1 (hker _ (by rw [Matrix.mulVec_sub, h, sub_self]))
  have hB : IsUnit B := Matrix.mulVec_injective_iff_isUnit.1 hinj
  have hBB : B *ᵥ (B⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).1 hB),
      Matrix.one_mulVec]
  have h := eigenvectorBasis_dotProduct_sub_smul_mulVec hA μ (B⁻¹ *ᵥ v) i
  rw [hBB] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.2 (hμ i)), one_mul]

/-- **Inverse iteration, angle bound.** Let `A` be real symmetric, `μ` not an eigenvalue,
`J` an index and `d > 0` with `|λᵢ − μ| ≥ d` for every `i ≠ J` (`λ_J` closest to `μ`, `d` the
distance of the second closest, T&B's `|μ − λ_K|`). Then the inverse-iteration iterates
satisfy `tan² ∠(u_J, (A − μI)^{-k} x₀) ≤ (|λ_J − μ|/d)^{2k} tan² ∠(u_J, x₀)`. Source:
Trefethen–Bau (1997) [`tb97`], Thm 27.2; Golub–Van Loan (2013) [`gvl13`], §8.2.2.
Deviations: squared tangents; unnormalised iterates (normalisation is bookkeeping,
`tanSqAngle_smul`).
atlas: inverse-iteration -/
theorem tanSqAngle_inverseIterate_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {μ : ℝ}
    (hμ : ∀ i, hA.eigenvalues i ≠ μ) (J : n) {d : ℝ} (hd : 0 < d)
    (hdJ : ∀ i, i ≠ J → d ≤ |hA.eigenvalues i - μ|) (x₀ : n → ℝ) (k : ℕ) :
    tanSqAngle (hA.eigenvectorBasis J : n → ℝ) (inverseIterate A μ x₀ k) ≤
      (|hA.eigenvalues J - μ| / d) ^ (2 * k) *
        tanSqAngle (hA.eigenvectorBasis J : n → ℝ) x₀ := by
  have hf := dotProduct_pow_mulVec_eq hA (B := (A - μ • (1 : Matrix n n ℝ))⁻¹)
    (f := fun i => (hA.eigenvalues i - μ)⁻¹)
    (fun i y => eigenvectorBasis_dotProduct_inv_sub_mulVec hA hμ y i) k
  have hM : ∀ i, i ≠ J → |(hA.eigenvalues i - μ)⁻¹ ^ k| ≤ d⁻¹ ^ k := fun i hi => by
    rw [abs_pow, abs_inv]
    exact pow_le_pow_left₀ (inv_nonneg.2 (abs_nonneg _))
      (inv_anti₀ hd (hdJ i hi)) k
  have h := tanSqAngle_le_of_dotProduct_eq_mul hA J (fun i => hf x₀ i) hM
  refine h.trans (le_of_eq ?_)
  congr 1
  have hJ : hA.eigenvalues J - μ ≠ 0 := sub_ne_zero.2 (hμ J)
  rw [← div_pow, ← pow_mul, mul_comm k 2, pow_mul, pow_mul, div_pow, div_pow |_|, sq_abs]
  congr 1
  field_simp

/-- **Inverse iteration, Rayleigh quotient.** Under the hypotheses of
`tanSqAngle_inverseIterate_le`, with `|λᵢ − λ_J| ≤ D` for all `i` and `u_J ⬝ x₀ ≠ 0`:
`|ρ(x_k) − λ_J| ≤ D (|λ_J − μ|/d)^{2k} tan² ∠(u_J, x₀)`. Source: Trefethen–Bau (1997) [`tb97`],
Thm 27.2 (second bound).
atlas: inverse-iteration -/
theorem abs_rayleighQuotient_inverseIterate_sub_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {μ : ℝ} (hμ : ∀ i, hA.eigenvalues i ≠ μ) (J : n) {d D : ℝ} (hd : 0 < d)
    (hdJ : ∀ i, i ≠ J → d ≤ |hA.eigenvalues i - μ|)
    (hD : ∀ i, |hA.eigenvalues i - hA.eigenvalues J| ≤ D) {x₀ : n → ℝ}
    (hx₀ : (hA.eigenvectorBasis J : n → ℝ) ⬝ᵥ x₀ ≠ 0) (k : ℕ) :
    |rayleighQuotient A (inverseIterate A μ x₀ k) - hA.eigenvalues J| ≤
      D * ((|hA.eigenvalues J - μ| / d) ^ (2 * k) *
        tanSqAngle (hA.eigenvectorBasis J : n → ℝ) x₀) := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD J)
  have hxk : (hA.eigenvectorBasis J : n → ℝ) ⬝ᵥ inverseIterate A μ x₀ k ≠ 0 := by
    rw [inverseIterate, powerIterate, dotProduct_pow_mulVec_eq hA
      (fun i y => eigenvectorBasis_dotProduct_inv_sub_mulVec hA hμ y i) k x₀ J]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (sub_ne_zero.2 (hμ J)))) hx₀
  exact (abs_rayleighQuotient_sub_le_mul_tanSqAngle hA J hD hxk).trans
    (mul_le_mul_of_nonneg_left (tanSqAngle_inverseIterate_le hA hμ J hd hdJ x₀ k) hD0)

/-! ### Bridge to principal angles -/

/-- SCAFFOLD: principal-angles-def
**`tanSqAngle` is the one-column `tan² θ_max`.** For a unit vector `u` (`u ⬝ u = 1`) and any
`x`, `tan θ_max(range u, range x)² = tan² ∠(u, x)`, both sides `0` when `u ⬝ x = 0`. Source:
Saad (2011) [`saad11`], §5.2 and §6.6.1. Proof sketch: `uᵀx` is the `1 × 1` matrix `(u ⬝ x)`, its
inverse is `(u ⬝ x)⁻¹`; `(I − uuᵀ)x (u ⬝ x)⁻¹` is a single column whose spectral norm is its
Euclidean norm (`specNorm` of an `n × 1` matrix: `‖M‖² = ‖MᵀM‖` = the `1 × 1` entry,
`Matrix.l2_opNorm_conjTranspose_mul_self`), and `‖(I − uuᵀ)x‖² = ‖x‖² − (u ⬝ x)²`.
atlas: principal-angles-def (partial) -/
theorem sq_tanThetaMax_replicateCol_eq_tanSqAngle {u : n → ℝ} (hu : u ⬝ᵥ u = 1) (x : n → ℝ) :
    tanThetaMax (Matrix.replicateCol Unit u) (Matrix.replicateCol Unit x) ^ 2 =
      tanSqAngle u x := by
  sorry

end NLAlib
