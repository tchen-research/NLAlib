import NLAlib.Matrix.GramSoftMin

/-!
# Spectral-coordinate formula for the Gram resolvent Laplacian

The inverse regularized Gram eigenbasis diagonalizes the original Gram
matrix as well. Trace powers therefore reduce the finite resolvent
Laplacian to scalar eigenvalue sums, suitable for its hard-edge limit.

Atlas: `wishart-lambda-min-tail` (operator calculus helpers).
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace NLAlib

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

private lemma sum_power_products_eq_diag_add_offDiag (b l : ι → ℝ) (n : ℕ) :
    (∑ a ∈ Finset.range (n + 1),
      ((∑ i, b i ^ (n - a + 1)) * (∑ i, l i * b i ^ (a + 1)) +
        (∑ i, b i ^ (a + 1)) * (∑ i, l i * b i ^ (n - a + 1)))) =
      2 * ((n : ℝ) + 1) * (∑ i, l i * b i ^ (n + 2)) +
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          (l i + l j) * ∑ a ∈ Finset.range (n + 1), b i ^ (n - a + 1) * b j ^ (a + 1) := by
  have hpair (a : ℕ) :
      (∑ i, b i ^ (n - a + 1)) * (∑ i, l i * b i ^ (a + 1)) +
        (∑ i, b i ^ (a + 1)) * (∑ i, l i * b i ^ (n - a + 1)) =
      ∑ i, ∑ j, (l i + l j) * b i ^ (n - a + 1) * b j ^ (a + 1) := by
    have h1 : (∑ i, b i ^ (n - a + 1)) * (∑ i, l i * b i ^ (a + 1)) =
        ∑ i, ∑ j, l j * b i ^ (n - a + 1) * b j ^ (a + 1) := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _; ring
    have h2 : (∑ i, b i ^ (a + 1)) * (∑ i, l i * b i ^ (n - a + 1)) =
        ∑ i, ∑ j, l i * b i ^ (n - a + 1) * b j ^ (a + 1) := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _; ring
    rw [h1, h2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _; ring
  rw [show (∑ a ∈ Finset.range (n + 1),
      ((∑ i, b i ^ (n - a + 1)) * (∑ i, l i * b i ^ (a + 1)) +
        (∑ i, b i ^ (a + 1)) * (∑ i, l i * b i ^ (n - a + 1)))) =
      ∑ a ∈ Finset.range (n + 1), ∑ i, ∑ j,
        (l i + l j) * b i ^ (n - a + 1) * b j ^ (a + 1) by
    apply Finset.sum_congr rfl
    intro a _; exact hpair a]
  have hswap : (∑ a ∈ Finset.range (n + 1), ∑ i, ∑ j,
      (l i + l j) * b i ^ (n - a + 1) * b j ^ (a + 1)) =
      ∑ i, ∑ j, (l i + l j) *
        ∑ a ∈ Finset.range (n + 1), b i ^ (n - a + 1) * b j ^ (a + 1) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _; ring
  rw [hswap]
  have hdiag (i : ι) : (∑ a ∈ Finset.range (n + 1), b i ^ (n - a + 1) * b i ^ (a + 1)) =
      ((n : ℝ) + 1) * b i ^ (n + 2) := by
    have he : (∑ a ∈ Finset.range (n + 1), b i ^ (n - a + 1) * b i ^ (a + 1)) =
        ∑ _a ∈ Finset.range (n + 1), b i ^ (n + 2) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← pow_add]
      have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      congr 1; omega
    rw [he]
    simp
  have hsplit (i : ι) : (∑ j, (l i + l j) *
        ∑ a ∈ Finset.range (n + 1), b i ^ (n - a + 1) * b j ^ (a + 1)) =
      (l i + l i) * (((n : ℝ) + 1) * b i ^ (n + 2)) +
        ∑ j ∈ Finset.univ.erase i, (l i + l j) *
          ∑ a ∈ Finset.range (n + 1), b i ^ (n - a + 1) * b j ^ (a + 1) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hdiag]
    ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _; ring

omit [DecidableEq κ] in
/-- In the inverse regularized Gram eigenbasis, the unregularized Gram
eigenvalues are the reciprocal inverse eigenvalues minus the regularizer.
Source: simultaneous diagonalization by the inverse relation; atlas
`wishart-lambda-min-tail` (helper). -/
theorem regularizedGram_inv_basis_conj_eq (ε : ℝ) (G : Matrix ι κ ℝ)
    (hpd : (regularizedGram ε G).PosDef) :
    let hR := hpd.inv.isHermitian
    let b := hR.eigenvalues
    Unitary.conjStarAlgAut ℝ _ (star hR.eigenvectorUnitary) (G * Gᵀ) =
      Matrix.diagonal (fun i => (b i)⁻¹ - ε) := by
  dsimp only
  let W := regularizedGram ε G
  let R := W⁻¹
  let hR := hpd.inv.isHermitian
  let b := hR.eigenvalues
  let U := star hR.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  have hb : ∀ i, b i ≠ 0 := fun i => (hpd.inv.eigenvalues_pos i).ne'
  have hdiag : φ R = Matrix.diagonal b := by
    dsimp only [φ, U, R, W, hR, b]
    simpa using hpd.inv.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hleft : φ W * Matrix.diagonal b = 1 := by
    rw [← hdiag, ← map_mul]
    change φ (W * W⁻¹) = 1
    rw [Matrix.mul_nonsing_inv W (Matrix.isUnit_iff_isUnit_det W |>.mp hpd.isUnit), map_one]
  have hright : Matrix.diagonal (fun i => (b i)⁻¹) * Matrix.diagonal b = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have he : (fun i => (b i)⁻¹ * b i) = (fun _ : ι => (1 : ℝ)) := by
      funext i
      exact inv_mul_cancel₀ (hb i)
    rw [he, Matrix.diagonal_one]
  have hWdiag : φ W = Matrix.diagonal (fun i => (b i)⁻¹) :=
    Matrix.left_inv_eq_left_inv hleft hright
  have hW : G * Gᵀ = W - ε • (1 : Matrix ι ι ℝ) := by
    dsimp only [W, regularizedGram]
    module
  change φ (G * Gᵀ) = _
  rw [hW, map_sub, map_smul, map_one, hWdiag]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  rfl

omit [DecidableEq κ] in
/-- The resolvent gradient weight is diagonal in the inverse Gram
eigenbasis, with explicit scalar entries. Source: operator tail proof;
atlas `wishart-lambda-min-tail` (helper). -/
theorem regularizedGram_inv_basis_conj_weight_eq (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ)
    (hpd : (regularizedGram ε G).PosDef) :
    let hR := hpd.inv.isHermitian
    let b := hR.eigenvalues
    let T := ∑ i, b i ^ n
    Unitary.conjStarAlgAut ℝ _ (star hR.eigenvectorUnitary)
      (inversePowerSoftMinWeight n (regularizedGram ε G)) =
      Matrix.diagonal (fun i => T ^ (-(n : ℝ)⁻¹ - 1) * b i ^ (n + 1)) := by
  dsimp only
  let U := star hpd.inv.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  have hdiag : φ (regularizedGram ε G)⁻¹ = Matrix.diagonal hpd.inv.isHermitian.eigenvalues := by
    simpa [φ, U] using hpd.inv.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have htrace : Matrix.trace ((regularizedGram ε G)⁻¹ ^ n) =
      ∑ i, hpd.inv.isHermitian.eigenvalues i ^ n := by
    calc _ = Matrix.trace (φ ((regularizedGram ε G)⁻¹ ^ n)) :=
          (trace_conjStarAlgAut U _).symm
      _ = _ := by simp only [map_pow, hdiag, Matrix.diagonal_pow,
        Matrix.trace_diagonal, Pi.pow_apply]
  change φ (inversePowerSoftMinWeight n (regularizedGram ε G)) = _
  unfold inversePowerSoftMinWeight
  rw [map_smul, map_pow, hdiag, Matrix.diagonal_pow, htrace]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal, hij]

omit [DecidableEq κ] in
/-- The Euler contraction of the Gram gradient is twice the weighted
Gram-eigenvalue sum. Source: operator tail proof; atlas
`wishart-lambda-min-tail` (helper). -/
theorem frobInner_gramSoftMinGradient_eq_spectral (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ)
    (hpd : (regularizedGram ε G).PosDef) :
    let b := hpd.inv.isHermitian.eigenvalues
    let T := ∑ i, b i ^ n
    frobInner G (gramSoftMinGradient n ε G) =
      2 * ∑ i, ((b i)⁻¹ - ε) * (T ^ (-(n : ℝ)⁻¹ - 1) * b i ^ (n + 1)) := by
  dsimp only
  let U := star hpd.inv.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  have hG := regularizedGram_inv_basis_conj_eq ε G hpd
  have hP := regularizedGram_inv_basis_conj_weight_eq n ε G hpd
  have h := (trace_conjStarAlgAut U
    (inversePowerSoftMinWeight n (regularizedGram ε G) * (G * Gᵀ))).symm
  change _ = Matrix.trace (φ (_ * _)) at h
  rw [map_mul, hG, hP, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal] at h
  rw [frobInner_gramSoftMinGradient_eq_trace, h]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq κ] in
/-- The squared Gram gradient is four times the Gram-eigenvalue sum
weighted by squared resolvent weights. Source: operator tail proof;
atlas `wishart-lambda-min-tail` (helper). -/
theorem frobSq_gramSoftMinGradient_eq_spectral (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ)
    (hpd : (regularizedGram ε G).PosDef) :
    let b := hpd.inv.isHermitian.eigenvalues
    let T := ∑ i, b i ^ n
    frobSq (gramSoftMinGradient n ε G) =
      4 * ∑ i, ((b i)⁻¹ - ε) * (T ^ (-(n : ℝ)⁻¹ - 1) * b i ^ (n + 1)) ^ 2 := by
  dsimp only
  let U := star hpd.inv.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  have hG := regularizedGram_inv_basis_conj_eq ε G hpd
  have hP := regularizedGram_inv_basis_conj_weight_eq n ε G hpd
  have h := (trace_conjStarAlgAut U
    (inversePowerSoftMinWeight n (regularizedGram ε G) ^ 2 * (G * Gᵀ))).symm
  change _ = Matrix.trace (φ (_ * _)) at h
  rw [map_mul, map_pow, hG, hP, Matrix.diagonal_pow,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal] at h
  rw [frobSq_gramSoftMinGradient_eq_trace n ε G hpd, h]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.pow_apply]
  ring

/-- The Gram resolvent Laplacian is exactly a finite scalar expression
in the inverse eigenvalues and the corresponding Gram eigenvalues.
Source: spectral form of the operator tail proof; atlas
`wishart-lambda-min-tail` (helper). -/
theorem gramSoftMinLaplacian_eq_spectral (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ)
    (hpd : (regularizedGram ε G).PosDef) :
    let b := hpd.inv.isHermitian.eigenvalues
    let l := fun i => (b i)⁻¹ - ε
    let T := ∑ i, b i ^ n
    gramSoftMinLaplacian n ε G =
      2 * Fintype.card κ * T ^ (-(n : ℝ)⁻¹ - 1) * (∑ i, b i ^ (n + 1)) +
      4 * ((n : ℝ) + 1) * T ^ (-(n : ℝ)⁻¹ - 2) * (∑ i, l i * b i ^ (2 * n + 2)) -
      T ^ (-(n : ℝ)⁻¹ - 1) *
        ∑ a ∈ Finset.range (n + 1),
          (2 * (∑ i, l i * b i ^ (n + 2)) +
            (∑ i, b i ^ (n - a + 1)) * (∑ i, l i * b i ^ (a + 1)) +
            (∑ i, b i ^ (a + 1)) * (∑ i, l i * b i ^ (n - a + 1))) := by
  dsimp only
  let R := (regularizedGram ε G)⁻¹
  let hR := hpd.inv.isHermitian
  let b := hR.eigenvalues
  let U := star hR.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  have hdiag : φ R = Matrix.diagonal b := by
    dsimp only [φ, U, R, hR, b]
    simpa using hpd.inv.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hGdiag : φ (G * Gᵀ) = Matrix.diagonal (fun i => (b i)⁻¹ - ε) :=
    regularizedGram_inv_basis_conj_eq ε G hpd
  have htrace (m : ℕ) : Matrix.trace (R ^ m) = ∑ i, b i ^ m := by
    calc _ = Matrix.trace (φ (R ^ m)) := (trace_conjStarAlgAut U _).symm
      _ = _ := by simp only [map_pow, hdiag, Matrix.diagonal_pow, Matrix.trace_diagonal, Pi.pow_apply]
  have htraceG (m : ℕ) : Matrix.trace (R ^ m * (G * Gᵀ)) =
      ∑ i, ((b i)⁻¹ - ε) * b i ^ m := by
    calc _ = Matrix.trace (φ (R ^ m * (G * Gᵀ))) := (trace_conjStarAlgAut U _).symm
      _ = _ := by
          simp only [map_mul, map_pow, hdiag, hGdiag, Matrix.diagonal_pow,
            Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Pi.pow_apply]
          apply Finset.sum_congr rfl
          intro i _; ring
  have h := gramSoftMinLaplacian_eq n ε G hpd
  dsimp only at h
  unfold inversePowerSoftMinWeight at h
  rw [Matrix.trace_smul, smul_eq_mul] at h
  dsimp only [R] at htrace htraceG
  simp_rw [htrace, htraceG] at h
  simpa only [mul_assoc] using h

/-- The scalar spectral Laplacian separates the diagonal cancellation
from the off-diagonal geometric power kernel. Source: operator tail proof;
atlas `wishart-lambda-min-tail` (helper). -/
theorem gramSoftMinLaplacian_eq_spectral_offDiag (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ)
    (hpd : (regularizedGram ε G).PosDef) :
    let b := hpd.inv.isHermitian.eigenvalues
    let l := fun i => (b i)⁻¹ - ε
    let T := ∑ i, b i ^ n
    let c := T ^ (-(n : ℝ)⁻¹ - 1)
    gramSoftMinLaplacian n ε G =
      2 * Fintype.card κ * c * (∑ i, b i ^ (n + 1)) +
        4 * ((n : ℝ) + 1) *
          (T ^ (-(n : ℝ)⁻¹ - 2) * (∑ i, l i * b i ^ (2 * n + 2)) -
            c * (∑ i, l i * b i ^ (n + 2))) -
        c * ∑ i, ∑ j ∈ Finset.univ.erase i,
          (l i + l j) * ∑ a ∈ Finset.range (n + 1), b i ^ (n - a + 1) * b j ^ (a + 1) := by
  dsimp only
  rw [gramSoftMinLaplacian_eq_spectral n ε G hpd]
  simp only [add_assoc]
  rw [Finset.sum_add_distrib]
  rw [sum_power_products_eq_diag_add_offDiag]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- Factoring any positive reference inverse eigenvalue normalizes the
resolvent Gram Laplacian into power sums and a geometric kernel. Source:
operator tail proof; atlas `wishart-lambda-min-tail` (helper). -/
theorem gramSoftMinLaplacian_eq_normalized [Nonempty ι] (n : ℕ) (hn : 0 < n)
    (ε : ℝ) (G : Matrix ι κ ℝ) (hpd : (regularizedGram ε G).PosDef)
    (b₀ : ℝ) (hb₀ : 0 < b₀) :
    let b := hpd.inv.isHermitian.eigenvalues
    let ρ := fun i => b i / b₀
    let l := fun i => (b i)⁻¹ - ε
    let S := ∑ i, ρ i ^ n
    let c := S ^ (-(n : ℝ)⁻¹ - 1)
    gramSoftMinLaplacian n ε G =
      2 * Fintype.card κ * c * (∑ i, ρ i ^ (n + 1)) +
        4 * ((n : ℝ) + 1) * b₀ * c *
          ((∑ i, l i * ρ i ^ (2 * n + 2)) / S - (∑ i, l i * ρ i ^ (n + 2))) -
        b₀ * c * ∑ i, ∑ j ∈ Finset.univ.erase i,
          (l i + l j) * ∑ a ∈ Finset.range (n + 1), ρ i ^ (n - a + 1) * ρ j ^ (a + 1) := by
  dsimp only
  let b := hpd.inv.isHermitian.eigenvalues
  let ρ := fun i => b i / b₀
  let l := fun i => (b i)⁻¹ - ε
  let S := ∑ i, ρ i ^ n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hρ : ∀ i, 0 < ρ i := fun i => div_pos (hpd.inv.eigenvalues_pos i) hb₀
  have hS : 0 < S := Finset.sum_pos (fun i _ => pow_pos (hρ i) _) Finset.univ_nonempty
  have hbscale (i : ι) : b i = b₀ * ρ i := by dsimp only [ρ]; field_simp
  have hsum (m : ℕ) : (∑ i, b i ^ m) = b₀ ^ m * ∑ i, ρ i ^ m := by
    simp_rw [hbscale, mul_pow]
    rw [Finset.mul_sum]
  have hsuml (m : ℕ) : (∑ i, l i * b i ^ m) = b₀ ^ m * ∑ i, l i * ρ i ^ m := by
    simp_rw [hbscale, mul_pow]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  have hconv (i j : ι) :
      (∑ a ∈ Finset.range (n + 1), b i ^ (n - a + 1) * b j ^ (a + 1)) =
      b₀ ^ (n + 2) * ∑ a ∈ Finset.range (n + 1), ρ i ^ (n - a + 1) * ρ j ^ (a + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hbscale i, hbscale j, mul_pow, mul_pow]
    have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have he : n - a + 1 + (a + 1) = n + 2 := by omega
    calc _ = b₀ ^ (n - a + 1 + (a + 1)) *
          (ρ i ^ (n - a + 1) * ρ j ^ (a + 1)) := by rw [pow_add]; ring
      _ = _ := by rw [he]
  have hoff : (∑ i, ∑ j ∈ Finset.univ.erase i,
      (l i + l j) * ∑ a ∈ Finset.range (n + 1), b i ^ (n - a + 1) * b j ^ (a + 1)) =
      b₀ ^ (n + 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        (l i + l j) * ∑ a ∈ Finset.range (n + 1), ρ i ^ (n - a + 1) * ρ j ^ (a + 1) := by
    simp_rw [hconv]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _; ring
  have hpow (a : ℝ) : (∑ i, b i ^ n) ^ (-(n : ℝ)⁻¹ - a) =
      b₀ ^ (-1 - (n : ℝ) * a) * S ^ (-(n : ℝ)⁻¹ - a) := by
    rw [hsum, Real.mul_rpow (pow_nonneg hb₀.le _) hS.le,
      ← Real.rpow_natCast b₀ n, ← Real.rpow_mul hb₀.le]
    congr 2
    field_simp
  have hcancel1 : b₀ ^ (-1 - (n : ℝ)) * b₀ ^ (n + 1) = 1 := by
    rw [← Real.rpow_natCast b₀ (n + 1), ← Real.rpow_add hb₀]
    rw [show -1 - (n : ℝ) + ((n + 1 : ℕ) : ℝ) = 0 by push_cast; ring,
      Real.rpow_zero]
  have hcancel2 : b₀ ^ (-1 - (n : ℝ)) * b₀ ^ (n + 2) = b₀ := by
    rw [← Real.rpow_natCast b₀ (n + 2), ← Real.rpow_add hb₀]
    rw [show -1 - (n : ℝ) + ((n + 2 : ℕ) : ℝ) = 1 by push_cast; ring,
      Real.rpow_one]
  have hcancel3 : b₀ ^ (-1 - (n : ℝ) * 2) * b₀ ^ (2 * n + 2) = b₀ := by
    rw [← Real.rpow_natCast b₀ (2 * n + 2), ← Real.rpow_add hb₀]
    rw [show -1 - (n : ℝ) * 2 + ((2 * n + 2 : ℕ) : ℝ) = 1 by push_cast; ring,
      Real.rpow_one]
  have hSpow : S ^ (-(n : ℝ)⁻¹ - 2) = S ^ (-(n : ℝ)⁻¹ - 1) / S := by
    rw [show -(n : ℝ)⁻¹ - 2 = (-(n : ℝ)⁻¹ - 1) - 1 by ring,
      Real.rpow_sub_one hS.ne']
  have h := gramSoftMinLaplacian_eq_spectral_offDiag n ε G hpd
  dsimp only at h
  change gramSoftMinLaplacian n ε G =
    2 * Fintype.card κ * (∑ i, b i ^ n) ^ (-(n : ℝ)⁻¹ - 1) * (∑ i, b i ^ (n + 1)) +
      4 * ((n : ℝ) + 1) * ((∑ i, b i ^ n) ^ (-(n : ℝ)⁻¹ - 2) *
        (∑ i, l i * b i ^ (2 * n + 2)) - (∑ i, b i ^ n) ^ (-(n : ℝ)⁻¹ - 1) *
        (∑ i, l i * b i ^ (n + 2))) -
      (∑ i, b i ^ n) ^ (-(n : ℝ)⁻¹ - 1) *
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          (l i + l j) * ∑ a ∈ Finset.range (n + 1), b i ^ (n - a + 1) * b j ^ (a + 1) at h
  rw [hpow 1, hpow 2, hsum (n + 1), hsuml (2 * n + 2), hsuml (n + 2), hoff] at h
  simp only [mul_one] at h
  have hfirst : 2 * Fintype.card κ * (b₀ ^ (-1 - (n : ℝ)) * S ^ (-(n : ℝ)⁻¹ - 1)) *
      (b₀ ^ (n + 1) * ∑ i, ρ i ^ (n + 1)) =
      2 * Fintype.card κ * S ^ (-(n : ℝ)⁻¹ - 1) * ∑ i, ρ i ^ (n + 1) := by
    calc _ = 2 * Fintype.card κ * (b₀ ^ (-1 - (n : ℝ)) * b₀ ^ (n + 1)) *
          S ^ (-(n : ℝ)⁻¹ - 1) * ∑ i, ρ i ^ (n + 1) := by ring
      _ = _ := by rw [hcancel1]; ring
  rw [hfirst] at h
  have hmiddle : (b₀ ^ (-1 - (n : ℝ) * 2) * S ^ (-(n : ℝ)⁻¹ - 2)) *
        (b₀ ^ (2 * n + 2) * ∑ i, l i * ρ i ^ (2 * n + 2)) -
      (b₀ ^ (-1 - (n : ℝ)) * S ^ (-(n : ℝ)⁻¹ - 1)) *
        (b₀ ^ (n + 2) * ∑ i, l i * ρ i ^ (n + 2)) =
      b₀ * S ^ (-(n : ℝ)⁻¹ - 1) *
        ((∑ i, l i * ρ i ^ (2 * n + 2)) / S - (∑ i, l i * ρ i ^ (n + 2))) := by
    calc _ = (b₀ ^ (-1 - (n : ℝ) * 2) * b₀ ^ (2 * n + 2)) *
          S ^ (-(n : ℝ)⁻¹ - 2) * (∑ i, l i * ρ i ^ (2 * n + 2)) -
        (b₀ ^ (-1 - (n : ℝ)) * b₀ ^ (n + 2)) *
          S ^ (-(n : ℝ)⁻¹ - 1) * (∑ i, l i * ρ i ^ (n + 2)) := by ring
      _ = _ := by rw [hcancel2, hcancel3, hSpow]; ring
  rw [hmiddle] at h
  have hlast : (b₀ ^ (-1 - (n : ℝ)) * S ^ (-(n : ℝ)⁻¹ - 1)) *
      (b₀ ^ (n + 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        (l i + l j) * ∑ a ∈ Finset.range (n + 1), ρ i ^ (n - a + 1) * ρ j ^ (a + 1)) =
      b₀ * S ^ (-(n : ℝ)⁻¹ - 1) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        (l i + l j) * ∑ a ∈ Finset.range (n + 1), ρ i ^ (n - a + 1) * ρ j ^ (a + 1) := by
    calc _ = (b₀ ^ (-1 - (n : ℝ)) * b₀ ^ (n + 2)) * S ^ (-(n : ℝ)⁻¹ - 1) *
          ∑ i, ∑ j ∈ Finset.univ.erase i,
            (l i + l j) * ∑ a ∈ Finset.range (n + 1), ρ i ^ (n - a + 1) * ρ j ^ (a + 1) := by ring
      _ = _ := by rw [hcancel2]
  rw [hlast] at h
  simpa only [mul_assoc] using h

end NLAlib
