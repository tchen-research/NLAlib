import NLAlib.Matrix.Spectral.HaynsworthInertia

/-!
# Rank-one inertia via Haynsworth additivity

For a real symmetric invertible matrix `M`, the rank-one update `M + vecMulVec v v`
gains exactly one positive eigenvalue once the (unshifted) barrier interaction
`v ⬝ᵥ (M⁻¹ *ᵥ v) < -1` holds.  The certificate is a one-step spectral argument:
the bordered matrix `[[M, v], [vᵀ, -1]]` is eliminated once through its leading
block `M` (Haynsworth additivity, positive index) and once through its bottom
block `-1` (the symmetric bottom-block Schur complement added here), and the two
counts are compared.

The update matrix is `vecMulVec v v`, and `M` is intentionally allowed to be
indefinite; the only quantitative hypothesis is the strict barrier `q < -1`.

-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Symmetric block elimination from the bottom-right block is an exact congruence to
the direct sum of that block and its Schur complement.  This is the bottom-right
analogue of `fromBlocks_eq_transpose_mul_schur_mul`; Horn--Johnson (2013),
Exercise 4.5.P21. -/
private theorem fromBlocks_eq_mul_schur_mul_conjTranspose_bottom
    {A : Matrix m m ℝ} {C : Matrix n n ℝ}
    (B : Matrix m n ℝ) (hC : C.IsHermitian) (hCu : IsUnit C) :
    fromBlocks A B Bᴴ C =
      (fromBlocks 1 (B * C⁻¹) 0 1) *
      fromBlocks (A - B * C⁻¹ * Bᴴ) 0 0 C *
      (fromBlocks 1 (B * C⁻¹) 0 1)ᴴ := by
  let : Invertible C := hCu.invertible
  have hCt : (C⁻¹)ᴴ = C⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hC.inv.eq
  simpa only [Matrix.invOf_eq_nonsing_inv, fromBlocks_conjTranspose,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hCt] using
    Matrix.fromBlocks_eq_of_invertible₂₂ A B Bᴴ C

omit [Fintype m] [DecidableEq m] in
/-- The Schur complement of a symmetric matrix at an invertible symmetric bottom-right
block is symmetric.  Horn--Johnson (2013), Exercise 4.5.P21. -/
private theorem isHermitian_schur_complement_bottom {A : Matrix m m ℝ} {C : Matrix n n ℝ}
    (hA : A.IsHermitian) (hC : C.IsHermitian) (B : Matrix m n ℝ) :
    (A - B * C⁻¹ * Bᴴ).IsHermitian := by
  apply hA.sub
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_mul_mul_conjTranspose B hC.inv

/-- Haynsworth's positive inertia additivity at an invertible bottom-right block.
Horn--Johnson (2013), Exercise 4.5.P21. -/
theorem inertiaPos_fromBlocks_eq_add_schur_bottom {A : Matrix m m ℝ} {C : Matrix n n ℝ}
    (hA : A.IsHermitian) (B : Matrix m n ℝ) (hC : C.IsHermitian) (hCu : IsUnit C) :
    inertiaPos (fromBlocks A B Bᴴ C) = inertiaPos C + inertiaPos (A - B * C⁻¹ * Bᴴ) := by
  let L : Matrix (m ⊕ n) (m ⊕ n) ℝ := fromBlocks 1 (B * C⁻¹) 0 1
  let S : Matrix m m ℝ := A - B * C⁻¹ * Bᴴ
  have hL : IsUnit L :=
    isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one, isUnit_one⟩
  have hLt : IsUnit (Lᴴ) := by
    simpa using hL
  have hS : S.IsHermitian :=
    isHermitian_schur_complement_bottom hA hC B
  have hSym : L * fromBlocks S 0 0 C * Lᴴ = (Lᴴ)ᴴ * fromBlocks S 0 0 C * Lᴴ := by
    nth_rw 1 [← Matrix.conjTranspose_conjTranspose L]
  calc
    inertiaPos (fromBlocks A B Bᴴ C) = inertiaPos (L * fromBlocks S 0 0 C * Lᴴ) := by
      rw [fromBlocks_eq_mul_schur_mul_conjTranspose_bottom B hC hCu]
    _ = inertiaPos (fromBlocks S 0 0 C) := by
      rw [hSym]
      exact inertiaPos_transpose_mul_mul (X := Lᴴ) (A := fromBlocks S 0 0 C) hLt
    _ = inertiaPos C + inertiaPos S := by
      rw [inertiaPos_fromBlocks_zero hS hC, add_comm]

/-- The one-by-one block `[-1]`, used as the bottom-right block of the bordered
matrix in the rank-one certificate. -/
private def oneByOneNeg : Matrix (Fin 1) (Fin 1) ℝ :=
  diagonal (fun _ : Fin 1 => (-1 : ℝ))

/-- Positive inertia of the one-by-one diagonal matrix `[c]` when `0 < c`. -/
private lemma inertiaPos_diagonal_one_pos (c : ℝ) (hc : 0 < c) :
    inertiaPos (diagonal (fun _ : Fin 1 => c)) = 1 := by
  rw [inertiaPos_diagonal]
  have hf : (Finset.univ.filter fun _ : Fin 1 => 0 < c) = Finset.univ := by
    ext x
    simp [hc]
  rw [hf]
  simp

/-- Positive inertia of the one-by-one diagonal matrix `[c]` when `c < 0`. -/
private lemma inertiaPos_diagonal_one_neg (c : ℝ) (hc : c < 0) :
    inertiaPos (diagonal (fun _ : Fin 1 => c)) = 0 := by
  rw [inertiaPos_diagonal]
  have hf : (Finset.univ.filter fun _ : Fin 1 => 0 < c) = ∅ := by
    ext x
    by_cases h : 0 < c
    · exfalso
      linarith
    · simp [h]
  rw [hf]
  simp

/-- The one-step spectral certificate for stable-rank restricted invertibility: a
real symmetric invertible `M` updated by the rank-one matrix `vecMulVec v v` gains
exactly one positive eigenvalue as soon as `v ⬝ᵥ (M⁻¹ *ᵥ v) < -1`.  No
positive-definiteness of `M` is assumed; the certificate is Haynsworth additivity
applied twice to the bordered matrix `[[M, v], [vᵀ, -1]]`. -/
theorem inertiaPos_add_vecMulVec_eq_add_one
    {M : Matrix n n ℝ} (hM : M.IsHermitian) (hMu : IsUnit M) (v : n → ℝ)
    (hlt : v ⬝ᵥ (M⁻¹ *ᵥ v) < -1) :
    inertiaPos (M + vecMulVec v v) = inertiaPos M + 1 := by
  classical
  let b : Matrix n (Fin 1) ℝ := fun i _ => v i
  let K : Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) ℝ := fromBlocks M b bᴴ oneByOneNeg
  have hD_herm : oneByOneNeg.IsHermitian := Matrix.isHermitian_diagonal _
  have hDD : oneByOneNeg * oneByOneNeg = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    dsimp [oneByOneNeg]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i
    fin_cases j
    norm_num
  have hDu : IsUnit oneByOneNeg := by
    refine ⟨⟨oneByOneNeg, oneByOneNeg, hDD, hDD⟩, rfl⟩
  have hK_top : inertiaPos K = inertiaPos M + inertiaPos (oneByOneNeg - bᴴ * M⁻¹ * b) := by
    simpa [K] using inertiaPos_fromBlocks_eq_add_schur hM hMu hD_herm b
  have hbMul : bᴴ * M⁻¹ * b = diagonal (fun _ : Fin 1 => v ⬝ᵥ (M⁻¹ *ᵥ v)) := by
    let e : Fin 1 → ℝ := fun _ => 1
    have hb : b = vecMulVec v e := by
      ext i j
      simp [b, vecMulVec, e]
    have hbT : bᴴ = vecMulVec e v := by
      rw [hb, Matrix.conjTranspose_vecMulVec]
      ext i j
      simp [e, vecMulVec]
    have hdot : (v ᵥ* M⁻¹ ⬝ᵥ v) = v ⬝ᵥ (M⁻¹ *ᵥ v) := by
      exact (Matrix.dotProduct_mulVec v M⁻¹ v).symm
    calc
      bᴴ * M⁻¹ * b = (vecMulVec e v * M⁻¹) * vecMulVec v e := by
        rw [hbT, hb]
      _ = (vecMulVec e (v ᵥ* M⁻¹)) * vecMulVec v e := by
        rw [Matrix.vecMulVec_mul]
      _ = vecMulVec e ((v ᵥ* M⁻¹ ⬝ᵥ v) • e) := by
        rw [Matrix.vecMulVec_mul_vecMulVec]
      _ = diagonal (fun _ : Fin 1 => v ⬝ᵥ (M⁻¹ *ᵥ v)) := by
        rw [hdot]
        ext i j
        fin_cases i
        fin_cases j
        simp [vecMulVec, e]
  have hDq : oneByOneNeg - bᴴ * M⁻¹ * b =
      diagonal (fun _ : Fin 1 => -1 - v ⬝ᵥ (M⁻¹ *ᵥ v)) := by
    dsimp [oneByOneNeg]
    rw [hbMul, ← Matrix.diagonal_sub]
  have hpos : 0 < -1 - v ⬝ᵥ (M⁻¹ *ᵥ v) := by linarith
  have hDschur : inertiaPos (oneByOneNeg - bᴴ * M⁻¹ * b) = 1 := by
    rw [hDq]
    exact inertiaPos_diagonal_one_pos (-1 - v ⬝ᵥ (M⁻¹ *ᵥ v)) hpos
  have hK_bottom : inertiaPos K = inertiaPos oneByOneNeg +
      inertiaPos (M - b * oneByOneNeg⁻¹ * bᴴ) := by
    simpa [K] using inertiaPos_fromBlocks_eq_add_schur_bottom hM b hD_herm hDu
  have hDinv : oneByOneNeg⁻¹ = oneByOneNeg := Matrix.inv_eq_right_inv hDD
  have hbb : b * bᴴ = vecMulVec v v := by
    let e : Fin 1 → ℝ := fun _ => 1
    have hb : b = vecMulVec v e := by
      ext i j
      simp [b, vecMulVec, e]
    have hbT : bᴴ = vecMulVec e v := by
      rw [hb, Matrix.conjTranspose_vecMulVec]
      ext i j
      simp [e, vecMulVec]
    have he : e ⬝ᵥ e = 1 := by
      rw [dotProduct, Fin.sum_univ_one]
      simp [e]
    calc
      b * bᴴ = vecMulVec v e * vecMulVec e v := by
        rw [hbT, hb]
      _ = vecMulVec v ((e ⬝ᵥ e) • v) := by
        rw [Matrix.vecMulVec_mul_vecMulVec]
      _ = vecMulVec v v := by
        rw [he, one_smul]
  have hbD : b * oneByOneNeg = -b := by
    ext i j
    dsimp [oneByOneNeg]
    rw [Matrix.mul_diagonal]
    simp [b]
  have hbDb : b * oneByOneNeg * bᴴ = -vecMulVec v v := by
    rw [hbD, Matrix.neg_mul, hbb]
  have hMupdate : M - b * oneByOneNeg⁻¹ * bᴴ = M + vecMulVec v v := by
    rw [hDinv, hbDb]
    rw [sub_neg_eq_add]
  have hD_inertia0 : inertiaPos oneByOneNeg = 0 := by
    dsimp [oneByOneNeg]
    exact inertiaPos_diagonal_one_neg (-1) (by norm_num)
  have hmain_top : inertiaPos K = inertiaPos M + 1 := by
    rw [hK_top, hDschur]
  have hmain_bottom : inertiaPos K = inertiaPos (M + vecMulVec v v) := by
    rw [hK_bottom, hMupdate, hD_inertia0]
    simp
  exact hmain_bottom.symm.trans hmain_top

/-- Shifted-barrier form: with `M = A - bI`, the positive inertia of the rank-one
update counts the eigenvalues of `A` strictly above `b` plus the one gained. -/
theorem inertiaPos_add_vecMulVec_eq_add_one_of_shift
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (b : ℝ) (v : n → ℝ)
    (hMu : IsUnit (A - b • (1 : Matrix n n ℝ)))
    (hlt : v ⬝ᵥ ((A - b • (1 : Matrix n n ℝ))⁻¹ *ᵥ v) < -1) :
    inertiaPos (A - b • (1 : Matrix n n ℝ) + vecMulVec v v) =
      (Finset.univ.filter fun i => b < hA.eigenvalues i).card + 1 := by
  have hI : (b • (1 : Matrix n n ℝ)).IsHermitian := by
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.isHermitian_diagonal _
  have hm :=
    inertiaPos_add_vecMulVec_eq_add_one (hA.sub hI) hMu v hlt
  rw [inertiaPos_sub_smul_one_eq_card hA b] at hm
  exact hm

end NLAlib
