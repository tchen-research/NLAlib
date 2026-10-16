import NLAlib.Matrix.Nonnegative.PerronIrreducible
import NLAlib.Matrix.Spectral.MatrixPowerBounds

/-! # Monotonicity and strict Perron comparison

Entrywise modulus domination controls the complex spectral radius. A nonzero
nonnegative perturbation strictly increases the Perron root when the smaller
matrix is irreducible: positive left and right eigenvectors detect every
nonzero perturbation entry. Source: Horn–Johnson, Matrix Analysis, Chapter 8.
-/

noncomputable section
open Matrix Finset
open scoped Matrix ENNReal

namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
/-- Entrywise monotonicity of powers for nonnegative real matrices. -/
theorem pow_apply_le_of_nonneg_of_le {A B : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hAB : ∀ i j, A i j ≤ B i j)
    (k : ℕ) (i j : ι) : (A ^ k) i j ≤ (B ^ k) i j := by
  have hB : ∀ i j, 0 ≤ B i j := fun i j => (hA i j).trans (hAB i j)
  induction k generalizing i j with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ, Matrix.mul_apply]
    exact Finset.sum_le_sum fun l _ => mul_le_mul (ih i l) (hAB l j)
      (hA l j) (Matrix.pow_apply_nonneg hB k i l)

omit [Nonempty ι] in
/-- Increasing an irreducible nonnegative matrix entrywise preserves irreducibility. -/
theorem IsIrreducible.mono_of_le {A B : Matrix ι ι ℝ}
    (hA : A.IsIrreducible) (hAB : ∀ i j, A i j ≤ B i j) : B.IsIrreducible := by
  have hB : ∀ i j, 0 ≤ B i j := fun i j => (hA.nonneg i j).trans (hAB i j)
  apply (isIrreducible_iff_exists_pow_pos hB).mpr
  intro i j
  obtain ⟨k, hk, hki⟩ := (isIrreducible_iff_exists_pow_pos hA.nonneg).mp hA i j
  exact ⟨k, hk, hki.trans_le (pow_apply_le_of_nonneg_of_le hA.nonneg hAB k i j)⟩

/-- Ordinary entrywise comparison of nonnegative matrices implies comparison
of their complex spectral radii, with no irreducibility assumption.
Source: Horn–Johnson, Chapter 8.
atlas: nonnegative-spectral-radius-comparison (partial) -/
theorem spectralRadius_complexification_mono {A B : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hAB : ∀ i j, A i j ≤ B i j) :
    spectralRadius ℂ (A.map Complex.ofReal) ≤ spectralRadius ℂ (B.map Complex.ofReal) := by
  apply spectralRadius_le_of_abs_le_nonnegative (fun i j => (hA i j).trans (hAB i j))
  intro i j
  simpa only [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA i j)]
    using hAB i j

/-- Every nonzero nonnegative entrywise perturbation strictly increases the
spectral radius of a nonzero irreducible nonnegative matrix.
Source: Horn–Johnson, Chapter 8.
atlas: nonnegative-spectral-radius-comparison (partial) -/
theorem IsIrreducible.spectralRadius_add_lt {A E : Matrix ι ι ℝ}
    (hA : A.IsIrreducible) (hAne : A ≠ 0) (hE : ∀ i j, 0 ≤ E i j) (hEne : E ≠ 0) :
    spectralRadius ℂ (A.map Complex.ofReal) < spectralRadius ℂ ((A + E).map Complex.ofReal) := by
  have hAB : ∀ i j, A i j ≤ (A + E) i j := fun i j => le_add_of_nonneg_right (hE i j)
  have hB := hA.mono_of_le hAB
  have hBne : A + E ≠ 0 := by
    intro hz
    apply hAne
    ext i j
    have hle := hAB i j
    rw [hz] at hle
    exact le_antisymm hle (hA.nonneg i j)
  obtain ⟨_, q, _, _, hq, _, _, _, hqA⟩ := hA.exists_positive_perron_pair hAne
  obtain ⟨p, _, _, hp, _, _, _, hBp, _⟩ := hB.exists_positive_perron_pair hBne
  have hpair : 0 < q ⬝ᵥ p := Finset.sum_pos (fun i _ => mul_pos (hq i) (hp i)) Finset.univ_nonempty
  obtain ⟨i, j, hij⟩ : ∃ i j, E i j ≠ 0 := by
    by_contra! h
    exact hEne (funext fun i => funext fun j => h i j)
  have hEp : 0 < (E *ᵥ p) i := (mul_pos (lt_of_le_of_ne (hE i j) hij.symm) (hp j)).trans_le
    (Finset.single_le_sum (fun k _ => mul_nonneg (hE i k) (hp k).le) (mem_univ j))
  have hpert : 0 < q ⬝ᵥ (E *ᵥ p) := (mul_pos (hq i) hEp).trans_le
    (Finset.single_le_sum (fun k _ => mul_nonneg (hq k).le
      (Finset.sum_nonneg fun l _ => mul_nonneg (hE k l) (hp l).le)) (mem_univ i))
  have heq : (spectralRadius ℂ ((A + E).map Complex.ofReal)).toReal * (q ⬝ᵥ p) =
      (spectralRadius ℂ (A.map Complex.ofReal)).toReal * (q ⬝ᵥ p) + q ⬝ᵥ (E *ᵥ p) := by
    calc
      _ = q ⬝ᵥ ((A + E) *ᵥ p) := by rw [hBp, dotProduct_smul]; rfl
      _ = _ := by
        rw [Matrix.add_mulVec, dotProduct_add, Matrix.dotProduct_mulVec, hqA, smul_dotProduct]
        rfl
  have hlt : (spectralRadius ℂ (A.map Complex.ofReal)).toReal <
      (spectralRadius ℂ ((A + E).map Complex.ofReal)).toReal := by nlinarith
  exact (ENNReal.toReal_lt_toReal (NLAlib.matrix_spectralRadius_ne_top _)
    (NLAlib.matrix_spectralRadius_ne_top _)).mp hlt

end Matrix
