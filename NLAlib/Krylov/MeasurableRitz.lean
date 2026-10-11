import NLAlib.Krylov.Polynomial
import NLAlib.Matrix.PowerRayleigh
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Measurable variational Lanczos values

Rational Krylov coefficients give a countable measurable supremum. Density extends
the resulting quadratic inequality to all real coefficients, proving equality
with the ordinary Rayleigh variational value of the actual Krylov subspace.
-/

noncomputable section
open scoped Matrix
open MeasureTheory
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A vector in the actual `q`-step Krylov span, specified by its real coefficients.
Source: manuscript `rt:random-start`, the matrix `K(b)c`. -/
def krylovCoefficientVector (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ}
    (c : Fin q → ℝ) : n → ℝ := ∑ j : Fin q, c j • ((A ^ (j : ℕ)) *ᵥ b)

/-- The coefficient representation equals the existing Krylov span, including `q=0`.
Source: manuscript `rt:random-start`; existing `krylovSpace` definition. -/
theorem mem_krylovSpace_iff_exists_coefficients (A : Matrix n n ℝ) (b : n → ℝ)
    (q : ℕ) (y : n → ℝ) :
    y ∈ krylovSpace A b q ↔ ∃ c : Fin q → ℝ, krylovCoefficientVector A b c = y := by
  exact Submodule.mem_span_range_iff_exists_fun ℝ

/-- The largest Lanczos Ritz value as a countable rational-coefficient supremum.
Source: manuscript `rt:random-start`, measurability paragraph. -/
def lanczosRitzValue (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) : ℝ :=
  ⨆ c : Fin q → ℚ, (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient
    (WithLp.toLp 2 (krylovCoefficientVector A b (fun j => (c j : ℝ))))

/-- Every rational Krylov coefficient vector belongs to the existing Krylov space.
Source: manuscript `rt:random-start`. -/
theorem krylovCoefficientVector_mem (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ}
    (c : Fin q → ℝ) : krylovCoefficientVector A b c ∈ krylovSpace A b q :=
  (mem_krylovSpace_iff_exists_coefficients A b q _).mpr ⟨c, rfl⟩

/-- The PSD variational Lanczos value is between zero and the spectral norm.
Source: manuscript `rt:random-start`, totalized Rayleigh convention. -/
theorem lanczosRitzValue_bounds {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (b : n → ℝ) (q : ℕ) : 0 ≤ lanczosRitzValue A b q ∧ lanczosRitzValue A b q ≤ specNorm A := by
  have hB : BddAbove (Set.range (fun c : Fin q → ℚ =>
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient
        (WithLp.toLp 2 (krylovCoefficientVector A b (fun j => (c j : ℝ)))))) :=
    ⟨specNorm A, by rintro _ ⟨c, rfl⟩; exact (rayleighQuotient_toEuclideanCLM_bounds hA _).2⟩
  constructor
  · have h := (rayleighQuotient_toEuclideanCLM_bounds hA
      (krylovCoefficientVector A b (fun j => ((0 : Fin q → ℚ) j : ℝ)))).1.trans
        (le_ciSup hB (0 : Fin q → ℚ))
    exact h
  · exact ciSup_le (fun c => (rayleighQuotient_toEuclideanCLM_bounds hA _).2)

/-- The rational variational Lanczos value is measurable in the starting vector.
Source: manuscript `rt:random-start`, countable supremum of polynomial-vector quotients. -/
theorem measurable_lanczosRitzValue (A : Matrix n n ℝ) (q : ℕ) :
    Measurable (fun b : n → ℝ => lanczosRitzValue A b q) := by
  apply Measurable.iSup
  intro c
  simp only [rayleighQuotient_toEuclideanCLM_eq, krylovCoefficientVector, Matrix.mulVec, dotProduct,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

/-- Density of rational coefficients proves the true variational comparison for every
vector in the actual Krylov space. Zero polynomial vectors are included.
Source: manuscript `rt:random-start`, measurability paragraph. -/
theorem rayleighQuotient_le_lanczosRitzValue_of_mem {A : Matrix n n ℝ}
    (hA : A.PosSemidef) (b : n → ℝ) (q : ℕ) {y : n → ℝ}
    (hy : y ∈ krylovSpace A b q) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient (WithLp.toLp 2 y) ≤
      lanczosRitzValue A b q := by
  let θ := lanczosRitzValue A b q
  have hθ : 0 ≤ θ := (lanczosRitzValue_bounds hA b q).1
  have hB : BddAbove (Set.range (fun c : Fin q → ℚ =>
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient
        (WithLp.toLp 2 (krylovCoefficientVector A b (fun j => (c j : ℝ)))))) :=
    ⟨specNorm A, by rintro _ ⟨c, rfl⟩; exact (rayleighQuotient_toEuclideanCLM_bounds hA _).2⟩
  have hRat : ∀ c : Fin q → ℚ,
      let v := krylovCoefficientVector A b (fun j => (c j : ℝ))
      v ⬝ᵥ (A *ᵥ v) ≤ θ * (v ⬝ᵥ v) := by
    intro c
    dsimp only
    let v := krylovCoefficientVector A b (fun j => (c j : ℝ))
    change v ⬝ᵥ (A *ᵥ v) ≤ θ * (v ⬝ᵥ v)
    by_cases hv : v = 0
    · simp only [hv, Matrix.mulVec_zero, dotProduct_zero, mul_zero, le_refl]
    · have hp : 0 < v ⬝ᵥ v := lt_of_le_of_ne (dotProduct_self_nonneg _)
        (Ne.symm fun h => hv (dotProduct_self_eq_zero.mp h))
      have h := le_ciSup hB c
      rw [rayleighQuotient_toEuclideanCLM_eq] at h
      exact (div_le_iff₀ hp).mp h
  have hDense : DenseRange (fun c : Fin q → ℚ => fun j => (c j : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨c, rfl⟩ := (mem_krylovSpace_iff_exists_coefficients A b q y).mp hy
  have hAll : (krylovCoefficientVector A b c) ⬝ᵥ (A *ᵥ krylovCoefficientVector A b c) ≤
      θ * (krylovCoefficientVector A b c ⬝ᵥ krylovCoefficientVector A b c) := by
    refine hDense.induction_on (p := fun c =>
      (krylovCoefficientVector A b c) ⬝ᵥ (A *ᵥ krylovCoefficientVector A b c) ≤
        θ * (krylovCoefficientVector A b c ⬝ᵥ krylovCoefficientVector A b c)) c ?_ hRat
    apply isClosed_le
    · simp only [krylovCoefficientVector, Matrix.mulVec, dotProduct, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      fun_prop
    · simp only [krylovCoefficientVector, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
  rw [rayleighQuotient_toEuclideanCLM_eq]
  by_cases hv : krylovCoefficientVector A b c = 0
  · simpa only [hv, Matrix.mulVec_zero, dotProduct_zero, div_zero] using hθ
  · have hp : 0 < krylovCoefficientVector A b c ⬝ᵥ krylovCoefficientVector A b c :=
      lt_of_le_of_ne (dotProduct_self_nonneg _) (Ne.symm fun h => hv (dotProduct_self_eq_zero.mp h))
    exact (div_le_iff₀ hp).mpr hAll

/-- The countable measurable value equals the ordinary Rayleigh supremum over the
actual Krylov space. Source: manuscript `rt:random-start`, definition of Lanczos Ritz value.
atlas: random-start-power (partial) -/
theorem lanczosRitzValue_eq_sSup {A : Matrix n n ℝ} (hA : A.PosSemidef) (b : n → ℝ) (q : ℕ) :
    lanczosRitzValue A b q = sSup {t : ℝ | ∃ y ∈ krylovSpace A b q,
      t = (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient (WithLp.toLp 2 y)} := by
  let S := {t : ℝ | ∃ y ∈ krylovSpace A b q,
    t = (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient (WithLp.toLp 2 y)}
  have hS : S.Nonempty := ⟨_, 0, (krylovSpace A b q).zero_mem, rfl⟩
  have hB : BddAbove S := ⟨specNorm A, by
    rintro _ ⟨y, _, rfl⟩
    exact (rayleighQuotient_toEuclideanCLM_bounds hA y).2⟩
  apply le_antisymm
  · apply ciSup_le
    intro c
    apply le_csSup hB
    exact ⟨_, krylovCoefficientVector_mem A b _, rfl⟩
  · apply csSup_le hS
    rintro _ ⟨y, hy, rfl⟩
    exact rayleighQuotient_le_lanczosRitzValue_of_mem hA b q hy

end NLAlib
