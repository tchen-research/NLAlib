import NLAlib.Matrix.Nonnegative.PerronExistence
import NLAlib.Matrix.Spectral.MatrixPowerBounds

/-! # Collatz–Wielandt certificates, including reducible matrices

The upper certificate uses a positive vector. The lower certificate permits
a nonnegative vector and only compares ratios on its positive support. Strict
positive subsolutions approximate the spectral radius from above, so the
general upper infimum is not incorrectly asserted to be attained.
Source: Horn–Johnson, Matrix Analysis, Chapter 8.
-/

noncomputable section
open Matrix Finset
open scoped Matrix
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A positive subsolution bounds the real value of the complex spectral radius.
Source: Horn–Johnson, Chapter 8.
atlas: collatz-wielandt-certificates (partial) -/
theorem spectralRadius_toReal_le_of_positive_subsolution {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    {r : ℝ} (hAp : ∀ i, (A *ᵥ p) i ≤ r * p i) :
    (spectralRadius ℂ (A.map Complex.ofReal)).toReal ≤ r := by
  have hr : 0 ≤ r := by
    let i : ι := Classical.choice ‹Nonempty ι›
    have hnonneg : 0 ≤ (A *ᵥ p) i := Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hp j).le
    exact (mul_nonneg_iff_of_pos_right (hp i)).mp (hnonneg.trans (hAp i))
  have hspec := spectralRadius_le_of_abs_le_of_positive_subsolution
    (A := A) (B := A.map Complex.ofReal) (fun i j => by
      simp only [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA i j), le_refl])
    hp hAp
  simpa only [ENNReal.toReal_ofReal hr] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hspec

/-- A nonzero nonnegative supersolution bounds the spectral radius from below.
No positive Perron vector or support-overlap assumption is required.
Source: Horn–Johnson, Chapter 8.
atlas: collatz-wielandt-certificates (partial) -/
theorem le_spectralRadius_toReal_of_nonnegative_supersolution {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hxne : x ≠ 0)
    {r : ℝ} (hAx : ∀ i, r * x i ≤ (A *ᵥ x) i) :
    r ≤ (spectralRadius ℂ (A.map Complex.ofReal)).toReal := by
  classical
  by_contra! hr
  obtain ⟨p, hp, hAp⟩ := exists_positive_strict_subsolution_of_spectralRadius_lt hA hr
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxne
  have hxj : 0 < x j := lt_of_le_of_ne (hx j) hj.symm
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun k => x k / p k)
    Finset.univ_nonempty
  let t := x i / p i
  have ht : 0 < t := (div_pos hxj (hp j)).trans_le (hi j (mem_univ j))
  have hxi : x i = t * p i := by dsimp [t]; field_simp [(hp i).ne']
  have hxle (k : ι) : x k ≤ t * p k := (div_le_iff₀ (hp k)).mp (hi k (mem_univ k))
  have hbound : (A *ᵥ x) i ≤ t * (A *ᵥ p) i := by
    calc
      _ ≤ ∑ k, A i k * (t * p k) := Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left (hxle k) (hA i k)
      _ = _ := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        congr 1
        funext k
        ring
  have hstrict := mul_lt_mul_of_pos_left (hAp i) ht
  have hstrict' : (A *ᵥ x) i < r * x i := hbound.trans_lt (by
    simpa only [hxi, mul_left_comm] using hstrict)
  exact not_lt_of_ge (hAx i) hstrict'

/-- The minimum/maximum ratio certificate for every strictly positive vector.
Source: Horn–Johnson, Chapter 8.
atlas: collatz-wielandt-certificates (partial) -/
theorem collatz_ratio_bounds {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {x : ι → ℝ} (hx : ∀ i, 0 < x i) :
    Finset.univ.inf' Finset.univ_nonempty (fun i => (A *ᵥ x) i / x i) ≤
      (spectralRadius ℂ (A.map Complex.ofReal)).toReal ∧
    (spectralRadius ℂ (A.map Complex.ofReal)).toReal ≤
      Finset.univ.sup' Finset.univ_nonempty (fun i => (A *ᵥ x) i / x i) := by
  have hxne : x ≠ 0 := by
    intro hz
    have h := hx (Classical.choice ‹Nonempty ι›)
    rw [hz] at h
    exact lt_irrefl _ h
  constructor
  · apply le_spectralRadius_toReal_of_nonnegative_supersolution hA (fun i => (hx i).le) hxne
    intro i
    exact (le_div_iff₀ (hx i)).mp (Finset.inf'_le _ (mem_univ i))
  · apply spectralRadius_toReal_le_of_positive_subsolution hA hx
    intro i
    exact (div_le_iff₀ (hx i)).mp
      (Finset.le_sup' (fun i => (A *ᵥ x) i / x i) (mem_univ i))

/-- The upper Collatz infimum equals the spectral radius: its explicit
greatest-lower-bound formulation includes cases where it is not attained.
Source: Horn–Johnson, Chapter 8.
atlas: collatz-wielandt-certificates (partial) -/
theorem isGLB_positive_collatz_max_ratios {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    IsGLB {s : ℝ | ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧
      s = Finset.univ.sup' Finset.univ_nonempty (fun i => (A *ᵥ x) i / x i)}
      (spectralRadius ℂ (A.map Complex.ofReal)).toReal := by
  constructor
  · rintro s ⟨x, hx, rfl⟩
    exact (collatz_ratio_bounds hA hx).2
  · intro a ha
    by_contra! hlt
    obtain ⟨x, hx, hAx⟩ := exists_positive_strict_subsolution_of_spectralRadius_lt hA hlt
    have hmax : Finset.univ.sup' Finset.univ_nonempty (fun i => (A *ᵥ x) i / x i) < a :=
      (Finset.sup'_lt_iff _).mpr fun i _ => (div_lt_iff₀ (hx i)).mpr (hAx i)
    exact (not_lt_of_ge (ha ⟨x, hx, rfl⟩)) hmax

/-- The support-aware lower Collatz maximum, expressed as the greatest scalar
for which some nonzero nonnegative supersolution exists. This is exactly the
maximum of `min_{i:xᵢ>0} (Ax)ᵢ/xᵢ`, and the Perron vector attains it.
Source: Horn–Johnson, Chapter 8.
atlas: collatz-wielandt-certificates (partial) -/
theorem isGreatest_nonnegative_collatz_supersolutions {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) :
    IsGreatest {r : ℝ | ∃ x : ι → ℝ, (∀ i, 0 ≤ x i) ∧ x ≠ 0 ∧
      ∀ i, r * x i ≤ (A *ᵥ x) i} (spectralRadius ℂ (A.map Complex.ofReal)).toReal := by
  constructor
  · obtain ⟨p, hp, hs, he⟩ := exists_nonnegative_perron_eigenvector hA
    refine ⟨p, hp, ?_, fun i => ?_⟩
    · intro hz
      simp [hz] at hs
    · rw [he]
      exact le_rfl
  · rintro r ⟨x, hx, hne, hAx⟩
    exact le_spectralRadius_toReal_of_nonnegative_supersolution hA hx hne hAx

end Matrix
