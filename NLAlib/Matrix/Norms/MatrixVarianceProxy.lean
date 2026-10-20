import NLAlib.Matrix.Norms.BilinearSquareMass
import NLAlib.Matrix.Norms.GramSquareMassDeletion

/-!
# The actual matrix variance proxy and its deletion self-bound

The proxy is computed from a bilinear unit-ball supremum and the native
spectral norm of actual summed Gram squares. This is the deterministic
content of arXiv:2201.05142v3, Lemma5.9. No desired self-bound, maximizer,
probability estimate, or moment comparison is supplied as an input.
-/

noncomputable section
set_option autoImplicit false
open Matrix Finset
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {ι n : Type*} [Fintype n] [DecidableEq n]

/-- The actual weighted bilinear/Gram square-mass proxy on a selected family. -/
def matrixVarianceProxy (D : ι → Matrix n n ℂ) (s : Finset ι) (α β : ℝ) : ℝ :=
  α * bilinearSquareMass D s + β * specNorm (∑ i ∈ s, (D i)ᴴ * D i)

/-- Nonnegativity of the actual proxy for nonnegative weights. -/
theorem matrixVarianceProxy_nonneg (D : ι → Matrix n n ℂ) (s : Finset ι)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) : 0 ≤ matrixVarianceProxy D s α β :=
  add_nonneg (mul_nonneg hα (bilinearSquareMass_nonneg D s))
    (mul_nonneg hβ (specNorm_nonneg _))

/-- Actual deletion can only reduce the proxy. -/
theorem matrixVarianceProxy_mono (D : ι → Matrix n n ℂ) {s t : Finset ι}
    (hst : s ⊆ t) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    matrixVarianceProxy D s α β ≤ matrixVarianceProxy D t α β :=
  add_le_add (mul_le_mul_of_nonneg_left (bilinearSquareMass_mono D hst) hα)
    (mul_le_mul_of_nonneg_left (specNorm_sum_gram_mono D hst) hβ)

open scoped Matrix.Norms.L2Operator in
/-- The actual proxy depends continuously on all complex entries. -/
theorem continuous_matrixVarianceProxy (s : Finset ι) (α β : ℝ) :
    Continuous (fun D : ι → Matrix n n ℂ => matrixVarianceProxy D s α β) := by
  have hgram : Continuous (fun D : ι → Matrix n n ℂ =>
      specNorm (∑ i ∈ s, (D i)ᴴ * D i)) := by
    simp only [specNorm_eq_norm]
    fun_prop
  exact (continuous_const.mul (continuous_bilinearSquareMass s)).add
    (continuous_const.mul hgram)

/-- The actual proxy is measurable without a separately assumed supremum
measurability hypothesis. -/
theorem measurable_matrixVarianceProxy [Fintype ι] (s : Finset ι) (α β : ℝ) :
    Measurable (fun D : ι → Matrix n n ℂ => matrixVarianceProxy D s α β) := by
  let : SecondCountableTopology (Matrix n n ℂ) :=
    inferInstanceAs (SecondCountableTopology (n → n → ℂ))
  exact (continuous_matrixVarianceProxy s α β).measurable

open scoped Matrix.Norms.L2Operator in
/-- Exact deterministic self-bounding for the actual computed proxy. The
matrix labels and the summand family may be empty; a zero bound is included. -/
theorem sum_sq_sub_matrixVarianceProxy_erase_le [Fintype ι] [DecidableEq ι]
    (D : ι → Matrix n n ℂ) {R α β : ℝ} (hR : 0 ≤ R) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hD : ∀ i, specNorm (D i) ≤ 2 * R) :
    ∑ i, (matrixVarianceProxy D Finset.univ α β -
      matrixVarianceProxy D (Finset.univ.erase i) α β) ^ 2 ≤
        8 * R ^ 2 * (α + β) * matrixVarianceProxy D Finset.univ α β := by
  obtain ⟨v, w, hv, hw, hV, hVgap⟩ := exists_bilinearSquareMass_erase_gap_le D
  obtain ⟨u, hu, hU, hUgap⟩ := exists_specNorm_sum_gram_erase_gap_le D
  let x : ι → ℝ := fun i => ‖star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp)‖ ^ 2
  let y : ι → ℝ := fun i => ‖WithLp.toLp 2 (D i *ᵥ u.ofLp)‖ ^ 2
  have hx0 (i : ι) : 0 ≤ x i := sq_nonneg _
  have hy0 (i : ι) : 0 ≤ y i := sq_nonneg _
  have hxb (i : ι) : x i ≤ 4 * R ^ 2 := by
    have hinner := norm_inner_le_norm (𝕜 := ℂ) v (WithLp.toLp 2 (D i *ᵥ w.ofLp))
    have heq : inner ℂ v (WithLp.toLp 2 (D i *ᵥ w.ofLp)) =
        star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp) := by
      rw [← WithLp.toLp_ofLp 2 v, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    rw [heq] at hinner
    have hmv := (D i).l2_opNorm_mulVec w
    have hprobe : ‖star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp)‖ ≤ 2 * R := by
      calc _ ≤ ‖v‖ * ‖WithLp.toLp 2 (D i *ᵥ w.ofLp)‖ := hinner
        _ ≤ ‖v‖ * (specNorm (D i) * ‖w‖) :=
          mul_le_mul_of_nonneg_left hmv (norm_nonneg _)
        _ ≤ 1 * (specNorm (D i) * ‖w‖) :=
          mul_le_mul_of_nonneg_right hv (mul_nonneg (specNorm_nonneg _) (norm_nonneg _))
        _ ≤ specNorm (D i) := by
          simpa only [one_mul, mul_one] using
            mul_le_mul_of_nonneg_left hw (specNorm_nonneg (D i))
        _ ≤ _ := hD i
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hR)).mpr hprobe
    simpa only [x, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hsq
  have hyb (i : ι) : y i ≤ 4 * R ^ 2 := by
    have hmv := (D i).l2_opNorm_mulVec u
    have hprobe : ‖WithLp.toLp 2 (D i *ᵥ u.ofLp)‖ ≤ 2 * R := by
      apply hmv.trans
      exact (mul_le_mul_of_nonneg_left hu (specNorm_nonneg _)).trans
        (by simpa only [mul_one] using hD i)
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hR)).mpr hprobe
    simpa only [y, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hsq
  have hpoint (i : ι) :
      (matrixVarianceProxy D Finset.univ α β -
        matrixVarianceProxy D (Finset.univ.erase i) α β) ^ 2 ≤
      8 * R ^ 2 * (α ^ 2 * x i + β ^ 2 * y i) := by
    have hδ0 := sub_nonneg.mpr
      (matrixVarianceProxy_mono D (Finset.erase_subset i Finset.univ) hα hβ)
    have hδ : matrixVarianceProxy D Finset.univ α β -
        matrixVarianceProxy D (Finset.univ.erase i) α β ≤ α * x i + β * y i := by
      have h1 := mul_le_mul_of_nonneg_left (hVgap i) hα
      have h2 := mul_le_mul_of_nonneg_left (hUgap i) hβ
      dsimp [matrixVarianceProxy, x, y] at *
      linarith
    have hsq := (sq_le_sq₀ hδ0 (add_nonneg (mul_nonneg hα (hx0 i))
      (mul_nonneg hβ (hy0 i)))).mpr hδ
    have hsum : (α * x i + β * y i) ^ 2 ≤
        2 * α ^ 2 * (x i) ^ 2 + 2 * β ^ 2 * (y i) ^ 2 := by
      nlinarith [sq_nonneg (α * x i - β * y i)]
    have hx := mul_le_mul_of_nonneg_right (hxb i) (hx0 i)
    have hy := mul_le_mul_of_nonneg_right (hyb i) (hy0 i)
    have hxs := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2 * α ^ 2 by positivity)
    have hys := mul_le_mul_of_nonneg_left hy (show 0 ≤ 2 * β ^ 2 by positivity)
    nlinarith
  have hs : ∑ i, (matrixVarianceProxy D Finset.univ α β -
      matrixVarianceProxy D (Finset.univ.erase i) α β) ^ 2 ≤
        8 * R ^ 2 * (α ^ 2 * bilinearSquareMass D Finset.univ +
          β ^ 2 * specNorm (∑ i, (D i)ᴴ * D i)) := by
    apply (Finset.sum_le_sum (fun i _ => hpoint i)).trans_eq
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← hV, ← hU]
  have hc : α ^ 2 * bilinearSquareMass D Finset.univ +
      β ^ 2 * specNorm (∑ i, (D i)ᴴ * D i) ≤
      (α + β) * matrixVarianceProxy D Finset.univ α β := by
    have hcross : 0 ≤ α * β *
        (bilinearSquareMass D Finset.univ + specNorm (∑ i, (D i)ᴴ * D i)) :=
      mul_nonneg (mul_nonneg hα hβ)
        (add_nonneg (bilinearSquareMass_nonneg D _) (specNorm_nonneg _))
    dsimp [matrixVarianceProxy]
    nlinarith
  exact hs.trans ((mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (by ring))

/-- The actual source-scaled resolvent variance proxy on a matrix difference
array. Gram squares give the source's Di^2 when each Di is Hermitian.
At zero height both totalized coefficients vanish, giving zero; actual
nonreal-resolvent applications have strictly positive height. -/
def resolventVarianceProxy (D : ι → Matrix n n ℂ) (s : Finset ι) (R η : ℝ) : ℝ :=
  matrixVarianceProxy D s (2 / η ^ 4) (8 * R ^ 2 / η ^ 6)

/-- Source Lemma5.9 with its actual constants and actual computed proxy.
No contour, derivative, probability, or desired self-bound is assumed. -/
theorem sum_sq_sub_resolventVarianceProxy_erase_le [Fintype ι] [DecidableEq ι]
    (D : ι → Matrix n n ℂ) {R η : ℝ} (hR : 0 ≤ R)
    (hD : ∀ i, specNorm (D i) ≤ 2 * R) :
    ∑ i, (resolventVarianceProxy D Finset.univ R η -
      resolventVarianceProxy D (Finset.univ.erase i) R η) ^ 2 ≤
      (16 * R ^ 2 / η ^ 4 + 64 * R ^ 4 / η ^ 6) *
        resolventVarianceProxy D Finset.univ R η := by
  have h := sum_sq_sub_matrixVarianceProxy_erase_le D hR
    (α := 2 / η ^ 4) (β := 8 * R ^ 2 / η ^ 6) (by positivity) (by positivity) hD
  have hc : 8 * R ^ 2 * (2 / η ^ 4 + 8 * R ^ 2 / η ^ 6) =
      16 * R ^ 2 / η ^ 4 + 64 * R ^ 4 / η ^ 6 := by ring
  simpa only [resolventVarianceProxy, hc] using h

/-- The actual variance proxy depends only on selected matrix coordinates. -/
theorem matrixVarianceProxy_congr {D E : ι → Matrix n n ℂ} (s : Finset ι)
    (h : ∀ i ∈ s, D i = E i) (α β : ℝ) :
    matrixVarianceProxy D s α β = matrixVarianceProxy E s α β := by
  have hg : (∑ i ∈ s, (D i)ᴴ * D i) = ∑ i ∈ s, (E i)ᴴ * E i := by
    exact Finset.sum_congr rfl (fun i hi => by rw [h i hi])
  simp only [matrixVarianceProxy, bilinearSquareMass_congr s h, hg]

/-- An actual common matrix norm bound yields a global proxy bound. -/
theorem matrixVarianceProxy_le_card_mul [Fintype ι]
    (D : ι → Matrix n n ℂ) {R α β : ℝ} (hR : 0 ≤ R) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hD : ∀ i, specNorm (D i) ≤ 2 * R) :
    matrixVarianceProxy D Finset.univ α β ≤ (α + β) * (Fintype.card ι : ℝ) * (4 * R ^ 2) := by
  have hs : (∑ i, specNorm (D i) ^ 2) ≤ (Fintype.card ι : ℝ) * (4 * R ^ 2) := by
    calc
      _ ≤ ∑ _i : ι, (4 * R ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        have h := (sq_le_sq₀ (specNorm_nonneg _) (by positivity : 0 ≤ 2 * R)).mpr (hD i)
        nlinarith
      _ = _ := by simp
  have h1 := (bilinearSquareMass_le_sum_specNorm_sq D Finset.univ).trans hs
  have h2 := (specNorm_sum_gram_le_sum_specNorm_sq D Finset.univ).trans hs
  dsimp only [matrixVarianceProxy]
  have h := add_le_add (mul_le_mul_of_nonneg_left h1 hα)
    (mul_le_mul_of_nonneg_left h2 hβ)
  nlinarith

end NLAlib
