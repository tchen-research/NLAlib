import NLAlib.Matrix.Perturbation.ExteriorEigenvalueBranches
import NLAlib.Matrix.Functions.TraceExponentialSpectrum

/-!
# Exterior inverse branches of a diagonal matrix pencil

Changing variables from an eigenvalue `λ` of `A - z B` to `u = λ + s z`
makes `z` an eigenvalue of an affine matrix pencil with slopes `(s - bᵢ)⁻¹`.
This file constructs those inverse branches and proves their spectral relation.
It is supporting infrastructure for the planar root-sum route to
`trace-exponential-stahl`; no contour substitution or density positivity is
asserted here.
-/

noncomputable section

open Filter
open scoped Matrix Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem tendsto_affine_branch_ratio {f : ℂ → ℂ} {a d : ℂ}
    (h : Tendsto (fun z => f z - z * d) (Bornology.cobounded ℂ) (𝓝 a)) :
    Tendsto (fun z => f z * z⁻¹) (Bornology.cobounded ℂ) (𝓝 d) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded
  have h' : Tendsto (fun z => (f z - z * d) * z⁻¹ + d)
      (Bornology.cobounded ℂ) (𝓝 d) := by
    simpa using (h.mul hi).add_const d
  apply h'.congr'
  filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with z hz
  have hzne : z ≠ 0 := by intro hzero; norm_num [hzero] at hz
  field_simp
  ring

private theorem tendsto_cobounded_of_affine_branch {f : ℂ → ℂ} {a d : ℂ}
    (hd : d ≠ 0)
    (h : Tendsto (fun z => f z - z * d) (Bornology.cobounded ℂ) (𝓝 a)) :
    Tendsto f (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
  have hq := tendsto_affine_branch_ratio h
  have hfi : Tendsto (fun z => (f z)⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := by
    have hh : Tendsto (fun z => (f z * z⁻¹)⁻¹ * z⁻¹)
        (Bornology.cobounded ℂ) (𝓝 0) := by
      simpa using (hq.inv₀ hd).mul (tendsto_inv₀_cobounded (α := ℂ))
    apply hh.congr'
    filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with z hz
    have hzne : z ≠ 0 := by intro hzero; norm_num [hzero] at hz
    simp only [mul_inv_rev, inv_inv]
    calc
      z * (f z)⁻¹ * z⁻¹ = (f z)⁻¹ * (z * z⁻¹) := by ring
      _ = (f z)⁻¹ := by rw [mul_inv_cancel₀ hzne, mul_one]
  have hne : ∀ᶠ z in Bornology.cobounded ℂ, (f z)⁻¹ ≠ 0 := by
    filter_upwards [hq.eventually_ne hd] with z hz
    exact inv_ne_zero (by intro hf; exact hz (by simp [hf]))
  have hi := tendsto_inv₀_nhdsNE_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hfi, hne⟩)
  simpa only [Function.comp_def, inv_inv] using hi

/-- The inverse spectral pencil exchanges `z` with `λ + s z`. Multiplication
by the invertible diagonal matrix preserves singularity, so this equivalence
does not require a choice of eigenvectors or eigenvalue branches. -/
theorem mem_spectrum_inverse_diagonal_pencil_iff
    (A : Matrix n n ℂ) (b : n → ℝ) (s : ℝ)
    (hs : ∀ i, s ≠ b i) (u z : ℂ) :
    z ∈ spectrum ℂ
        (-(Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹) * A) +
          u • Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹)) ↔
      u - (s : ℂ) * z ∈ spectrum ℂ
        (A - z • Matrix.diagonal (fun i => (b i : ℂ))) := by
  classical
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ))
  let E : Matrix n n ℂ := Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹)
  have hc : ∀ i, ((s - b i : ℝ) : ℂ) ≠ 0 := by
    intro i
    exact_mod_cast sub_ne_zero.mpr (hs i)
  have hDE : D * E = 1 := by
    dsimp only [D, E]
    rw [Matrix.diagonal_mul_diagonal]
    simpa only [mul_inv_cancel₀ (hc _)] using (Matrix.diagonal_one :
      (Matrix.diagonal (fun _ : n => (1 : ℂ))) = 1)
  have hD : IsUnit D := by
    apply (Matrix.isUnit_iff_isUnit_det D).mpr
    dsimp only [D]
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => hc i))
  have heq : D * (algebraMap ℂ (Matrix n n ℂ) z - (-(E * A) + u • E)) =
      -(algebraMap ℂ (Matrix n n ℂ) (u - (s : ℂ) * z) -
        (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) := by
    simp only [mul_sub, mul_add, mul_neg, mul_smul_comm,
      ← mul_assoc, hDE, one_mul, Algebra.algebraMap_eq_smul_one,
      mul_one]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
      ring
    · simp [D, hij]
  rw [spectrum.mem_iff, spectrum.mem_iff]
  change (¬ IsUnit (algebraMap ℂ (Matrix n n ℂ) z - (-(E * A) + u • E))) ↔ _
  rw [← Units.isUnit_units_mul hD.unit, IsUnit.unit_spec, heq]
  rw [IsUnit.neg_iff]

/-- Distinct real slopes, away from `s`, give all exterior inverse branches.
The affine asymptote is `(u - Aᵢᵢ) / (s - bᵢ)`, with the diagonal entry of
`A` interpreted as a complex number. These branches are constructed from the
actual matrix pencil, rather than postulated as local inverses.
atlas: trace-exponential-stahl (partial) -/
theorem exists_exterior_inverse_eigenvalue_branches
    (A : Matrix n n ℂ) (b : n → ℝ) (hb : Function.Injective b)
    (s : ℝ) (hs : ∀ i, s ≠ b i) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {u | R < ‖u‖} ∧
        Tendsto (fun u => branch i u - u / ((s - b i : ℝ) : ℂ))
          (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ)))) ∧
      ∀ u, R < ‖u‖ →
        (∀ i, u - (s : ℂ) * branch i u ∈ spectrum ℂ
          (A - branch i u • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
        Function.Injective (fun i => branch i u) := by
  let E : Matrix n n ℂ := Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹)
  have hd : Function.Injective (fun i => ((s - b i : ℝ) : ℂ)⁻¹) := by
    intro i j hij
    apply hb
    have h := Complex.ofReal_injective (inv_injective hij)
    linarith
  obtain ⟨R, hR, branch, hbranch, hspec⟩ :=
    exists_exterior_eigenvalue_branches_of_diagonal
      (fun i => ((s - b i : ℝ) : ℂ)⁻¹) hd (-(E * A))
  refine ⟨R, hR, branch, ?_, ?_⟩
  · intro i
    refine ⟨(hbranch i).1, ?_⟩
    simpa only [div_eq_mul_inv, Matrix.neg_apply, Matrix.diagonal_mul, E, neg_mul, mul_neg,
      mul_comm]
      using (hbranch i).2
  · intro u hu
    exact ⟨fun i => (mem_spectrum_inverse_diagonal_pencil_iff A b s hs u _).mp
      ((hspec u hu).1 i), (hspec u hu).2⟩

/-- The affine asymptotes match an inverse branch to its original exterior
eigenvalue branch. In particular, the index is determined by the distinct
slopes, not by making an arbitrary spectral choice at each parameter. -/
theorem eventually_exterior_inverse_eigenvalue_branches_eq
    (A : Matrix n n ℂ) (b : n → ℝ) (hb : Function.Injective b)
    (s : ℝ) (hs : ∀ i, s ≠ b i)
    {R S : ℝ} {forward inverse : n → ℂ → ℂ}
    (hforward : ∀ i, Tendsto (fun z => forward i z + (b i : ℂ) * z)
      (Bornology.cobounded ℂ) (𝓝 (A i i)))
    (hforwardSpec : ∀ z, R < ‖z‖ →
      (∀ i, forward i z ∈ spectrum ℂ
        (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
      Function.Injective (fun i => forward i z))
    (hinverse : ∀ i, Tendsto (fun u => inverse i u - u / ((s - b i : ℝ) : ℂ))
      (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ))))
    (hinverseSpec : ∀ u, S < ‖u‖ → ∀ i,
      u - (s : ℂ) * inverse i u ∈ spectrum ℂ
        (A - inverse i u • Matrix.diagonal (fun i => (b i : ℂ)))) :
    ∀ᶠ u in Bornology.cobounded ℂ,
      ∀ i, forward i (inverse i u) + (s : ℂ) * inverse i u = u := by
  have hc (i : n) : ((s - b i : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (hs i)
  have hiratio (i : n) : Tendsto (fun u => inverse i u * u⁻¹)
      (Bornology.cobounded ℂ) (𝓝 (((s - b i : ℝ) : ℂ)⁻¹)) := by
    exact tendsto_affine_branch_ratio (by simpa only [div_eq_mul_inv] using hinverse i)
  have hicob (i : n) : Tendsto (inverse i) (Bornology.cobounded ℂ)
      (Bornology.cobounded ℂ) := by
    exact tendsto_cobounded_of_affine_branch (inv_ne_zero (hc i))
      (by simpa only [div_eq_mul_inv] using hinverse i)
  have hneq : ∀ i j, ∀ᶠ u in Bornology.cobounded ℂ,
      i ≠ j → u - (s : ℂ) * inverse i u ≠ forward j (inverse i u) := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => False.elim (h hij))
    have hres : Tendsto
        (fun u => (forward j (inverse i u) + (b j : ℂ) * inverse i u) * u⁻¹)
        (Bornology.cobounded ℂ) (𝓝 0) := by
      simpa using ((hforward j).comp (hicob i)).mul
        (tendsto_inv₀_cobounded (α := ℂ))
    have hlim : Tendsto
        (fun u => (u - (s : ℂ) * inverse i u - forward j (inverse i u)) * u⁻¹)
        (Bornology.cobounded ℂ)
        (𝓝 (1 + ((b j : ℂ) - (s : ℂ)) * ((s - b i : ℝ) : ℂ)⁻¹)) := by
      have hh := ((hiratio i).const_mul ((b j : ℂ) - (s : ℂ))).const_add 1 |>.sub hres
      simp only [sub_zero] at hh
      apply hh.congr'
      filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with u hu
      have hune : u ≠ 0 := by intro hzero; norm_num [hzero] at hu
      field_simp
      ring
    have hlimne : 1 + ((b j : ℂ) - (s : ℂ)) * ((s - b i : ℝ) : ℂ)⁻¹ ≠ 0 := by
      intro heq
      have hne : (b j : ℂ) ≠ (b i : ℂ) := by
        intro heq'
        exact hij (hb (Complex.ofReal_injective heq'.symm))
      apply hne
      have hc' := hc i
      push_cast at heq hc'
      field_simp at heq
      linear_combination heq
    filter_upwards [hlim.eventually_ne hlimne] with u hu _ heq
    exact hu (by rw [sub_eq_zero.mpr heq, zero_mul])
  have hneq' : ∀ᶠ u in Bornology.cobounded ℂ, ∀ i j,
      i ≠ j → u - (s : ℂ) * inverse i u ≠ forward j (inverse i u) := by
    simpa only [Filter.eventually_all] using hneq
  have hlarge : ∀ᶠ u in Bornology.cobounded ℂ, ∀ i, R < ‖inverse i u‖ := by
    simp only [Filter.eventually_all]
    intro i
    exact ((tendsto_norm_cobounded_atTop (E := ℂ)).comp (hicob i)).eventually_gt_atTop R
  filter_upwards [hneq', hlarge,
    (tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop S] with u hne hR hS i
  have hmem := hinverseSpec u hS i
  have hspec := hforwardSpec (inverse i u) (hR i)
  rw [spectrum_eq_range_of_injective_mem_spectrum _ _ hspec.2 hspec.1] at hmem
  obtain ⟨j, hj⟩ := hmem
  have hji : i = j := by
    by_contra hij
    exact hne i j hij hj.symm
  subst j
  linear_combination hj

end NLAlib
