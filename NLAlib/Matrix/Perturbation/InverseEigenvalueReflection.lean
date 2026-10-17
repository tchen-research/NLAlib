import NLAlib.Matrix.Perturbation.InverseEigenvalueHalfPlane
import NLAlib.Matrix.Perturbation.ExteriorEigenvalueReflection
import NLAlib.ForMathlib.Analysis.Complex.ExteriorReflection

/-!
# Schwarz reflection of inverse spectral branches

Although the inverse matrix pencil is generally non-Hermitian, its spectral
equation has the required joint conjugation symmetry. Real distinct asymptotic
slopes therefore give Schwarz reflection for each labelled exterior branch.
This supports the planar route to `trace-exponential-stahl`.
-/

noncomputable section

open Complex Filter
open scoped Matrix Topology ComplexConjugate

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- A complete inverse branch family of a Hermitian diagonal pencil eventually
satisfies Schwarz reflection label by label. Its inverse matrix itself need not
be Hermitian: the proof uses the equivalent forward spectral equation. -/
theorem eventually_exterior_inverse_eigenvalue_branches_conj_eq
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ)
    (hb : Function.Injective b) (s : ℝ) (hs : ∀ i, s ≠ b i)
    {R : ℝ} {branch : n → ℂ → ℂ}
    (hlim : ∀ i, Tendsto (fun u => branch i u - u / ((s - b i : ℝ) : ℂ))
      (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ))))
    (hspec : ∀ u, R < ‖u‖ →
      (∀ i, u - (s : ℂ) * branch i u ∈ spectrum ℂ
        (A - branch i u • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
      Function.Injective (fun i => branch i u)) :
    ∀ᶠ u in Bornology.cobounded ℂ, ∀ i, branch i (conj u) = conj (branch i u) := by
  let d : n → ℝ := fun i => (s - b i)⁻¹
  have hd : Function.Injective d := by
    intro i j hij
    apply hb
    have heq := inv_injective hij
    linarith
  apply Complex.eventually_conj_eq_of_tendsto_affine_of_finite_matching
    branch d (fun i => -A i i / ((s - b i : ℝ) : ℂ)) hd
  · intro i
    simpa only [d, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using hlim i
  filter_upwards [(tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop R]
    with u hu i
  let M : Matrix n n ℂ :=
    -(Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹) * A) +
      u • Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹)
  have hM : ∀ j, branch j u ∈ spectrum ℂ M := fun j =>
    (mem_spectrum_inverse_diagonal_pencil_iff A b s hs u _).mpr ((hspec u hu).1 j)
  have hconjR : R < ‖conj u‖ := by simpa only [norm_conj] using hu
  have hc := conj_mem_spectrum_conjTranspose ((hspec (conj u) hconjR).1 i)
  have hD : (Matrix.diagonal (fun i => (b i : ℂ)) : Matrix n n ℂ).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
  have hstar : (A - branch i (conj u) • Matrix.diagonal (fun i => (b i : ℂ)))ᴴ =
      A - conj (branch i (conj u)) • Matrix.diagonal (fun i => (b i : ℂ)) := by
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hA.eq, hD.eq]
  rw [hstar] at hc
  have hc' : u - (s : ℂ) * conj (branch i (conj u)) ∈ spectrum ℂ
      (A - conj (branch i (conj u)) • Matrix.diagonal (fun i => (b i : ℂ))) := by
    simpa using hc
  have hmem : conj (branch i (conj u)) ∈ spectrum ℂ M :=
    (mem_spectrum_inverse_diagonal_pencil_iff A b s hs u _).mpr hc'
  rw [spectrum_eq_range_of_injective_mem_spectrum _ _ (hspec u hu).2 hM] at hmem
  obtain ⟨j, hj⟩ := hmem
  exact ⟨j, hj.symm⟩

open scoped Matrix.Norms.L2Operator in
/-- Constructed inverse branches of a Hermitian pencil have both the correct
upper-half-plane labels and Schwarz reflection on one common exterior domain.

atlas: trace-exponential-stahl (partial) -/
theorem exists_exterior_inverse_eigenvalue_branches_im_pos_iff_conj_eq
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ)
    (hb : Function.Injective b) (s : ℝ) (hs : ∀ i, s ≠ b i) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {u | R < ‖u‖} ∧
        Tendsto (fun u => branch i u - u / ((s - b i : ℝ) : ℂ))
          (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ)))) ∧
      (∀ u, R < ‖u‖ →
        (∀ i, u - (s : ℂ) * branch i u ∈ spectrum ℂ
          (A - branch i u • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
        Function.Injective (fun i => branch i u)) ∧
      (∀ u, R < ‖u‖ → 0 < u.im → ∀ i, 0 < (branch i u).im ↔ b i < s) ∧
      ∀ i u, R < ‖u‖ → branch i (conj u) = conj (branch i u) := by
  obtain ⟨R, hR, branch, hbranch, hspec, hlabel⟩ :=
    exists_exterior_inverse_eigenvalue_branches_im_pos_iff hA b hb s hs
  have href := eventually_exterior_inverse_eigenvalue_branches_conj_eq hA b hb s hs
    (fun i => (hbranch i).2) hspec
  obtain ⟨S, _, hS⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp href
  refine ⟨max R S, hR.trans_le (le_max_left _ _), branch, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hbranch i).1.mono (fun u hu => (le_max_left R S).trans_lt hu), (hbranch i).2⟩
  · intro u hu
    exact hspec u ((le_max_left R S).trans_lt hu)
  · intro u hu him i
    exact hlabel u ((le_max_left R S).trans_lt hu) him i
  · intro i u hu
    exact hS ((le_max_right R S).trans hu.le) i

end NLAlib
