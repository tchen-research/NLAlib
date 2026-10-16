import NLAlib.Matrix.Perturbation.BauerFike
import NLAlib.Matrix.Functions.HermitianCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# A flat scalar remainder is flat on Hermitian matrices

Spectral variation for normal matrices transfers first-order scalar
vanishing at a finite spectrum to a uniform matrix remainder. This is
the analytic step in finite-Hermite Daleckii--Krein differentiation.
Tropp (2022), Theorem 14.13; toolkit derivations, formula (F8).
-/

noncomputable section
open Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A scalar function flat to first order on the spectrum has zero
Fréchet derivative along the real subspace of Hermitian matrices.
Only differentiability at the finitely many eigenvalues is needed. -/
theorem hasFDerivWithinAt_cfc_zero_of_spectral_vanishing
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {g : ℝ → ℝ}
    (hg : ∀ i, g (hA.eigenvalues i) = 0)
    (hg' : ∀ i, HasDerivAt g 0 (hA.eigenvalues i)) :
    HasFDerivWithinAt (fun B : Matrix n n ℂ => cfc g B)
      (0 : Matrix n n ℂ →L[ℝ] Matrix n n ℂ) {B | B.IsHermitian} A := by
  have hgA : cfc g A = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm ?_ (norm_nonneg _)
    apply norm_cfc_le le_rfl
    intro x hx
    obtain ⟨i, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
    simp only [hg i, norm_zero, le_refl]
  apply HasFDerivWithinAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hnear (i : n) : ∀ᶠ B : Matrix n n ℂ in 𝓝 A,
      ∀ x : ℝ, ‖x - hA.eigenvalues i‖ ≤ ‖B - A‖ →
        ‖g x‖ ≤ ε * ‖x - hA.eigenvalues i‖ := by
    have hs := (hg' i).isLittleO.bound hε
    simp only [hg i, smul_zero, sub_zero] at hs
    obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp hs
    have hn : ∀ᶠ B : Matrix n n ℂ in 𝓝 A, ‖B - A‖ < δ := by
      have hc : ContinuousAt (fun B : Matrix n n ℂ => ‖B - A‖) A := by fun_prop
      have ht := hc.tendsto.eventually (gt_mem_nhds (by simpa only [sub_self, norm_zero] using hδ))
      exact ht
    filter_upwards [hn] with B hB
    intro x hx
    exact hbound (by simpa only [dist_eq_norm] using hx.trans_lt hB)
  have hnearall : ∀ᶠ B : Matrix n n ℂ in 𝓝 A,
      ∀ i x, ‖x - hA.eigenvalues i‖ ≤ ‖B - A‖ →
        ‖g x‖ ≤ ε * ‖x - hA.eigenvalues i‖ := Filter.eventually_all.mpr hnear
  filter_upwards [hnearall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with B hB hherm
  simp only [hgA, sub_zero, zero_apply]
  apply norm_cfc_le (mul_nonneg hε.le (norm_nonneg _))
  intro x hx
  have hBH : B.IsHermitian := hherm
  have hxc : (x : ℂ) ∈ spectrum ℂ B := by
    rw [hBH.spectrum_eq_image_range]
    exact ⟨x, hBH.spectrum_real_eq_range_eigenvalues ▸ hx, rfl⟩
  have hnormal : A * A.conjTranspose = A.conjTranspose * A := by rw [hA.eq]
  obtain ⟨z, hz, hdist⟩ := exists_mem_spectrum_distance_le_norm_perturbation_of_normal
    (E := B - A) hnormal (by simpa only [add_sub_cancel] using hxc)
  rw [hA.spectrum_eq_image_range] at hz
  obtain ⟨y, ⟨i, rfl⟩, rfl⟩ := hz
  have hd : ‖x - hA.eigenvalues i‖ ≤ ‖B - A‖ := by
    change ‖(hA.eigenvalues i : ℂ) - (x : ℂ)‖ ≤ ‖B - A‖ at hdist
    have heq : (hA.eigenvalues i : ℂ) - (x : ℂ) = ((hA.eigenvalues i - x : ℝ) : ℂ) :=
      (Complex.ofReal_sub _ _).symm
    rw [heq, Complex.norm_real] at hdist
    simpa only [Real.norm_eq_abs, abs_sub_comm, specNorm_eq_norm] using hdist
  exact (hB i x hd).trans (mul_le_mul_of_nonneg_left hd hε.le)

end NLAlib
