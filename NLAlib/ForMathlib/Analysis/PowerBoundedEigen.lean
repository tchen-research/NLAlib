import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Module

/-!
# Peripheral eigenspaces of operators with bounded power orbits

A nontrivial length-two Jordan chain at a unit-modulus eigenvalue forces
linear orbit growth. Bounded power orbits therefore exclude such chains,
and all generalized eigenvectors there are ordinary eigenvectors.
-/

noncomputable section
open Module

namespace NLAlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A bounded power orbit excludes a nontrivial length-two Jordan chain
at a unit-modulus eigenvalue. Source: Horn–Johnson (2013), §5.6;
helper for the power-boundedness criterion. -/
theorem eq_zero_of_bounded_pow_orbit_of_jordan_chain
    (f : Module.End ℂ E) {μ : ℂ} (hμ : ‖μ‖ = 1) {x y : E}
    (hx : f x = μ • x) (hy : f y = μ • y + x)
    (hb : ∃ C : ℝ, ∀ k : ℕ, ‖(f ^ k) y‖ ≤ C) : x = 0 := by
  have hμne : μ ≠ 0 := by intro h; simp [h] at hμ
  let u := μ⁻¹ • x
  have hfu : f u = μ • u := by simp only [u, map_smul, hx, smul_smul, mul_comm]
  have hfy : f y = μ • (y + u) := by
    change f y = μ • (y + μ⁻¹ • x)
    rw [hy, smul_add, smul_smul, mul_inv_cancel₀ hμne, one_smul]
  have hpow (k : ℕ) : (f ^ k) y = μ ^ k • (y + (k : ℂ) • u) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, map_add, map_smul, hfy, hfu]
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      module
  obtain ⟨C, hC⟩ := hb
  have hbound (k : ℕ) : (k : ℝ) * ‖u‖ ≤ C + ‖y‖ := by
    have hnorm : ‖y + (k : ℂ) • u‖ ≤ C := by
      have h := hC k
      simpa only [hpow, norm_smul, norm_pow, hμ, one_pow, one_mul] using h
    calc
      (k : ℝ) * ‖u‖ = ‖(k : ℂ) • u‖ := by
        conv_rhs => rw [norm_smul, Complex.norm_natCast]
      _ = ‖(y + (k : ℂ) • u) - y‖ := by congr 1; module
      _ ≤ ‖y + (k : ℂ) • u‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ C + ‖y‖ := add_le_add hnorm le_rfl
  have hu : u = 0 := by
    by_contra hune
    have hpos := norm_pos_iff.mpr hune
    obtain ⟨k, hk⟩ := exists_nat_gt ((C + ‖y‖) / ‖u‖)
    have hlt : C + ‖y‖ < (k : ℝ) * ‖u‖ := (div_lt_iff₀ hpos).mp hk
    exact (not_lt_of_ge (hbound k)) hlt
  have hxu : x = μ • u := by simp only [u, smul_smul, mul_inv_cancel₀ hμne, one_smul]
  rw [hxu, hu, smul_zero]

/-- Bounded power orbits force every unit-modulus generalized eigenspace
to equal the ordinary eigenspace. Source: Horn–Johnson (2013), §5.6;
the induction excludes Jordan chains without a Jordan normal form. -/
theorem maxGenEigenspace_eq_eigenspace_of_bounded_pow_orbits
    (f : Module.End ℂ E) (hb : ∀ x : E, ∃ C : ℝ, ∀ k : ℕ, ‖(f ^ k) x‖ ≤ C)
    {μ : ℂ} (hμ : ‖μ‖ = 1) : f.maxGenEigenspace μ = f.eigenspace μ := by
  let N := f - μ • (1 : Module.End ℂ E)
  have hstep (z : E) (hz : N (N z) = 0) : N z = 0 := by
    apply eq_zero_of_bounded_pow_orbit_of_jordan_chain f hμ (y := z)
    · have h := sub_eq_zero.mp hz
      exact h
    · change f z = μ • z + (f z - μ • z)
      abel
    · exact hb z
  have hpower (k : ℕ) (z : E) (hz : (N ^ k) z = 0) : N z = 0 := by
    induction k generalizing z with
    | zero =>
      have hz0 : z = 0 := by simpa using hz
      rw [hz0, map_zero]
    | succ k ih =>
      apply hstep z
      apply ih (N z)
      simpa only [pow_succ, Module.End.mul_apply] using hz
  apply le_antisymm _ Module.End.eigenspace_le_maxGenEigenspace
  intro z hz
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace f μ z).mp hz
  apply Module.End.mem_eigenspace_iff.mpr
  exact sub_eq_zero.mp (hpower k z hk)

/-- An eigenvalue with a bounded nonzero eigenvector orbit has modulus at
most one. Source: Horn–Johnson (2013), §5.6; powers of a scalar larger than
one are unbounded. -/
theorem norm_eigenvalue_le_one_of_bounded_pow_orbit
    (f : Module.End ℂ E) {μ : ℂ} {x : E} (hx : f.HasEigenvector μ x)
    (hb : ∃ C : ℝ, ∀ k : ℕ, ‖(f ^ k) x‖ ≤ C) : ‖μ‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := hb
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx.2
  have hpow (k : ℕ) : ‖μ‖ ^ k ≤ C / ‖x‖ := by
    apply (le_div_iff₀ hxpos).mpr
    simpa only [hx.pow_apply, norm_smul, norm_pow] using hC k
  by_contra h
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C / ‖x‖) (lt_of_not_ge h)
  exact (not_lt_of_ge (hpow k)) hk

end NLAlib
