import NLAlib.Matrix.Functions.SignNewtonCayley
import NLAlib.Matrix.Functions.SignCharacterization
import NLAlib.Matrix.Spectral.HurwitzCayley
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Newton convergence on the positive-stable half-plane

The actual Newton recursion has an exact Cayley-power formula. A
Hurwitz Cayley transform supplies spectral contraction for arbitrary
positive-stable matrices. Higham, Functions of Matrices, Chapter 5.
-/

noncomputable section
open Matrix Filter
open scoped Matrix.Norms.L2Operator Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The total Newton sign recursion. Theorems below certify that every
solved inverse is nonsingular on the spectrally separated domain. -/
def signNewtonIterate (A : Matrix n n ℂ) : ℕ → Matrix n n ℂ
  | 0 => A
  | k+1 => (2 : ℂ)⁻¹ • (signNewtonIterate A k+(signNewtonIterate A k)⁻¹)

/-- A convergent-power Cayley coordinate gives the exact actual Newton
iterate, with a doubly exponential power. -/
theorem signNewtonIterate_inverseCayley {G : Matrix n n ℂ}
    (hG : Tendsto (fun k : ℕ => G^k) atTop (𝓝 0)) (k : ℕ) :
    signNewtonIterate (inverseCayley G) k = inverseCayley (G^(2^k)) := by
  induction k with
  | zero => simp [signNewtonIterate]
  | succ k ih =>
    obtain ⟨hm, hp⟩ := isUnit_one_sub_and_add_matrix_pow hG (pow_pos (by norm_num : 0 < (2 : ℕ)) k)
    rw [signNewtonIterate, ih, half_smul_inverseCayley_add_inv _ hm hp,
      ← pow_mul, pow_succ]

/-- Inverse Cayley values converge to the identity as their coordinates
converge to zero. -/
theorem tendsto_inverseCayley_one {ι : Type*} {l : Filter ι} {G : ι → Matrix n n ℂ}
    (hG : Tendsto G l (𝓝 0)) : Tendsto (fun k => inverseCayley (G k)) l (𝓝 1) := by
  have hc : ContinuousAt (Ring.inverse : Matrix n n ℂ → Matrix n n ℂ) 1 :=
    NormedRing.inverse_continuousAt (1 : (Matrix n n ℂ)ˣ)
  have hd : Tendsto (fun k => (1-G k)⁻¹) l (𝓝 1) := by
    have hsub : Tendsto (fun k => (1 : Matrix n n ℂ)-G k) l (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds.sub hG)
    have h := hc.tendsto.comp hsub
    have hh : Tendsto (fun k => Ring.inverse (1-G k)) l (𝓝 1) := by
      simpa only [Function.comp_def, Ring.inverse_one] using h
    convert! hh using 1
    funext k
    exact Matrix.nonsing_inv_eq_ringInverse _
  have hadd : Tendsto (fun k => (1 : Matrix n n ℂ)+G k) l (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hG)
  simpa only [inverseCayley, mul_one] using hd.mul hadd

/-- A convergent-power Cayley coordinate yields convergence of the actual
Newton recursion to the identity. -/
theorem tendsto_signNewtonIterate_inverseCayley {G : Matrix n n ℂ}
    (hG : Tendsto (fun k : ℕ => G^k) atTop (𝓝 0)) :
    Tendsto (signNewtonIterate (inverseCayley G)) atTop (𝓝 1) := by
  convert! tendsto_inverseCayley_one (hG.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ)<2))) using 1
  funext k
  exact signNewtonIterate_inverseCayley hG k

/-- The positive-half-plane Cayley transform. -/
def positiveCayley (A : Matrix n n ℂ) : Matrix n n ℂ := (A-1)*(A+1)⁻¹

/-- Negating a positive-stable matrix is Hurwitz. -/
theorem IsPositiveStable.isHurwitz_neg {A : Matrix n n ℂ} (hA : IsPositiveStable A) :
    IsHurwitz (-A) := by
  intro z hz
  have hz' : -z ∈ spectrum ℂ A := by
    rw [← spectrum.neg_eq] at hz
    exact Set.mem_neg.mp hz
  have h := hA (-z) hz'
  simpa only [Complex.neg_re, neg_pos] using h

/-- The positive Cayley denominator is nonsingular. -/
theorem IsPositiveStable.isUnit_add_one {A : Matrix n n ℂ} (hA : IsPositiveStable A) :
    IsUnit (A+1) := by
  have h := (hA.isHurwitz_neg.isUnit_sub_pos_smul_one 1 zero_lt_one).neg
  simpa [sub_neg_eq_add, add_comm] using h

/-- The positive Cayley coordinate has spectral radius below one,
without a normality hypothesis. -/
theorem IsPositiveStable.spectralRadius_positiveCayley_lt_one {A : Matrix n n ℂ}
    (hA : IsPositiveStable A) : spectralRadius ℂ (positiveCayley A)<1 := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit_add_one
  have hi : (-(A+1))⁻¹ = -(A+1)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    simp only [neg_mul, mul_neg, neg_neg, Matrix.mul_nonsing_inv _ hd]
  have he : cayleyTransform (-A) 1 = positiveCayley A := by
    simp only [cayleyTransform, positiveCayley, RCLike.ofReal_one, one_smul]
    rw [show -A-1=-(A+1) by abel, hi, show -A+1=-(A-1) by abel]
    noncomm_ring
  rw [← he]
  exact hA.isHurwitz_neg.spectralRadius_cayleyTransform_lt_one 1 zero_lt_one

/-- The inverse Cayley formula reconstructs every positive-stable matrix. -/
theorem IsPositiveStable.inverseCayley_positiveCayley {A : Matrix n n ℂ}
    (hA : IsPositiveStable A) : inverseCayley (positiveCayley A)=A := by
  let R := bicommutantAlgebra A
  let a : R := ⟨A, self_mem_bicommutantAlgebra A⟩
  let e : R := bicommutantInverse (a+1)
  have he : (a+1)*e=1 := Subtype.ext (Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit_add_one))
  have hh := congrArg Subtype.val (CommRing.one_sub_cayley_mul a e he)
  have hc : (1-positiveCayley A)*A=1+positiveCayley A := hh
  have hu := isUnit_one_sub_of_matrix_spectralRadius_lt_one hA.spectralRadius_positiveCayley_lt_one
  rw [inverseCayley, ← hc, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.one_mul]

/-- Positive-stable Newton iterates have the exact Cayley formula and
are nonsingular at every step. -/
theorem IsPositiveStable.signNewtonIterate_eq_and_isUnit {A : Matrix n n ℂ}
    (hA : IsPositiveStable A) (k : ℕ) :
    signNewtonIterate A k=inverseCayley ((positiveCayley A)^(2^k)) ∧
      IsUnit (signNewtonIterate A k) := by
  have hp := tendsto_matrix_pow_zero_of_spectralRadius_lt_one hA.spectralRadius_positiveCayley_lt_one
  have he := signNewtonIterate_inverseCayley hp k
  rw [hA.inverseCayley_positiveCayley] at he
  refine ⟨he, ?_⟩
  rw [he]
  obtain ⟨hm, hp⟩ := isUnit_one_sub_and_add_matrix_pow hp (pow_pos (by norm_num : 0 < (2 : ℕ)) k)
  exact isUnit_inverseCayley hm hp

/-- Newton iteration converges to the identity for every positive-stable
matrix, including defective and nonnormal matrices. -/
theorem IsPositiveStable.tendsto_signNewtonIterate {A : Matrix n n ℂ}
    (hA : IsPositiveStable A) : Tendsto (signNewtonIterate A) atTop (𝓝 1) := by
  have h := tendsto_signNewtonIterate_inverseCayley
    (tendsto_matrix_pow_zero_of_spectralRadius_lt_one hA.spectralRadius_positiveCayley_lt_one)
  rwa [hA.inverseCayley_positiveCayley] at h

end NLAlib
