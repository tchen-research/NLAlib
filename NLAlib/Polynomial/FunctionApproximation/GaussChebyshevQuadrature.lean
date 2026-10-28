import NLAlib.Polynomial.Chebyshev.CosineBasis
import NLAlib.Polynomial.Quadrature.ChebyshevLobatto
import NLAlib.Polynomial.FunctionApproximation.ChebyshevPolynomial
import NLAlib.Polynomial.FunctionApproximation.JacksonKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# The explicit equal-weight Gauss-Chebyshev quadrature

The roots grid has `L` nodes and equal positive weights `π/L`. A finite
trigonometric identity proves exactness through degree `2L-1` directly.
-/

noncomputable section
open Real Polynomial Polynomial.Chebyshev MeasureTheory Finset
namespace NLAlib

/-- The actual `L`-node first-kind Gauss-Chebyshev rule. -/
def gaussChebyshevRule (L : ℕ) (f : ℝ → ℝ) : ℝ :=
  (π/L)*∑ j : Fin L,f (chebyshevZero L j)

private theorem sum_cos_gaussChebyshev_eq_zero {L k : ℕ}
    (hL : 0 < L) (hk : 0 < k) (hkL : k < 2*L) :
    (∑ j ∈ range L,cos ((k : ℝ)*((2*(j : ℝ)+1)*π/(2*L)))) = 0 := by
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  let a : ℝ := (k : ℝ)*π/L
  have ha : 0 < a/2 := by dsimp [a];positivity
  have haπ : a/2 < π := by
    dsimp [a]
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2),div_lt_iff₀ hLR]
    have hkR : (k : ℝ) < 2*L := by exact_mod_cast hkL
    nlinarith [pi_pos]
  have hsin : sin (a/2) ≠ 0 := (sin_pos_of_pos_of_lt_pi ha haπ).ne'
  have ht := sin_mul_sum_cos L a (a/2)
  have h₁ : (L : ℝ)*a/2 = (k : ℝ)*π/2 := by dsimp [a];field_simp
  have h₂ : ((L : ℝ)-1)*a/2+a/2 = (k : ℝ)*π/2 := by rw [show ((L : ℝ)-1)*a/2+a/2 = (L : ℝ)*a/2 by ring,h₁]
  rw [h₁,h₂] at ht
  have hs : sin ((k : ℝ)*π/2)*cos ((k : ℝ)*π/2) = 0 := by
    have h := sin_two_mul ((k : ℝ)*π/2)
    rw [show 2*((k : ℝ)*π/2) = (k : ℝ)*π by ring,sin_nat_mul_pi] at h
    linarith
  rw [hs] at ht
  have hsum := (mul_eq_zero.mp ht).resolve_left hsin
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  dsimp [a]
  ring

/-- All nonconstant frequencies below the first alias have zero quadrature sum. -/
theorem gaussChebyshevRule_eval_T {L k : ℕ} (hL : 0 < L) (hkL : k < 2*L) :
    gaussChebyshevRule L (T ℝ (k : ℤ)).eval = if k=0 then π else 0 := by
  by_cases hk : k=0
  · subst k
    simp only [gaussChebyshevRule,Nat.cast_zero,T_zero,eval_one,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_one]
    exact div_mul_cancel₀ π (by exact_mod_cast hL.ne' : (L : ℝ) ≠ 0)
  rw [if_neg hk,gaussChebyshevRule]
  have he : (∑ j : Fin L,(T ℝ (k : ℤ)).eval (chebyshevZero L j)) = 0 := by
    simp only [chebyshevZero,T_real_cos,Int.cast_natCast]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => cos ((k : ℝ)*((2*(j : ℝ)+1)*π/(2*L))))]
    exact sum_cos_gaussChebyshev_eq_zero hL (Nat.pos_of_ne_zero hk) hkL
  rw [he,mul_zero]

/-- The explicit positive root-grid rule integrates every polynomial of degree
strictly less than `2L`, with no assumed quadrature exactness. -/
theorem integral_eval_measureT_eq_gaussChebyshevRule {L : ℕ} (hL : 0 < L)
    {p : ℝ[X]} (hp : p.degree < (2*L : ℕ)) :
    (∫ x,p.eval x ∂measureT) = gaussChebyshevRule L p.eval := by
  let I := polynomialIntegral measureT hasPolynomialMoments_measureT
  let Q : ℝ[X] →ₗ[ℝ] ℝ :=
    { toFun := fun p => gaussChebyshevRule L p.eval
      map_add' := by intro p q;simp [gaussChebyshevRule,mul_add,Finset.sum_add_distrib]
      map_smul' := by
        intro c p
        simp only [gaussChebyshevRule,eval_smul,smul_eq_mul,RingHom.id_apply,← Finset.mul_sum]
        ring }
  have hT (k : ℕ) (hk : k<2*L) : I (T ℝ (k : ℤ)) = Q (T ℝ (k : ℤ)) := by
    change (∫ x,(T ℝ (k : ℤ)).eval x ∂measureT) = gaussChebyshevRule L (T ℝ (k : ℤ)).eval
    rw [gaussChebyshevRule_eval_T hL hk]
    by_cases hk0 : k=0
    · subst k
      simpa only [Nat.cast_zero,if_true] using integral_eval_T_real_measureT_zero
    · rw [if_neg hk0]
      exact integral_eval_T_real_measureT_of_ne_zero (by exact_mod_cast hk0)
  by_cases hp0 : p=0
  · simp [hp0,gaussChebyshevRule]
  have hp' : p.degree ≤ (2*L-1 : ℕ) := by
    rw [degree_eq_natDegree hp0] at hp ⊢
    have hd : p.natDegree < 2*L := by exact_mod_cast hp
    exact_mod_cast (show p.natDegree ≤ 2*L-1 by omega)
  obtain ⟨c,hc⟩ := exists_sum_smul_T_eq_of_degree_le hp'
  change I p = Q p
  rw [← hc,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul,map_smul,hT k (by have := mem_range.mp hk;omega)]

/-- Positive equal weights sum to the actual Chebyshev measure mass. -/
theorem gaussChebyshevRule_one {L : ℕ} (hL : 0 < L) :
    gaussChebyshevRule L (fun _ => 1) = π := by
  simpa using gaussChebyshevRule_eval_T hL (k := 0) (by omega)

/-- The finite root-grid basis is orthonormal through degree `L-1`. -/
theorem gaussChebyshevRule_normalized_mul {L j k : ℕ} (hL : 0 < L)
    (hj : j<L) (hk : k<L) :
    gaussChebyshevRule L (fun x => normalizedChebyshev j x * normalizedChebyshev k x) =
      if j=k then 1 else 0 := by
  let p := normalizedChebyshevPolynomial j * normalizedChebyshevPolynomial k
  have hd (l : ℕ) : (normalizedChebyshevPolynomial l).degree = (l : ℕ) := by
    rw [normalizedChebyshevPolynomial,degree_C_mul (normalizedChebyshevWeight_pos l).ne',degree_T]
    simp
  have hdeg : p.degree < (2*L : ℕ) := by
    apply lt_of_le_of_lt (degree_mul_le _ _)
    rw [hd,hd,← Nat.cast_add]
    exact_mod_cast (show j+k<2*L by omega)
  have he := integral_eval_measureT_eq_gaussChebyshevRule hL hdeg
  simp only [p,eval_mul,eval_normalizedChebyshevPolynomial] at he
  exact he.symm.trans (integral_normalizedChebyshev_mul j k)

end NLAlib
