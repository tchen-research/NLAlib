import NLAlib.Matrix.Structured.FiniteGroupFourierBasic
import NLAlib.ForMathlib.RepresentationTheory.MatrixCoefficients
import NLAlib.Matrix.Subspaces.Projections

/-! # Orthonormal finite group Fourier coefficients

Actual Schur averaging proves the normalized coefficient rows and Fourier
columns orthonormal before completeness or any dimension formula is used.
Source: finite Schur route for `gaussian-cayley-fourier-block-law`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset Representation
open scoped Matrix
namespace NLAlib

universe u v
variable {G : Type u} [Group G] [Fintype G]
  {P : Type v} {D : P → Type u} [∀ p, Fintype (D p)] [∀ p, DecidableEq (D p)]
  [∀ p, Nonempty (D p)] [Fintype P] [DecidableEq P]
  (ρ : ∀ p, Representation ℂ G (D p → ℂ)) [∀ p, Representation.IsIrreducible (ρ p)]

/-- The normalized coefficient transform has orthonormal rows, derived from
native irreducibility and pairwise inequivalence by finite Schur averaging.
atlas: gaussian-cayley-fourier-block-law (partial) -/
theorem finiteGroupCoefficientTransform_mul_conjTranspose
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q))) :
    finiteGroupCoefficientTransform ρ * (finiteGroupCoefficientTransform ρ)ᴴ = 1 := by
  have hN : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  ext ⟨p, a, b⟩ ⟨q, c, e⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    finiteGroupCoefficientTransform, star_mul, Complex.star_def, Complex.conj_ofReal]
  have hfactor : (∑ g : G,
      ((Real.sqrt ((Fintype.card (D p) : ℝ) / Fintype.card G) : ℂ) *
        LinearMap.toMatrix' (ρ p g) a b) *
      (star (LinearMap.toMatrix' (ρ q g) c e) *
        (Real.sqrt ((Fintype.card (D q) : ℝ) / Fintype.card G) : ℂ))) =
      (Real.sqrt ((Fintype.card (D p) : ℝ) / Fintype.card G) : ℂ) *
        (Real.sqrt ((Fintype.card (D q) : ℝ) / Fintype.card G) : ℂ) *
        ∑ g : G, LinearMap.toMatrix' (ρ p g) a b *
          star (LinearMap.toMatrix' (ρ q g) c e) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun g _ => by ring)
  refine hfactor.trans ?_
  by_cases hpq : p = q
  · subst q
    have hself := Representation.matrix_coefficients_orthogonality_self
      (ρ p) (hu p) a c b e
    have hsum : (∑ g : G, LinearMap.toMatrix' (ρ p g) a b *
        star (LinearMap.toMatrix' (ρ p g) c e)) =
        (Fintype.card G : ℂ) *
          (if b = e then (Fintype.card (D p) : ℂ)⁻¹ *
            (if a = c then 1 else 0) else 0) := by
      calc
        _ = (Fintype.card G : ℂ) * ((Fintype.card G : ℂ)⁻¹ *
            ∑ g : G, LinearMap.toMatrix' (ρ p g) a b *
              star (LinearMap.toMatrix' (ρ p g) c e)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul]
        _ = _ := congrArg ((Fintype.card G : ℂ) * ·) hself
    rw [hsum]
    have hs : (Real.sqrt ((Fintype.card (D p) : ℝ) / Fintype.card G) : ℂ) ^ 2 =
        (Fintype.card (D p) : ℂ) / Fintype.card G := by
      simp only [← Complex.ofReal_pow,
        Real.sq_sqrt (show 0 ≤ (Fintype.card (D p) : ℝ) / Fintype.card G by positivity),
        Complex.ofReal_div, Complex.ofReal_natCast]
    by_cases hac : a = c <;> by_cases hbe : b = e
    · subst c; subst e
      simp only [if_pos rfl, mul_one, Matrix.one_apply, Prod.mk.injEq, and_self,
        Sigma.mk.inj_iff, heq_eq_eq, and_true, dite_true]
      rw [← pow_two, hs]
      field_simp
      simp
    · simp [hac, hbe, Matrix.one_apply]
    · simp [hac, hbe, Matrix.one_apply]
    · simp [hac, hbe, Matrix.one_apply]
  · have hcross := Representation.matrix_coefficients_orthogonality_of_inequivalent
      (ρ q) (ρ p) (hne q p (Ne.symm hpq)) (hu q) a b c e
    have hz : (∑ g : G, LinearMap.toMatrix' (ρ p g) a b *
        star (LinearMap.toMatrix' (ρ q g) c e)) = 0 :=
      (mul_eq_zero.mp hcross).resolve_left (inv_ne_zero hN)
    rw [hz]
    simp [Matrix.one_apply, hpq]

/-- The inverse-element Fourier matrix has orthonormal columns, including the
correct order of its multiplicity and representation indices.
atlas: gaussian-cayley-fourier-block-law (partial) -/
theorem finiteGroupFourierMatrix_hasOrthonormalCols
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q))) :
    HasOrthonormalCols (finiteGroupFourierMatrix ρ) := by
  have hF := finiteGroupCoefficientTransform_mul_conjTranspose ρ hu hne
  change (finiteGroupFourierMatrix ρ)ᴴ * finiteGroupFourierMatrix ρ = 1
  ext s t
  have hh := congrArg (fun M : Matrix (FiniteGroupFourierIndex D)
    (FiniteGroupFourierIndex D) ℂ => M t s) hF
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at hh ⊢
  rw [show (∑ g : G, star (finiteGroupFourierMatrix ρ g s) *
      finiteGroupFourierMatrix ρ g t) =
      ∑ g : G, finiteGroupCoefficientTransform ρ t g *
        star (finiteGroupCoefficientTransform ρ s g) from ?_]
  · simpa only [Matrix.one_apply, eq_comm] using hh
  · exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => mul_comm _ _)

end NLAlib
