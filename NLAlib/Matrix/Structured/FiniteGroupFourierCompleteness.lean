import NLAlib.Matrix.Structured.FiniteGroupFourierBasic
import NLAlib.ForMathlib.RepresentationTheory.Subrepresentation
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Completeness of finite group matrix coefficients

An irreducible subrepresentation of the orthogonal complement would, by
evaluation at the identity, consist of listed matrix coefficients. This
contradiction proves spanning without assuming a dimension formula.
Source: finite Schur route for `gaussian-cayley-fourier-block-law`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset Representation
open scoped Matrix ComplexInnerProductSpace
namespace NLAlib

universe u v
variable {G : Type u} [Group G] [Fintype G]
  {P : Type v} {D : P → Type u} [∀ p, Fintype (D p)] [∀ p, DecidableEq (D p)]

/-- The counting inner product is invariant under actual left translation. -/
theorem inner_finiteGroupLeftRegularL2Representation (h : G)
    (f k : EuclideanSpace ℂ G) :
    ⟪finiteGroupLeftRegularL2Representation h f,
      finiteGroupLeftRegularL2Representation h k⟫ = ⟪f, k⟫ := by
  simp only [PiLp.inner_apply, finiteGroupLeftRegularL2Representation_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ (fun _ => rfl)

/-- Left translation of a coefficient acts on its second matrix index; the
first index is the multiplicity coordinate. -/
theorem finiteGroupLeftRegularL2Representation_coefficient
    (ρ : ∀ p, Representation ℂ G (D p → ℂ)) (h : G) (p : P) (a b : D p) :
    finiteGroupLeftRegularL2Representation h (finiteGroupCoefficient ρ ⟨p, a, b⟩) =
      ∑ c : D p, LinearMap.toMatrix' (ρ p h) c b •
        finiteGroupCoefficient ρ ⟨p, a, c⟩ := by
  ext g
  simp only [finiteGroupLeftRegularL2Representation_apply, finiteGroupCoefficient,
    PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    _root_.mul_inv_rev, inv_inv, map_mul, LinearMap.toMatrix'_mul, Matrix.mul_apply]
  exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)

/-- The span of actual matrix coefficients is an invariant subspace of the
counting-inner-product regular representation. -/
def finiteGroupCoefficientSubrepresentation
    (ρ : ∀ p, Representation ℂ G (D p → ℂ)) :
    Subrepresentation (finiteGroupLeftRegularL2Representation (G := G)) where
  toSubmodule := finiteGroupCoefficientSpan ρ
  apply_mem_toSubmodule h f hf := by
    apply Submodule.span_induction (p := fun f _ =>
      finiteGroupLeftRegularL2Representation h f ∈ finiteGroupCoefficientSpan ρ) ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨⟨p, a, b⟩, rfl⟩
      rw [finiteGroupLeftRegularL2Representation_coefficient]
      exact Submodule.sum_mem _ (fun c _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨⟨p, a, c⟩, rfl⟩))
    · simp
    · intro x y hx hy hix hiy
      simpa using Submodule.add_mem (finiteGroupCoefficientSpan ρ) hix hiy
    · intro c x hx hix
      simpa using Submodule.smul_mem (finiteGroupCoefficientSpan ρ) c hix

/-- The orthogonal complement of the coefficient span is invariant as well,
because left translations preserve the counting inner product. -/
def finiteGroupCoefficientOrthogonalSubrepresentation
    (ρ : ∀ p, Representation ℂ G (D p → ℂ)) :
    Subrepresentation (finiteGroupLeftRegularL2Representation (G := G)) where
  toSubmodule := (finiteGroupCoefficientSpan ρ)ᗮ
  apply_mem_toSubmodule h f hf := by
    intro k hk
    have hkin : finiteGroupLeftRegularL2Representation h⁻¹ k ∈
        finiteGroupCoefficientSpan ρ :=
      (finiteGroupCoefficientSubrepresentation ρ).apply_mem_toSubmodule h⁻¹ hk
    have hh := inner_finiteGroupLeftRegularL2Representation h
      (finiteGroupLeftRegularL2Representation h⁻¹ k) f
    rw [Representation.self_inv_apply] at hh
    exact hh.trans (hf _ hkin)

/-- Evaluation at the identity expresses every vector in the image of an
intertwiner from a listed representation as a finite linear combination of
its actual matrix coefficients. -/
theorem intertwiningMap_mem_finiteGroupCoefficientSpan
    (ρ : ∀ p, Representation ℂ G (D p → ℂ)) (p : P)
    (f : IntertwiningMap (ρ p) (finiteGroupLeftRegularL2Representation (G := G)))
    (v : D p → ℂ) : f v ∈ finiteGroupCoefficientSpan ρ := by
  let F : (D p → ℂ) →ₗ[ℂ] (G → ℂ) :=
    (WithLp.linearEquiv 2 ℂ (G → ℂ)).toLinearMap.comp f.toLinearMap
  have he (g : G) : f v g = F (ρ p g⁻¹ v) 1 := by
    have hh := congrArg (fun w : EuclideanSpace ℂ G => w 1)
      (Representation.IntertwiningMap.isIntertwining (ρ p)
        finiteGroupLeftRegularL2Representation f g⁻¹ v)
    simpa [F] using hh.symm
  have hsum : f v = ∑ a : D p, ∑ b : D p,
      (LinearMap.toMatrix' F 1 a * v b) • finiteGroupCoefficient ρ ⟨p, a, b⟩ := by
    ext g
    rw [he, ← LinearMap.toMatrix'_mulVec F]
    simp only [Matrix.mulVec, dotProduct, ← LinearMap.toMatrix'_mulVec (ρ p g⁻¹),
      finiteGroupCoefficient, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply,
      WithLp.ofLp_smul, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hsum]
  exact Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun b _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨p, a, b⟩, rfl⟩)))

/-- Completeness of the irreducible list forces the actual finite coefficient
span to be the whole regular space. No dimension-sum identity is assumed.
Source: finite Schur averaging and evaluation at the group identity.
atlas: gaussian-cayley-fourier-block-law (partial) -/
theorem finiteGroupCoefficientSpan_eq_top
    (ρ : ∀ p, Representation ℂ G (D p → ℂ)) (hcomplete : IsCompleteIrreducibleFamily ρ) :
    finiteGroupCoefficientSpan ρ = ⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  by_contra horth
  let S := finiteGroupCoefficientOrthogonalSubrepresentation ρ
  have hS : S ≠ ⊥ := by
    intro hh
    exact horth (congrArg Subrepresentation.toSubmodule hh)
  obtain ⟨T, hTS, hT⟩ := Subrepresentation.exists_irreducible_le S hS
  obtain ⟨p, ⟨e⟩⟩ := hcomplete T.toSubmodule T.toRepresentation hT
  let f : IntertwiningMap (ρ p) finiteGroupLeftRegularL2Representation :=
    T.subtype.comp e.toIntertwiningMap
  have hTM : T.toSubmodule ≤ finiteGroupCoefficientSpan ρ := by
    intro w hw
    obtain ⟨v, hv⟩ := e.toLinearEquiv.surjective ⟨w, hw⟩
    have hh := intertwiningMap_mem_finiteGroupCoefficientSpan ρ p f v
    have hfv : f v = w := congrArg (fun x : T.toSubmodule =>
      (x : EuclideanSpace ℂ G)) hv
    exact hfv ▸ hh
  have hzero : T.toSubmodule = ⊥ := by
    apply eq_bot_iff.mpr
    intro w hw
    have hm := hTM hw
    have ho := hTS hw
    have hz : ⟪w, w⟫ = (0 : ℂ) := ho w hm
    exact (inner_self_eq_zero.mp hz)
  have hTbot : T = ⊥ := Subrepresentation.toSubmodule_injective hzero
  exact ((Subrepresentation.isIrreducible_toRepresentation_iff T).mp hT).ne_bot hTbot

end NLAlib
