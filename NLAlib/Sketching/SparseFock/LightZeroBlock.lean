/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightGradeNorm

/-!
# Vanishing of shared-leg operators on zero-light blocks

Partition of the literal shared-leg proof from sparse-Fock commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`.
The original `LightSectorConcrete` import re-exports this unchanged namespace.
Supports the `sparse-ose` moment proof.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
namespace NLAlib.SparseFock.LightSectorConcrete
open ParsevalFrame LocalOperator FiniteOperator ExternalOperator FiniteHilbert
variable {d m n ell : ℕ}

/-! ## The zero-light block -/

/-- Literal coordinate support in one fixed-heavy/fixed-light block.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def SupportedOnBlock (T : Finset (Site m n)) (ell : ℕ)
    (x : Fin d × Pattern m n → ℝ) : Prop :=
  ∀ a, ¬ InBlock T ell a.2 → x a = 0

/-- A nonzero annihilation entry requires an occupied input site.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem pAt_ne_zero_input_one (r : Fin m) (i : Fin n)
    (out inp : Pattern m n) (h : pAt r i out inp ≠ 0) :
    inp (r, i) = .one := by
  classical
  simp only [pAt, siteKernel] at h
  by_cases hoff : agreesOutsideSite (r, i) out inp
  · simp only [hoff, if_pos, pDestroy, ketBra] at h
    by_contra hne
    simp [hne] at h
  · simp [hoff] at h

/-- A zero-light block contains no occupied light site.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem no_light_site_of_block_zero {T : Finset (Site m n)}
    {p : Pattern m n} (hp : InBlock T 0 p) (s : Site m n) :
    p s ≠ .one := by
  intro hs
  have hempty : p.light = ∅ := Finset.card_eq_zero.mp hp.2
  have : s ∈ p.light := by simp [hs]
  simp [hempty] at this

/-- Every annihilation map kills a vector supported on a zero-light block.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Ctranspose_mulVec_eq_zero_of_zeroLight
    (F : Frame n d) (T : Finset (Site m n))
    (x : Fin d × Pattern m n → ℝ) (hx : SupportedOnBlock T 0 x)
    (r : Fin m) :
    (CMatrix F r).transpose.mulVec x = 0 := by
  funext p
  simp only [Matrix.mulVec, dotProduct, CMatrix_transpose_apply,
    Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro out _hout
  by_cases hb : InBlock T 0 out.2
  · apply mul_eq_zero.mpr
    left
    apply Finset.sum_eq_zero
    intro i _hi
    apply mul_eq_zero.mpr
    right
    by_contra hne
    exact no_light_site_of_block_zero hb (r, i)
      (pAt_ne_zero_input_one r i p out.2 hne)
  · rw [hx out hb, mul_zero]

/-- The concrete `G-hat` quadratic form is identically zero on the block with
no light sites, including all same-site terms.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ghat_mulVec_eq_zero_of_zeroLight
    (F : Frame n d) (T : Finset (Site m n))
    (x : Fin d × Pattern m n → ℝ) (hx : SupportedOnBlock T 0 x) :
    (ghat (m := m) F).mulVec x = 0 := by
  rw [ghat, Matrix.sum_mulVec]
  funext out
  simp only [Finset.sum_apply, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro r _hr
  rw [← Matrix.mulVec_mulVec]
  rw [Ctranspose_mulVec_eq_zero_of_zeroLight F T x hx r]
  simp

/-- The shared-leg quadratic form vanishes on vectors supported on a zero-light block.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem ghat_quadratic_eq_zero_of_zeroLight
    (F : Frame n d) (T : Finset (Site m n))
    (x : Fin d × Pattern m n → ℝ) (hx : SupportedOnBlock T 0 x) :
    quadratic (ghat (m := m) F) x = 0 := by
  rw [quadratic, ghat_mulVec_eq_zero_of_zeroLight F T x hx]
  simp

end NLAlib.SparseFock.LightSectorConcrete
