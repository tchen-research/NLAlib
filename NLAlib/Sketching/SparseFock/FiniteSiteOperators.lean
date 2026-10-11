/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.BandInventory
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Finite sparse-Fock site kernels

One-site and distinct-pair kernels act on the actual finite pattern basis, with transpose, product, and occupation-shift identities.
Ported from `SparseFockFormal.FiniteSiteOperators` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock

namespace FiniteOperator

open LocalOperator BandInventory

variable {m n : ℕ}

/-- A finite matrix on the sparse-Fock pattern basis.

Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev FockOp (m n : ℕ) := Matrix (Pattern m n) (Pattern m n) ℝ

/-- The integer pattern grade sums the occupation weights of all physical sites.
Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def gradeZ (p : Pattern m n) : ℤ :=
  ∑ s, weightZ (p s)

/-- Two patterns agree outside a site when every other site has equal level.
Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def agreesOutsideSite (s : Site m n) (out inp : Pattern m n) : Prop :=
  ∀ x, x ≠ s → out x = inp x

/-- Two patterns agree outside a marked pair when every other site has equal level.
Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def agreesOutsidePair (s t : Site m n) (out inp : Pattern m n) : Prop :=
  ∀ x, x ≠ s → x ≠ t → out x = inp x

/-- Agreement outside one site is symmetric.
Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem agreesOutsideSite_symm {s : Site m n} {out inp : Pattern m n} :
    agreesOutsideSite s out inp ↔ agreesOutsideSite s inp out := by
  constructor <;> intro h x hx <;> exact (h x hx).symm

/-- Agreement outside a site pair is symmetric.
Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem agreesOutsidePair_symm {s t : Site m n} {out inp : Pattern m n} :
    agreesOutsidePair s t out inp ↔ agreesOutsidePair s t inp out := by
  constructor <;> intro h x hxs hxt <;> exact (h x hxs hxt).symm

/-- Swapping the marked pair leaves outside agreement unchanged.
Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem agreesOutsidePair_swap {s t : Site m n} {out inp : Pattern m n} :
    agreesOutsidePair s t out inp ↔ agreesOutsidePair t s out inp := by
  constructor <;> intro h x hxt hxs <;> exact h x hxs hxt

/-- Lift a local matrix to one specified site of the finite tensor-product basis.

Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def siteKernel (s : Site m n) (A : LocalOperator.Op) : FockOp m n := by
  classical
  exact fun out inp =>
    if agreesOutsideSite s out inp then A (out s) (inp s) else 0

/-- Lift two local matrices to two specified sites.

Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def pairKernel (s t : Site m n) (A B : LocalOperator.Op) : FockOp m n := by
  classical
  exact fun out inp =>
    if agreesOutsidePair s t out inp then A (out s) (inp s) * B (out t) (inp t) else 0

/-- Transposing a one-site lifted kernel transposes its local matrix.
Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem transpose_siteKernel (s : Site m n) (A : LocalOperator.Op) :
    (siteKernel s A).transpose = siteKernel s A.transpose := by
  ext out inp
  simp only [Matrix.transpose_apply]
  by_cases h : agreesOutsideSite s inp out
  · have h' : agreesOutsideSite s out inp := agreesOutsideSite_symm.mpr h
    simp [siteKernel, h, h']
  · have h' : ¬ agreesOutsideSite s out inp := by
      intro hs
      exact h (agreesOutsideSite_symm.mp hs)
    simp [siteKernel, h, h']

/-- Transposing a two-site lifted kernel transposes its two local matrices.
Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem transpose_pairKernel (s t : Site m n) (A B : LocalOperator.Op) :
    (pairKernel s t A B).transpose = pairKernel s t A.transpose B.transpose := by
  ext out inp
  simp only [Matrix.transpose_apply]
  by_cases h : agreesOutsidePair s t inp out
  · have h' : agreesOutsidePair s t out inp := agreesOutsidePair_symm.mpr h
    simp [pairKernel, h, h']
  · have h' : ¬ agreesOutsidePair s t out inp := by
      intro hs
      exact h (agreesOutsidePair_symm.mp hs)
    simp [pairKernel, h, h']

/-- Swapping the two marked sites and local factors preserves their lifted pair kernel.
Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pairKernel_swap (s t : Site m n) (A B : LocalOperator.Op) :
    pairKernel s t A B = pairKernel t s B A := by
  ext out inp
  by_cases h : agreesOutsidePair s t out inp
  · have h' : agreesOutsidePair t s out inp := agreesOutsidePair_swap.mp h
    simp [pairKernel, h, h', mul_comm]
  · have h' : ¬ agreesOutsidePair t s out inp := by
      intro hs
      exact h (agreesOutsidePair_swap.mpr hs)
    simp [pairKernel, h, h']

/-- Patterns agreeing outside one site differ in grade exactly by that site's occupation change.
Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem gradeZ_sub_eq_site {s : Site m n} {out inp : Pattern m n}
    (h : agreesOutsideSite s out inp) :
    gradeZ out - gradeZ inp = weightZ (out s) - weightZ (inp s) := by
  classical
  rw [gradeZ, gradeZ, ← Finset.sum_sub_distrib]
  calc
    (∑ x, (weightZ (out x) - weightZ (inp x))) =
        ∑ x, if x = s then weightZ (out s) - weightZ (inp s) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = s
          · subst x
            simp
          · have heq := h x hx
            simp [hx, heq]
    _ = weightZ (out s) - weightZ (inp s) := by simp

/-- Patterns agreeing outside a distinct pair differ in grade by the two site occupation changes.
Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem gradeZ_sub_eq_pair {s t : Site m n} {out inp : Pattern m n}
    (hst : s ≠ t) (h : agreesOutsidePair s t out inp) :
    gradeZ out - gradeZ inp =
      (weightZ (out s) - weightZ (inp s)) +
      (weightZ (out t) - weightZ (inp t)) := by
  classical
  rw [gradeZ, gradeZ, ← Finset.sum_sub_distrib]
  calc
    (∑ x, (weightZ (out x) - weightZ (inp x))) =
        ∑ x, if x = s then weightZ (out s) - weightZ (inp s)
          else if x = t then weightZ (out t) - weightZ (inp t) else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hxs : x = s
            · subst x
              simp
            · by_cases hxt : x = t
              · subst x
                simp [hxs]
              · have heq := h x hxs hxt
                simp [hxs, hxt, heq]
    _ = ∑ x, ((if x = s then weightZ (out s) - weightZ (inp s) else 0) +
        (if x = t then weightZ (out t) - weightZ (inp t) else 0)) := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hxs : x = s
          · subst x
            simp [hst]
          · by_cases hxt : x = t
            · subst x
              simp [hxs]
            · simp [hxs, hxt]
    _ = (weightZ (out s) - weightZ (inp s)) +
        (weightZ (out t) - weightZ (inp t)) := by simp [Finset.sum_add_distrib]

/-- A finite pattern matrix changes total grade by `δ` on every nonzero entry.

Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def Homogeneous (δ : ℤ) (K : FockOp m n) : Prop :=
  ∀ ⦃out inp : Pattern m n⦄, K out inp ≠ 0 → gradeZ out = gradeZ inp + δ

/-- A one-site lifted kernel inherits its local matrix's grade shift.
Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem siteKernel_homogeneous {δ : ℤ} {A : LocalOperator.Op}
    (hA : LocalOperator.Homogeneous δ A) (s : Site m n) :
    Homogeneous δ (siteKernel s A) := by
  intro out inp hnonzero
  by_cases hoff : agreesOutsideSite s out inp
  · have hlocal : A (out s) (inp s) ≠ 0 := by
      simpa [siteKernel, hoff] using hnonzero
    have hw := hA hlocal
    have hd := gradeZ_sub_eq_site hoff
    omega
  · exact (hnonzero (by simp [siteKernel, hoff])).elim

/-- A distinct-pair lifted kernel has the sum of its local factors' grade shifts.
Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pairKernel_homogeneous {δ ε : ℤ} {A B : LocalOperator.Op}
    (hA : LocalOperator.Homogeneous δ A)
    (hB : LocalOperator.Homogeneous ε B)
    {s t : Site m n} (hst : s ≠ t) :
    Homogeneous (δ + ε) (pairKernel s t A B) := by
  intro out inp hnonzero
  by_cases hoff : agreesOutsidePair s t out inp
  · have hprod : A (out s) (inp s) * B (out t) (inp t) ≠ 0 := by
      simpa [pairKernel, hoff] using hnonzero
    have hAlocal : A (out s) (inp s) ≠ 0 := (mul_ne_zero_iff.mp hprod).1
    have hBlocal : B (out t) (inp t) ≠ 0 := (mul_ne_zero_iff.mp hprod).2
    have hwA := hA hAlocal
    have hwB := hB hBlocal
    have hd := gradeZ_sub_eq_pair hst hoff
    omega
  · exact (hnonzero (by simp [pairKernel, hoff])).elim

/-- A typed two-leg word is lifted to its literal pair kernel on the finite pattern basis.
Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def wordKernel (s t : Site m n) (w : Word) : FockOp m n :=
  pairKernel s t w.1.op w.2.op

/-- A distinct-site word kernel has its recorded total word degree.
Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem wordKernel_homogeneous (w : Word) {s t : Site m n} (hst : s ≠ t) :
    Homogeneous w.degree (wordKernel s t w) := by
  simpa [wordKernel, Word.degree] using
    pairKernel_homogeneous w.1.op_homogeneous w.2.op_homogeneous hst

/-- Matrix transpose agrees with the adjoint word after swapping the ordered sites.

Source: ported from `SparseFockFormal.FiniteSiteOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem transpose_wordKernel (s t : Site m n) (w : Word) :
    (wordKernel s t w).transpose = wordKernel t s w.orderedAdjoint := by
  rw [wordKernel, transpose_pairKernel, pairKernel_swap]
  rcases w with ⟨a, b⟩
  simp [wordKernel, Word.orderedAdjoint, Leg.transpose_op]

end FiniteOperator

end NLAlib.SparseFock
