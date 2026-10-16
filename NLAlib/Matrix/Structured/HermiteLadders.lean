import NLAlib.Matrix.Structured.HermiteIndices
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-! # Finite Hermite creation and annihilation matrices

The creation matrices raise total occupation by one and vanish on the top
degree. Their adjoints lower occupation. Every identity is finite-dimensional;
the canonical commutator is restricted to the interior cutoff.
Supports `gaussian-series-partial-transpose-norm`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset
open scoped Matrix
namespace NLAlib
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}

/-- A truncated creation matrix in the normalized occupation basis. Its
nonzero entries raise one occupation number and hence total degree. -/
def hermiteCreation (p : ℕ) (i : ι) : Matrix (HermiteIndex ι p) (HermiteIndex ι p) ℂ :=
  fun a b => if h : b.degree < p then
    if a = b.raise i h then (Real.sqrt (b.val i + 1) : ℂ) else 0 else 0

/-- The diagonal projector onto degrees strictly below the cutoff. -/
def hermiteInterior (p : ℕ) : Matrix (HermiteIndex ι p) (HermiteIndex ι p) ℂ :=
  diagonal fun a => if a.degree < p then 1 else 0

/-- The finite occupation-number matrix. -/
def hermiteNumber (p : ℕ) : Matrix (HermiteIndex ι p) (HermiteIndex ι p) ℂ :=
  diagonal fun a => (a.degree : ℂ)

/-- Creation vanishes on the top occupation degree. -/
theorem hermiteCreation_top (i : ι) (a b : HermiteIndex ι p) (hb : ¬ b.degree < p) :
    hermiteCreation p i a b = 0 := by
  simp [hermiteCreation, hb]

/-- Creation has exactly one possible nonzero output from an interior basis
vector, with the usual square-root occupation coefficient. -/
theorem hermiteCreation_apply_of_lt (i : ι) (a b : HermiteIndex ι p)
    (hb : b.degree < p) :
    hermiteCreation p i a b =
      if a = b.raise i hb then (Real.sqrt (b.val i + 1) : ℂ) else 0 := by
  simp [hermiteCreation, hb]

private theorem lower_degree_lt (a : HermiteIndex ι p) (i : ι) (hi : 0 < a.val i) :
    (a.lower i).degree < p := by
  have h := a.degree_lower i hi
  have ha := a.property
  change a.degree ≤ p at ha
  omega

/-- An entry of creation is equivalently read by lowering its output index.
This form includes the vacuum and automatically enforces the cutoff. -/
theorem hermiteCreation_apply (i : ι) (a b : HermiteIndex ι p) :
    hermiteCreation p i a b =
      if 0 < a.val i ∧ a.lower i = b then (Real.sqrt (a.val i) : ℂ) else 0 := by
  by_cases hb : b.degree < p
  · rw [hermiteCreation_apply_of_lt _ _ _ hb]
    by_cases hab : a = b.raise i hb
    · subst a
      simp
    · have hn : ¬ (0 < a.val i ∧ a.lower i = b) := by
        rintro ⟨ha, he⟩
        have he' := a.raise_lower i ha (lower_degree_lt a i ha)
        apply hab
        subst b
        exact he'.symm
      simp [hab, hn]
  · rw [hermiteCreation_top _ _ _ hb]
    have hn : ¬ (0 < a.val i ∧ a.lower i = b) := by
      rintro ⟨ha, he⟩
      apply hb
      rw [← he]
      exact lower_degree_lt a i ha
    simp [hn]

/-- Creation acts by the explicit lower-index formula on arbitrary vectors. -/
theorem hermiteCreation_mulVec (i : ι) (z : HermiteIndex ι p → ℂ)
    (a : HermiteIndex ι p) :
    (hermiteCreation p i *ᵥ z) a =
      if 0 < a.val i then (Real.sqrt (a.val i) : ℂ) * z (a.lower i) else 0 := by
  simp only [Matrix.mulVec, dotProduct, hermiteCreation_apply]
  by_cases ha : 0 < a.val i
  · simp [ha, eq_comm]
  · simp [ha]

/-- The adjoint creation matrix acts by a single permitted raising step. -/
theorem hermiteCreation_conjTranspose_mulVec (i : ι) (z : HermiteIndex ι p → ℂ)
    (a : HermiteIndex ι p) :
    ((hermiteCreation p i)ᴴ *ᵥ z) a =
      if h : a.degree < p then
        (Real.sqrt (a.val i + 1) : ℂ) * z (a.raise i h) else 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, hermiteCreation]
  by_cases ha : a.degree < p
  · simp [ha, eq_comm, apply_ite]
  · simp [ha]

/-- Truncated creation factors through the interior projection on its input. -/
theorem hermiteCreation_mul_interior (i : ι) :
    hermiteCreation p i * hermiteInterior p = hermiteCreation p i := by
  ext a b
  by_cases hb : b.degree < p
  · simp [hermiteInterior, Matrix.mul_diagonal, hb]
  · simp [hermiteInterior, Matrix.mul_diagonal, hermiteCreation, hb]

/-- An occupied coordinate of a bounded multiindex is strictly positive, so
its lowering coefficient squared is its occupation number. -/
theorem hermiteCreation_mul_conjTranspose_self (i : ι) :
    hermiteCreation p i * (hermiteCreation p i)ᴴ =
      diagonal (fun a : HermiteIndex ι p => (a.val i : ℂ)) := by
  ext a b
  simp only [Matrix.mul_apply, hermiteCreation_apply, Matrix.conjTranspose_apply]
  by_cases ha : 0 < a.val i
  · have hl := lower_degree_lt a i ha
    have hr := a.raise_lower i ha hl
    have hcoeff : (a.lower i).val i + 1 = a.val i := by
      simp only [HermiteIndex.lower_val, if_true]
      omega
    rw [Finset.sum_eq_single (a.lower i)]
    · simp only [ha, true_and, ↓reduceIte, and_true]
      by_cases hab : a = b
      · subst b
        simp only [ha, true_and, eq_self_iff_true, ↓reduceIte, Complex.star_def,
          Complex.conj_ofReal, Matrix.diagonal_apply_eq]
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
        simp
      · have hn : ¬ (0 < b.val i ∧ b.lower i = a.lower i) := by
          rintro ⟨hb, he⟩
          have hb' := b.raise_lower i hb (lower_degree_lt b i hb)
          have he' : b = a := by
            calc b = (b.lower i).raise i (lower_degree_lt b i hb) := hb'.symm
                 _ = (a.lower i).raise i hl := by congr 1
                 _ = a := hr
          exact hab he'.symm
        simp [hn, Matrix.diagonal_apply, hab]
    · intro c _ hc
      simp [ha, Ne.symm hc]
    · intro hn
      exact (hn (Finset.mem_univ _)).elim
  · have haz : a.val i = 0 := by omega
    simp [ha, Matrix.diagonal_apply, haz]

/-- Summed creation-annihilation energy is exactly the number matrix. -/
theorem sum_hermiteCreation_mul_conjTranspose :
    (∑ i : ι, hermiteCreation p i * (hermiteCreation p i)ᴴ) = hermiteNumber p := by
  simp only [hermiteCreation_mul_conjTranspose_self, hermiteNumber]
  ext a b
  by_cases hab : a = b
  · subst b
    simp [Matrix.sum_apply, Matrix.diagonal_apply, HermiteIndex.degree]
  · simp [Matrix.sum_apply, Matrix.diagonal_apply, hab]

private theorem conjTranspose_mul_apply_of_lt (i j : ι) (a b : HermiteIndex ι p)
    (hb : b.degree < p) :
    ((hermiteCreation p i)ᴴ * hermiteCreation p j) a b =
      star (hermiteCreation p i (b.raise j hb) a) *
        (Real.sqrt (b.val j + 1) : ℂ) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [hermiteCreation_apply_of_lt j _ b hb]
  simp [mul_ite]

private theorem mul_conjTranspose_apply (i j : ι) (a b : HermiteIndex ι p) :
    (hermiteCreation p j * (hermiteCreation p i)ᴴ) a b =
      if 0 < b.val i then hermiteCreation p j a (b.lower i) *
        (Real.sqrt (b.val i) : ℂ) else 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [hermiteCreation_apply i b]
  by_cases hb : 0 < b.val i
  · simp [hb, apply_ite, mul_ite, eq_comm]
  · simp [hb]

private theorem sqrt_nat_mul_self (n : ℕ) :
    (Real.sqrt (n : ℝ) : ℂ) * (Real.sqrt (n : ℝ) : ℂ) = (n : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp

private theorem sqrt_nat_add_one_mul_self (n : ℕ) :
    (Real.sqrt ((n : ℝ) + 1) : ℂ) * (Real.sqrt ((n : ℝ) + 1) : ℂ) = (n : ℂ) + 1 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  simp

/-- The finite canonical commutation relation, at interior input degree.
Restricting the input is essential: the unrestricted relation fails at the
top cutoff. -/
theorem hermiteCreation_commutator_apply (i j : ι) (a b : HermiteIndex ι p)
    (hb : b.degree < p) :
    ((hermiteCreation p i)ᴴ * hermiteCreation p j) a b =
      (if i = j then (1 : Matrix (HermiteIndex ι p) (HermiteIndex ι p) ℂ) a b else 0) +
        (hermiteCreation p j * (hermiteCreation p i)ᴴ) a b := by
  rw [conjTranspose_mul_apply_of_lt _ _ _ _ hb, mul_conjTranspose_apply]
  by_cases hij : i = j
  · subst j
    rw [hermiteCreation_apply]
    simp only [HermiteIndex.raise_val, if_true, HermiteIndex.lower_raise,
      Nat.lt_add_one_iff, Nat.zero_le, true_and, ↓reduceIte]
    by_cases hbi : 0 < b.val i
    · have hl := lower_degree_lt b i hbi
      rw [if_pos hbi, hermiteCreation_apply_of_lt _ _ _ hl, b.raise_lower i hbi hl]
      have hcoeff : ((b.lower i).val i : ℝ) + 1 = b.val i := by
        exact_mod_cast (show (b.lower i).val i + 1 = b.val i by
          simp only [HermiteIndex.lower_val, if_true]; omega)
      rw [hcoeff]
      by_cases hab : a = b
      · subst b
        simp only [Matrix.one_apply, if_pos rfl, apply_ite, if_true,
          Complex.star_def, Complex.conj_ofReal, Nat.cast_add, Nat.cast_one,
          sqrt_nat_mul_self, sqrt_nat_add_one_mul_self]
        ring
      · simp [hab, Ne.symm hab, Matrix.one_apply, apply_ite]
    · have hbi0 : b.val i = 0 := by omega
      by_cases hab : a = b
      · subst b
        simp [hbi, hbi0, Matrix.one_apply, apply_ite]
      · simp [hab, Ne.symm hab, hbi, Matrix.one_apply, apply_ite]
  · rw [if_neg hij, zero_add, hermiteCreation_apply]
    simp only [HermiteIndex.raise_val, if_neg hij]
    by_cases hbi : 0 < b.val i
    · have hl : (b.lower i).degree < p := (b.degree_lower_le i).trans_lt hb
      have hc := b.lower_raise_of_ne hij hb hl
      rw [if_pos hbi, hermiteCreation_apply_of_lt _ _ _ hl]
      simp only [hbi, true_and, hc, HermiteIndex.lower_val, if_neg (Ne.symm hij)]
      by_cases ha : a = (b.lower i).raise j hl
      · simp [ha, apply_ite, mul_comm]
      · simp [ha, Ne.symm ha, apply_ite]
    · simp [hbi]

/-- The finite canonical commutation identity as a matrix equation, with the
interior projector explicitly on the input. -/
theorem hermiteCreation_commutator (i j : ι) :
    ((hermiteCreation p i)ᴴ * hermiteCreation p j) * hermiteInterior p =
      ((if i = j then 1 else 0) + hermiteCreation p j * (hermiteCreation p i)ᴴ) *
        hermiteInterior p := by
  ext a b
  simp only [hermiteInterior, Matrix.mul_diagonal]
  by_cases hb : b.degree < p
  · simp only [hb, if_true, mul_one, Matrix.add_apply]
    rw [hermiteCreation_commutator_apply _ _ _ _ hb]
    split_ifs <;> rfl
  · simp [hb]

end NLAlib
