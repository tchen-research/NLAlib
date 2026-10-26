import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Gram--Schmidt depends only on the input prefix

Changing vectors after position `j` leaves the `j`-th orthogonalized and normalized
vectors unchanged. This permits finite-history implementations of a Gram--Schmidt
construction indexed by all natural numbers. Candidate for Mathlib's GramSchmidtOrtho file.
-/

namespace InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Gram--Schmidt at index `j` only depends on input vectors at indices at most `j`. -/
theorem gramSchmidt_eq_of_eq_prefix {f g : ℕ → E} {j : ℕ}
    (h : ∀ i ≤ j, f i = g i) : gramSchmidt 𝕜 f j = gramSchmidt 𝕜 g j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rw [gramSchmidt_def, gramSchmidt_def, h j le_rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i < j := Finset.mem_Iio.mp hi
    rw [ih i hij (fun k hk => h k (hk.trans hij.le))]

/-- Normalized Gram--Schmidt also depends only on the input prefix, including a zero
orthogonalized vector at breakdown. -/
theorem gramSchmidtNormed_eq_of_eq_prefix {f g : ℕ → E} {j : ℕ}
    (h : ∀ i ≤ j, f i = g i) : gramSchmidtNormed 𝕜 f j = gramSchmidtNormed 𝕜 g j := by
  simp only [gramSchmidtNormed, gramSchmidt_eq_of_eq_prefix h]

end InnerProductSpace
