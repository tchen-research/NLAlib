import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.LinearCombination

/-!
# Matrices invariant under ensemble signs and permutations

Exact entry symmetries force a matrix on a tensor index to be a tensor with
the identity on the ensemble coordinate. The proof works over a field of
characteristic zero and includes the empty ensemble index.
Source: the finite signed-permutation averaging in arXiv:2108.06312v2, Lemma 5.2.
-/

noncomputable section
set_option autoImplicit false
open scoped Kronecker

namespace NLAlib

/-- The actual signed-permutation entry invariants are exactly a tensor
matrix with identity on the ensemble coordinate. The hypotheses are literal
entry symmetries; no trace, scalar-block, or spectral conclusion is assumed. -/
theorem exists_eq_kronecker_one_of_ensemble_entry_invariant
    {𝕜 d n : Type*} [Field 𝕜] [CharZero 𝕜] [DecidableEq n]
    (M : Matrix (d × n) (d × n) 𝕜)
    (hperm : ∀ (σ : Equiv.Perm n) (a b : d) (r s : n),
      M (a,σ r) (b,σ s) = M (a,r) (b,s))
    (hflip : ∀ (t : n) (a b : d) (r s : n),
      M (a,r) (b,s) = (if r=t then (-1 : 𝕜) else 1)*M (a,r) (b,s)*
        (if s=t then (-1 : 𝕜) else 1)) :
    ∃ Q : Matrix d d 𝕜, M = Q⊗ₖ(1 : Matrix n n 𝕜) := by
  classical
  rcases isEmpty_or_nonempty n with hn|hn
  · let : IsEmpty n := hn
    refine ⟨0,?_⟩
    ext ab ce
    exact isEmptyElim ab.2
  · let r₀ : n := Classical.choice hn
    let Q : Matrix d d 𝕜 := fun a b => M (a,r₀) (b,r₀)
    have hoff (a b : d) (r s : n) (hrs : r≠s) : M (a,r) (b,s)=0 := by
      have h := hflip r a b r s
      have h' : M (a,r) (b,s) = -M (a,r) (b,s) := by simpa [hrs.symm] using h
      linear_combination (1/2 : 𝕜)*h'
    have hdiag (a b : d) (r : n) : M (a,r) (b,r)=Q a b := by
      simpa only [Equiv.swap_apply_left] using hperm (Equiv.swap r₀ r) a b r₀ r₀
    refine ⟨Q,?_⟩
    ext ab ce
    rcases ab with ⟨a,r⟩
    rcases ce with ⟨b,s⟩
    by_cases hrs : r=s
    · subst s
      simpa only [Matrix.kronecker_apply,Matrix.one_apply_eq,mul_one] using hdiag a b r
    · simp only [Matrix.kronecker_apply,Matrix.one_apply_ne hrs,mul_zero,hoff a b r s hrs]

end NLAlib

end
