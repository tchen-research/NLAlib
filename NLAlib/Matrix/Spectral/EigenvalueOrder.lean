import NLAlib.Matrix.Spectral.CourantFischer
/-!
# Negation, strict subspace tests, and eigenvalue counts

Negating a real symmetric matrix reverses its sorted eigenvalues.
Strict Rayleigh tests on a subspace force strict eigenvalue bounds, and
positive or nonnegative subspaces bound the corresponding eigenvalue counts.
Source: Horn--Johnson (2013), Observation 4.2.5, Theorem 4.2.10,
Corollary 4.2.12. Atlas: `eigenvalue-order-and-counting`.
-/

noncomputable section

open Matrix Module

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Negation reverses and negates sorted eigenvalues, including repeated
eigenvalues. Horn--Johnson (2013), Observation 4.2.5.
atlas: eigenvalue-order-and-counting (partial) -/
theorem eigenvalues₀_neg {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) : hA.neg.eigenvalues₀ k = -hA.eigenvalues₀ k.rev := by
  apply le_antisymm
  · obtain ⟨S, hS, hAS⟩ := exists_submodule_eigenvalues₀_mul_le hA k.rev
    apply eigenvalues₀_le_of_forall_mem hA.neg k S
    · simp only [Fin.val_rev] at hS
      omega
    · intro x hx
      have h := hAS x hx
      simp only [Matrix.neg_mulVec, dotProduct_neg]
      nlinarith
  · obtain ⟨S, hS, hAS⟩ := exists_submodule_le_eigenvalues₀_mul hA k.rev
    apply le_eigenvalues₀_of_forall_mem hA.neg k S
    · simp only [Fin.val_rev] at hS
      omega
    · intro x hx
      have h := hAS x hx
      simp only [Matrix.neg_mulVec, dotProduct_neg]
      nlinarith

omit [DecidableEq n] in
/-- Subspaces whose dimensions sum to more than the ambient dimension
have a common nonzero vector. Dimension formula; helper for the strict
subspace tests in `eigenvalue-order-and-counting`. -/
theorem exists_ne_zero_mem_inf_of_card_lt_finrank_add
    (S W : Submodule ℝ (n → ℝ))
    (h : Fintype.card n < finrank ℝ S + finrank ℝ W) :
    ∃ x : n → ℝ, x ∈ S ∧ x ∈ W ∧ x ≠ 0 := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq S W
  have hsup : finrank ℝ (S ⊔ W : Submodule ℝ (n → ℝ)) ≤ Fintype.card n := by
    simpa [Module.finrank_fintype_fun_eq_card] using (S ⊔ W).finrank_le
  have hpos : 0 < finrank ℝ (S ⊓ W : Submodule ℝ (n → ℝ)) := by omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  exact ⟨x, x.property.1, x.property.2, fun h => hx (Subtype.ext h)⟩

/-- A strict lower Rayleigh bound on a subspace of dimension at least
`k+1` implies a strict bound for the `k`-th largest eigenvalue.
Horn--Johnson (2013), Theorem 4.2.10.
atlas: eigenvalue-order-and-counting (partial) -/
theorem lt_eigenvalues₀_of_forall_mem {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) (S : Submodule ℝ (n → ℝ))
    (hS : (k : ℕ) + 1 ≤ finrank ℝ S) {c : ℝ}
    (hAS : ∀ x ∈ S, x ≠ 0 → c * (x ⬝ᵥ x) < quadForm A x) :
    c < hA.eigenvalues₀ k := by
  obtain ⟨W, hW, hAW⟩ := exists_submodule_le_eigenvalues₀_mul hA k
  obtain ⟨x, hxS, hxW, hx0⟩ :=
    exists_ne_zero_mem_inf_of_card_lt_finrank_add S W (by omega)
  have h₁ := hAS x hxS hx0
  have h₂ := hAW x hxW
  have hxpos : 0 < x ⬝ᵥ x :=
    lt_of_le_of_ne (dotProduct_self_nonneg x)
      (fun h => hx0 (dotProduct_self_eq_zero.mp h.symm))
  have h : c * (x ⬝ᵥ x) < hA.eigenvalues₀ k * (x ⬝ᵥ x) := h₁.trans_le h₂
  nlinarith

/-- A strict upper Rayleigh bound on a subspace of codimension at most
`k` implies a strict bound for the `k`-th largest eigenvalue.
Horn--Johnson (2013), Theorem 4.2.10.
atlas: eigenvalue-order-and-counting (partial) -/
theorem eigenvalues₀_lt_of_forall_mem {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) (W : Submodule ℝ (n → ℝ))
    (hW : Fintype.card n ≤ finrank ℝ W + k) {c : ℝ}
    (hAW : ∀ x ∈ W, x ≠ 0 → quadForm A x < c * (x ⬝ᵥ x)) :
    hA.eigenvalues₀ k < c := by
  obtain ⟨S, hS, hAS⟩ := exists_submodule_eigenvalues₀_mul_le hA k
  obtain ⟨x, hxS, hxW, hx0⟩ :=
    exists_ne_zero_mem_inf_of_card_lt_finrank_add S W (by omega)
  have h₁ := hAS x hxS
  have h₂ := hAW x hxW hx0
  have hxpos : 0 < x ⬝ᵥ x :=
    lt_of_le_of_ne (dotProduct_self_nonneg x)
      (fun h => hx0 (dotProduct_self_eq_zero.mp h.symm))
  have h : hA.eigenvalues₀ k * (x ⬝ᵥ x) < c * (x ⬝ᵥ x) := h₁.trans_lt h₂
  nlinarith

/-- A nonnegative subspace forces at least its dimension many nonnegative
eigenvalues. Horn--Johnson (2013), Corollary 4.2.12.
atlas: eigenvalue-order-and-counting (partial) -/
theorem finrank_le_card_eigenvalues₀_nonneg {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (S : Submodule ℝ (n → ℝ)) (hAS : ∀ x ∈ S, 0 ≤ quadForm A x) :
    finrank ℝ S ≤ (Finset.univ.filter fun i => 0 ≤ hA.eigenvalues₀ i).card := by
  classical
  have hd : finrank ℝ S ≤ Fintype.card n := by
    simpa [Module.finrank_fintype_fun_eq_card] using S.finrank_le
  let f : Fin (finrank ℝ S) → {i : Fin (Fintype.card n) // 0 ≤ hA.eigenvalues₀ i} := fun i =>
    ⟨⟨i, i.isLt.trans_le hd⟩,
      le_eigenvalues₀_of_forall_mem hA _ S (Nat.succ_le_of_lt i.isLt)
        (by simpa [quadForm] using hAS)⟩
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun t => t.val.val) h
  simpa only [Fintype.card_fin, Fintype.card_subtype] using Fintype.card_le_of_injective f hf

/-- A positive subspace forces at least its dimension many positive
eigenvalues. Horn--Johnson (2013), Corollary 4.2.12.
atlas: eigenvalue-order-and-counting (partial) -/
theorem finrank_le_card_eigenvalues₀_pos {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (S : Submodule ℝ (n → ℝ)) (hAS : ∀ x ∈ S, x ≠ 0 → 0 < quadForm A x) :
    finrank ℝ S ≤ (Finset.univ.filter fun i => 0 < hA.eigenvalues₀ i).card := by
  classical
  have hd : finrank ℝ S ≤ Fintype.card n := by
    simpa [Module.finrank_fintype_fun_eq_card] using S.finrank_le
  let f : Fin (finrank ℝ S) → {i : Fin (Fintype.card n) // 0 < hA.eigenvalues₀ i} := fun i =>
    ⟨⟨i, i.isLt.trans_le hd⟩,
      lt_eigenvalues₀_of_forall_mem hA _ S (Nat.succ_le_of_lt i.isLt)
        (by simpa only [zero_mul] using hAS)⟩
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun t => t.val.val) h
  simpa only [Fintype.card_fin, Fintype.card_subtype] using Fintype.card_le_of_injective f hf

/-- Negation, strict subspace testing, and nonnegative/positive eigenvalue
counts hold for the actual sorted spectral list. Horn--Johnson (2013),
Observation 4.2.5, Theorem 4.2.10, Corollary 4.2.12.
atlas: eigenvalue-order-and-counting -/
theorem eigenvalue_order_and_counting {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (∀ k, hA.neg.eigenvalues₀ k = -hA.eigenvalues₀ k.rev) ∧
    (∀ (k : Fin (Fintype.card n)) (S : Submodule ℝ (n → ℝ)) (c : ℝ),
      (k : ℕ) + 1 ≤ finrank ℝ S →
      (∀ x ∈ S, x ≠ 0 → c * (x ⬝ᵥ x) < quadForm A x) → c < hA.eigenvalues₀ k) ∧
    (∀ S : Submodule ℝ (n → ℝ), (∀ x ∈ S, 0 ≤ quadForm A x) →
      finrank ℝ S ≤ (Finset.univ.filter fun i => 0 ≤ hA.eigenvalues₀ i).card) ∧
    (∀ S : Submodule ℝ (n → ℝ), (∀ x ∈ S, x ≠ 0 → 0 < quadForm A x) →
      finrank ℝ S ≤ (Finset.univ.filter fun i => 0 < hA.eigenvalues₀ i).card) :=
  ⟨eigenvalues₀_neg hA,
    fun k S c hS hAS => lt_eigenvalues₀_of_forall_mem hA k S hS (c := c) hAS,
    finrank_le_card_eigenvalues₀_nonneg hA, finrank_le_card_eigenvalues₀_pos hA⟩

end NLAlib
