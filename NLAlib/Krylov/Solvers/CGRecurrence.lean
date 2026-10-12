import NLAlib.Krylov.Solvers.CG
/-!
# The Hestenes–Stiefel recurrence for conjugate gradients

The conjugate-gradient *method* is the predicate `IsCGIterate` (`NLAlib.Krylov.Solvers.CG`); this file
adds the *algorithm* that computes it, as a total recursion on a state `(x, r, p)`
(`docs/ALGORITHM_CONVENTIONS.md` §1, `docs/KRYLOV_DEFINITIONS.md` §3.6):

```
α_k = r_kᵀ r_k / p_kᵀ A p_k,   x_{k+1} = x_k + α_k p_k,   r_{k+1} = r_k − α_k A p_k,
β_k = r_{k+1}ᵀ r_{k+1} / r_kᵀ r_k,   p_{k+1} = r_{k+1} + β_k p_k,   p_0 = r_0 = c − A x₀.
```

Lean's `x / 0 = 0` keeps the recursion total: once `r_k = 0` the state is `(x_k, 0, 0)` from the
next step on (`cgRecurrence_add_of_r_eq_zero`). For positive definite `A` the recursion never
breaks down before it has solved the system: the only vanishing denominators occur at `r_k = 0`,
which happens exactly from the grade `ν(A, r₀)` on. CG has no separate success predicate: the
hypothesis `A.PosDef` plays that role.

## Main declarations

* `CGState`, `cgStep`, `cgInit`, `cgRecurrence A c x₀ k = (cgStep A)^[k] (cgInit A c x₀)`.
* Hypothesis-free facts (proved): the residual identity `cgRecurrence_r_eq`
  (`r_k = c − A x_k`), the Krylov memberships `cgRecurrence_mem_krylovSpace`
  (`x_k − x₀ ∈ K_k`, `r_k, p_k ∈ K_{k+1}`), freezing after a zero residual,
  `span_cgRecurrence_p_eq_span_r`, and no breakdown before the grade
  `cgRecurrence_r_ne_zero_of_lt_krylovGrade`.
* The classical invariants for `A ≻ 0` (scaffolds): `dotProduct_cgRecurrence_r_eq_zero`
  (`r_iᵀ r_j = 0`) and `dotProduct_cgRecurrence_p_mulVec_eq_zero` (`p_iᵀ A p_j = 0`).
* From them (proved): `span_cgRecurrence_r`, `span_cgRecurrence_p`
  (`span r_{<k} = span p_{<k} = K_k(A, r₀)`), Galerkin orthogonality, the realisation theorem
  `isCGIterate_cgRecurrence` (`x_k` is a `k`-th CG iterate for every `k`), and termination
  `cgRecurrence_x_eq_of_krylovGrade_le`, `cgRecurrence_r_eq_zero_of_krylovGrade_le`.

Source: Hestenes–Stiefel (1952); Trefethen–Bau (1997) [`tb97`], Alg. 38.1 and Thm 38.1;
Saad (2011) [`saad11`], §6.7, Props 6.19–6.20; Greenbaum (1997) [`greenbaum97`], §2.1.
Atlas: `cg-recurrence`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

/-- The state of the conjugate-gradient recursion: iterate `x`, residual `r`, search direction
`p`. Source: Trefethen–Bau (1997) [`tb97`], Alg. 38.1. Atlas: `cg-recurrence`. -/
structure CGState (n : Type*) where
  /-- The iterate `x_k`. -/
  x : n → ℝ
  /-- The residual `r_k` (equal to `c − A x_k`, `cgRecurrence_r_eq`). -/
  r : n → ℝ
  /-- The search direction `p_k`. -/
  p : n → ℝ

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- One Hestenes–Stiefel step: `α = rᵀr / pᵀAp`, `x' = x + α p`, `r' = r − α A p`,
`β = r'ᵀr' / rᵀr`, `p' = r' + β p`. Total: with `x / 0 = 0` a zero residual gives `α = β = 0`
(`cgStep_of_r_eq_zero`). Source: Trefethen–Bau (1997) [`tb97`], Alg. 38.1; Saad (2011)
[`saad11`], Alg. 6.18. Atlas: `cg-recurrence`. -/
def cgStep (A : Matrix n n ℝ) (s : CGState n) : CGState n :=
  let α := (s.r ⬝ᵥ s.r) / (s.p ⬝ᵥ (A *ᵥ s.p))
  let r' := s.r - α • (A *ᵥ s.p)
  ⟨s.x + α • s.p, r', r' + ((r' ⬝ᵥ r') / (s.r ⬝ᵥ s.r)) • s.p⟩

/-- The initial state `(x₀, r₀, r₀)` with `r₀ = c − A x₀`. Source: Trefethen–Bau (1997)
[`tb97`], Alg. 38.1. Atlas: `cg-recurrence`. -/
def cgInit (A : Matrix n n ℝ) (c x₀ : n → ℝ) : CGState n :=
  ⟨x₀, c - A *ᵥ x₀, c - A *ᵥ x₀⟩

/-- The **conjugate-gradient recursion**: the state after `k` Hestenes–Stiefel steps from
`(x₀, r₀, r₀)`, as `Nat.iterate`. `(cgRecurrence A c x₀ k).x` is the CG iterate `x_k`
(`isCGIterate_cgRecurrence`). Source: Trefethen–Bau (1997) [`tb97`], Alg. 38.1; Hestenes–Stiefel
(1952). Atlas: `cg-recurrence`. -/
def cgRecurrence (A : Matrix n n ℝ) (c x₀ : n → ℝ) (k : ℕ) : CGState n :=
  (cgStep A)^[k] (cgInit A c x₀)

variable {A : Matrix n n ℝ} {c x₀ : n → ℝ}

omit [DecidableEq n] in
/-- The recursion starts at `(x₀, r₀, r₀)`. Atlas: `cg-recurrence`. -/
@[simp] theorem cgRecurrence_zero (A : Matrix n n ℝ) (c x₀ : n → ℝ) :
    cgRecurrence A c x₀ 0 = cgInit A c x₀ := rfl

omit [DecidableEq n] in
/-- One more step of the recursion. Atlas: `cg-recurrence`. -/
theorem cgRecurrence_succ (A : Matrix n n ℝ) (c x₀ : n → ℝ) (k : ℕ) :
    cgRecurrence A c x₀ (k + 1) = cgStep A (cgRecurrence A c x₀ k) :=
  Function.iterate_succ_apply' _ _ _

omit [DecidableEq n] in
/-- **The residual identity** `r_k = c − A x_k`, for every `A` and every `k` (no hypothesis).
Source: Trefethen–Bau (1997) [`tb97`], Alg. 38.1 (the update of `r` is the update of
`c − A x`). Helper for `cg-recurrence`. -/
theorem cgRecurrence_r_eq (A : Matrix n n ℝ) (c x₀ : n → ℝ) (k : ℕ) :
    (cgRecurrence A c x₀ k).r = c - A *ᵥ (cgRecurrence A c x₀ k).x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [cgRecurrence_succ]
    simp only [cgStep, ih, Matrix.mulVec_add, Matrix.mulVec_smul]
    abel

/-- **Krylov memberships**, for every `A` (no hypothesis): `x_k − x₀ ∈ K_k(A, r₀)` and
`r_k, p_k ∈ K_{k+1}(A, r₀)`. Induction on `k` with `mulVec_mem_krylovSpace_succ`.
Source: Trefethen–Bau (1997) [`tb97`], Thm 38.1 (the inclusion half).
Helper for `cg-recurrence`. -/
theorem cgRecurrence_mem_krylovSpace (A : Matrix n n ℝ) (c x₀ : n → ℝ) (k : ℕ) :
    (cgRecurrence A c x₀ k).x - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) k ∧
      (cgRecurrence A c x₀ k).r ∈ krylovSpace A (c - A *ᵥ x₀) (k + 1) ∧
        (cgRecurrence A c x₀ k).p ∈ krylovSpace A (c - A *ᵥ x₀) (k + 1) := by
  set K := krylovSpace A (c - A *ᵥ x₀)
  induction k with
  | zero =>
    refine ⟨by simp [cgInit], self_mem_krylovSpace_succ _ _ 0,
      self_mem_krylovSpace_succ _ _ 0⟩
  | succ k ih =>
    obtain ⟨hx, hr, hp⟩ := ih
    have hmono : K (k + 1) ≤ K (k + 2) := krylovSpace_mono _ _ (by omega)
    have hAp : A *ᵥ (cgRecurrence A c x₀ k).p ∈ K (k + 2) := mulVec_mem_krylovSpace_succ _ _ hp
    have hr' : (cgRecurrence A c x₀ k).r -
        ((cgRecurrence A c x₀ k).r ⬝ᵥ (cgRecurrence A c x₀ k).r /
          ((cgRecurrence A c x₀ k).p ⬝ᵥ (A *ᵥ (cgRecurrence A c x₀ k).p))) •
          (A *ᵥ (cgRecurrence A c x₀ k).p) ∈ K (k + 2) :=
      Submodule.sub_mem _ (hmono hr) (Submodule.smul_mem _ _ hAp)
    rw [cgRecurrence_succ]
    refine ⟨?_, hr', Submodule.add_mem _ hr' (Submodule.smul_mem _ _ (hmono hp))⟩
    simp only [cgStep]
    rw [add_sub_right_comm]
    exact Submodule.add_mem _ (krylovSpace_mono _ _ (by omega) hx) (Submodule.smul_mem _ _ hp)

omit [DecidableEq n] in
/-- **A zero residual freezes the state**: if `r = 0` then `cgStep A s = (x, 0, 0)` (`α = 0`
and `β = 0/0 = 0`). Atlas: `cg-recurrence` (totality). -/
theorem cgStep_of_r_eq_zero (A : Matrix n n ℝ) {s : CGState n} (hs : s.r = 0) :
    cgStep A s = ⟨s.x, 0, 0⟩ := by
  simp [cgStep, hs]

omit [DecidableEq n] in
/-- After a zero residual the recursion is constant: if `r_k = 0` then for every `m ≥ 1` the
state `k + m` is `(x_k, 0, 0)`. Atlas: `cg-recurrence` (totality). -/
theorem cgRecurrence_add_of_r_eq_zero (A : Matrix n n ℝ) (c x₀ : n → ℝ) {k : ℕ}
    (hk : (cgRecurrence A c x₀ k).r = 0) (m : ℕ) :
    cgRecurrence A c x₀ (k + (m + 1)) = ⟨(cgRecurrence A c x₀ k).x, 0, 0⟩ := by
  induction m with
  | zero => rw [cgRecurrence_succ, cgStep_of_r_eq_zero A hk]
  | succ m ih =>
    rw [show k + (m + 1 + 1) = k + (m + 1) + 1 by omega, cgRecurrence_succ, ih,
      cgStep_of_r_eq_zero A rfl]

omit [DecidableEq n] in
/-- A zero residual forces a zero search direction: `r_k = 0 → p_k = 0` (for `k = 0`, `p_0 = r_0`;
otherwise `β_{k−1} = 0`). No hypothesis on `A`. Atlas: `cg-recurrence` (totality). -/
theorem cgRecurrence_p_eq_zero_of_r_eq_zero (A : Matrix n n ℝ) (c x₀ : n → ℝ) {k : ℕ}
    (hk : (cgRecurrence A c x₀ k).r = 0) : (cgRecurrence A c x₀ k).p = 0 := by
  cases k with
  | zero => simpa [cgInit] using hk
  | succ k =>
    rw [cgRecurrence_succ] at hk ⊢
    simp only [cgStep] at hk ⊢
    rw [hk]
    simp

/-- **No breakdown before the grade**: `r_k ≠ 0` for `k < ν(A, r₀)`, for every `A` (no
definiteness needed). With `cgRecurrence_r_eq_zero_of_krylovGrade_le` this says that for `A ≻ 0`
the recursion stops (`r_k = 0`, the only case in which a denominator vanishes, since
`pᵀAp = 0 ↔ p = 0`) exactly at the grade. Source: Trefethen–Bau (1997) [`tb97`], Thm 38.1 (the
hypothesis "`r_{k−1} ≠ 0`" is automatic below the grade); Saad (2003) [`saad03`], Prop. 6.3.
Proof: if `r_k = 0` then `r₀ = A (x_k − x₀) ∈ A K_k`, so `K_{k+1} ≤ A K_k` and
`min (k+1) ν ≤ min k ν` (`finrank_krylovSpace`), forcing `ν ≤ k`.
atlas: cg-recurrence (partial) -/
theorem cgRecurrence_r_ne_zero_of_lt_krylovGrade (A : Matrix n n ℝ) (c x₀ : n → ℝ) {k : ℕ}
    (hk : k < krylovGrade A (c - A *ᵥ x₀)) : (cgRecurrence A c x₀ k).r ≠ 0 := by
  intro h0
  set r₀ := c - A *ᵥ x₀
  have hx := (cgRecurrence_mem_krylovSpace A c x₀ k).1
  have hr₀ : A *ᵥ ((cgRecurrence A c x₀ k).x - x₀) = r₀ := by
    have h := cgRecurrence_r_eq A c x₀ k
    rw [h0, eq_comm, sub_eq_zero] at h
    rw [Matrix.mulVec_sub, ← h]
  have hle : krylovSpace A r₀ (k + 1) ≤ (krylovSpace A r₀ k).map A.mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    induction i using Fin.cases with
    | zero => exact ⟨_, hx, by simpa using hr₀⟩
    | succ j =>
      refine ⟨(A ^ (j : ℕ)) *ᵥ r₀, pow_mulVec_mem_krylovSpace A r₀ j.isLt, ?_⟩
      simp [pow_succ', Matrix.mulVec_mulVec]
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_map_le A.mulVecLin (krylovSpace A r₀ k)
  rw [finrank_krylovSpace] at h1 h2
  omega

/-! ### The classical invariants (positive definite `A`) -/

/-- SCAFFOLD: cg-recurrence
**Residuals are mutually orthogonal**: for `A ≻ 0`, `r_iᵀ r_j = 0` for `i ≠ j` (all `i, j`; after
the grade the residuals are `0`). Source: Trefethen–Bau (1997) [`tb97`], Thm 38.1 (orthogonality
of the residuals); Saad (2011) [`saad11`], Prop. 6.19. Proof sketch: joint strong induction on
`k` for `∀ j < k, r_kᵀ r_j = 0 ∧ p_kᵀ A p_j = 0`, using `r_j ∈ span p_{≤j}` and
`p_j ∈ span r_{≤j}` (from the recurrence), the symmetry `uᵀ A v = vᵀ A u`, the identities
`r_kᵀ p_k = r_kᵀ r_k` and `p_kᵀ A p_k = r_kᵀ A p_k`, and `A p_j = (r_j − r_{j+1}) / α_j` when
`α_j ≠ 0`. Degenerate steps: `pᵀAp = 0 → p = 0` (`Matrix.PosDef.dotProduct_mulVec_pos`) and then
`r = 0` (from `r_kᵀ p_k = r_kᵀ r_k`), after which the state freezes
(`cgRecurrence_add_of_r_eq_zero`). Deferred: a long case analysis, not hard mathematics. -/
theorem dotProduct_cgRecurrence_r_eq_zero (hA : A.PosDef) {i j : ℕ} (hij : i ≠ j) :
    (cgRecurrence A c x₀ i).r ⬝ᵥ (cgRecurrence A c x₀ j).r = 0 := by
  sorry

/-- SCAFFOLD: cg-recurrence
**Search directions are `A`-conjugate**: for `A ≻ 0`, `p_iᵀ A p_j = 0` for `i ≠ j`.
Source: Trefethen–Bau (1997) [`tb97`], Thm 38.1 (conjugacy of the search directions); Saad
(2011) [`saad11`], Prop. 6.20. Proof sketch: the joint induction of
`dotProduct_cgRecurrence_r_eq_zero` (the two invariants are proved together; for `j < k`,
`p_{k+1}ᵀ A p_j = r_{k+1}ᵀ A p_j + β_k p_kᵀ A p_j`, the first term is
`r_{k+1}ᵀ (r_j − r_{j+1}) / α_j = 0`, and for `j = k` the choice of `β_k` cancels the two terms). -/
theorem dotProduct_cgRecurrence_p_mulVec_eq_zero (hA : A.PosDef) {i j : ℕ} (hij : i ≠ j) :
    (cgRecurrence A c x₀ i).p ⬝ᵥ (A *ᵥ (cgRecurrence A c x₀ j).p) = 0 := by
  sorry

/-- **The residuals span the Krylov space**: for `A ≻ 0` and every `k`,
`span (r_0, …, r_{k−1}) = K_k(A, r₀)`. Source: Trefethen–Bau (1997) [`tb97`], Thm 38.1,
eq. (38.2); Saad (2011) [`saad11`], Prop. 6.20. Proof: `≤` from `cgRecurrence_mem_krylovSpace`;
for `k ≤ ν` the residuals are nonzero (`cgRecurrence_r_ne_zero_of_lt_krylovGrade`) and
orthogonal (`dotProduct_cgRecurrence_r_eq_zero`), hence independent, and both sides have
dimension `k` (`finrank_krylovSpace`); for `k ≥ ν`, `K_k = K_ν`
(`krylovSpace_eq_of_krylovGrade_le`). Deviation: stated for every `k`, not only while `r_k ≠ 0`.
atlas: cg-recurrence (partial) -/
theorem span_cgRecurrence_r (hA : A.PosDef) (k : ℕ) :
    Submodule.span ℝ (Set.range fun i : Fin k => (cgRecurrence A c x₀ i).r) =
      krylovSpace A (c - A *ᵥ x₀) k := by
  set ν := krylovGrade A (c - A *ᵥ x₀)
  have hle : ∀ m, Submodule.span ℝ (Set.range fun i : Fin m => (cgRecurrence A c x₀ i).r) ≤
      krylovSpace A (c - A *ᵥ x₀) m := fun m => by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact krylovSpace_mono _ _ (show (i : ℕ) + 1 ≤ m from i.isLt)
      (cgRecurrence_mem_krylovSpace A c x₀ i).2.1
  have heq : ∀ m ≤ ν, Submodule.span ℝ (Set.range fun i : Fin m => (cgRecurrence A c x₀ i).r) =
      krylovSpace A (c - A *ᵥ x₀) m := fun m hm => by
    have hli : LinearIndependent ℝ (fun i : Fin m => (cgRecurrence A c x₀ i).r) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg j
      have h := congrArg (fun v => (cgRecurrence A c x₀ j).r ⬝ᵥ v) hg
      simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, dotProduct_zero] at h
      rw [Finset.sum_eq_single j (fun i _ hij => by
        rw [dotProduct_cgRecurrence_r_eq_zero hA (fun h => hij (Fin.ext h.symm)), mul_zero])
        (by simp)] at h
      have hne : (cgRecurrence A c x₀ j).r ⬝ᵥ (cgRecurrence A c x₀ j).r ≠ 0 := fun h0 =>
        cgRecurrence_r_ne_zero_of_lt_krylovGrade A c x₀ (lt_of_lt_of_le j.isLt hm)
          (dotProduct_self_eq_zero.1 h0)
      exact (mul_eq_zero.1 h).resolve_right hne
    refine Submodule.eq_of_le_of_finrank_eq (hle m) ?_
    rw [finrank_span_eq_card hli, Fintype.card_fin, finrank_krylovSpace, min_eq_left hm]
  rcases le_total k ν with h | h
  · exact heq k h
  · refine le_antisymm (hle k) ?_
    rw [krylovSpace_eq_of_krylovGrade_le _ _ h, ← heq ν le_rfl]
    exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Fin.castLE h i, rfl⟩)

omit [Fintype n] [DecidableEq n] in
/-- `span {x} ⊔ S = span {y} ⊔ S` when `x − y ∈ S`. -/
private lemma span_singleton_sup_eq_of_sub_mem {S : Submodule ℝ (n → ℝ)} {x y : n → ℝ}
    (h : x - y ∈ S) : (ℝ ∙ x) ⊔ S = (ℝ ∙ y) ⊔ S := by
  have key : ∀ {u v : n → ℝ}, u - v ∈ S → (ℝ ∙ u) ⊔ S ≤ (ℝ ∙ v) ⊔ S := fun {u v} huv =>
    sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 (by
      rw [show u = v + (u - v) by abel]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v))
        (Submodule.mem_sup_right huv))) le_sup_right
  exact le_antisymm (key h) (key (by rw [← neg_sub]; exact S.neg_mem h))

omit [Fintype n] [DecidableEq n] in
/-- `span (g 0, …, g k) = span {g k} ⊔ span (g 0, …, g (k−1))` for `ℕ`-indexed families. -/
private lemma span_range_fin_succ (g : ℕ → n → ℝ) (k : ℕ) :
    Submodule.span ℝ (Set.range fun i : Fin (k + 1) => g i) =
      (ℝ ∙ g k) ⊔ Submodule.span ℝ (Set.range fun i : Fin k => g i) := by
  have hr : ∀ m, Set.range (fun i : Fin m => g i) = g '' Set.Iio m := fun m => by
    ext x
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨j, j.isLt, rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩
  rw [hr, hr, show Set.Iio (k + 1) = insert k (Set.Iio k) by ext; simp,
    Set.image_insert_eq, Submodule.span_insert]

omit [DecidableEq n] in
/-- **Search directions and residuals span the same spaces**: `span (p_0, …, p_{k−1}) =
span (r_0, …, r_{k−1})` for every `A` and `k` (no hypothesis). Induction on `k` with
`p_k − r_k = β_{k−1} p_{k−1}`. Source: Trefethen–Bau (1997) [`tb97`], Thm 38.1, eq. (38.2).
Helper for `cg-recurrence`. -/
theorem span_cgRecurrence_p_eq_span_r (A : Matrix n n ℝ) (c x₀ : n → ℝ) (k : ℕ) :
    Submodule.span ℝ (Set.range fun i : Fin k => (cgRecurrence A c x₀ i).p) =
      Submodule.span ℝ (Set.range fun i : Fin k => (cgRecurrence A c x₀ i).r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [span_range_fin_succ (fun i => (cgRecurrence A c x₀ i).p),
      span_range_fin_succ (fun i => (cgRecurrence A c x₀ i).r), ih]
    refine span_singleton_sup_eq_of_sub_mem ?_
    cases k with
    | zero => simp [cgInit]
    | succ k =>
      rw [cgRecurrence_succ]
      simp only [cgStep, add_sub_cancel_left]
      refine Submodule.smul_mem _ _ ?_
      rw [← ih, span_range_fin_succ (fun i => (cgRecurrence A c x₀ i).p)]
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)

/-- **The search directions span the Krylov space**: for `A ≻ 0` and every `k`,
`span (p_0, …, p_{k−1}) = K_k(A, r₀)`. Source: Trefethen–Bau (1997) [`tb97`], Thm 38.1,
eq. (38.2). Proof: `span_cgRecurrence_p_eq_span_r` and `span_cgRecurrence_r`.
atlas: cg-recurrence (partial) -/
theorem span_cgRecurrence_p (hA : A.PosDef) (k : ℕ) :
    Submodule.span ℝ (Set.range fun i : Fin k => (cgRecurrence A c x₀ i).p) =
      krylovSpace A (c - A *ᵥ x₀) k := by
  rw [span_cgRecurrence_p_eq_span_r, span_cgRecurrence_r hA]

/-- **Galerkin orthogonality of the recursion**: for `A ≻ 0`, `r_k ⟂ K_k(A, r₀)`.
Source: Trefethen–Bau (1997) [`tb97`], Thm 38.1; Saad (2011) [`saad11`], Prop. 6.19.
Proof: `K_k = span r_{<k}` (`span_cgRecurrence_r`) and `r_k ⟂ r_j` for `j < k`
(`dotProduct_cgRecurrence_r_eq_zero`). Helper for `cg-recurrence`. -/
theorem dotProduct_cgRecurrence_r_eq_zero_of_mem (hA : A.PosDef) {k : ℕ} {z : n → ℝ}
    (hz : z ∈ krylovSpace A (c - A *ᵥ x₀) k) : z ⬝ᵥ (cgRecurrence A c x₀ k).r = 0 := by
  rw [← span_cgRecurrence_r hA k] at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact dotProduct_cgRecurrence_r_eq_zero hA (Nat.ne_of_lt i.isLt)
  | zero => exact zero_dotProduct _
  | add y z _ _ hy hz => rw [add_dotProduct, hy, hz, add_zero]
  | smul a y _ hy => rw [smul_dotProduct, hy, smul_zero]

/-- **The recursion realises the CG iterate**: for positive definite `A`, every `c`, `x₀` and
every `k`, `x_k = (cgRecurrence A c x₀ k).x` is a `k`-th CG iterate (the `A`-norm-error minimiser
over `x₀ + K_k(A, r₀)`). No grade hypothesis: after the grade the state is frozen at the
solution. Source: Trefethen–Bau (1997) [`tb97`], Thm 38.1–38.2; Saad (2011) [`saad11`], §6.7;
KRYLOV_DEFINITIONS §3.6. Proof: `cgRecurrence_mem_krylovSpace`, `cgRecurrence_r_eq` and
Galerkin orthogonality `dotProduct_cgRecurrence_r_eq_zero_of_mem`, then
`isCGIterate_of_forall_dotProduct_eq_zero`. Uses atlas `cg-convergence` (the predicate).
Deviation: the brief's form had `k ≤ krylovGrade A r₀`; the statement holds for all `k`.
atlas: cg-recurrence -/
theorem isCGIterate_cgRecurrence (hA : A.PosDef) (c x₀ : n → ℝ) (k : ℕ) :
    IsCGIterate A c x₀ k (cgRecurrence A c x₀ k).x := by
  refine isCGIterate_of_forall_dotProduct_eq_zero hA.isHermitian
    (fun i => (hA.eigenvalues_pos i).le) (cgRecurrence_mem_krylovSpace A c x₀ k).1
    fun z hz => ?_
  rw [← cgRecurrence_r_eq]
  exact dotProduct_cgRecurrence_r_eq_zero_of_mem hA hz

/-- **Finite termination of the recursion**: for `A ≻ 0` and `A x⋆ = c`, `x_k = x⋆` once
`k ≥ ν(A, r₀)`. Source: Trefethen–Bau (1997) [`tb97`], Thm 38.1 (CG converges in at most `n`
steps); Saad (2003) [`saad03`], §6.7. Proof: `isCGIterate_cgRecurrence` and
`eq_of_isCGIterate_of_krylovGrade_le` (atlas `cg-finite-termination`).
atlas: cg-recurrence (partial) -/
theorem cgRecurrence_x_eq_of_krylovGrade_le (hA : A.PosDef) {xs : n → ℝ} (hxs : A *ᵥ xs = c)
    {k : ℕ} (hk : krylovGrade A (c - A *ᵥ x₀) ≤ k) : (cgRecurrence A c x₀ k).x = xs :=
  eq_of_isCGIterate_of_krylovGrade_le hA hxs hk (isCGIterate_cgRecurrence hA c x₀ k)

/-- **The residual vanishes from the grade on**: for `A ≻ 0`, `r_k = 0` when
`k ≥ ν(A, r₀)`. Source: Trefethen–Bau (1997) [`tb97`], Thm 38.1. Proof:
`cgRecurrence_x_eq_of_krylovGrade_le` with `x⋆ = A⁻¹ c` and `cgRecurrence_r_eq`.
atlas: cg-recurrence (partial) -/
theorem cgRecurrence_r_eq_zero_of_krylovGrade_le (hA : A.PosDef) {k : ℕ}
    (hk : krylovGrade A (c - A *ᵥ x₀) ≤ k) : (cgRecurrence A c x₀ k).r = 0 := by
  have hU : IsUnit A := hA.isUnit
  have hxs : A *ᵥ (A⁻¹ *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).1 hU),
      Matrix.one_mulVec]
  rw [cgRecurrence_r_eq, cgRecurrence_x_eq_of_krylovGrade_le hA hxs hk, hxs, sub_self]

end NLAlib
