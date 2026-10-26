import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Stationary tree-indexed finite Markov chains

A finite tree is grown from a single edge by successive leaf attachments.
The product of a stationary initial distribution and transition probabilities
defines a probability weight on its labelings. Every vertex retains the initial
stationary marginal. This finite construction is useful for weighted graph
partition inequalities, including Gaussian variance-profile moment estimates.
-/

noncomputable section

open scoped BigOperators

namespace NLAlib

/-- A tree with `n + 2` vertices obtained from an edge by attaching `n` leaves.
Each new leaf has index zero and shifts all previous vertex indices. -/
inductive LeafTree : ℕ → Type
  /-- The initial tree consists of one edge on two vertices. -/
  | edge : LeafTree 0
  /-- Add a new leaf at the chosen parent, shifting previous vertex indices. -/
  | attach {n : ℕ} (t : LeafTree n) (parent : Fin (n + 2)) : LeafTree (n + 1)

namespace LeafTree

variable {α : Type*} [Fintype α]

/-- The oriented edge list of a leaf-grown tree. The orientation only records
the construction and carries no restriction on an undirected edge kernel. -/
def edgeList : {n : ℕ} → LeafTree n → List (Fin (n + 2) × Fin (n + 2))
  | _, edge => [(0, 1)]
  | _, attach t p =>
      (p.succ, 0) :: t.edgeList.map (fun e => (e.1.succ, e.2.succ))

/-- A tree with `n + 2` vertices has `n + 1` edges. -/
theorem edgeList_length {n : ℕ} (t : LeafTree n) : t.edgeList.length = n + 1 := by
  induction t with
  | edge => rfl
  | attach t p ih => simp [edgeList, ih]

/-- Reindexing a sum of finite tuples separates the first coordinate from
the remaining coordinates. -/
theorem sum_labelings_succ {n : ℕ} (F : (Fin (n + 1) → α) → ℝ) :
    (∑ x, F x) = ∑ y : Fin n → α, ∑ a : α, F (Fin.cons a y) := by
  classical
  calc
    (∑ x, F x) = ∑ p : α × (Fin n → α), F (Fin.cons p.1 p.2) :=
      (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => α)) F).symm
    _ = _ := Fintype.sum_prod_type_right _

/-- The tree-indexed Markov probability weight of a labeling. The base edge
starts with distribution `π`; every newly attached leaf uses transition `K`
from its parent. -/
def markovWeight (π : α → ℝ) (K : α → α → ℝ) :
    {n : ℕ} → LeafTree n → (Fin (n + 2) → α) → ℝ
  | _, edge, x => π (x 0) * K (x 0) (x 1)
  | _, attach t p, x =>
      markovWeight π K t (fun i => x i.succ) * K (x p.succ) (x 0)

omit [Fintype α] in
/-- Nonnegative initial and transition weights give nonnegative tree weights. -/
theorem markovWeight_nonneg (π : α → ℝ) (K : α → α → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hK : ∀ i j, 0 ≤ K i j)
    {n : ℕ} (t : LeafTree n) (x : Fin (n + 2) → α) :
    0 ≤ t.markovWeight π K x := by
  induction t with
  | edge => exact mul_nonneg (hπ _) (hK _ _)
  | attach t p ih => exact mul_nonneg (ih _) (hK _ _)

/-- Every vertex of a tree-indexed Markov chain has the stationary marginal,
expressed by integration of an arbitrary scalar test function. -/
theorem sum_markovWeight_mul_vertex (π : α → ℝ) (K : α → α → ℝ)
    (hK : ∀ i, ∑ j, K i j = 1)
    (hstationary : ∀ j, ∑ i, π i * K i j = π j)
    {n : ℕ} (t : LeafTree n) (v : Fin (n + 2)) (f : α → ℝ) :
    (∑ x, t.markovWeight π K x * f (x v)) = ∑ i, π i * f i := by
  classical
  induction t generalizing f with
  | edge =>
      have hs (F : α → α → ℝ) :
          (∑ x : Fin 2 → α, F (x 0) (x 1)) = ∑ a, ∑ b, F a b := by
        rw [sum_labelings_succ, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        change (∑ y : Fin 1 → α, F a (y 0)) = _
        exact Equiv.sum_comp (Equiv.funUnique (Fin 1) α) (F a)
      fin_cases v
      · change (∑ x : Fin 2 → α, π (x 0) * K (x 0) (x 1) * f (x 0)) = _
        rw [hs (fun a b => π a * K a b * f a)]
        simp_rw [mul_right_comm _ _ (f _), ← Finset.mul_sum, hK, mul_one]
      · change (∑ x : Fin 2 → α, π (x 0) * K (x 0) (x 1) * f (x 1)) = _
        rw [hs (fun a b => π a * K a b * f b), Finset.sum_comm]
        simp_rw [← Finset.sum_mul, hstationary]
  | @attach n t p ih =>
      rw [sum_labelings_succ]
      simp only [markovWeight, Fin.cons_succ, Fin.cons_zero]
      refine Fin.cases ?_ (fun v => ?_) v
      · simp only [Fin.cons_zero, mul_assoc, ← Finset.mul_sum]
        calc
          (∑ x : Fin (n + 2) → α,
              t.markovWeight π K x * ∑ a, K (x p) a * f a) =
              ∑ i, π i * ∑ a, K i a * f a := ih p (fun i => ∑ a, K i a * f a)
          _ = ∑ i, π i * f i := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            simp_rw [← mul_assoc, ← Finset.sum_mul, hstationary]
      · simp only [Fin.cons_succ]
        simp_rw [mul_right_comm _ _ (f _), ← Finset.mul_sum, hK, mul_one]
        exact ih v f

/-- The stationary Markov weights of all tree labelings sum to one. -/
theorem sum_markovWeight (π : α → ℝ) (K : α → α → ℝ)
    (hπ : ∑ i, π i = 1) (hK : ∀ i, ∑ j, K i j = 1)
    (hstationary : ∀ j, ∑ i, π i * K i j = π j)
    {n : ℕ} (t : LeafTree n) : (∑ x, t.markovWeight π K x) = 1 := by
  have h := t.sum_markovWeight_mul_vertex π K hK hstationary 0 (fun _ => 1)
  simpa only [mul_one, hπ] using h

/-- The degree minus one of a vertex. Both vertices of the initial edge have
value zero; attaching a leaf increments the value at its parent. -/
def degreeExcess : {n : ℕ} → LeafTree n → Fin (n + 2) → ℕ
  | _, edge, _ => 0
  | _, attach t p, v =>
      Fin.cons (α := fun _ => ℕ) 0
        (fun i => degreeExcess t i + if i = p then 1 else 0) v

/-- The sum of degree excesses in a tree with `n + 2` vertices is `n`. -/
theorem sum_degreeExcess {n : ℕ} (t : LeafTree n) :
    (∑ v, t.degreeExcess v) = n := by
  classical
  induction t with
  | edge => simp [degreeExcess]
  | attach t p ih => simp [degreeExcess, Fin.sum_univ_succ, Finset.sum_add_distrib, ih]

omit [Fintype α] in
/-- The product of an edge kernel over the edges of a leaf-grown tree. -/
def edgeWeight (w : α → α → ℝ) :
    {n : ℕ} → LeafTree n → (Fin (n + 2) → α) → ℝ
  | _, edge, x => w (x 0) (x 1)
  | _, attach t p, x =>
      edgeWeight w t (fun i => x i.succ) * w (x p.succ) (x 0)

omit [Fintype α] in
/-- The recursive edge weight is the product over the actual tree edge list. -/
theorem edgeWeight_eq_prod_edgeList (w : α → α → ℝ)
    {n : ℕ} (t : LeafTree n) (x : Fin (n + 2) → α) :
    t.edgeWeight w x = (t.edgeList.map (fun e => w (x e.1) (x e.2))).prod := by
  induction t with
  | edge => simp [edgeWeight, edgeList]
  | attach t p ih =>
      simp only [edgeWeight, edgeList, List.map_cons, List.prod_cons, List.map_map]
      rw [ih]
      exact mul_comm _ _

omit [Fintype α] in
/-- A nonnegative edge kernel gives nonnegative tree edge-product weights. -/
theorem edgeWeight_nonneg (w : α → α → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    {n : ℕ} (t : LeafTree n) (x : Fin (n + 2) → α) : 0 ≤ t.edgeWeight w x := by
  induction t with
  | edge => exact hw _ _
  | attach t p ih => exact mul_nonneg (ih _) (hw _ _)

/-- The partition function of the initial edge is the total edge-kernel mass. -/
theorem sum_edgeWeight_edge (w : α → α → ℝ) :
    (∑ x : Fin 2 → α, edge.edgeWeight w x) = ∑ i, ∑ j, w i j := by
  classical
  change (∑ x : Fin 2 → α, w (x 0) (x 1)) = _
  rw [sum_labelings_succ, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ y : Fin 1 → α, w i (y 0)) = _
  exact Equiv.sum_comp (Equiv.funUnique (Fin 1) α) (w i)

omit [Fintype α] in
/-- The degree-excess factor in the density of a stationary tree law. -/
def excessWeight (d : α → ℝ) {n : ℕ} (t : LeafTree n)
    (x : Fin (n + 2) → α) : ℝ := ∏ v, d (x v) ^ t.degreeExcess v

omit [Fintype α] in
/-- Adding a leaf multiplies the degree-excess factor by the degree at the parent. -/
theorem excessWeight_attach (d : α → ℝ) {n : ℕ} (t : LeafTree n)
    (p : Fin (n + 2)) (x : Fin (n + 1 + 2) → α) :
    (attach t p).excessWeight d x =
      t.excessWeight d (fun i => x i.succ) * d (x p.succ) := by
  classical
  unfold excessWeight
  rw [Fin.prod_univ_succ]
  simp only [degreeExcess, Fin.cons_zero,
    pow_zero, Fin.cons_succ, one_mul, pow_add, Finset.prod_mul_distrib]
  congr 1
  simp only [pow_ite, pow_one, pow_zero]
  simp

omit [Fintype α] in
/-- The stationary tree probability weight has the exact edge-product density.
This algebraic identity also includes zero degrees whenever `d i * K i j = w i j`.
It requires neither division nor strict positivity of individual degrees. -/
theorem edgeWeight_eq_mul_markovWeight_excessWeight
    (π d : α → ℝ) (K w : α → α → ℝ) (D : ℝ)
    (hπ : ∀ i, D * π i = d i) (hK : ∀ i j, d i * K i j = w i j)
    {n : ℕ} (t : LeafTree n) (x : Fin (n + 2) → α) :
    t.edgeWeight w x = D * t.markovWeight π K x * t.excessWeight d x := by
  induction t with
  | edge =>
      simp only [edgeWeight, markovWeight, excessWeight, degreeExcess, pow_zero,
        Finset.prod_const_one, mul_one]
      rw [← mul_assoc, hπ, hK]
  | attach t p ih =>
      rw [edgeWeight, markovWeight, excessWeight_attach, ih]
      rw [← hK (x p.succ) (x 0)]
      ring

/-- A symmetric nonnegative edge kernel of positive total mass admits a
stationary probability law on all labelings of every leaf-grown tree. Its
vertex marginal is the degree distribution, and its exact density factors the
edge product into a probability weight and the vertex degree-excess factors.
Zero-degree labels are included through a stochastic fallback transition. -/
theorem exists_stationary_edgeWeight_factorization
    (w : α → α → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hsymm : ∀ i j, w i j = w j i)
    (hD : 0 < ∑ i, ∑ j, w i j)
    {n : ℕ} (t : LeafTree n) :
    ∃ P : (Fin (n + 2) → α) → ℝ,
      (∀ x, 0 ≤ P x) ∧ (∑ x, P x) = 1 ∧
      (∀ v (f : α → ℝ), (∑ x, P x * f (x v)) =
        ∑ i, ((∑ j, w i j) / (∑ i, ∑ j, w i j)) * f i) ∧
      ∀ x, t.edgeWeight w x = (∑ i, ∑ j, w i j) * P x *
        t.excessWeight (fun i => ∑ j, w i j) x := by
  classical
  let d : α → ℝ := fun i => ∑ j, w i j
  let D : ℝ := ∑ i, d i
  have hD0 : D ≠ 0 := ne_of_gt hD
  have hd (i : α) : 0 ≤ d i := Finset.sum_nonneg fun j _ => hw i j
  have hwzero (i j : α) (hi : d i = 0) : w i j = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hw i k)).mp hi j (by simp)
  let π : α → ℝ := fun i => d i / D
  let K : α → α → ℝ := fun i j => if d i = 0 then π j else w i j / d i
  have hπnonneg (i : α) : 0 ≤ π i := div_nonneg (hd i) hD.le
  have hKnonneg (i j : α) : 0 ≤ K i j := by
    dsimp [K]
    split_ifs
    · exact hπnonneg j
    · exact div_nonneg (hw i j) (hd i)
  have hπsum : ∑ i, π i = 1 := by
    simp only [π, ← Finset.sum_div]
    exact div_self hD0
  have hKsum (i : α) : ∑ j, K i j = 1 := by
    by_cases hi : d i = 0
    · simp only [K, hi, if_pos]
      exact hπsum
    · simp only [K, hi, if_false, ← Finset.sum_div]
      exact div_self hi
  have hπdegree (i : α) : D * π i = d i := by
    dsimp [π]
    exact mul_div_cancel₀ _ hD0
  have hKdegree (i j : α) : d i * K i j = w i j := by
    by_cases hi : d i = 0
    · simp only [K, hi, if_pos, zero_mul, hwzero i j hi]
    · simp only [K, hi, if_false]
      exact mul_div_cancel₀ _ hi
  have hstationary (j : α) : ∑ i, π i * K i j = π j := by
    have hterm (i : α) : π i * K i j = w i j / D := by
      calc
        π i * K i j = (d i * K i j) / D := by dsimp [π]; ring
        _ = _ := by rw [hKdegree]
    simp_rw [hterm, ← Finset.sum_div, hsymm _ j]
    rfl
  refine ⟨t.markovWeight π K, t.markovWeight_nonneg π K hπnonneg hKnonneg,
    t.sum_markovWeight π K hπsum hKsum hstationary, ?_, ?_⟩
  · exact fun v f => t.sum_markovWeight_mul_vertex π K hKsum hstationary v f
  · exact t.edgeWeight_eq_mul_markovWeight_excessWeight π d K w D hπdegree hKdegree

end LeafTree

end NLAlib
