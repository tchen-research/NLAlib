import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Logic.Function.Iterate

/-! # A compact monotone iteration produces a genuine fixed point

The proof constructs the iterates, takes a convergent subsequence, and uses
closed order to show that its limit equals its actual image. No complete
lattice structure or fixed-point existence hypothesis is required.
-/

noncomputable section
set_option autoImplicit false
open Set Filter Function
open scoped Topology

variable {X : Type*} [MetricSpace X] [PartialOrder X] [OrderClosedTopology X]

/-- A continuous order-preserving self-map of a compact set has a fixed
point above every increasing initial iterate. The fixed point and all
iterate bounds are constructed from compactness and closed order. -/
theorem IsCompact.exists_fixedPoint_of_monotoneOn
    {K : Set X} (hK : IsCompact K) {F : X → X}
    (hF : ContinuousOn F K) (hmap : MapsTo F K K) (hmono : MonotoneOn F K)
    {a : X} (ha : a ∈ K) (hsub : a ≤ F a) :
    ∃ z ∈ K, F z = z ∧ ∀ n : ℕ, F^[n] a ≤ z := by
  let u : ℕ → X := fun n => F^[n] a
  have hu0 : u 0 = a := rfl
  have hus (n : ℕ) : u (n + 1) = F (u n) := Function.iterate_succ_apply' F n a
  have huK (n : ℕ) : u n ∈ K := by
    induction n with
    | zero => exact ha
    | succ n hn => rw [hus]; exact hmap hn
  have hum : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    induction n with
    | zero => simpa only [hu0, hus] using hsub
    | succ n hn =>
      simpa only [hus] using hmono (huK n) (huK (n + 1)) hn
  obtain ⟨z, hz, φ, hφ, hlim⟩ := hK.isSeqCompact.subseq_of_frequently_in
    (Filter.Eventually.of_forall huK).frequently
  have hupper (n : ℕ) : u n ≤ z := by
    apply ge_of_tendsto hlim
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop n)] with k hk
    exact hum hk
  have hfLim : Tendsto (fun k => F (u (φ k))) atTop (𝓝 (F z)) :=
    (hF z hz).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hlim, Eventually.of_forall fun k => huK (φ k)⟩)
  have hsLim : Tendsto (fun k => u (φ k + 1)) atTop (𝓝 (F z)) := by
    simpa only [hus] using hfLim
  have hlow : z ≤ F z := le_of_tendsto_of_tendsto hlim hsLim
    (Eventually.of_forall fun k => hum (Nat.le_succ (φ k)))
  have hupp : F z ≤ z := le_of_tendsto hsLim
    (Eventually.of_forall fun k => hupper (φ k + 1))
  exact ⟨z, hz, le_antisymm hupp hlow, hupper⟩
