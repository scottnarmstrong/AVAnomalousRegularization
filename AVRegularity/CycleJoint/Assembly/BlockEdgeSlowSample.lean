-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.Assembly.ScalarResidualContraction
public import AVRegularity.CycleJoint.Assembly.PatchBridges
public import AVRegularity.CycleJoint.PlanePolynomialJetMultiplierDensity
import AVRegularity.CycleReference.TransitionZero
import AVRegularity.CycleComparison.Charts.ChartDeviation
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.CycleComparison.Reconstruction.Tested
import AVRegularity.CycleJoint.PreparationScaledFlowBudget
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Combinatorics.SimpleGraph.Basic

section
/-! Ingredient CJ06: exact componentwise L² contraction of source-free torus solutions. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology

universe u v

namespace AVRegularity.CycleJointProofs.Assembly

/-- Contraction for every positive mass choice implies each component's contraction. -/
theorem component_le_of_positive_mass {J : Type*} [Fintype J] (A B : J → ℝ)
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    (hmass : ∀ π : J → ℝ, (∀ j, 0 < π j) → ∑ j, (π j)⁻¹ * A j ≤ ∑ j, (π j)⁻¹ * B j)
    (i : J) : A i ≤ B i := by
  classical
  have he (ε : ℝ) (hε : 0 < ε) : A i ≤ B i + ε * ∑ j, B j := by
    let π := fun j => if j = i then (1 : ℝ) else ε⁻¹
    have hπ (j : J) : 0 < π j := by
      dsimp only [π]
      split_ifs <;> positivity
    have hl : A i ≤ ∑ j, (π j)⁻¹ * A j := by
      have hh := Finset.single_le_sum (s := (Finset.univ : Finset J))
        (f := fun j => (π j)⁻¹ * A j)
        (fun j _ => mul_nonneg (inv_pos.mpr (hπ j)).le (hA j)) (Finset.mem_univ i)
      simpa only [π, ite_eq_left rfl, inv_one, one_mul] using hh
    apply (hl.trans (hmass π hπ)).trans
    calc
      _ ≤ ∑ j, ((if j = i then B j else 0) + ε * B j) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j = i
        · simp only [π, ite_eq_left hj, inv_one, one_mul]
          exact le_add_of_nonneg_right (mul_nonneg hε.le (hB j))
        · simp only [π, ite_eq_right hj, inv_inv, zero_add, le_refl]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp
  have ht : Tendsto (fun n : ℕ => B i + (1 / ((n : ℝ) + 1)) * ∑ j, B j)
      atTop (𝓝 (B i)) := by
    simpa only [zero_mul, add_zero] using
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (∑ j, B j))
  exact ge_of_tendsto ht (Eventually.of_forall (fun n : ℕ => he (1 / ((n : ℝ) + 1)) (by positivity)))

/-- Source-free scalar torus solutions contract every component with leading constant one. -/
theorem scalarContraction : ScalarContractionStatement.{u, v} := by
  intro ι _ h _ _ _ _ _ _ φ hφ ν a b hν D f u w hs i t ht
  classical
  have hs0 := scalar_weak_solution_no_coupling ν a b (AVenhance.streamVel φ) D f u w hs
  have hst := scalar_weak_solution_restrict ν a b t (AVenhance.streamVel φ) ht.2 f u w hs0
  obtain ⟨Bv⟩ := scalarDriftWindow_of_stream φ hφ a t
  have hmass (π : ι → ℝ) (hπ : ∀ j, 0 < π j) :
      (∑ j, (π j)⁻¹ * ‖u j t‖ ^ 2) ≤ ∑ j, (π j)⁻¹ * ‖f j‖ ^ 2 := by
    have hh := scalar_endpoint_mass_contraction ν a t ht.1 hν (AVenhance.streamVel φ)
      Bv f u w hst π hπ
    simpa only [scalar_mass_norm] using hh
  have hh := component_le_of_positive_mass (fun j => ‖u j t‖ ^ 2) (fun j => ‖f j‖ ^ 2)
    (fun j => sq_nonneg _) (fun j => sq_nonneg _) hmass i
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hh

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **Level C, letter fluxes: statements**.

The two identities that read the insertions of the retained responses as the letter fluxes of
the word chains (`letterAdmissibleFlux`, the flux of a word-chain level computed from the previous
level), on a level of a word chain with slots `K` on every level:

* `MetricLetterFluxStatement`: the metric letter's flux is the metric Taylor insertion
  `planeMatrixGradientFlux (taylorSlow 1 Ks (G t ·) 0 z)` (via `taylorSlow_rescale`).
* `SourceLetterFluxStatement`: at a time of the family window, the source letter's flux is
  the sum over identities of the block raw readout `blockLetterFieldFlux` (descending slots make
  every edge order admissible; the time weights and the slow Taylor polynomial are linear). -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleJointProofs

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- **The metric letter's flux.** -/
def MetricLetterFluxStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D N : ℕ} (_hD : 2 ≤ D) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (X₀ : Vec 2) (δ : ℝ)
    (_hδ : δ ≠ 0) (Ks : ℕ) (θ : ℝ) (b : ι → ι → ℝ) (K : ι → ℕ) (j : Fin N) (v : ι)
    (W : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (t : ℝ) (z : Vec 2),
    Weighted.letterAdmissibleFlux (blockMetricLetter (D := D) G X₀ δ Ks θ b)
        (fun p : Fin (N + 1) × ι => K p.2) (j.succ, v) (fun u => (j.castSucc, u)) v 1 X₀ δ W t z =
      planeMatrixGradientFlux (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z) (W v) z

/-- **The source letter's flux.** -/
def SourceLetterFluxStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D : ℕ} {P : Type w} {Ctx : P → Type x} (F : ChartedFamily ι h D P Ctx) (S : Finset P)
    (actual : ∀ p, Ctx p) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (Wt : Set ℝ) (l : ℤ)
    (σ : ℝ) (yc : Vec 2) (e E ℓ2 : ℝ) (_he : e ≠ 0) (_hE : E ≠ 0) (Ks : ℕ) (θ : ℝ)
    (b : ι → ι → ℝ) (K : ι → ℕ) (_hdesc : F.IsDescending K) (N : ℕ) (j : Fin N) (v : ι)
    (W : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (t : ℝ) (_ht : ℓ2 * t ∈ Wt) (z : Vec 2),
    Weighted.letterAdmissibleFlux (blockSourceLetter F S actual hφ Wt l σ yc e E ℓ2 Ks θ b)
        (fun p : Fin (N + 1) × ι => K p.2) (j.succ, v) (fun u => (j.castSucc, u)) v 0
        (E⁻¹ • yc) (e / E) W t z =
      ∑ u, ∑ γ : F.Γ v u, blockLetterFieldFlux Ks F S actual K ℓ2 hφ l σ e E yc v u γ (W u) t z

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs.Assembly

/-! Exact coefficient and order identities for the two block letter fluxes. -/

/-- Subtracting a constant leaves every positive Taylor degree unchanged, even for a rough field. -/
theorem letterFlux_taylor_positive_sub_const (Ks : ℕ) (f : Vec 2 → ℝ) (c : ℝ)
    (X Δ : Vec 2) : taylorSlow 1 Ks (fun x => f x - c) X Δ = taylorSlow 1 Ks f X Δ := by
  unfold taylorSlow
  apply Finset.sum_congr rfl
  intro r hr
  have hpos := (Finset.mem_Icc.mp hr).1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  have hder : fderiv ℝ (fun x => f x - c) = fderiv ℝ f := funext (fun _ => fderiv_sub_const c)
  rw [hder]

/-- The native order list contains one additional, absent top order. -/
theorem letterFlux_sum_orders {V : Type*} [AddCommMonoid V] (D : ℕ) (hD : 1 ≤ D)
    (R : ℕ → V) (hz : R (D + 1) = 0) :
    (∑ j : Fin D, R (j.val + 2)) = ∑ d ∈ Finset.Icc 2 D, R d := by
  calc
    _ = ∑ j ∈ Finset.range D, R (j + 2) := Fin.sum_univ_eq_sum_range (fun j => R (j + 2)) D
    _ = ∑ d ∈ Finset.Ico 2 (D + 2), R d := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel, Nat.add_comm]
    _ = ∑ d ∈ Finset.Icc 2 (D + 1), R d := rfl
    _ = _ := by rw [Finset.sum_Icc_succ_top (by omega), hz, add_zero]

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

section Coefficient
variable [∀ i, NormedSpace ℝ (h i)]

/-- An order above the original identity is absent in either branch of the block coefficient. -/
theorem letterFlux_block_coefficient_zero (F : ChartedFamily ι h D P Ctx)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (p : P) (c : Ctx p)
    (v u : ι) (γ : F.Γ v u) (l : ℤ) (σ : ℝ) (yc : Vec 2) (e E ℓ2 : ℝ)
    (d : ℕ) (hd : (F.identity v u γ).maxOrder < d) (h2 : 2 ≤ d)
    (I : DerivativeWord2 (d - 1)) (τ : ℝ) (X z : Vec 2) :
    blockLetterCoefficient F hφ p c v u γ l σ yc e E ℓ2 d I τ X z = 0 := by
  unfold blockLetterCoefficient
  split_ifs
  · rw [F.flux_zero p c v u γ d I (by omega)]
  · unfold transportedCoeff
    have he : Finset.Icc (d - 1 + 1) (F.identity v u γ).maxOrder = ∅ :=
      Finset.Icc_eq_empty_of_lt (by omega)
    simp only [he, Finset.sum_empty]
    rfl

end Coefficient

variable [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, MeasurableSpace (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The aggregate coefficient is identically zero at every absent order. -/
theorem letterFlux_block_array_zero (F : ChartedFamily ι h D P Ctx) (S : Finset P)
    (actual : ∀ p, Ctx p) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (l : ℤ) (σ e E : ℝ) (yc : Vec 2) (ℓ2 : ℝ) (Ks : ℕ) (v u : ι) (γ : F.Γ v u)
    (r : ℕ) (hr : (F.identity v u γ).maxOrder < r + 1) (hr1 : 1 ≤ r) (t : ℝ) (z : Vec 2) :
    blockLetterNativeArray Ks F S actual v u γ ℓ2 hφ l σ e E yc r t z = 0 := by
  have hc (I : DerivativeWord2 r) (k : Fin 2) :
      (fun X => blockLetterAggCoeff F S actual hφ l σ yc e E ℓ2 v u γ (r + 1) I t X z k) =
        fun _ => 0 := by
    funext X
    unfold blockLetterAggCoeff
    simp only [letterFlux_block_coefficient_zero F hφ _ _ v u γ l σ yc e E ℓ2
      (r + 1) hr (by omega) _ t X z, smul_zero, Finset.sum_const_zero, Pi.zero_apply]
  unfold blockLetterNativeArray
  simp only [hc, taylorSlow, iteratedFDeriv_fun_zero, Pi.zero_apply, zero_apply, mul_zero, Finset.sum_const_zero]
  exact map_zero (nativeArrayAssembly r (F.identity v u γ).map)

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! The positive metric letter has the exact matrix Taylor insertion flux. -/

@[expose] public noncomputable section

open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted

universe u v

namespace AVRegularity.CycleJointProofs.Assembly

/-- The diagonal order-two edge is the literal singleton, without a dependent cast. -/
theorem letterFlux_metric_edge_self {ι : Type*} [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (hD : 2 ≤ D)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (X₀ : Vec 2) (δ : ℝ) (v : ι) :
    metricEdges G X₀ δ v v ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, hD⟩⟩ =
      [metricConstituent (h v) G X₀ δ] := by
  unfold metricEdges
  rw [dite_eq_left (show v = v ∧ 2 = 2 from ⟨rfl, rfl⟩)]
  rfl

/-- The frozen constant metric part does not contribute to the positive Taylor insertion. -/
theorem metricLetterFlux : MetricLetterFluxStatement.{u, v} := by
  classical
  intro ι _ _ h _ _ _ _ _ _ D N hD G X₀ δ hδ Ks θ b K j v W t z
  let κ := fun p : Fin (N + 1) × ι => K p.2
  let a := (j.succ, v)
  let src := fun u : ι => (j.castSucc, u)
  let o : admissibleOrders κ D a (src v) := ⟨2, by simp [admissibleOrders, κ, a, src, hD]⟩
  unfold letterAdmissibleFlux
  rw [Finset.sum_eq_single v]
  · rw [Finset.sum_eq_single o]
    · change slowEvalCoefficient (fun f z => taylorSlow 1 Ks f X₀ (δ • z))
        (metricEdges G X₀ δ v v (admissibleLetterOrder κ D a (src v) o)) t z _ = _
      change slowEvalCoefficient (fun f z => taylorSlow 1 Ks f X₀ (δ • z))
        (metricEdges G X₀ δ v v ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, hD⟩⟩) t z _ = _
      rw [letterFlux_metric_edge_self hD G X₀ δ v]
      change slowEvalCoefficient (fun f z => taylorSlow 1 Ks f X₀ (δ • z))
        [metricConstituent (h v) G X₀ δ] t z
        (WithLp.toLp 2 (fun w : DerivativeWord2 1 =>
          (W v).toFunction.jet ⟨⟨1, by omega⟩, w⟩ z)) = _
      rw [slowEvalCoefficient_value_expansion]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      change (∑ w : DerivativeWord2 1, ∑ k : Fin 2,
        taylorSlow 1 Ks (fun X => G t (δ⁻¹ • (X - X₀)) k (w 0) - G t 0 k (w 0)) X₀ (δ • z) •
          fluxCoordinateInjection k (ContinuousLinearMap.id ℝ (h v))
            ((W v).toFunction.jet ⟨⟨1, by omega⟩, w⟩ z)) = _
      have htaylor (k l : Fin 2) :
          taylorSlow 1 Ks (fun X => G t (δ⁻¹ • (X - X₀)) k l - G t 0 k l) X₀ (δ • z) =
            taylorSlow 1 Ks (fun y => G t y k l) 0 z :=
        (letterFlux_taylor_positive_sub_const Ks (fun X => G t (δ⁻¹ • (X - X₀)) k l)
          (G t 0 k l) X₀ (δ • z)).trans
          (taylorSlow_rescale 1 Ks (fun y => G t y k l) X₀ z hδ)
      conv_lhs =>
        arg 2
        intro w
        arg 2
        intro k
        rw [htaylor k (w 0)]
      rw [← ((Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp
        (fun w : DerivativeWord2 1 => ∑ k : Fin 2,
          taylorSlow 1 Ks (fun y => G t y k (w 0)) 0 z •
            fluxCoordinateInjection k (ContinuousLinearMap.id ℝ (h v))
              ((W v).toFunction.jet ⟨⟨1, by omega⟩, w⟩ z)))]
      unfold planeMatrixGradientFlux
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro k _
      congr 2
    · intro o' _ hne
      have ho : o'.1 ≠ 2 := fun hh => hne (Subtype.ext hh)
      have hedge : metricEdges (h := h) G X₀ δ v v (admissibleLetterOrder κ D a (src v) o') = [] := by
        simp [metricEdges, admissibleLetterOrder, ho]
      change slowEvalCoefficient _ (metricEdges G X₀ δ v v _) t z _ = 0
      rw [hedge]
      rfl
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  · intro u _ huv
    apply Finset.sum_eq_zero
    intro o' _
    have hedge : metricEdges (h := h) G X₀ δ v u (admissibleLetterOrder κ D a (src u) o') = [] := by
      simp [metricEdges, admissibleLetterOrder, Ne.symm huv]
    change slowEvalCoefficient _ (metricEdges G X₀ δ v u _) t z _ = 0
    rw [hedge]
    rfl
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! Exact source insertion identities, with the Taylor polynomial applied to the weighted sum. -/

@[expose] public noncomputable section

open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

section Order

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- At a window time the source edge evaluates exactly the aggregate native array of its identities. -/
theorem letterFlux_source_order (F : ChartedFamily ι h D P Ctx) (S : Finset P)
    (actual : ∀ p, Ctx p) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (Wt : Set ℝ) (l : ℤ) (σ : ℝ) (yc : Vec 2) (e E ℓ2 : ℝ) (Ks : ℕ)
    (v u : ι) (d : Finset.Icc 2 D) (t : ℝ) (ht : ℓ2 * t ∈ Wt) (z : Vec 2)
    (Z : PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) :
    slowEvalCoefficient (fun f z => taylorSlow 0 Ks f (E⁻¹ • yc) ((e / E) • z))
      (blockSourceEdges F S actual hφ Wt l σ yc e E ℓ2 v u d) t z Z =
      ∑ γ : F.Γ v u, blockLetterNativeArray Ks F S actual v u γ ℓ2 hφ l σ e E yc (d.1 - 1) t z Z := by
  classical
  rcases d with ⟨dval, hdval⟩
  obtain ⟨r, hr⟩ : ∃ r, dval = r + 2 := ⟨dval - 2, by
    have hh := (Finset.mem_Icc.mp hdval).1
    omega⟩
  subst dval
  let d : Finset.Icc 2 D := ⟨r + 2, hdval⟩
  have h2 := (Finset.mem_Icc.mp d.2).1
  have hs (L : List (F.Γ v u)) :
      slowEvalCoefficient (fun f z => taylorSlow 0 Ks f (E⁻¹ • yc) ((e / E) • z))
        (L.filterMap (fun γ => if hd : d.1 ≤ (F.identity v u γ).maxOrder then
          some (sourceConstituent F S actual hφ v u γ d.1 hd Wt l σ yc e E ℓ2) else none)) t z Z =
      (L.map fun γ => blockLetterNativeArray Ks F S actual v u γ ℓ2 hφ l σ e E yc
        (d.1 - 1) t z Z).sum := by
    induction L with
    | nil => simp only [List.filterMap_nil, slowEvalCoefficient, List.map_nil, List.sum_nil, zero_apply]
    | cons γ L ih =>
      by_cases hd : d.1 ≤ (F.identity v u γ).maxOrder
      · simp only [List.filterMap_cons, dite_eq_left hd, List.map_cons, List.sum_cons]
        simp only [slowEvalCoefficient, List.map_cons, List.sum_cons, add_apply] at ih ⊢
        rw [ih]
        congr 1
        change nativeArrayAssembly (d.1 - 1) (F.identity v u γ).map
          (fun k I => taylorSlow 0 Ks (fun X => (sourceConstituent F S actual hφ v u γ d.1 hd
            Wt l σ yc e E ℓ2).coeff I t X z k) (E⁻¹ • yc) ((e / E) • z)) Z = _
        unfold blockLetterNativeArray
        congr 1
        apply congrArg (nativeArrayAssembly (d.1 - 1) (F.identity v u γ).map)
        funext k I
        congr 2
        funext X
        simp only [sourceConstituent, blockLetterAggCoeff, Set.indicator_of_mem ht,
          Finset.sum_apply, Pi.smul_apply]
        rfl
      · have hz := letterFlux_block_array_zero F S actual hφ l σ e E yc ℓ2 Ks v u γ
          (d.1 - 1) (by omega) (by omega) t z
        simp only [List.filterMap_cons, dite_eq_right hd, List.map_cons,
          List.sum_cons, hz, zero_apply, zero_add]
        exact ih
  unfold blockSourceEdges
  rw [hs]
  exact Finset.sum_map_toList _ _

end Order

/-- The source letter and the block readout expand the same weighted aggregate, at every order. -/
theorem sourceLetterFlux : SourceLetterFluxStatement.{u, v, w, x} := by
  classical
  intro ι _ _ h _ _ _ _ _ _ D P Ctx F S actual φ hφ Wt l σ yc e E ℓ2 he hE Ks θ b K
    hdesc N j v W t ht z
  by_cases hD : 2 ≤ D
  swap
  · unfold letterAdmissibleFlux
    apply Finset.sum_congr rfl
    intro u _
    let letterFluxEmptyIdentity : IsEmpty (F.Γ v u) := ⟨fun γ => by
      have hmin := (F.identity v u γ).two_le
      have hmax := (F.identity v u γ).le_D
      omega⟩
    let letterFluxEmptyOrder : IsEmpty (admissibleOrders
        (fun p : Fin (N + 1) × ι => K p.2) D (j.succ, v) (j.castSucc, u)) := ⟨fun o => by
      have hh := Finset.mem_Icc.mp (Finset.mem_filter.mp o.2).1
      omega⟩
    simp only [Fintype.sum_empty]
  let κ := fun p : Fin (N + 1) × ι => K p.2
  let a := (j.succ, v)
  let src := fun u : ι => (j.castSucc, u)
  let R := fun (u : ι) (d : ℕ) => ∑ γ : F.Γ v u,
    blockLetterNativeArray Ks F S actual v u γ ℓ2 hφ l σ e E yc (d - 1) t z
      (WithLp.toLp 2 (fun I => planeJetOrder (W u) (d - 1) I z))
  have hz (u : ι) (d : ℕ) (hd : 2 ≤ d)
      (hmax : ∀ γ : F.Γ v u, (F.identity v u γ).maxOrder < d) : R u d = 0 := by
    apply Finset.sum_eq_zero
    intro γ _
    rw [letterFlux_block_array_zero F S actual hφ l σ e E yc ℓ2 Ks v u γ
      (d - 1) (by have hh := hmax γ; omega) (by omega) t z, zero_apply]
  have horder (u : ι) (o : admissibleOrders κ D a (src u)) :
      slowEvalCoefficient (fun f z => taylorSlow 0 Ks f (E⁻¹ • yc) ((e / E) • z))
        ((blockSourceLetter F S actual hφ Wt l σ yc e E ℓ2 Ks θ b).edge v u
          (admissibleLetterOrder κ D a (src u) o)) t z
        (WithLp.toLp 2 (fun w => (W u).toFunction.jet
          (admissibleLetterSourceIndex κ D a (src u) o w) z)) = R u o.1 := by
    have hreserve : o.1 - 1 ≤ K u + 1 := by
      have hh := admissible_letter_source_reserve κ D a (src u) o
      dsimp only [κ, a, src] at hh
      omega
    have harr : WithLp.toLp 2 (fun w => (W u).toFunction.jet
        (admissibleLetterSourceIndex κ D a (src u) o w) z) =
        WithLp.toLp 2 (fun I => planeJetOrder (W u) (o.1 - 1) I z) := by
      congr 1
      funext I
      simp only [planeJetOrder, dite_eq_left hreserve]
      rfl
    change slowEvalCoefficient (fun f z => taylorSlow 0 Ks f (E⁻¹ • yc) ((e / E) • z))
      (blockSourceEdges F S actual hφ Wt l σ yc e E ℓ2 v u
        ⟨o.1, (Finset.mem_filter.mp o.2).1⟩) t z
      (WithLp.toLp 2 (fun w : DerivativeWord2 (o.1 - 1) => (W u).toFunction.jet
        (admissibleLetterSourceIndex κ D a (src u) o w) z)) = R u o.1
    rw [harr]
    exact letterFlux_source_order F S actual hφ Wt l σ yc e E ℓ2 Ks v u
      (admissibleLetterOrder κ D a (src u) o) t ht z _
  unfold letterAdmissibleFlux
  change (∑ u : ι, ∑ o : admissibleOrders κ D a (src u), _) = _
  trans ∑ u : ι, ∑ o : admissibleOrders κ D a (src u), R u o.1
  · apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro o _
    exact horder u o
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_coe_sort]
  have hsum : (∑ d ∈ admissibleOrders κ D a (src u), R u d) =
      ∑ d ∈ Finset.Icc 2 D, R u d := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    apply hz u d (Finset.mem_Icc.mp hd).1
    intro γ
    have hn : ¬ K v + d ≤ K u + 2 := by
      simpa only [admissibleOrders, Finset.mem_filter, hd, true_and, κ, a, src] using hnot
    have hh := hdesc v u γ
    omega
  rw [hsum]
  have htop : R u (D + 1) = 0 := hz u (D + 1) (by omega)
    (fun γ => Nat.lt_succ_of_le (F.identity v u γ).le_D)
  rw [← letterFlux_sum_orders D (by omega) (R u) htop]
  unfold blockLetterFieldFlux
  dsimp only [R]
  rw [Finset.sum_comm]
  rfl

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CycleWords AVRegularity.CycleComparison.Charts
namespace AVRegularity.CycleJointProofs.Assembly

/-! Taylor readouts on a fixed renewal block: finite sums, affine coordinates,
and the identity transition of a piece carrying the block's own label. -/

/-- Taylor expansion commutes with a finite weighted sum of sufficiently smooth fields. -/
theorem blockEdge_taylor_sum {P : Type*} (S : Finset P) (Ks : ℕ)
    (w : P → ℝ) (f : P → Vec 2 → ℝ)
    (hf : ∀ p ∈ S, ContDiff ℝ (Ks : ℕ) (f p)) (X Z : Vec 2) :
    taylorSlow 0 Ks (fun Y => ∑ p ∈ S, w p * f p Y) X Z =
      ∑ p ∈ S, w p * taylorSlow 0 Ks (f p) X Z := by
  classical
  unfold taylorSlow
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hsm p hp : ContDiffAt ℝ (r : ℕ) (fun Y => w p * f p Y) X :=
    ((hf p hp).of_le (by exact_mod_cast (Finset.mem_Icc.mp hr).2)).contDiffAt.const_smul (w p)
  rw [iteratedFDeriv_fun_sum_apply hsm]
  simp only [_root_.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpr : ContDiffAt ℝ (r : ℕ) (f p) X :=
    ((hf p hp).of_le (by exact_mod_cast (Finset.mem_Icc.mp hr).2)).contDiffAt
  rw [show (fun Y => w p * f p Y) = w p • f p from rfl,
    iteratedFDeriv_const_smul_apply hpr]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

/-- A piece with zero weight contributes zero even if its coefficient has no regularity. -/
theorem blockEdge_taylor_sum_active {P : Type*} (S : Finset P) (Ks : ℕ)
    (w : P → ℝ) (f : P → Vec 2 → ℝ)
    (hf : ∀ p ∈ S, w p ≠ 0 → ContDiff ℝ (Ks : ℕ) (f p)) (X Z : Vec 2) :
    taylorSlow 0 Ks (fun Y => ∑ p ∈ S, w p * f p Y) X Z =
      ∑ p ∈ S, w p * taylorSlow 0 Ks (f p) X Z := by
  classical
  let g := fun p => if w p = 0 then (fun _ : Vec 2 => 0) else f p
  have hg (p : P) (hp : p ∈ S) : ContDiff ℝ (Ks : ℕ) (g p) := by
    dsimp only [g]
    split_ifs with hw
    · exact contDiff_const
    · exact hf p hp hw
  have he p Y : w p * g p Y = w p * f p Y := by
    dsimp only [g]
    split_ifs with hw
    · simp only [hw, zero_mul]
    · rfl
  have ht p : w p * taylorSlow 0 Ks (g p) X Z =
      w p * taylorSlow 0 Ks (f p) X Z := by
    dsimp only [g]
    split_ifs with hw
    · simp only [hw, zero_mul]
    · rfl
  have h := blockEdge_taylor_sum S Ks w g hg X Z
  simpa only [he, ht] using h

/-- At equal anchor and reference times the natural inverse-Piola matrix is the identity. -/
theorem blockEdge_naturalJacobian_self {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (y : Vec 2) :
    naturalPreparationJacobian hφ s s y = 1 := by
  have hf : (fun x => streamFlow φ hφ s x s) = id := by
    funext x
    exact streamFlow_self hφ x s
  unfold naturalPreparationJacobian
  rw [show streamFlow φ hφ s y s = y from congrFun hf y]
  change chartJacobian (fun x => streamFlow φ hφ s x s) y = _
  rw [hf]
  change jacMatrix id y = 1
  exact AVRegularity.CycleReference.jacMatrix_identity y

/-- The identity chart does not mix ordered derivative words. -/
theorem blockEdge_transition_identity (I A : List (Fin 2)) :
    transitionT (fun _ : Vec 2 => (1 : Matrix (Fin 2) (Fin 2) ℝ)) I A =
      fun _ => if I = A then 1 else 0 := by
  classical
  induction I generalizing A with
  | nil =>
    cases A <;> simp [transitionT]
  | cons i I ih =>
    have hd (A : List (Fin 2)) (y : Vec 2) :
        fderiv ℝ (fun _ : Vec 2 => if I = A then (1 : ℝ) else 0) y = 0 :=
      congrFun (fderiv_const (𝕜 := ℝ) (E := Vec 2) (if I = A then (1 : ℝ) else 0)) y
    funext y
    cases A with
    | nil => simp [transitionT, ih, hd]
    | cons a A =>
      simp only [transitionT, ih, hd, zero_apply, mul_zero, Finset.sum_const_zero,
        zero_add, Matrix.one_apply]
      by_cases hia : a = i
      · subst a
        simp only [ite_true, one_mul, List.cons.injEq, true_and]
      · have hia' : i ≠ a := Ne.symm hia
        simp only [hia, hia', ite_false, zero_mul, List.cons.injEq, false_and]

/-- The open core of one integer-labelled block meets the closed block of another
label only when the labels coincide. -/
theorem blockEdge_core_label_eq {T c t : ℝ} (hT : 0 ≤ T) (hc : 0 < c)
    (j l : ℤ)
    (hcore : t ∈ Set.Ioo (((j : ℝ) - 1 / 2) * T + c)
      (((j : ℝ) + 1 / 2) * T - c))
    (hblock : ((l : ℝ) - 1 / 2) * T ≤ t ∧ t ≤ ((l : ℝ) + 1 / 2) * T) :
    j = l := by
  rcases lt_trichotomy j l with hj | he | hj
  · have hjl : (j : ℝ) + 1 / 2 ≤ (l : ℝ) - 1 / 2 := by
      have hj' : (j : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast (show j + 1 ≤ l by omega)
      linarith only [hj']
    have hm := mul_le_mul_of_nonneg_right hjl hT
    linarith only [hm, hcore.2, hblock.1, hc]
  · exact he
  · have hlj : (l : ℝ) + 1 / 2 ≤ (j : ℝ) - 1 / 2 := by
      have hj' : (l : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (show l + 1 ≤ j by omega)
      linarith only [hj']
    have hm := mul_le_mul_of_nonneg_right hlj hT
    linarith only [hm, hcore.1, hblock.2, hc]

/-- The core margin `τ' - τ/24` of the trimmed quiet times is positive. -/
theorem trimmedCoreMargin_pos {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) :
    0 < ocTauP α q Λ m - ocTau α q Λ m / 24 := by
  have hT := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ
  have hL : (1 : ℝ) ≤ ocL α q Λ m := by
    have : 1 ≤ ocL α q Λ m := by unfold ocL; omega
    exact_mod_cast this
  have hP := EntryScales.ocTauP_pos' (α := α) (q := q) (m := m) hΛ
  have hle : ocTau α q Λ m ≤ ocTauP α q Λ m := by
    unfold ocTau ocTauP
    rw [pow_two, ← div_div]
    exact div_le_self (div_nonneg hT.le (by linarith)) hL
  linarith

/-- Every output of a piece with a different label in a block lies in the
supplied quiet set, by the core condition outside that set. -/
theorem blockEdge_misaligned_quiet {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
    {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ)
    {tS tZ : ℝ} (F : ChartedFamily ι h D P' Ctx)
    (S : Set ℝ) (hcoreS : IsCoreOutside α q Λ m F tS tZ S)
    (p : P') (l : ℤ) (hl : (F.piece p).label ≠ l) (t : ℝ)
    (ht : t ∈ (F.piece p).output ∩ Set.Icc tS tZ)
    (hblock : ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ t ∧
      t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m) :
    t ∈ S := by
  by_contra hn
  have hc := hcoreS p t ht hn
  exact hl (blockEdge_core_label_eq (Construction.Stream.ocTauPP_pos hΛ).le
    (trimmedCoreMargin_pos hΛ) (F.piece p).label l hc hblock)

/-- Transport by the identity matrix retains precisely the original native order. -/
theorem blockEdge_transported_identity (D r : ℕ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2)
    (A : DerivativeWord2 r) (y : Vec 2) :
    transportedCoeff (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) D B r A y =
      if r + 1 ≤ D then B (r + 1) A else 0 := by
  classical
  funext k
  unfold transportedCoeff
  simp only [blockEdge_transition_identity]
  have hi (d : ℕ) (I : DerivativeWord2 (d - 1)) :
      (∑ i : Fin 2, (1 : Matrix (Fin 2) (Fin 2) ℝ) k i * B d I i *
        (if List.ofFn I = List.ofFn A then 1 else 0)) =
      B d I k * (if List.ofFn I = List.ofFn A then 1 else 0) := by
    simp [Matrix.one_apply]
  simp_rw [hi]
  by_cases hd : r + 1 ≤ D
  · rw [ite_eq_left hd]
    rw [Finset.sum_eq_single (r + 1)]
    · change (∑ I : DerivativeWord2 r, B (r + 1) I k *
          (if List.ofFn I = List.ofFn A then 1 else 0)) = B (r + 1) A k
      simp only [List.ofFn_inj]
      simp
    · intro d hdmem hdne
      have hdlo := (Finset.mem_Icc.mp hdmem).1
      apply Finset.sum_eq_zero
      intro I _
      have hneq : List.ofFn I ≠ List.ofFn A := by
        intro he
        have hh := congrArg List.length he
        simp only [List.length_ofFn] at hh
        omega
      rw [ite_eq_right hneq, mul_zero]
    · intro hn
      exact (hn (Finset.mem_Icc.mpr ⟨le_rfl, hd⟩)).elim
  · have hs : Finset.Icc (r + 1) D = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    simp only [hs, Finset.sum_empty, ite_eq_right hd, Pi.zero_apply]

/-- For a different label, the block's slow Taylor readout is the ordinary
Taylor polynomial of the complete transported slow field in cell coordinates. -/
theorem blockEdge_misaligned_taylor {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (p : P) (c : Ctx p)
    (v u : ι) (γ : F.Γ v u) (l : ℤ) (hl : (F.piece p).label ≠ l)
    (σ e E ℓ2 : ℝ) (hδ : e / E ≠ 0) (yc z : Vec 2)
    (Ks r : ℕ) (I : DerivativeWord2 r) (τ : ℝ) (k : Fin 2) :
    taylorSlow 0 Ks
      (fun X => blockLetterCoefficient F hφ p c v u γ l σ yc e E ℓ2 (r + 1) I τ X z k)
      (E⁻¹ • yc) ((e / E) • z) =
    taylorSlow 0 Ks (fun x => transportedCoeff
      (fun y => naturalPreparationJacobian hφ (F.piece p).anchor σ (yc + e • y))
      (F.identity v u γ).maxOrder
      (fun d A k => F.flux p c v u γ d A (ℓ2 * τ)
        (E⁻¹ • streamFlow φ hφ (F.piece p).anchor (yc + e • x) σ) 0 k)
      r I x k) 0 z := by
  let g := fun x => transportedCoeff
    (fun y => naturalPreparationJacobian hφ (F.piece p).anchor σ (yc + e • y))
    (F.identity v u γ).maxOrder
    (fun d A k => F.flux p c v u γ d A (ℓ2 * τ)
      (E⁻¹ • streamFlow φ hφ (F.piece p).anchor (yc + e • x) σ) 0 k)
    r I x k
  have he : (fun X => blockLetterCoefficient F hφ p c v u γ l σ yc e E ℓ2 (r + 1) I τ X z k) =
      fun X => g ((e / E)⁻¹ • (X - E⁻¹ • yc)) := by
    funext X
    simp only [blockLetterCoefficient, ite_eq_right hl]
    rfl
  rw [he]
  exact taylorSlow_rescale 0 Ks g (E⁻¹ • yc) z hδ

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.ChartTransport AVRegularity.CycleComparison.Lift
open AVRegularity.CycleComparison.Reconstruction
namespace AVRegularity.CycleJointProofs.Assembly

/-! Finite Taylor jets of the transported slow field. The polynomial has the same
jets at the origin through its degree and no higher jets anywhere. -/

/-- Finite differentiability suffices for permutation symmetry on basis directions. -/
theorem blockEdge_iterated_basis_perm {n : ℕ} {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (n : ℕ) f) (w : DerivativeWord2 n)
    (σ : Equiv.Perm (Fin n)) (x : Vec 2) :
    iteratedFDeriv ℝ n f x (fun i => basisVec (w (σ i))) =
      iteratedFDeriv ℝ n f x (fun i => basisVec (w i)) := by
  let w₁ : DerivativeWord2 n := fun i => w (σ (Fin.rev i))
  let w₀ : DerivativeWord2 n := fun i => w (Fin.rev i)
  have hp : (List.ofFn w₁).Perm (List.ofFn w₀) :=
    (Fin.revPerm.ofFn_comp_perm (w ∘ σ)).trans
      ((σ.ofFn_comp_perm w).trans (Fin.revPerm.ofFn_comp_perm w).symm)
  have hh := congrFun
    (orderedListDerivative_perm_of_contDiff hp n f hf (by simp only [List.length_ofFn]; exact le_rfl)) x
  change orderedDerivative w₁ f x = orderedDerivative w₀ f x at hh
  rw [orderedDerivative_eq_iteratedFDeriv w₁ hf, orderedDerivative_eq_iteratedFDeriv w₀ hf] at hh
  simpa only [w₁, w₀, Fin.rev_rev] using hh

/-- A finite scalar Taylor polynomial is smooth at every spatial order. -/
theorem blockEdge_taylor_contDiff (Ks N : ℕ) (f : Vec 2 → ℝ) :
    ContDiff ℝ (N : ℕ) (taylorSlow 0 Ks f 0) := by
  unfold taylorSlow
  apply ContDiff.sum
  intro r _
  exact contDiff_const.mul
    ((iteratedFDeriv ℝ r f 0).contDiff.comp (contDiff_pi.mpr (fun _ => contDiff_id)))

/-- The literal finite Taylor polynomial is the sum of its truncated power series. -/
theorem blockEdge_taylor_series (Ks : ℕ) (f : Vec 2 → ℝ) :
    let p : FormalMultilinearSeries ℝ (Vec 2) ℝ := fun n =>
      if n ≤ Ks then ((n.factorial : ℝ))⁻¹ • iteratedFDeriv ℝ n f 0 else 0
    HasFiniteFPowerSeriesOnBall (taylorSlow 0 Ks f 0) p 0 (Ks + 1) ⊤ := by
  dsimp only
  let p : FormalMultilinearSeries ℝ (Vec 2) ℝ := fun n =>
    if n ≤ Ks then ((n.factorial : ℝ))⁻¹ • iteratedFDeriv ℝ n f 0 else 0
  have hp n (hn : Ks + 1 ≤ n) : p n = 0 := by simp only [p, ite_eq_right (by omega : ¬ n ≤ Ks)]
  have he : p.sum = taylorSlow 0 Ks f 0 := by
    funext x
    rw [p.sum_of_finite hp]
    unfold FormalMultilinearSeries.partialSum taylorSlow
    rw [← Nat.range_succ_eq_Icc_zero]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [p, ite_eq_left (by have := Finset.mem_range.mp hn; omega : n ≤ Ks), smul_apply, smul_eq_mul]
  rw [← he]
  exact p.hasFiniteFPowerSeriesOnBall_of_finite hp

/-- Taylor truncation matches every reserved derivative on the basis words at its centre. -/
theorem blockEdge_taylor_jet_zero {Ks n : ℕ} (hn : n ≤ Ks) {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (Ks : ℕ) f) (w : DerivativeWord2 n) :
    iteratedFDeriv ℝ n (taylorSlow 0 Ks f 0) 0 (fun i => basisVec (w i)) =
      iteratedFDeriv ℝ n f 0 (fun i => basisVec (w i)) := by
  have hs := blockEdge_taylor_series Ks f
  have hh := hs.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace
    (fun i => basisVec (w i))
  simp only [ite_eq_left hn, smul_apply, smul_eq_mul] at hh
  have hfn : ContDiff ℝ (n : ℕ) f := hf.of_le (by exact_mod_cast hn)
  simp_rw [blockEdge_iterated_basis_perm hfn w] at hh
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul] at hh
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [hh]
  field_simp

/-- All derivatives strictly above the Taylor degree vanish at every point. -/
theorem blockEdge_taylor_jet_above {Ks n : ℕ} (hn : Ks < n) (f : Vec 2 → ℝ) (x : Vec 2) :
    iteratedFDeriv ℝ n (taylorSlow 0 Ks f 0) x = 0 := by
  have hs := blockEdge_taylor_series Ks f
  have hx := hs.changeOrigin (y := x) ENNReal.coe_lt_top
  have hh := hx.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace (n := n)
  ext v
  have he := hh v
  simp only [zero_add] at he
  rw [he]
  apply Finset.sum_eq_zero
  intro σ _
  rw [hx.finite n (by omega), zero_apply]

/-- The Taylor remainder is flat to its degree at the origin. -/
theorem blockEdge_remainder_flat {Ks n : ℕ} (hn : n ≤ Ks) {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (Ks : ℕ) f) :
    iteratedFDeriv ℝ n (fun z => f z - taylorSlow 0 Ks f 0 z) 0 = 0 := by
  have hfn : ContDiff ℝ (n : ℕ) f := hf.of_le (by exact_mod_cast hn)
  have htn := blockEdge_taylor_contDiff Ks n f
  have he : iteratedFDeriv ℝ n (fun z => f z - taylorSlow 0 Ks f 0 z) 0 =
      iteratedFDeriv ℝ n f 0 - iteratedFDeriv ℝ n (taylorSlow 0 Ks f 0) 0 :=
    iteratedFDeriv_sub_apply hfn.contDiffAt htn.contDiffAt
  have hb (w : DerivativeWord2 n) :
      (iteratedFDeriv ℝ n (fun z => f z - taylorSlow 0 Ks f 0 z) 0) (fun i => basisVec (w i)) = 0 := by
    rw [he, sub_apply, blockEdge_taylor_jet_zero hn hf w, sub_self]
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have h := norm_le_sum_basisVec (iteratedFDeriv ℝ n (fun z => f z - taylorSlow 0 Ks f 0 z) 0)
  simpa only [hb, norm_zero, Finset.sum_const_zero] using h

/-- The low derivatives of a Taylor remainder use only the derivative just above
its degree. Higher derivatives use their own quantitative bounds. -/
theorem blockEdge_remainder_jet_budget (Ks Kmax : ℕ) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (max Kmax (Ks + 1) : ℕ) f)
    (ϖ ρ ζ A : ℝ) (hϖ : 0 < ϖ) (hρ : 0 ≤ ρ) (hscale : ρ * ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hA : 0 ≤ A)
    (hlow : ∀ x, ‖iteratedFDeriv ℝ (Ks + 1) f x‖ ≤ A * (ζ * ϖ) ^ (Ks + 1))
    (hhigh : ∀ j, Ks < j → j ≤ Kmax → ∀ x,
      ρ ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤ A * ζ ^ (Ks + 1)) :
    ∀ j ≤ Kmax, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => f x - taylorSlow 0 Ks f 0 x) z‖ ≤
        2 ^ Kmax * A * ζ ^ (Ks + 1) * polynomialMomentRoot ϖ z ^ (Ks + 1) := by
  intro j hj z
  let R := fun x => f x - taylorSlow 0 Ks f 0 x
  have hR : ContDiff ℝ (max Kmax (Ks + 1) : ℕ) R :=
    hf.sub (blockEdge_taylor_contDiff Ks (max Kmax (Ks + 1)) f)
  have hroot : 1 ≤ polynomialMomentRoot ϖ z := polynomialMomentRoot_one_le ϖ z
  have hpow : 1 ≤ (2 : ℝ) ^ Kmax := one_le_pow₀ (by norm_num)
  have hrootpow : 1 ≤ polynomialMomentRoot ϖ z ^ (Ks + 1) := one_le_pow₀ hroot
  by_cases hjKs : j ≤ Ks
  · let m := Ks - j + 1
    have hm : m + j = Ks + 1 := by dsimp only [m]; omega
    have hfKs : ContDiff ℝ (Ks : ℕ) f := hf.of_le (by exact_mod_cast (show Ks ≤ max Kmax (Ks + 1) by omega))
    have hcoeff (w : DerivativeWord2 j) :
        ‖iteratedFDeriv ℝ j R z (fun i => basisVec (w i))‖ ≤
          A * (ζ * ϖ) ^ (Ks + 1) * ‖z‖ ^ m := by
      let g := fun x => iteratedFDeriv ℝ j R x (fun i => basisVec (w i))
      have hgj : ContDiff ℝ (m : ℕ) g :=
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Vec 2) ℝ
          (fun i => basisVec (w i))).contDiff.comp
          (hR.iteratedFDeriv_right (by exact_mod_cast (show m + j ≤ max Kmax (Ks + 1) by omega)))
      have hgjets (k : ℕ) (hk : k ≤ Ks - j) : iteratedFDeriv ℝ k g 0 = 0 := by
        have hn : k + j ≤ max Kmax (Ks + 1) := by omega
        have hb := norm_iterated_coefficient_word_jet_le j k
          (hR.of_le (by exact_mod_cast hn)) w 0
        have hz := blockEdge_remainder_flat (by omega : k + j ≤ Ks) hfKs
        change iteratedFDeriv ℝ (k + j) R 0 = 0 at hz
        rw [hz, norm_zero] at hb
        exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
      have hgt : taylorSlow 0 (Ks - j) g 0 z = 0 := by
        unfold taylorSlow
        apply Finset.sum_eq_zero
        intro k hk
        rw [hgjets k (Finset.mem_Icc.mp hk).2, zero_apply, mul_zero]
      have hbound (x : Vec 2) : ‖iteratedFDeriv ℝ m g x‖ ≤ A * (ζ * ϖ) ^ (Ks + 1) := by
        have hb := norm_iterated_coefficient_word_jet_le j m
          (hR.of_le (by exact_mod_cast (show m + j ≤ max Kmax (Ks + 1) by omega))) w x
        rw [hm] at hb
        have he : iteratedFDeriv ℝ (Ks + 1) R x = iteratedFDeriv ℝ (Ks + 1) f x := by
          change iteratedFDeriv ℝ (Ks + 1) (f - taylorSlow 0 Ks f 0) x = _
          rw [iteratedFDeriv_sub_apply
            (hf.of_le (by exact_mod_cast (le_max_right Kmax (Ks + 1)))).contDiffAt
            (blockEdge_taylor_contDiff Ks (Ks + 1) f).contDiffAt,
            blockEdge_taylor_jet_above (Nat.lt_succ_self Ks), sub_zero]
        rw [he] at hb
        exact hb.trans (hlow x)
      have ht := norm_taylorSlow_remainder_le (Ks - j) hgj
        (A * (ζ * ϖ) ^ (Ks + 1)) hbound 0 z
      simp only [zero_add, hgt, sub_zero] at ht
      exact ht.trans (div_le_self (by positivity)
        (by exact_mod_cast (show 1 ≤ (Ks - j + 1).factorial from Nat.factorial_pos _)))
    have hb : ‖iteratedFDeriv ℝ j R z‖ ≤
        2 ^ j * (A * (ζ * ϖ) ^ (Ks + 1) * ‖z‖ ^ m) := by
      apply (norm_le_sum_basisVec (iteratedFDeriv ℝ j R z)).trans
      calc
        _ ≤ ∑ _w : DerivativeWord2 j, A * (ζ * ϖ) ^ (Ks + 1) * ‖z‖ ^ m :=
          Finset.sum_le_sum (fun w _ => hcoeff w)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hrad : ρ ^ j * (ζ * ϖ) ^ (Ks + 1) * ‖z‖ ^ m =
        ζ ^ (Ks + 1) * (ρ * ϖ) ^ j * (ϖ * ‖z‖) ^ m := by
      have hp : ϖ ^ (Ks + 1) = ϖ ^ j * ϖ ^ m := by rw [← pow_add]; congr 1; omega
      simp only [mul_pow]
      rw [hp]
      ring
    have hrad1 : (ρ * ϖ) ^ j ≤ 1 := pow_le_one₀ (mul_nonneg hρ hϖ.le) hscale
    have hmle : (ϖ * ‖z‖) ^ m ≤ polynomialMomentRoot ϖ z ^ (Ks + 1) :=
      (pow_le_pow_left₀ (mul_nonneg hϖ.le (norm_nonneg _))
        (scaledNorm_le_polynomialMomentRoot hϖ.le z) m).trans
        (pow_le_pow_right₀ hroot (by dsimp only [m]; omega))
    have hjpow : (2 : ℝ) ^ j ≤ 2 ^ Kmax := pow_le_pow_right₀ (by norm_num) hj
    change ρ ^ j * ‖iteratedFDeriv ℝ j R z‖ ≤ _
    calc
      _ ≤ ρ ^ j * (2 ^ j * (A * (ζ * ϖ) ^ (Ks + 1) * ‖z‖ ^ m)) :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg hρ _)
      _ = 2 ^ j * A * (ζ ^ (Ks + 1) * (ρ * ϖ) ^ j * (ϖ * ‖z‖) ^ m) := by
        rw [← hrad]; ring
      _ ≤ 2 ^ j * A * (ζ ^ (Ks + 1) * 1 * polynomialMomentRoot ϖ z ^ (Ks + 1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (mul_le_mul_of_nonneg_left hrad1 (pow_nonneg hζ _)) hmle
            (by positivity) (by positivity)) (mul_nonneg (by positivity) hA)
      _ ≤ _ := by
        rw [mul_one]
        convert mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hjpow hA)
          (mul_nonneg (pow_nonneg hζ (Ks + 1))
            (pow_nonneg (zero_le_one.trans hroot) (Ks + 1))) using 1; ring
  · have he : iteratedFDeriv ℝ j R z = iteratedFDeriv ℝ j f z := by
      change iteratedFDeriv ℝ j (f - taylorSlow 0 Ks f 0) z = _
      rw [iteratedFDeriv_sub_apply
        (hf.of_le (by exact_mod_cast (le_max_of_le_left hj))).contDiffAt
        (blockEdge_taylor_contDiff Ks j f).contDiffAt,
        blockEdge_taylor_jet_above (by omega : Ks < j), sub_zero]
    change ρ ^ j * ‖iteratedFDeriv ℝ j R z‖ ≤ _
    rw [he]
    apply (hhigh j (by omega) hj z).trans
    calc
      A * ζ ^ (Ks + 1) ≤ 2 ^ Kmax * (A * ζ ^ (Ks + 1)) :=
        le_mul_of_one_le_left (mul_nonneg hA (pow_nonneg hζ _)) hpow
      _ ≤ (2 ^ Kmax * (A * ζ ^ (Ks + 1))) * polynomialMomentRoot ϖ z ^ (Ks + 1) :=
        le_mul_of_one_le_right (by positivity) hrootpow
      _ = _ := by ring

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs.Assembly

/-! Slow coefficients at a variable physical radius. Above the Taylor degree,
the radius rho/zeta uses the original mixed molecular reserve and loses only
zeta to the excess derivative order. -/

/-- Extract a uniform finite jet bound at the enlarged physical radius.
The quantitative slow reserve stops at L; the remaining derivatives are weighted. -/
theorem blockEdge_slow_reserve (L n : ℕ) (f : Vec 2 → ℝ)
    (η ζ : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (M : ℕ → ℝ) (hM : ∀ j ≤ L, 0 ≤ M j)
    (hlow : ∀ j ≤ L, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ M j)
    (hhigh : ∀ a, a + L ≤ n → ∀ x,
      (ζ * η) ^ a * ‖iteratedFDeriv ℝ (L + a) f x‖ ≤ M L) :
    ∀ j ≤ n, ∀ x, η ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤
      ζ⁻¹ ^ (n - L) * ∑ a ∈ Finset.range (L + 1), M a := by
  intro j hj x
  let S := ∑ a ∈ Finset.range (L + 1), M a
  have hS : 0 ≤ S := Finset.sum_nonneg (fun a ha => hM a (by have := Finset.mem_range.mp ha; omega))
  have hMs (a : ℕ) (ha : a ≤ L) : M a ≤ S :=
    Finset.single_le_sum (fun b hb => hM b (by have := Finset.mem_range.mp hb; omega))
      (Finset.mem_range.mpr (by omega))
  have hζinv : 1 ≤ ζ⁻¹ := (one_le_inv₀ hζ).mpr hζ1
  have hloss : 1 ≤ ζ⁻¹ ^ (n - L) := one_le_pow₀ hζinv
  by_cases hjL : j ≤ L
  · calc
      _ ≤ 1 * M j := mul_le_mul (pow_le_one₀ hη hη1) (hlow j hjL x)
        (norm_nonneg _) (by norm_num)
      _ ≤ S := by rw [one_mul]; exact hMs j hjL
      _ ≤ _ := le_mul_of_one_le_left hS hloss
  · have hja : L + (j - L) = j := by omega
    have hs := hhigh (j - L) (by omega) x
    rw [hja] at hs
    have hp : η ^ j = η ^ L * ζ⁻¹ ^ (j - L) * (ζ * η) ^ (j - L) := by
      have hi : ζ⁻¹ ^ (j - L) * ζ ^ (j - L) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hζ.ne', one_pow]
      rw [mul_pow]
      calc
        _ = η ^ L * 1 * η ^ (j - L) := by rw [mul_one, ← pow_add, hja]
        _ = _ := by rw [← hi]; ring
    calc
      _ = (η ^ L * ζ⁻¹ ^ (j - L)) *
          ((ζ * η) ^ (j - L) * ‖iteratedFDeriv ℝ j f x‖) := by rw [hp]; ring
      _ ≤ (η ^ L * ζ⁻¹ ^ (j - L)) * M L :=
        mul_le_mul_of_nonneg_left hs (mul_nonneg (pow_nonneg hη _) (by positivity))
      _ ≤ (1 * ζ⁻¹ ^ (n - L)) * S :=
        mul_le_mul (mul_le_mul (pow_le_one₀ hη hη1)
          (pow_le_pow_right₀ hζinv (by omega)) (by positivity) (by norm_num))
          (hMs L le_rfl) (hM L le_rfl) (by positivity)
      _ = _ := by rw [one_mul]

/-- Slow-variable dilation converts the physical coefficient jet exactly. -/
theorem blockEdge_physical_slow_jet (j : ℕ) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (j : ℕ) f) (R E : ℝ) (hE : 0 < E) (x : Vec 2) :
    R ^ j * ‖iteratedFDeriv ℝ j (fun y => f (E⁻¹ • y)) x‖ =
      (R / E) ^ j * ‖iteratedFDeriv ℝ j f (E⁻¹ • x)‖ := by
  rw [congrFun (iteratedFDeriv_comp_const_smul E⁻¹ hf) x, norm_smul,
    Real.norm_of_nonneg (pow_nonneg (inv_pos.mpr hE).le j), div_eq_mul_inv, mul_pow]
  ring

/-- Existing finite-order chart composition supplies the enlarged-radius cell jets. -/
theorem blockEdge_sample_cell_jets {α q : ℝ} {Λ m : ℕ}
    {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
    {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (s σ : ℝ)
    (hs : s ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |s - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (n : ℕ) (hn : n ≤ Jchart + 1) (e R : ℝ) (he : 0 < e) (hR : 0 < R)
    (hRE : R ≤ ocEpsilon q Λ (m - 1)) (yc : Vec 2)
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (n : ℕ) f) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ j ≤ n, ∀ x,
      (R / ocEpsilon q Λ (m - 1)) ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    let C := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
    ∀ j ≤ n, ∀ x,
      (R / e) ^ j * ‖iteratedFDeriv ℝ j (fun z =>
        f ((ocEpsilon q Λ (m - 1))⁻¹ • streamFlow φ hφ s (yc + e • z) σ)) x‖ ≤
        (n.factorial : ℝ) * C ^ n * ((n + 1 : ℕ) * B) := by
  dsimp only
  have hE : 0 < ocEpsilon q Λ (m - 1) := hR.trans_le hRE
  let g := fun y => f ((ocEpsilon q Λ (m - 1))⁻¹ • y)
  have hg : ContDiff ℝ (n : ℕ) g := hf.comp (contDiff_id.const_smul _)
  have hgb (j : ℕ) (hj : j ≤ n) (x : Vec 2) : R ^ j * ‖iteratedFDeriv ℝ j g x‖ ≤ B := by
    dsimp only [g]
    rw [blockEdge_physical_slow_jet j f (hf.of_le (by exact_mod_cast hj)) R _ hE]
    exact hb j hj _
  have hh := preparation_flow_uniform_sample_jets hc ha R hR hRE s σ hs hσ hage n hn g hg B hB hgb
  intro j hj x
  have hflow : ContDiff ℝ (j : ℕ) (fun y => g (streamFlow φ hφ s y σ)) :=
    (hg.comp ((hc.smooth s hs σ hσ).of_le (by exact_mod_cast hn))).of_le (by exact_mod_cast hj)
  change (R / e) ^ j * ‖iteratedFDeriv ℝ j
    (fun z => (fun y => g (streamFlow φ hφ s y σ)) (yc + e • z)) x‖ ≤ _
  rw [affineSample_scaled_jet_identity j _ hflow e R he]
  exact hh j hj _

end AVRegularity.CycleJointProofs.Assembly
end
end
