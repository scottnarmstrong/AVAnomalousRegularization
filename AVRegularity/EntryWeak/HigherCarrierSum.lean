-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.CellAffineHomeomorph
public import AVRegularity.EntryWeak.SobolevSummableMajorantBound
import AVRegularity.CycleReference.ChartIntegrandAlgebra
public import AVRegularity.CoupledEnergy.Variational.GradientTensorCLM
import AVRegularity.CycleEvolution.CellJetSlices
public import AVRegularity.CycleComparison.Lift.WordPolynomialFiniteExtraction
public import AVRegularity.CycleEvolution.CellTimeReverseAdmissibility
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleReference.SingleModeFlux
import AVRegularity.Velocity.Port.StreamRegularity
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.CategoryTheory.Types.Basic

@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Native spatial derivative norms equal the raw geometry norms; mixed parameter derivatives are separate. -/

theorem centeredGeometryChart_fderiv_norm (g : ChainGeom) (hg : GeomSpatialSmooth g)
    (ρ : ℝ) (hρ : 0 < ρ) (u : ℝ) (X : Vec 2) :
    ‖fderiv ℝ (centeredGeometryChart g ρ u) X‖ =
      ‖fderiv ℝ (fun y => g.1 u y g.2.2) (g.2.1 + ρ • X)‖ := by
  have hh := CycleWords.cell_rescaled_iteratedFDeriv_norm (fun y => g.1 u y g.2.2)
    (hg u g.2.2) ρ hρ (g.1 u g.2.1 g.2.2) g.2.1 1 (by omega) X
  change ‖fderiv ℝ (fun Z => ρ⁻¹ •
    (g.1 u (g.2.1 + ρ • Z) g.2.2 - g.1 u g.2.1 g.2.2)) X‖ = _
  simpa only [Nat.sub_self, pow_zero, one_mul, norm_iteratedFDeriv_one] using hh

theorem centeredGeometryChartInv_fderiv_norm (g : ChainGeom) (hg : GeomSpatialSmooth g)
    (ρ : ℝ) (hρ : 0 < ρ) (u : ℝ) (X : Vec 2) :
    ‖fderiv ℝ (centeredGeometryChartInv g ρ u) X‖ =
      ‖fderiv ℝ (fun y => g.1 g.2.2 y u) (g.1 u g.2.1 g.2.2 + ρ • X)‖ := by
  have hh := CycleWords.cell_rescaled_iteratedFDeriv_norm (fun y => g.1 g.2.2 y u)
    (hg g.2.2 u) ρ hρ g.2.1 (g.1 u g.2.1 g.2.2) 1 (by omega) X
  change ‖fderiv ℝ (fun Z => ρ⁻¹ •
    (g.1 g.2.2 (g.1 u g.2.1 g.2.2 + ρ • Z) u - g.2.1)) X‖ = _
  simpa only [Nat.sub_self, pow_zero, one_mul, norm_iteratedFDeriv_one] using hh

/-! Literal chain extensions identify the joint parameter geometry without extra smoothness premises. -/

section
variable {P : Type*}

theorem independentChainExtension_wellSlotted (A : P → RealChain)
    (es : List (ℤ × (P → ChainChild))) (hA : ∀ Y, (A Y).WellSlotted) :
    ∀ Y, (independentChainExtension A es Y).WellSlotted := by
  induction es generalizing A with
  | nil => exact hA
  | cons e rest ih =>
    exact ih (independentChainAppend A e) (independentChainAppend_wellSlotted A e hA)

theorem independentChainExtension_geom (D : OCData) (es : List (ℤ × (P → ChainChild)))
    (A : P → RealChain) (hA : ∀ Y, (A Y).WellSlotted) (level : ℕ) (slot : ℤ)
    (hlevel : ∀ Y, (A Y).ctxLevel = level) (hslot : ∀ Y, (A Y).slot = slot) (Y : P) :
    (independentChainExtension A es Y).geom D =
      independentChainExtensionGeom D level slot (fun Y => (A Y).geom D) es Y := by
  induction es generalizing A level slot with
  | nil => rfl
  | cons e rest ih =>
    let A' := independentChainAppend A e
    have hA' := independentChainAppend_wellSlotted A e hA
    have hl' Z : (A' Z).ctxLevel = level + 1 := by
      rw [independentChainAppend_ctxLevel, hlevel]
    have hs' Z : (A' Z).slot = e.1 := independentChainAppend_slot A e Z
    have hg : (fun Z => (A' Z).geom D) =
        (fun Z => D.childGeom level slot (D.slotAnchor (level + 1) e.1) (e.2 Z) ((A Z).geom D)) := by
      funext Z
      rw [independentChainAppend_geom D A e hA, hlevel, hslot]
    change (independentChainExtension A' rest Y).geom D = _
    rw [ih A' hA' (level + 1) e.1 hl' hs', hg]
    rfl
end

/-! Finite independent chain extension is literal concatenation of slots and children. -/

section
variable {P : Type*}

theorem independentChainExtension_eq_chain (A : P → RealChain)
    (es : List (ℤ × (P → ChainChild))) (Y : P) :
    independentChainExtension A es Y =
      { A Y with
        slots := (A Y).slots ++ es.map Prod.fst
        children := (A Y).children ++ es.map (fun e => e.2 Y) } := by
  induction es generalizing A with
  | nil => simp only [independentChainExtension, List.map_nil, List.append_nil]
  | cons e es ih =>
    rw [independentChainExtension, ih]
    simp only [independentChainAppend, List.map_cons, List.append_assoc, List.singleton_append]
end

/-! Actual coordinate injections give finite-vector source budgets. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem scalarCoordinateInjection_norm_le_one (i : ι) : ‖scalarCoordinateInjection i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro r
  rw [one_mul]
  apply pi_norm_le_iff_of_nonneg (norm_nonneg r) |>.mpr
  intro j
  by_cases h : j = i
  · simp only [scalarCoordinateInjection, ContinuousLinearMap.pi_apply, ite_eq_left h,
      ContinuousLinearMap.id_apply, le_refl]
  · simp only [scalarCoordinateInjection, ContinuousLinearMap.pi_apply, ite_eq_right h,
      zero_apply, norm_zero]
    exact norm_nonneg _
end

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVenhance.Infra.Heat Filter Topology
namespace AVRegularity.EntryWeakProofs

/-! Uniform higher bounds upgrade weak Fourier convergence to absolute jet convergence. -/

theorem realJetFourier_norm_sum_tendsto_zero {A : Type*} {l : Filter A}
    (K : ℕ) (f : A → TorusHk K ℝ) (a : JetIndex2 K) (ha : a.1.val + 4 ≤ K)
    (R : ℝ) (hR : ∀ᶠ x in l, ‖f x‖ ≤ R)
    (hc : ∀ k, Tendsto (fun x => realJetFourier K (f x) a k) l (𝓝 0)) :
    Tendsto (fun x => ∑' k, ‖realJetFourier K (f x) a k‖) l (𝓝 0) := by
  apply fourier_norm_sum_tendsto_zero _
    (fun k => (16 * ‖Complex.ofRealCLM‖ * R) * (1 / latticeWeight k) ^ 2)
    (latticeReciprocal_square_summable.mul_left _) hc
  filter_upwards [hR] with x hx
  intro k
  exact (realJetFourier_summable_majorant K (f x) a ha k).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hx (by positivity)) (sq_nonneg _))

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The literal appended center is smooth in the coupled slow offset and fast phase. -/

theorem weak_transfer_child_center_eq (D : OCData) (A : RealChain) (hl : A.WellSlotted)
    (slot : ℤ) (t : ℝ) (z h : Vec 2) :
    (((A.recenter D h).appendChild D slot t (z + (D.eps A.ctxLevel)⁻¹ • h)).geom D).2.1 =
      (A.geom D).1 (D.slotAnchor (A.ctxLevel + 1) slot)
        ((A.geom D).2.1 + h + D.eps A.ctxLevel •
          D.relDisp A.ctxLevel A.slot (D.slotAnchor (A.ctxLevel + 1) slot) t
            (z + (D.eps A.ctxLevel)⁻¹ • h)) (A.geom D).2.2 := by
  obtain ⟨hb, hs, hc⟩ := weak_recenter_metadata D A h
  have hl' : (A.recenter D h).WellSlotted := by
    change (A.recenter D h).slots.length = (A.recenter D h).children.length + 1
    rw [hs, hc]
    exact hl
  have hctx : (A.recenter D h).ctxLevel = A.ctxLevel := by
    simp only [RealChain.ctxLevel, RealChain.lastLevel, hb, hc]
  have hslot : (A.recenter D h).slot = A.slot := by simp only [RealChain.slot, hs]
  rw [weak_appendChild_geom D (A.recenter D h) hl', hctx, hslot, geom_recenter D A hl h]
  rfl

theorem weak_transfer_child_center_joint_smooth (D : OCData) (A : RealChain) (hl : A.WellSlotted)
    (slot : ℤ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Z : Vec 2 × Vec 2 =>
      (((A.recenter D Z.2).appendChild D slot t
        (Z.1 + (D.eps A.ctxLevel)⁻¹ • Z.2)).geom D).2.1) := by
  have he : (fun Z : Vec 2 × Vec 2 =>
      (((A.recenter D Z.2).appendChild D slot t
        (Z.1 + (D.eps A.ctxLevel)⁻¹ • Z.2)).geom D).2.1) =
      fun Z => (A.geom D).1 (D.slotAnchor (A.ctxLevel + 1) slot)
        ((A.geom D).2.1 + Z.2 + D.eps A.ctxLevel •
          D.relDisp A.ctxLevel A.slot (D.slotAnchor (A.ctxLevel + 1) slot) t
            (Z.1 + (D.eps A.ctxLevel)⁻¹ • Z.2)) (A.geom D).2.2 := by
    funext Z
    exact weak_transfer_child_center_eq D A hl slot t Z.1 Z.2
  rw [he]
  have hf := geomSpatialSmooth_geom D A (D.slotAnchor (A.ctxLevel + 1) slot) (A.geom D).2.2
  have hδ := relDisp_spatial_smooth D A.ctxLevel A.slot (D.slotAnchor (A.ctxLevel + 1) slot) t
  apply hf.comp
  have hphase : ContDiff ℝ (⊤ : ℕ∞) (fun Z : Vec 2 × Vec 2 => Z.1 + (D.eps A.ctxLevel)⁻¹ • Z.2) := by
    fun_prop
  exact (contDiff_const.add contDiff_snd).add ((hδ.comp hphase).const_smul _)

/-! Genuine positive chart jets bound every Jacobian entry after a controlled center change. -/

theorem composed_chart_jacobian_entry_jet_bound
    (F g : Vec 2 → Vec 2) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (K r : ℕ) (hr : r ≤ K) (B C : ℝ) (hB : 1 ≤ B)
    (hFj : ∀ n, 1 ≤ n → n ≤ K + 1 → ∀ y, ‖iteratedFDeriv ℝ n F y‖ ≤ B)
    (hgj : ∀ n, 1 ≤ n → n ≤ K → ∀ y, ‖iteratedFDeriv ℝ n g y‖ ≤ C)
    (i j : Fin 2) (x : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun y => jacMatrix F (g y) i j) x‖ ≤
      positiveJetCompositionBudget K (max B C) := by
  have hj (n : ℕ) (hn : n ≤ K) (y : Vec 2) :
      ‖iteratedFDeriv ℝ n (fun z => jacMatrix F z i j) y‖ ≤ B :=
    (jacobian_entry_derivative_norm_le F hF i j n y).trans (hFj (n + 1) (by omega) (by omega) y)
  have hM : 1 ≤ max B C := hB.trans (le_max_left _ _)
  by_cases hr0 : r = 0
  · subst r
    have hh := (hj 0 (Nat.zero_le _) (g x)).trans
      ((le_max_left B C).trans (positiveJetCompositionBudget_ge_self K (max B C) hM))
    simpa only [norm_iteratedFDeriv_zero] using hh
  · exact finite_positive_jet_composition_bound (fun y => jacMatrix F y i j) g
      (CycleReference.jacMatrix_entry_smooth hF i j) hg K r (by omega) hr x
      (max B C) hM
      (fun n _ hnK => (hj n hnK (g x)).trans (le_max_left _ _))
      (fun n hn hnK => (hgj n hn hnK x).trans (le_max_right _ _))

/-! Constant initial tests carry exactly the diagonal grade-zero weight. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def JointSourceReserve.const (H : ℕ) (c : E) :
    JointSourceReserve H (fun _ _ _ => c) where
  regular _ := contDiff_const
  periodic _ _ _ _ := rfl
  measurable _ := measurable_const
  budget n := if n = 0 then ‖c‖ else 0
  budget_nonneg n := by
    by_cases hn : n = 0
    · rw [ite_eq_left hn]
      exact norm_nonneg _
    · rw [ite_eq_right hn]
  derivative_bound n _ _ X := by
    by_cases hn : n = 0
    · subst n
      simp only [norm_iteratedFDeriv_zero, ite_true, le_refl]
    · rw [iteratedFDeriv_const_of_ne hn]
      simp only [Pi.zero_apply, norm_zero, ite_eq_right hn, le_refl]

omit [BorelSpace E] [SecondCountableTopology E] in
theorem JointSourceReserve.const_budget_le (H : ℕ) (c : E) (r : ℕ) :
    (JointSourceReserve.const H c).budget r ≤ ‖c‖ := by
  change (if r = 0 then ‖c‖ else 0) ≤ ‖c‖
  split_ifs
  · exact le_refl _
  · exact norm_nonneg _

theorem constant_test_matrix_budget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ℕ) (A : ι → ι → ℝ) (v u : ι) (r : ℕ) :
    (JointSourceReserve.const H (if v = u then (1 : ℝ) else 0)).budget r ≤
      CycleComparison.Lift.finiteMatrixPower A 0 v u := by
  rw [CycleComparison.Lift.finiteMatrixPower_zero]
  apply (JointSourceReserve.const_budget_le H _ r).trans_eq
  by_cases h : v = u
  · simp only [ite_eq_left h, norm_one]
  · simp only [ite_eq_right h, norm_zero]
end

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVenhance.Infra.Heat Filter Topology
namespace AVRegularity.EntryWeakProofs

/-! Uniform higher bounds turn Fourier convergence into convergence of classical derivatives. -/

theorem realFourierLift_derivative_majorant_bound (K : ℕ) (f : TorusHk K ℝ)
    (n : ℕ) (hn : n + 2 ≤ K) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (realFourierLift K f) x‖ ≤
      ∑' k : Frequency, realFourierMajorant K f n k := by
  have hs (j : ℕ) (hj : (j : ℕ∞) ≤ (n : ℕ∞)) :
      Summable (realFourierMajorant K f j) := by
    have hjn : j ≤ n := by exact_mod_cast hj
    exact realFourierMajorant_summable K f j (by omega)
  have hd := iteratedFDeriv_tsum_apply (𝕜 := ℝ) (N := (n : ℕ∞))
    (f := realFourierMode K f) (v := realFourierMajorant K f)
    (fun k => (realFourierMode_contDiff K f k).of_le (by simp)) hs
    (fun j k y _ => realFourierMode_derivative_bound K f j k y) (le_refl _) x
  change ‖iteratedFDeriv ℝ n (fun y => ∑' k : Frequency, realFourierMode K f k y) x‖ ≤ _
  rw [hd]
  exact tsum_of_norm_bounded (realFourierMajorant_summable K f n hn).hasSum
    (fun k => realFourierMode_derivative_bound K f n k x)

theorem realFourierLift_derivative_norm_tendsto_zero {A : Type*} {l : Filter A}
    (K : ℕ) (f : A → TorusHk K ℝ) (n : ℕ) (hn : n + 4 ≤ K)
    (R : ℝ) (hR : ∀ᶠ x in l, ‖f x‖ ≤ R)
    (hc : ∀ w : DerivativeWord2 n, ∀ k,
      Tendsto (fun x => realJetFourier K (f x) ⟨⟨n, by omega⟩, w⟩ k) l (𝓝 0))
    (x : Vec 2) :
    Tendsto (fun a => ‖iteratedFDeriv ℝ n (realFourierLift K (f a)) x‖) l (𝓝 0) := by
  have hw (w : DerivativeWord2 n) :
      Tendsto (fun a => ∑' k : Frequency,
        ‖realJetFourier K (f a) ⟨⟨n, by omega⟩, w⟩ k‖) l (𝓝 0) :=
    realJetFourier_norm_sum_tendsto_zero K f ⟨⟨n, by omega⟩, w⟩ hn R hR (hc w)
  have hh := tendsto_finsetSum Finset.univ (fun w _ => hw w)
  have he (a : A) : (∑' k : Frequency, realFourierMajorant K (f a) n k) =
      ∑ w : DerivativeWord2 n, ∑' k : Frequency,
        ‖realJetFourier K (f a) ⟨⟨n, by omega⟩, w⟩ k‖ := by
    simp_rw [realFourierMajorant_eq_word_sum K (f a) n (by omega)]
    exact (hasSum_sum (fun w (_ : w ∈ Finset.univ) =>
      (realJetFourier_norm_summable K (f a) ⟨⟨n, by omega⟩, w⟩ (by change n + 2 ≤ K; omega)).hasSum)).tsum_eq
  have hm : Tendsto (fun a => ∑' k : Frequency, realFourierMajorant K (f a) n k) l (𝓝 0) := by
    simpa only [← he, Finset.sum_const_zero] using hh
  exact squeeze_zero' (Eventually.of_forall (fun a => norm_nonneg _))
    (Eventually.of_forall (fun a => realFourierLift_derivative_majorant_bound K (f a) n
      (by omega) x)) hm

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance.Infra.Heat Filter Topology
namespace AVRegularity.EntryWeakProofs

/-! Convergence of the value class controls every fixed Fourier derivative coefficient. -/

theorem realJetFourier_tendsto_zero_of_value {A : Type*} {l : Filter A}
    (K : ℕ) (f : A → TorusHk K ℝ)
    (hv : Tendsto (fun a => (f a).val (valueIndex2 K)) l (𝓝 0))
    (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n) (k : Frequency) :
    Tendsto (fun a => realJetFourier K (f a) ⟨⟨n, by omega⟩, w⟩ k) l (𝓝 0) := by
  have h0 : Tendsto (fun a => realJetFourier K (f a) (valueIndex2 K) k) l (𝓝 0) := by
    simpa only [realJetFourier_eq_cellCoeff, map_zero, Function.comp_def] using
      (cellFourierCoeffCLM k).continuous.continuousAt.tendsto.comp
        (complexifyCellClass.continuous.continuousAt.tendsto.comp hv)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp_rw [realJetFourier_word_norm K _ n hn w k]
  simpa only [norm_zero, mul_zero] using h0.norm.const_mul
    ((2 * Real.pi) ^ n * ∏ j : Fin n, |(k (w j) : ℝ)|)

theorem realFourierLift_derivative_tendsto_zero_of_value {A : Type*} {l : Filter A}
    (K : ℕ) (f : A → TorusHk K ℝ) (n : ℕ) (hn : n + 4 ≤ K)
    (R : ℝ) (hR : ∀ᶠ a in l, ‖f a‖ ≤ R)
    (hv : Tendsto (fun a => (f a).val (valueIndex2 K)) l (𝓝 0)) (x : Vec 2) :
    Tendsto (fun a => ‖iteratedFDeriv ℝ n (realFourierLift K (f a)) x‖) l (𝓝 0) :=
  realFourierLift_derivative_norm_tendsto_zero K f n hn R hR
    (fun w k => realJetFourier_tendsto_zero_of_value K f hv n (by omega) w k) x

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVenhance
open AVRegularity.Velocity AVRegularity.Velocity.Port
namespace AVRegularity.EntryWeakProofs

/-! Source higher-flow word estimates give full operator-norm estimates in Vec 2. -/

theorem source_flow_derivative_norm {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 1 ≤ m)
    (r t : ℝ) (ht : |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹)
    (n : ℕ) (hn : 1 ≤ n) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun y =>
      Section2FlowIdentities.constructionFlow D hseq m (r + t) y r) x‖ ≤
      (2 : ℝ) ^ n * (2 * n.factorial * (2 ^ 14 * (D.epsilon m)⁻¹) ^ (n - 1)) := by
  generalize hβ : α + 1 = β
  have hα : α = β - 1 := by linarith
  subst α
  obtain ⟨_, C, _, hf⟩ := StreamRegularity.section2_induction_outputs_from_source_data D hseq
  refine (ChartTransport.norm_le_sum_basisVec _).trans ?_
  calc
    _ ≤ ∑ _ : Sobolev.DerivativeWord2 n,
        2 * n.factorial * (2 ^ 14 * (D.epsilon m)⁻¹) ^ (n - 1) :=
      Finset.sum_le_sum (fun J _ => hf.flow_higher_derivative m hm r t ht n hn x J)
    _ = _ := by simp [Sobolev.DerivativeWord2, Fintype.card_fin]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! The literal fast and slow partials in the lift recursion spend one joint derivative. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def JointSourceReserve.fastPartial {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (R : ℕ) (hR : 1 + R ≤ H) (i : Fin 2) :
    JointSourceReserve R (fun t z Y => AVRegularity.fastPartial i (fun X y => f t y X) Y z) := by
  have he : sourceFastWord f 1 (fun _ => basisVec i) =
      fun t z Y => AVRegularity.fastPartial i (fun X y => f t y X) Y z := by
    funext t z Y
    simp only [sourceFastWord, realWordJet, iteratedFDeriv_one_apply, AVRegularity.fastPartial]
  exact (Q.fastWord 1 R hR (fun _ => basisVec i)
    (fun _ => by rw [AVRegularity.ChartTransport.norm_basisVec])).congrSource he

def JointSourceReserve.slowPartial {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (R : ℕ) (hR : 1 + R ≤ H) (i : Fin 2) :
    JointSourceReserve R (fun t z Y => AVRegularity.slowPartial i (fun X y => f t y X) Y z) := by
  have he : sourceSlowWord f 1 (fun _ => basisVec i) =
      fun t z Y => AVRegularity.slowPartial i (fun X y => f t y X) Y z := by
    funext t z Y
    simp only [sourceSlowWord, realWordJet, iteratedFDeriv_one_apply, AVRegularity.slowPartial]
  exact (Q.slowWord 1 R hR (fun _ => basisVec i)
    (fun _ => by rw [AVRegularity.ChartTransport.norm_basisVec])).congrSource he

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVenhance
open AVRegularity.Velocity AVRegularity.Velocity.Port
namespace AVRegularity.EntryWeakProofs

/-! Full spatial derivative bounds for the actual coarse flow. -/

theorem actual_coarse_flow_derivative_norm (D : OCData) (s : ℝ)
    (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - D.α) / 2)
    (hq : IsAdmissibleQ D.α s D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (m : ℕ) (hm : 1 ≤ m) (r t : ℝ)
    (ht : |t - r| ≤ 2 ^ (-25 : ℤ) * (ocA D.α D.q D.Λ m)⁻¹)
    (n : ℕ) (hn : 1 ≤ n) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun y => D.flowOf m t y r) x‖ ≤
      (2 : ℝ) ^ n * (2 * n.factorial * (2 ^ 14 * (D.eps m)⁻¹) ^ (n - 1)) := by
  let J := ocJetRecursionData D.α s hα₀ hα₁ hs₀ hs₁ D.q hq D.Λ hΛ D.ζ hζ
  have hc := source_flow_derivative_norm J hseq m hm r (t - r) ht n hn x
  simpa only [Section2FlowIdentities.constructionFlow, OCData.flowOf,
    Section2FlowIdentities.streamFlow, AVRegularity.streamFlow, J, ocJetRecursionData,
    add_sub_cancel, OCData.eps] using hc

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVenhance.Infra.Heat Filter Topology
namespace AVRegularity.EntryWeakProofs

/-! Canonical classical difference quotients and convergence from bounded higher error carriers. -/

theorem realClassicalLift_sub (K : ℕ) (hK : 2 ≤ K) (f g : TorusHk K ℝ) :
    realClassicalLift K (f - g) = realClassicalLift K f - realClassicalLift K g := by
  rw [sub_eq_add_neg, show -g = (-1 : ℝ) • g by simp]
  rw [realClassicalLift_add K hK, realClassicalLift_smul K hK]
  simp only [neg_one_smul, sub_eq_add_neg]

theorem realClassicalLift_derivative_tendsto_zero_of_value {A : Type*} {l : Filter A}
    (K : ℕ) (f : A → TorusHk K ℝ) (n : ℕ) (hn : n + 4 ≤ K)
    (R : ℝ) (hR : ∀ᶠ a in l, ‖f a‖ ≤ R)
    (hv : Tendsto (fun a => (f a).val (valueIndex2 K)) l (𝓝 0)) (x : Vec 2) :
    Tendsto (fun a => ‖iteratedFDeriv ℝ n (realClassicalLift K (f a)) x‖) l (𝓝 0) := by
  have hh := realFourierLift_derivative_tendsto_zero_of_value K f n hn R hR hv x
  have hb (a : A) : ‖iteratedFDeriv ℝ n (realClassicalLift K (f a)) x‖ ≤
      ‖Complex.reCLM‖ * ‖iteratedFDeriv ℝ n (realFourierLift K (f a)) x‖ := by
    change ‖iteratedFDeriv ℝ n (Complex.reCLM ∘ realFourierLift K (f a)) x‖ ≤ _
    rw [Complex.reCLM.iteratedFDeriv_comp_left
      (realFourierLift_contDiff K n (by omega) (f a)).contDiffAt (le_refl _)]
    exact Complex.reCLM.norm_compContinuousMultilinearMap_le _
  have hz := hh.const_mul ‖Complex.reCLM‖
  simp only [mul_zero] at hz
  exact squeeze_zero (fun _ => norm_nonneg _) hb hz

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! The relative shear Jacobian is small on a finer renewal window. -/

theorem childShearMap_fderiv_sub_id (D : OCData) (k : ℕ) (hε : 0 < D.eps k)
    (pk : ℤ) (u r : ℝ) (c : ChainChild) (g : ChainGeom) (x : Vec 2) :
    fderiv ℝ (childShearMap D k pk u r c g) x - ContinuousLinearMap.id ℝ (Vec 2) =
      (∫ t in r..u, ocPulse D.α D.q D.Λ D.ζ k pk t) •
        fderiv ℝ (ocShearVel D.α D.q D.Λ k pk)
          (x + D.eps k • (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center))) := by
  let γ := D.eps k • (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center))
  let I := ∫ t in r..u, ocPulse D.α D.q D.Λ D.ζ k pk t
  have hs := ((ocShearVel_spatial_smooth D.α D.q D.Λ k pk).differentiable
    (by simp) (x + γ)).hasFDerivAt
  have ht := hs.comp x ((hasFDerivAt_id x).add_const γ)
  have hf := (hasFDerivAt_id x).add (ht.const_smul I)
  have he : childShearMap D k pk u r c g = fun y => y + I • ocShearVel D.α D.q D.Λ k pk (y + γ) :=
    funext (childShearMap_physical D k hε pk u r c g)
  have hfd : fderiv ℝ (fun y => y + I • ocShearVel D.α D.q D.Λ k pk (y + γ)) x =
      ContinuousLinearMap.id ℝ (Vec 2) + I • fderiv ℝ (ocShearVel D.α D.q D.Λ k pk) (x + γ) := by
    simpa only [Function.comp_def, Pi.add_def, Pi.smul_def, id_eq,
      ContinuousLinearMap.comp_id] using hf.fderiv
  rw [he, hfd]
  simp only [add_sub_cancel_left]
  rfl

theorem childShearMap_operator_close (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (k : ℕ) (pk : ℤ) (hpk : Odd pk)
    (u r : ℝ) (c : ChainChild) (g : ChainGeom) (x : Vec 2) :
    ‖fderiv ℝ (childShearMap D k pk u r c g) x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
      |u - r| * ((4 * Real.pi ^ 2) * ocA D.α D.q D.Λ k) := by
  have hε : 0 < D.eps k := Construction.Stream.ocEpsilon_pos hΛ
  rw [childShearMap_fderiv_sub_id D k hε, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (pulse_integral_abs_le D hζ k pk u r)
    (physical_shear_fderiv_norm_le hΛ pk hpk _) (norm_nonneg _)
    (abs_nonneg _)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Finite classical fast jets preserve the genuine linear higher-carrier readout. -/

theorem realClassicalLift_jet_sub (K n : ℕ) (hn : n + 2 ≤ K)
    (f g : TorusHk K ℝ) (z : Vec 2) :
    iteratedFDeriv ℝ n (realClassicalLift K (f - g)) z =
      iteratedFDeriv ℝ n (realClassicalLift K f) z -
        iteratedFDeriv ℝ n (realClassicalLift K g) z := by
  rw [realClassicalLift_sub K (by omega)]
  exact iteratedFDeriv_sub_apply (realClassicalLift_contDiff K n hn f).contDiffAt
    (realClassicalLift_contDiff K n hn g).contDiffAt

theorem realClassicalLift_jet_smul (K n : ℕ) (hn : n + 2 ≤ K)
    (c : ℝ) (f : TorusHk K ℝ) (z : Vec 2) :
    iteratedFDeriv ℝ n (realClassicalLift K (c • f)) z =
      c • iteratedFDeriv ℝ n (realClassicalLift K f) z := by
  rw [realClassicalLift_smul K (by omega)]
  exact iteratedFDeriv_const_smul_apply (realClassicalLift_contDiff K n hn f).contDiffAt

theorem realClassicalLift_jet_quotient_error (K n : ℕ) (hn : n + 2 ≤ K)
    (c : ℝ) (f f₀ g : TorusHk K ℝ) (z : Vec 2) :
    iteratedFDeriv ℝ n (realClassicalLift K (c • (f - f₀) - g)) z =
      c • (iteratedFDeriv ℝ n (realClassicalLift K f) z -
        iteratedFDeriv ℝ n (realClassicalLift K f₀) z) -
          iteratedFDeriv ℝ n (realClassicalLift K g) z := by
  rw [realClassicalLift_jet_sub K n hn, realClassicalLift_jet_smul K n hn,
    realClassicalLift_jet_sub K n hn]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.CycleReference
namespace AVRegularity.EntryWeakProofs

/-! Every odd-slot relative shear preserves area. -/

theorem childShearMap_jacobian_det_one (D : OCData) (k : ℕ) (hε : 0 < D.eps k)
    (pk : ℤ) (hpk : Odd pk) (u r : ℝ) (c : ChainChild) (g : ChainGeom) (x : Vec 2) :
    (jacMatrix (childShearMap D k pk u r c g) x).det = 1 := by
  let γ := D.eps k • (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center))
  let I := ∫ t in r..u, ocPulse D.α D.q D.Λ D.ζ k pk t
  let A := 2 * Real.pi * ocEpsilon D.q D.Λ k ^ (1 + D.α) *
    (ocEpsilon D.q D.Λ k)⁻¹
  let ω := 2 * Real.pi * (ocEpsilon D.q D.Λ k)⁻¹
  have hmod : pk % 4 = 1 ∨ pk % 4 = 3 := by
    rcases hpk with ⟨l, hl⟩
    have hn := Int.emod_nonneg pk (b := 4) (by norm_num)
    have hu := Int.emod_lt pk (b := 4) (by norm_num)
    omega
  have he : childShearMap D k pk u r c g =
      fun y => y + I • ocShearVel D.α D.q D.Λ k pk (y + γ) :=
    funext (childShearMap_physical D k hε pk u r c g)
  rw [he]
  rcases hmod with h1 | h3
  · have hf : (fun y : Vec 2 => y + I • ocShearVel D.α D.q D.Λ k pk (y + γ)) =
        fun y => y + (I * A * Real.cos (ω * (y 0 + γ 0))) • basisVec 1 := by
      funext y
      rw [ocShearVel_horizontal h1 (y + γ)]
      ext i
      fin_cases i <;> simp [basisVec, A, ω, smul_eq_mul, mul_assoc]
    rw [hf]
    exact transverse_shear_jacobian_det_one
      (fun z => I * A * Real.cos (ω * (z + γ 0))) (by fun_prop) 0 x
  · have hf : (fun y : Vec 2 => y + I • ocShearVel D.α D.q D.Λ k pk (y + γ)) =
        fun y => y + (-I * A * Real.cos (ω * (y 1 + γ 1))) • basisVec 0 := by
      funext y
      rw [ocShearVel_vertical h3 (y + γ)]
      ext i
      fin_cases i <;> simp [basisVec, A, ω, smul_eq_mul, mul_assoc]
    rw [hf]
    exact transverse_shear_jacobian_det_one
      (fun z => -I * A * Real.cos (ω * (z + γ 1))) (by fun_prop) 1 x

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! Normalized slow differentiation and scalar products retain genuine joint reserves. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def sourceCovariantSlow (A : Vec 2 →L[ℝ] ℝ) (i : Fin 2)
    (f : ℝ → Vec 2 → Vec 2 → E) (t : ℝ) (z Y : Vec 2) : E :=
  AVRegularity.slowPartial i (fun X y => f t y X) Y z + A (basisVec i) • f t z Y

def JointSourceReserve.covariantSlow {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (R : ℕ) (hR : 1 + R ≤ H)
    (A : Vec 2 →L[ℝ] ℝ) (i : Fin 2) : JointSourceReserve R (sourceCovariantSlow A i f) :=
  (Q.slowPartial R hR i).add
    ((Q.mono R (by omega)).map (A (basisVec i) • ContinuousLinearMap.id ℝ E))

def JointSourceReserve.scalarProduct {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → ℝ}
    {g : ℝ → Vec 2 → Vec 2 → E} (Q : JointSourceReserve H f)
    (R : JointSourceReserve H g) : JointSourceReserve H (fun t z Y => f t z Y • g t z Y) :=
  Q.bilinear R (ContinuousLinearMap.lsmul ℝ ℝ)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Mean-free scalar extensions give mean-free continuous linear coefficient maps. -/

variable {ι : Type*}

theorem realLinearMap_field_continuous_of_value_one {X : Type*} [TopologicalSpace X]
    (f : X → ℝ →L[ℝ] ℝ) (hf : Continuous (fun x => f x 1)) : Continuous f := by
  have he : f = fun x => f x 1 • ContinuousLinearMap.id ℝ ℝ := by
    funext x
    apply DFunLike.ext
    intro r
    have h := (f x).map_smul r 1
    simpa only [smul_eq_mul, mul_one, smul_apply, ContinuousLinearMap.id_apply, mul_comm]
      using h
  rw [he]
  exact hf.smul continuous_const

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Bounded complex higher traces upgrade value convergence to classical real-jet convergence. -/

theorem higherRealPart_derivative_tendsto_zero {A : Type*} {l : Filter A}
    (K : ℕ) (f : A → TorusHk K ℂ) (n : ℕ) (hn : n + 4 ≤ K)
    (R : ℝ) (hR : ∀ᶠ a in l, ‖f a‖ ≤ R)
    (hv : Tendsto (fun a => (f a).val (valueIndex2 K)) l (𝓝 0)) (x : Vec 2) :
    Tendsto (fun a => ‖iteratedFDeriv ℝ n
      (realClassicalLift K (mapTorusHk Complex.reCLM (f a))) x‖) l (𝓝 0) := by
  let L := mapTorusHkCLM K Complex.reCLM
  have hb : ∀ᶠ a in l, ‖L (f a)‖ ≤ ‖L‖ * R := by
    filter_upwards [hR] with a ha
    exact (L.le_opNorm (f a)).trans (mul_le_mul_of_nonneg_left ha (norm_nonneg L))
  have hh : Tendsto (fun a => (mapTorusHk Complex.reCLM (f a)).val (valueIndex2 K)) l (𝓝 0) := by
    simp_rw [mapTorusHk_jet_eq_compLp]
    have ht := (Complex.reCLM.compLpL 2 (volume.restrict AVenhance.unitCube)).continuous.continuousAt.tendsto.comp hv
    simpa only [Function.comp_def, map_zero] using ht
  exact realClassicalLift_derivative_tendsto_zero_of_value K
    (fun a => mapTorusHk Complex.reCLM (f a)) n hn (‖L‖ * R) (by simpa only [L, mapTorusHkCLM_apply] using hb) hh x

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Slow differentiation of an exponential test is the literal bounded covariant operation. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalized_slowPartial_exp_smul (A : Vec 2 →L[ℝ] ℝ) (i : Fin 2)
    (f : ℝ → Vec 2 → Vec 2 → E) (t : ℝ) (z Y : Vec 2)
    (hf : DifferentiableAt ℝ (fun X => f t z X) Y) :
    (Real.exp (A Y))⁻¹ • AVRegularity.slowPartial i
      (fun X y => Real.exp (A X) • f t y X) Y z = sourceCovariantSlow A i f t z Y := by
  have hd := (A.hasFDerivAt (x := Y)).exp.smul hf.hasFDerivAt
  change HasFDerivAt (fun X => Real.exp (A X) • f t z X) _ Y at hd
  rw [AVRegularity.slowPartial, hd.fderiv]
  simp only [sourceCovariantSlow, AVRegularity.slowPartial, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, smul_add, smul_smul,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero _), one_mul, one_smul]

theorem slowPartial_exp_smul (A : Vec 2 →L[ℝ] ℝ) (i : Fin 2)
    (f : ℝ → Vec 2 → Vec 2 → E) (t : ℝ) (z Y : Vec 2)
    (hf : DifferentiableAt ℝ (fun X => f t z X) Y) :
    AVRegularity.slowPartial i (fun X y => Real.exp (A X) • f t y X) Y z =
      Real.exp (A Y) • sourceCovariantSlow A i f t z Y := by
  calc
    _ = Real.exp (A Y) • ((Real.exp (A Y))⁻¹ • AVRegularity.slowPartial i
        (fun X y => Real.exp (A X) • f t y X) Y z) := by
      rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
    _ = _ := by rw [normalized_slowPartial_exp_smul A i f t z Y hf]

theorem normalized_fastPartial_exp_smul (A : Vec 2 →L[ℝ] ℝ) (i : Fin 2)
    (f : ℝ → Vec 2 → Vec 2 → E) (t : ℝ) (z Y : Vec 2)
    (hf : DifferentiableAt ℝ (fun y => f t y Y) z) :
    (Real.exp (A Y))⁻¹ • AVRegularity.fastPartial i
      (fun X y => Real.exp (A X) • f t y X) Y z =
      AVRegularity.fastPartial i (fun X y => f t y X) Y z := by
  have hd := hf.hasFDerivAt.const_smul (Real.exp (A Y))
  change HasFDerivAt (fun y => Real.exp (A Y) • f t y Y) _ z at hd
  rw [AVRegularity.fastPartial, hd.fderiv]
  simp only [smul_apply, smul_smul, inv_mul_cancel₀ (Real.exp_ne_zero _), one_smul,
    AVRegularity.fastPartial]

theorem fastPartial_exp_smul (A : Vec 2 →L[ℝ] ℝ) (i : Fin 2)
    (f : ℝ → Vec 2 → Vec 2 → E) (t : ℝ) (z Y : Vec 2)
    (hf : DifferentiableAt ℝ (fun y => f t y Y) z) :
    AVRegularity.fastPartial i (fun X y => Real.exp (A X) • f t y X) Y z =
      Real.exp (A Y) • AVRegularity.fastPartial i (fun X y => f t y X) Y z := by
  calc
    _ = Real.exp (A Y) • ((Real.exp (A Y))⁻¹ • AVRegularity.fastPartial i
        (fun X y => Real.exp (A X) • f t y X) Y z) := by
      rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
    _ = _ := by rw [normalized_fastPartial_exp_smul A i f t z Y hf]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Locally bounded higher carriers give continuity of every reserved classical fast jet. -/

theorem higher_carrier_real_jet_tendsto {A : Type*} (l : Filter A)
    (K n : ℕ) (hn : n + 4 ≤ K) (w : A → TorusHk K ℂ) (v : TorusHk K ℂ)
    (hv : Tendsto (fun a => (w a - v).val (valueIndex2 K)) l (𝓝 0))
    (R : ℝ) (hb : ∀ᶠ a in l, ‖w a‖ ≤ R) (z : Vec 2) :
    Tendsto (fun a => iteratedFDeriv ℝ n
      (realClassicalLift K (mapTorusHk Complex.reCLM (w a))) z) l
      (𝓝 (iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM v)) z)) := by
  have he : ∀ᶠ a in l, ‖w a - v‖ ≤ R + ‖v‖ := by
    filter_upwards [hb] with a ha
    exact (norm_sub_le _ _).trans (add_le_add ha (le_refl ‖v‖))
  have ht := higherRealPart_derivative_tendsto_zero K (fun a => w a - v)
    n hn (R + ‖v‖) he hv z
  have hid (a : A) :
      iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM (w a - v))) z =
      iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM (w a))) z -
        iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM v)) z := by
    simp only [← mapTorusHkCLM_apply, map_sub]
    exact realClassicalLift_jet_sub K n (by omega) _ _ z
  simp_rw [hid] at ht
  exact tendsto_sub_nhds_zero_iff.mp (tendsto_zero_iff_norm_tendsto_zero.mpr ht)

/-! Genuine slow derivatives of every reserved classical fast jet. -/

theorem higher_carrier_real_jet_hasDerivAt (K n : ℕ) (hn : n + 4 ≤ K)
    (w : ℝ → TorusHk K ℂ) (v : TorusHk K ℂ)
    (hv : Tendsto (fun h : ℝ =>
      (h⁻¹ • (w h - w 0) - v).val (valueIndex2 K)) (𝓝[≠] 0) (𝓝 0))
    (R : ℝ) (hb : ∀ᶠ h : ℝ in 𝓝[≠] 0, ‖h⁻¹ • (w h - w 0) - v‖ ≤ R)
    (z : Vec 2) :
    HasDerivAt (fun h => iteratedFDeriv ℝ n
      (realClassicalLift K (mapTorusHk Complex.reCLM (w h))) z)
      (iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM v)) z) 0 := by
  have ht := higherRealPart_derivative_tendsto_zero K
    (fun h : ℝ => h⁻¹ • (w h - w 0) - v) n hn R hb hv z
  have he (h : ℝ) :
      iteratedFDeriv ℝ n
        (realClassicalLift K (mapTorusHk Complex.reCLM (h⁻¹ • (w h - w 0) - v))) z =
      h⁻¹ • (iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM (w h))) z -
        iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM (w 0))) z) -
          iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM v)) z := by
    simp only [← mapTorusHkCLM_apply, map_sub, map_smul]
    exact realClassicalLift_jet_quotient_error K n (by omega) _ _ _ _ z
  simp_rw [he] at ht
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add]
  exact tendsto_sub_nhds_zero_iff.mp (tendsto_zero_iff_norm_tendsto_zero.mpr ht)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Ordered exponential tests consume only the actual length of their slow word. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def sourceCovariantWord (A : Vec 2 →L[ℝ] ℝ) (f : ℝ → Vec 2 → Vec 2 → E) :
    (n : ℕ) → DerivativeWord2 n → ℝ → Vec 2 → Vec 2 → E
  | 0, _ => f
  | n + 1, α => sourceCovariantSlow A (α (Fin.last n))
      (sourceCovariantWord A f n (fun i => α i.castSucc))

def JointSourceReserve.covariantWord {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (n R : ℕ) (h : n + R ≤ H)
    (A : Vec 2 →L[ℝ] ℝ) (α : DerivativeWord2 n) :
    JointSourceReserve R (sourceCovariantWord A f n α) := by
  induction n generalizing R with
  | zero => exact Q.mono R (by omega)
  | succ n ih =>
      exact (ih (R + 1) (by omega) (fun i => α i.castSucc)).covariantSlow R
        (by omega) A (α (Fin.last n))

theorem orderedDerivative_exp_smul_covariantWord {H : ℕ}
    {f : ℝ → Vec 2 → Vec 2 → E} (Q : JointSourceReserve H f)
    (n : ℕ) (hn : n ≤ H) (A : Vec 2 →L[ℝ] ℝ) (α : DerivativeWord2 n)
    (t : ℝ) (z Y : Vec 2) :
    orderedDerivative α (fun X => Real.exp (A X) • f t z X) Y =
      Real.exp (A Y) • sourceCovariantWord A f n α t z Y := by
  induction n generalizing Y with
  | zero => rfl
  | succ n ih =>
      rw [orderedDerivative_succ]
      have he : orderedDerivative (fun i => α i.castSucc)
          (fun X => Real.exp (A X) • f t z X) =
          fun X => Real.exp (A X) •
            sourceCovariantWord A f n (fun i => α i.castSucc) t z X :=
        funext (fun X => ih (by omega) (fun i => α i.castSucc) X)
      rw [he]
      let R := Q.covariantWord n 1 (by omega) A (fun i => α i.castSucc)
      have hd : DifferentiableAt ℝ
          (fun X => sourceCovariantWord A f n (fun i => α i.castSucc) t z X) Y :=
        ((R.regular t).comp₂ (contDiff_const (c := z)) contDiff_id).differentiable
          (by simp) Y
      exact slowPartial_exp_smul A (α (Fin.last n)) _ t z Y hd

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Entrywise extraction of the actual coarse-flow Jacobian estimate. -/

theorem jacobian_entry_close_of_operator_norm (f : Vec 2 → Vec 2) (x : Vec 2)
    (B : ℝ) (hb : ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ B)
    (i j : Fin 2) :
    |jacMatrix f x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ B := by
  have he : jacMatrix f x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j =
      (fderiv ℝ f x - ContinuousLinearMap.id ℝ (Vec 2)) (basisVec j) i := by
    simp [jacMatrix, basisVec, Matrix.one_apply, Pi.single_apply]
  rw [he, ← Real.norm_eq_abs]
  have hj : ‖basisVec j‖ = 1 := by simp [basisVec, Pi.norm_single]
  exact (norm_le_pi_norm _ i).trans
    (((fderiv ℝ f x - ContinuousLinearMap.id ℝ (Vec 2)).le_opNorm _).trans
      (by simpa only [hj, mul_one] using hb))

/-! Directional derivative constructors preserve the literal shifted source budget. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem JointSourceReserve.fastPartial_budget {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (R : ℕ) (hR : 1 + R ≤ H) (i : Fin 2) (n : ℕ) :
    (Q.fastPartial R hR i).budget n = Q.budget (1 + n) := by
  simp only [JointSourceReserve.fastPartial, JointSourceReserve.congrSource_budget]
  rfl

theorem JointSourceReserve.slowPartial_budget {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (R : ℕ) (hR : 1 + R ≤ H) (i : Fin 2) (n : ℕ) :
    (Q.slowPartial R hR i).budget n = Q.budget (1 + n) := by
  simp only [JointSourceReserve.slowPartial, JointSourceReserve.congrSource_budget]
  rfl

theorem JointSourceReserve.covariantSlow_budget {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (R : ℕ) (hR : 1 + R ≤ H)
    (A : Vec 2 →L[ℝ] ℝ) (i : Fin 2) (n : ℕ) :
    (Q.covariantSlow R hR A i).budget n = Q.budget (1 + n) +
      ‖A (basisVec i) • ContinuousLinearMap.id ℝ E‖ * Q.budget n := by
  change (Q.slowPartial R hR i).budget n +
    ‖A (basisVec i) • ContinuousLinearMap.id ℝ E‖ * Q.budget n = _
  rw [JointSourceReserve.slowPartial_budget]
end

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Literal spatially constant metric fluxes in the higher Sobolev carrier. -/

abbrev ComplexCellVector := PiLp 2 (fun _ : Fin 2 => ℂ)

def vectorSlotCLM (i : Fin 2) : ℂ →L[ℝ] ComplexCellVector :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℂ) i)

def metricEntryFiberCLM (i j : Fin 2) : ComplexCellVector →L[ℝ] ComplexCellVector :=
  (vectorSlotCLM i).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j)

def metricEntryGradientCLM (K : ℕ) (i j : Fin 2) :
    TorusHk (K + 1) ℂ →L[ℝ] TorusHk K ComplexCellVector :=
  (mapTorusHkCLM K (metricEntryFiberCLM i j)).comp (torusGradientTensorCLM K)

def metricGradientCarrier (K : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (w : TorusHk (K + 1) ℂ) : TorusHk K ComplexCellVector :=
  ∑ i : Fin 2, ∑ j : Fin 2, A i j • metricEntryGradientCLM K i j w

def metricGradientCarrierConstant (K : ℕ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, ‖metricEntryGradientCLM K i j‖

theorem metricGradientCarrierConstant_nonneg (K : ℕ) : 0 ≤ metricGradientCarrierConstant K := by
  unfold metricGradientCarrierConstant
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact norm_nonneg (metricEntryGradientCLM K i j)

theorem metricGradientCarrier_norm_le (K : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ B) (w : TorusHk (K + 1) ℂ) :
    ‖metricGradientCarrier K A w‖ ≤ B * metricGradientCarrierConstant K * ‖w‖ := by
  unfold metricGradientCarrier
  apply (norm_sum_le _ _).trans
  calc
    (∑ i : Fin 2, ‖∑ j : Fin 2, A i j • metricEntryGradientCLM K i j w‖) ≤
        ∑ i : Fin 2, ∑ j : Fin 2, B * (‖metricEntryGradientCLM K i j‖ * ‖w‖) := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hA i j) ((metricEntryGradientCLM K i j).le_opNorm w)
        (norm_nonneg _) hB
    _ = _ := by
      simp only [metricGradientCarrierConstant, Finset.mul_sum, Finset.sum_mul, mul_assoc]

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Measurable periodic H^K slice classes for raw product-space weak jets. -/

/-- Inject one spatial L² class into the finite ordered-jet Hilbert product. -/
def dataJetEntryCLM (K : ℕ) (a : JetIndex2 K) :
    Lp ℂ 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      JetL2 (volume.restrict AVenhance.unitCube) K ℂ :=
  let L : Lp ℂ 2 (volume.restrict AVenhance.unitCube) →ₗ[ℝ]
      JetL2 (volume.restrict AVenhance.unitCube) K ℂ :=
    { toFun := PiLp.single (β := fun _ : JetIndex2 K => Lp ℂ 2 (volume.restrict AVenhance.unitCube)) 2 a
      map_add' := by intro x y; exact PiLp.single_add (β := fun _ : JetIndex2 K => Lp ℂ 2 (volume.restrict AVenhance.unitCube)) 2 a
      map_smul' := by
        intro r x
        apply PiLp.ext
        intro b
        by_cases h : b = a
        · subst b; simp
        · simp [h] }
  L.mkContinuous 1 (by
    intro x
    change ‖PiLp.single (β := fun _ : JetIndex2 K =>
      Lp ℂ 2 (volume.restrict AVenhance.unitCube)) 2 a x‖ ≤ 1 * ‖x‖
    rw [PiLp.norm_single, one_mul])

/-- Total spatial class of every ordered raw jet component. -/
def dataRawJetSlices (K : ℕ) (D : ℝ → RawJet2 K ℂ) (t : ℝ) :
    JetL2 (volume.restrict AVenhance.unitCube) K ℂ :=
  ∑ a : JetIndex2 K, dataJetEntryCLM K a (cellSourceSlice (fun s x => D s a x) t)

/-- The raw jet class is Bochner L² when every raw component is product L². -/
theorem dataRawJetSlices_memLp (K : ℕ) (I : Set ℝ) (D : ℝ → RawJet2 K ℂ)
    (hD : ∀ a, MemLp (fun p : ℝ × Vec 2 => D p.1 a p.2) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    MemLp (dataRawJetSlices K D) 2 (volume.restrict I) := by
  apply memLp_finsetSum Finset.univ
  intro a _
  exact (dataJetEntryCLM K a).comp_memLp' (cellSourceSlice_memLp I (fun t x => D t a x) (hD a))

/-- At every genuine weak-jet slice this is its literal spatial Sobolev class. -/
theorem dataRawJetSlices_eq_toL2 (K : ℕ) (D : ℝ → RawJet2 K ℂ) (t : ℝ)
    (ht : HasPeriodicOrderedWeakJet (D t)) :
    dataRawJetSlices K D t = torusJetToL2 (D t) ht.2.1 := by
  apply PiLp.ext
  intro a
  simp [dataRawJetSlices, dataJetEntryCLM, cellSourceSlice, dite_eq_left (ht.2.1 a), torusJetToL2]

/-- Project the total raw class onto the closed periodic H^K graph. Exceptional slices are harmless. -/
def dataHkSlice (K : ℕ) (D : ℝ → RawJet2 K ℂ) (t : ℝ) : TorusHk K ℂ :=
  (torusHkGraph (E := ℂ) K).toSubmodule.orthogonalProjectionOnto (dataRawJetSlices K D t)

/-- The periodic H^K slice classes are Bochner L². -/
theorem dataHkSlice_memLp (K : ℕ) (I : Set ℝ) (D : ℝ → RawJet2 K ℂ)
    (hD : ∀ a, MemLp (fun p : ℝ × Vec 2 => D p.1 a p.2) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    MemLp (dataHkSlice K D) 2 (volume.restrict I) :=
  (torusHkGraph (E := ℂ) K).toSubmodule.orthogonalProjectionOnto.comp_memLp'
    (dataRawJetSlices_memLp K I D hD)

/-- Projection does not change an actual periodic weak jet. -/
theorem dataHkSlice_eq_toHk (K : ℕ) (D : ℝ → RawJet2 K ℂ) (t : ℝ)
    (ht : HasPeriodicOrderedWeakJet (D t)) :
    dataHkSlice K D t = (TorusHkFunction.mk (D t) ht).toHk := by
  unfold dataHkSlice
  rw [dataRawJetSlices_eq_toL2 K D t ht]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    ((TorusHkFunction.mk (D t) ht).toHk)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! One representative per two-dimensional word orbit preserves exact symmetry without averaging costs. -/

def canonicalDerivativeWord {m : ℕ} (α : DerivativeWord2 m) : DerivativeWord2 m :=
  Classical.choose (show ∃ β : DerivativeWord2 m,
    wordZeroMultiplicity β = wordZeroMultiplicity α from ⟨α, rfl⟩)

theorem canonicalDerivativeWord_multiplicity {m : ℕ} (α : DerivativeWord2 m) :
    wordZeroMultiplicity (canonicalDerivativeWord α) = wordZeroMultiplicity α :=
  Classical.choose_spec (show ∃ β : DerivativeWord2 m,
    wordZeroMultiplicity β = wordZeroMultiplicity α from ⟨α, rfl⟩)

theorem wordZeroMultiplicity_comp_perm {m : ℕ} (α : DerivativeWord2 m)
    (σ : Equiv.Perm (Fin m)) : wordZeroMultiplicity (α ∘ σ) = wordZeroMultiplicity α := by
  apply Fintype.card_congr
  exact {
    toFun := fun i => ⟨σ i.val, i.property⟩
    invFun := fun i => ⟨σ.symm i.val, by
      change α (σ (σ.symm i.val)) = 0
      rw [σ.apply_symm_apply]
      exact i.property⟩
    left_inv := fun i => Subtype.ext (σ.symm_apply_apply i.val)
    right_inv := fun i => Subtype.ext (σ.apply_symm_apply i.val) }

theorem canonicalDerivativeWord_comp_perm {m : ℕ} (α : DerivativeWord2 m)
    (σ : Equiv.Perm (Fin m)) : canonicalDerivativeWord (α ∘ σ) = canonicalDerivativeWord α := by
  simp only [canonicalDerivativeWord, wordZeroMultiplicity_comp_perm]

theorem symmetric_word_canonical_value {m : ℕ} {E : Type*} (c : DerivativeWord2 m → E)
    (hs : ∀ α (σ : Equiv.Perm (Fin m)), c (α ∘ σ) = c α) (α : DerivativeWord2 m) :
    c (canonicalDerivativeWord α) = c α :=
  symmetric_word_value_of_fiber_card c hs _ α
    (word_fiber_card_eq_of_zeroMultiplicity _ α (canonicalDerivativeWord_multiplicity α))

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Literal readout algebra for finite sums of higher source carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

theorem higherCarrier_add_value_ae (K : ℕ) (u v : TorusHk K E) (f g : Vec 2 → E)
    (hu : torusHkValueCLM u =ᵐ[volume.restrict AVenhance.unitCube] f)
    (hv : torusHkValueCLM v =ᵐ[volume.restrict AVenhance.unitCube] g) :
    torusHkValueCLM (u + v) =ᵐ[volume.restrict AVenhance.unitCube] f + g := by
  rw [map_add]
  exact (Lp.coeFn_add _ _).trans (hu.add hv)

end AVRegularity.EntryWeakProofs
end
