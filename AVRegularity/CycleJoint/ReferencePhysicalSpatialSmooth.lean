-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlaneScalarWeightedEnergyHomogeneity
import AVRegularity.CycleJoint.PlaneJetMultiplierSuperposition
import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
import AVRegularity.CycleJoint.WeightedGradientLiftComparison
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! A scalar partition weight bounded by one contracts the actual polynomial factorial energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem chartScalarEnergy_unit_smul_le (q : Vec 2 → ℝ) (hq : ∀ x, 0 ≤ q x)
    (c : ℝ) (hc : |c| ≤ 1) (U : Lp E 2 (volume : Measure (Vec 2))) :
    chartScalarEnergy q (c • U) ≤ chartScalarEnergy q U := by
  apply lintegral_mono_ae
  filter_upwards [Lp.coeFn_smul c U] with x hx
  rw [hx]
  have hn : ‖c • U x‖ ≤ ‖U x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg (U x))
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hn 2) (hq x))

theorem storedChartFactorialEnergy_unit_smul_le {K : ℕ} (ρ : ℝ)
    (q : Vec 2 → ℝ) (hq : ∀ x, 0 ≤ q x) (c : ℝ) (hc : |c| ≤ 1)
    (U : PlaneHk Set.univ K E) :
    storedChartFactorialEnergy ρ q (c • U) ≤ storedChartFactorialEnergy ρ q U := by
  unfold storedChartFactorialEnergy
  apply Finset.sum_le_sum
  intro α _
  rw [(planeJetReadoutOperator K α).map_smul]
  simpa only [mul_comm] using mul_le_mul_left
    (chartScalarEnergy_unit_smul_le (E := E) q hq c hc (planeJetReadoutOperator K α U))
    (ENNReal.ofReal (factorialWeight ρ α.1.val))

theorem weightedFactorialNormSq_unit_smul_le {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ c : ℝ) (hc : |c| ≤ 1)
    (U : PlaneHk Set.univ K E) :
    weightedFactorialNormSq n ϖ zc ρ K (c • U) ≤ weightedFactorialNormSq n ϖ zc ρ K U := by
  rw [weightedFactorialNormSq_stored_readout, weightedFactorialNormSq_stored_readout]
  apply storedChartFactorialEnergy_unit_smul_le ρ _ _ c hc U
  intro x
  unfold planeMomentPolynomial
  positivity

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The actual stored value energy is a summand of the public factorial energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem polynomial_value_energy_le (n : ℕ) (ϖ : ℝ) (z : Vec 2) (ρ : ℝ)
    (u : PlaneHk Set.univ K E) :
    chartScalarEnergy (planeMomentPolynomial n ϖ z)
      (planeJetReadoutOperator K (valueIndex2 K) u) ≤ weightedFactorialNormSq n ϖ z ρ K u := by
  rw [weightedFactorialNormSq_stored_readout]
  have hh := Finset.single_le_sum (f := fun α : JetIndex2 K =>
    ENNReal.ofReal (factorialWeight ρ α.1.val) *
      chartScalarEnergy (planeMomentPolynomial n ϖ z) (planeJetReadoutOperator K α u))
    (fun _ _ => bot_le) (Finset.mem_univ (valueIndex2 K))
  have hw : factorialWeight ρ (valueIndex2 K).1.val = 1 := by
    simp [factorialWeight, valueIndex2, valueIndex]
  change _ ≤ ∑ α : JetIndex2 K, ENNReal.ofReal (factorialWeight ρ α.1.val) *
    chartScalarEnergy (planeMomentPolynomial n ϖ z) (planeJetReadoutOperator K α u)
  simpa only [hw, ENNReal.ofReal_one, one_mul] using hh

theorem plane_value_readout_truncate {L : ℕ} (hKL : K ≤ L) (u : PlaneHk Set.univ L E) :
    planeJetReadoutOperator K (valueIndex2 K) (truncatePlaneHk hKL u) =
      planeJetReadoutOperator L (valueIndex2 L) u := rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Genuine H1 carriers of compact smooth spacetime test slices. -/

def compactSpacetimeH1 (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : HasCompactSupport f) (t : ℝ) : PlaneHk univ 1 ℝ :=
  smoothCompactPlaneHk 1 (fun x => f (t, x))
    (hf.comp (contDiff_const.prodMk contDiff_id)) (compactSpacetime_slice_compact f hs t)

theorem compactSpacetimeH1_value_ae (f : ℝ × Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (t : ℝ) :
    (compactSpacetimeH1 f hf hs t).val (valueIndex2 1) =ᵐ[volume.restrict univ]
      fun x => f (t, x) := by
  have h := smoothCompactPlaneHk_jet_ae 1 (fun x => f (t, x))
    (hf.comp (contDiff_const.prodMk contDiff_id)) (compactSpacetime_slice_compact f hs t)
    0 (Nat.zero_le _) Fin.elim0
  rw [planeJetOrder_eq_stored (Nat.zero_le 1)] at h
  change (compactSpacetimeH1 f hf hs t).val (valueIndex2 1) =ᵐ[volume]
    orderedDerivative Fin.elim0 (fun x => f (t, x)) at h
  simpa only [orderedDerivative_zero, Measure.restrict_univ] using h

theorem compactSpacetimeH1_gradient_ae (f : ℝ × Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (t : ℝ)
    (w : DerivativeWord2 1) :
    (compactSpacetimeH1 f hf hs t).val ⟨⟨1, by omega⟩, w⟩ =ᵐ[volume.restrict univ]
      fun x => fderiv ℝ f (t, x) (0, basisVec (w 0)) := by
  have h := smoothCompactPlaneHk_jet_ae 1 (fun x => f (t, x))
    (hf.comp (contDiff_const.prodMk contDiff_id)) (compactSpacetime_slice_compact f hs t)
    1 le_rfl w
  rw [planeJetOrder_eq_stored (le_refl 1)] at h
  simp only [CycleComparison.Lift.orderedDerivative_one,
    joint_spatial_gradient_eq f (hf.of_le (by simp))] at h
  change (compactSpacetimeH1 f hf hs t).val ⟨⟨1, by omega⟩, w⟩ =ᵐ[volume]
    (fun x => fderiv ℝ f (t, x) (0, basisVec (w 0))) at h
  simpa only [Measure.restrict_univ] using h

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Actual native time-L² lift curves have measurable polynomial gradient energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weightedGradFactorialNormSq_time_aemeasurable {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (μ : Measure ℝ)
    (U : ℝ → PlaneHk Set.univ (K + 1) E) (hU : MemLp U 2 μ) :
    AEMeasurable (fun t => weightedGradFactorialNormSq n ϖ zc ρ K (U t)) μ := by
  classical
  unfold weightedGradFactorialNormSq
  apply Finset.aemeasurable_fun_sum
  intro j hj
  have hj' : j + 1 ≤ K + 1 := Nat.succ_le_succ
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  have hm : AEMeasurable (fun t => ∑ w : DerivativeWord2 (j + 1),
      chartScalarEnergy (planeMomentPolynomial n ϖ zc)
        (planeJetReadoutOperator (K + 1) ⟨⟨j + 1, Nat.lt_succ_of_le hj'⟩, w⟩ (U t))) μ := by
    apply Finset.aemeasurable_fun_sum
    intro w _
    exact chartScalarEnergy_stationary_time_aemeasurable _
      (by unfold planeMomentPolynomial; fun_prop)
      (fun x => by unfold planeMomentPolynomial; positivity) μ _
      ((planeJetReadoutOperator (E := E) (K + 1) ⟨⟨j + 1, Nat.lt_succ_of_le hj'⟩, w⟩).comp_memLp' hU)
  have he (t : ℝ) := planeJetOrder_moment_readout hj' n ϖ zc (U t)
  apply (hm.const_mul (ENNReal.ofReal (ρ ^ (2 * j) / (j.factorial : ℝ) ^ 2))).congr
  apply Filter.Eventually.of_forall
  intro t
  simp only [planeJetReadoutOperator_apply]
  rw [← he t]
  rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual inherited constituent in common reference cell coordinates retains its native Piola array. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem weighted_reference_piece_cell_operator_natural
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (hν : ν ≠ 0) (he : 0 < e) (p : P') (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (r : ℕ) (hr : 1 ≤ r) (s : ℝ) (t : Set.Icc tS tZ) (yc z : Vec 2) :
    let Y := streamFlow φ hφ (F.piece p).anchor (yc + e • z) s
    let J := naturalPreparationJacobian hφ (F.piece p).anchor s
    ((e * (e ^ r)⁻¹) * ν⁻¹) • (F.weight p t • nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff
        (chartInvJacobian ⇑(pieceReferenceMaterial F hφ s p t).symm)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e E p c v u γ d I t
          ((pieceReferenceMaterial F hφ s p t).symm (yc + e • z))
          (e⁻¹ • (pieceReferenceMaterial F hφ s p t).symm (yc + e • z))) r A (yc + e • z) a)) =
    F.weight p t • nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff (fun x => J (yc + e • x)) (F.identity v u γ).maxOrder
        (fun d I => F.flux p c v u γ d I t (E⁻¹ • Y) (e⁻¹ • Y)) r A z a) := by
  dsimp only
  rw [weighted_reference_piece_operator_eq_natural F hc ν e E p c v u γ r s t (yc + e • z),
    smul_comm, ← (nativeArrayAssembly r (F.identity v u γ).map).map_smul]
  apply congrArg (fun X => F.weight p t • X)
  apply congrArg (nativeArrayAssembly r (F.identity v u γ).map)
  funext a A
  have hJ : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞)
      (fun x => naturalPreparationJacobian hφ (F.piece p).anchor s x i j) :=
    fun i j => (naturalPreparationJacobian_entry_smooth hφ (F.piece p).anchor i j).comp
      (contDiff_const.prodMk contDiff_id)
  exact congrFun (transportedCoeff_cell_normalization _ hJ (F.identity v u γ).maxOrder r hr A
    (fun d I => F.flux p c v u γ d I t
      (E⁻¹ • streamFlow φ hφ (F.piece p).anchor (yc + e • z) s)
      (e⁻¹ • streamFlow φ hφ (F.piece p).anchor (yc + e • z) s)) e ν he hν yc z) a

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleWords AVRegularity.Sobolev AVRegularity.ChartTransport
namespace AVRegularity.CycleJointProofs

/-! The slow remainder retains its small ratio after composition with the genuine natural cell flow. -/

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem naturalPreparation_slow_remainder_uniform_jet_budget (K n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
    (_hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (_ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ),
    r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m →
    ∀ (e : ℝ), 0 < e → ∀ (yc X0 : Vec 2) (s ϖ δ ζ B : ℝ),
    0 < s → s ≤ ocEpsilon q Λ (m - 1) / e → 0 < ϖ → s * ϖ ≤ 1 →
    0 ≤ ζ → 0 ≤ B → δ = ζ * ϖ → n ≤ Jchart + 1 →
    ∀ (f : Vec 2 → Vec 2 → ℝ),
    ContDiff ℝ (n + (K + 1) : ℕ) (Function.uncurry f) →
    (∀ a b : ℕ, a + b ≤ n → ∀ X z,
      s ^ (a + b) * |δ| ^ a *
        ‖iteratedFDeriv ℝ (K + 1 + a) (fun X' => iteratedFDeriv ℝ b (f X') z) X‖ ≤ B) →
    ∀ z j, j ≤ n →
    let Ψ := naturalPreparationCellFlow hφ r σ e yc
    let D := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
    s ^ j * ‖iteratedFDeriv ℝ j (fun x =>
      f (X0 + δ • Ψ x) (Ψ x) -
        taylorSlow 0 K (fun X => f X (Ψ x)) X0 (δ • Ψ x)) z‖ ≤
      (n.factorial : ℝ) * D ^ n * ((n + 1 : ℕ) * (C * B * ζ ^ (K + 1))) *
        (3 + max (Cchart 0) 0) ^ (K + 1) * polynomialMomentRoot ϖ z ^ (K + 1) := by
  obtain ⟨C, hC, hb⟩ := centeredSlow_remainder_jet_budget K n
  refine ⟨C, hC, ?_⟩
  intro hc ha r σ hr hσ hage e he yc X0 s ϖ δ ζ B hs hsE hϖ hscale hζ hB hδ hn f hf hjet z j hj
  let g := fun x => f (X0 + δ • x) x -
    taylorSlow 0 K (fun X => f X x) X0 (δ • x)
  have hg : ContDiff ℝ (n : ℕ∞) g := by
    have hf0 : ContDiff ℝ (n : ℕ) (Function.uncurry f) := hf.of_le (by exact_mod_cast Nat.le_add_right n (K + 1))
    have hf1 : ContDiff ℝ (K + n : ℕ) (Function.uncurry f) := hf.of_le (by exact_mod_cast (show K + n ≤ n + (K + 1) by omega))
    exact (hf0.comp ((contDiff_const.add (contDiff_id.const_smul δ)).prodMk contDiff_id)).sub
      (Weighted.taylorSlow_spatial_contDiff 0 K n f hf1 X0 δ)
  have hgj : ContDiff ℝ (j : ℕ∞) g := hg.of_le (by exact_mod_cast hj)
  have hh := naturalPreparationCellFlow_weighted_jet_bound hc ha r σ hr hσ hage e he yc
    s hs hsE ϖ hϖ.le j (K + 1) (hj.trans hn) g hgj (C * B * ζ ^ (K + 1)) (by positivity)
    (fun l hl y => hb f hf ϖ s δ ζ B hϖ hs hscale hζ hB hδ hjet X0 l (hl.trans hj) y) z
  dsimp only at hh ⊢
  let D := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
  have hmono := factorialChartPrice_mono hj (one_le_jetConst (preparationFlowJetConstant Cchart) (Jchart + 1))
  have hrest : 0 ≤ (C * B * ζ ^ (K + 1)) *
      (3 + max (Cchart 0) 0) ^ (K + 1) * polynomialMomentRoot ϖ z ^ (K + 1) := by
    apply mul_nonneg (by positivity)
    exact pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) _
  calc
    _ ≤ _ := hh
    _ = ((j.factorial : ℝ) * D ^ j * (j + 1 : ℕ)) *
        ((C * B * ζ ^ (K + 1)) * (3 + max (Cchart 0) 0) ^ (K + 1) *
          polynomialMomentRoot ϖ z ^ (K + 1)) := by dsimp only [D]; ring
    _ ≤ ((n.factorial : ℝ) * D ^ n * (n + 1 : ℕ)) *
        ((C * B * ζ ^ (K + 1)) * (3 + max (Cchart 0) 0) ^ (K + 1) *
          polynomialMomentRoot ϖ z ^ (K + 1)) :=
      mul_le_mul_of_nonneg_right hmono hrest
    _ = _ := by dsimp only [D]; ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The original-mass dissipation is bounded by the actual supremum-plus-dissipation energy. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeFamily_dissipation_le_energy
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (a b : ℝ) (π : ι → ℝ)
    (V : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) :
    (∫⁻ t in Set.Icc a b, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedGradFactorialNormSq n ϖ zc ρ (K i) (w i t)) ≤
      ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        ((⨆ t ∈ Set.Icc a b, weightedFactorialNormSq n ϖ zc ρ (K i) (V i t)) +
          ∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ zc ρ (K i) (w i t)) := by
  classical
  have hm i := weightedGradFactorialNormSq_time_aemeasurable n ϖ zc ρ _ (w i) (hw i)
  rw [lintegral_finsetSum' _ (fun i _ => (hm i).const_mul _)]
  apply Finset.sum_le_sum
  intro i _
  rw [lintegral_const_mul'' _ (hm i)]
  exact mul_le_mul_of_nonneg_left (le_add_left le_rfl) zero_le

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The native polynomial endpoint energy controls the physical factorial norm. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem storedChartFactorialEnergy_one {K : ℕ} (ρ : ℝ) (U : PlaneHk Set.univ K E) :
    storedChartFactorialEnergy ρ (fun _ => 1) U =
      ENNReal.ofReal (factorialNormSq ρ U.val) := by
  have he (a : JetIndex2 K) :
      chartScalarEnergy (fun _ => 1) (planeJetReadoutOperator K a U) =
        ENNReal.ofReal (‖U.val a‖ ^ 2) := by
    have hh := chartScalarEnergy_eq_weighted_representative_norm (fun _ => 1)
      (planeJetReadoutOperator K a U) (planeJetReadoutOperator K a U)
      (Filter.Eventually.of_forall (fun _ => (one_smul ℝ _).symm))
    simpa only [one_pow, planeJetReadoutOperator_apply, univToPlane.norm_map] using hh
  unfold storedChartFactorialEnergy
  rw [factorialNormSq_eq_sum_indices, ENNReal.ofReal_sum_of_nonneg
    (fun a _ => mul_nonneg (factorialWeight_nonneg ρ a.1.val) (sq_nonneg _))]
  apply Finset.sum_congr rfl
  intro a _
  rw [he, ENNReal.ofReal_mul (factorialWeight_nonneg ρ a.1.val)]

theorem factorialNormSq_le_weightedFactorialNormSq {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (U : PlaneHk Set.univ K E) :
    ENNReal.ofReal (factorialNormSq ρ U.val) ≤ weightedFactorialNormSq n ϖ zc ρ K U := by
  rw [weightedFactorialNormSq_stored_readout, ← storedChartFactorialEnergy_one]
  apply storedChartFactorialEnergy_mono
  intro x
  have hb : 1 ≤ 1 + ϖ ^ 2 * ((x 0 - zc 0) ^ 2 + (x 1 - zc 1) ^ 2) :=
    le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  exact one_le_pow₀ hb

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Actual constituent coefficients inherit positive active-piece budgets without counting pieces. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem positive_reference_constituentPhysical_jet_assembly (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u)
    (d n : ℕ) (s ρ B : ℝ) (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (t : Set.Icc tS tZ)
    (g : P' → Vec 2 →
      ((PiLp 2 (fun _ : DerivativeWord2 (d - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))))
    (hg : ∀ p y, g p y = nativeArrayAssembly (d - 1) (F.identity v u γ).map
      (fun a A => transportedCoeff (naturalPreparationJacobian hφ (F.piece p).anchor s)
        (F.identity v u γ).maxOrder
        (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I t
          (streamFlow φ hφ (F.piece p).anchor y s)
          (e⁻¹ • streamFlow φ hφ (F.piece p).anchor y s)) (d - 1) A y a))
    (hgs : ∀ p, (t : ℝ) ∈ (F.piece p).output → ContDiff ℝ (n : ℕ) (g p))
    (hjet : ∀ p, (t : ℝ) ∈ (F.piece p).output → ∀ y,
      ρ ^ n * ‖iteratedFDeriv ℝ n (g p) y‖ ≤ B) (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n
      (constituentPhysical (referenceChartedFamily F hφ s) ν e E actual v u γ d t) x‖ ≤ B := by
  let f := fun p y => F.weight p t • g p y
  have he : constituentPhysical (referenceChartedFamily F hφ s) ν e E actual v u γ d t = fun y => ∑ᶠ p, f p y := by
    funext y
    unfold constituentPhysical
    dsimp only [referenceChartedFamily]
    apply finsum_congr
    intro p
    change F.weight p t • (nativeArrayAssembly (d - 1) (F.identity v u γ).map
      (fun a A => transportedCoeff (chartInvJacobian ⇑(pieceReferenceMaterial F hφ s p t).symm)
        (F.identity v u γ).maxOrder
        (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I t
          ((pieceReferenceMaterial F hφ s p t).symm y)
          (e⁻¹ • (pieceReferenceMaterial F hφ s p t).symm y)) (d - 1) A y a)) = _
    rw [weighted_reference_piece_operator_eq_natural F hc ν e E p (actual p) v u γ (d - 1) s t y]
    rw [← hg p y]
  rw [he]
  have hz p (hout : (t : ℝ) ∉ (F.piece p).output) : f p = fun _ => 0 := by
    funext y
    dsimp only [f]
    rw [F.weight_zero p t hout]
    exact zero_smul ℝ (g p y)
  apply positive_piece_jet_assembly_total F tS tZ t t.property f n
    (fun p => by
      by_cases hout : (t : ℝ) ∈ (F.piece p).output
      · exact (hgs p hout).const_smul _
      · rw [hz p hout]
        exact contDiff_const) _ ρ B hρ hB _ x
  · intro p y hout
    exact congrFun (hz p hout) y
  · intro p y
    by_cases hout : (t : ℝ) ∈ (F.piece p).output
    · dsimp only [f]
      rw [iteratedFDeriv_const_smul_apply' (hgs p hout).contDiffAt, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (F.weight_nonneg p t)]
      have hh := mul_le_mul_of_nonneg_left (hjet p hout y) (F.weight_nonneg p t)
      convert hh using 1; ring
    · rw [hz p hout, iteratedFDeriv_fun_zero, F.weight_zero p t hout]
      simp only [Pi.zero_apply, norm_zero, mul_zero, zero_mul, le_refl]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Smooth compact directional fields used by moving H1 tests. -/

def spacetimeDirectionalField (f : ℝ × Vec 2 → ℝ) (v : ℝ × Vec 2) :
    ℝ × Vec 2 → ℝ := fun p => fderiv ℝ f p v

theorem spacetimeDirectionalField_smooth (f : ℝ × Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : ℝ × Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) (spacetimeDirectionalField f v) :=
  (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem spacetimeDirectionalField_compact (f : ℝ × Vec 2 → ℝ)
    (hs : HasCompactSupport f) (v : ℝ × Vec 2) :
    HasCompactSupport (spacetimeDirectionalField f v) := hs.fderiv_apply ℝ v

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleWords AVRegularity.Sobolev AVRegularity.ChartTransport
namespace AVRegularity.CycleJointProofs

/-! The slow remainder retains its small ratio after composition with the genuine natural cell flow. -/

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem naturalPreparation_slow_remainder_fixed_price_jet_bound (K n : ℕ) :
    ∀
    (_hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (_ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ),
    r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m →
    ∀ (e : ℝ), 0 < e → ∀ (yc X0 : Vec 2) (s ϖ δ ζ B : ℝ),
    0 < s → s ≤ ocEpsilon q Λ (m - 1) / e → 0 < ϖ → s * ϖ ≤ 1 →
    0 ≤ ζ → 0 ≤ B → δ = ζ * ϖ → n ≤ Jchart + 1 →
    ∀ (f : Vec 2 → Vec 2 → ℝ),
    ContDiff ℝ (n + (K + 1) : ℕ) (Function.uncurry f) →
    (∀ a b : ℕ, a + b ≤ n → ∀ X z,
      s ^ (a + b) * |δ| ^ a *
        ‖iteratedFDeriv ℝ (K + 1 + a) (fun X' => iteratedFDeriv ℝ b (f X') z) X‖ ≤ B) →
    ∀ z j, j ≤ n →
    let Ψ := naturalPreparationCellFlow hφ r σ e yc
    let D := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
    s ^ j * ‖iteratedFDeriv ℝ j (fun x =>
      f (X0 + δ • Ψ x) (Ψ x) -
        taylorSlow 0 K (fun X => f X (Ψ x)) X0 (δ • Ψ x)) z‖ ≤
      (n.factorial : ℝ) * D ^ n * ((n + 1 : ℕ) * (centeredSlowRemainderJetPrice K n * B * ζ ^ (K + 1))) *
        (3 + max (Cchart 0) 0) ^ (K + 1) * polynomialMomentRoot ϖ z ^ (K + 1) := by
  let C := centeredSlowRemainderJetPrice K n
  have hC : 0 ≤ C := centeredSlowRemainderJetPrice_nonneg K n
  have hb := centeredSlowRemainderJetPrice_bound K n
  intro hc ha r σ hr hσ hage e he yc X0 s ϖ δ ζ B hs hsE hϖ hscale hζ hB hδ hn f hf hjet z j hj
  let g := fun x => f (X0 + δ • x) x -
    taylorSlow 0 K (fun X => f X x) X0 (δ • x)
  have hg : ContDiff ℝ (n : ℕ∞) g := by
    have hf0 : ContDiff ℝ (n : ℕ) (Function.uncurry f) := hf.of_le (by exact_mod_cast Nat.le_add_right n (K + 1))
    have hf1 : ContDiff ℝ (K + n : ℕ) (Function.uncurry f) := hf.of_le (by exact_mod_cast (show K + n ≤ n + (K + 1) by omega))
    exact (hf0.comp ((contDiff_const.add (contDiff_id.const_smul δ)).prodMk contDiff_id)).sub
      (Weighted.taylorSlow_spatial_contDiff 0 K n f hf1 X0 δ)
  have hgj : ContDiff ℝ (j : ℕ∞) g := hg.of_le (by exact_mod_cast hj)
  have hh := naturalPreparationCellFlow_weighted_jet_bound hc ha r σ hr hσ hage e he yc
    s hs hsE ϖ hϖ.le j (K + 1) (hj.trans hn) g hgj (C * B * ζ ^ (K + 1)) (by positivity)
    (fun l hl y => hb f hf ϖ s δ ζ B hϖ hs hscale hζ hB hδ hjet X0 l (hl.trans hj) y) z
  dsimp only at hh ⊢
  let D := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
  have hmono := factorialChartPrice_mono hj (one_le_jetConst (preparationFlowJetConstant Cchart) (Jchart + 1))
  have hrest : 0 ≤ (C * B * ζ ^ (K + 1)) *
      (3 + max (Cchart 0) 0) ^ (K + 1) * polynomialMomentRoot ϖ z ^ (K + 1) := by
    apply mul_nonneg (by positivity)
    exact pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) _
  calc
    _ ≤ _ := hh
    _ = ((j.factorial : ℝ) * D ^ j * (j + 1 : ℕ)) *
        ((C * B * ζ ^ (K + 1)) * (3 + max (Cchart 0) 0) ^ (K + 1) *
          polynomialMomentRoot ϖ z ^ (K + 1)) := by dsimp only [D]; ring
    _ ≤ ((n.factorial : ℝ) * D ^ n * (n + 1 : ℕ)) *
        ((C * B * ζ ^ (K + 1)) * (3 + max (Cchart 0) 0) ^ (K + 1) *
          polynomialMomentRoot ϖ z ^ (K + 1)) :=
      mul_le_mul_of_nonneg_right hmono hrest
    _ = _ := by dsimp only [D]; ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVenhance.Infra.Section5 AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The schedule retains joint measurability of the complete coefficient array in an exact reference chart. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem reference_constituentPhysical_joint_measurable
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) E n)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (actual : ∀ p, Ctx p) (s : ℝ) (v u : ι) (γ : F.Γ v u) (d : ℕ) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 =>
      constituentPhysical (referenceChartedFamily F hφ s) ν e E actual v u γ d z.1 z.2) := by
  let b := fun p (z : Set.Icc tS tZ × Vec 2) k (A : DerivativeWord2 (d - 1)) =>
    transportedCoeff (naturalPreparationJacobian hφ (F.piece p).anchor s)
      (F.identity v u γ).maxOrder
      (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I z.1
        (streamFlow φ hφ (F.piece p).anchor z.2 s)
        (e⁻¹ • streamFlow φ hφ (F.piece p).anchor z.2 s)) (d - 1) A z.2 k
  have heq : (fun z : Set.Icc tS tZ × Vec 2 =>
      constituentPhysical (referenceChartedFamily F hφ s) ν e E actual v u γ d z.1 z.2) =
      fun z => ∑ᶠ p, F.weight p z.1 • nativeArrayAssembly (d - 1) (F.identity v u γ).map (b p z) := by
    funext z
    exact congrFun (reference_constituentPhysical_eq_natural F hc ν e E actual v u γ d s z.1) z.2
  rw [heq]
  apply measurable_piece_finsum_onWindow F tS tZ
  · intro p
    have hm := nativeArrayAssembly_measurable (d - 1) (F.identity v u γ).map
      (fun z k A => F.weight p z.1 * b p z k A)
      (fun k A => weighted_reference_piece_array_joint_measurable F ν e E tS tZ n hs hmeas hwmeas
        hφ s p (actual p) v u γ (d - 1) A k)
    convert hm using 1
    funext z
    exact ((nativeArrayAssembly (d - 1) (F.identity v u γ).map).map_smul
      (F.weight p z.1) (b p z)).symm
  · intro p z hout
    rw [F.weight_zero p z.1 hout]
    exact zero_smul ℝ (nativeArrayAssembly (d - 1) (F.identity v u γ).map (b p z))

theorem reference_physicalCoefficient_joint_measurable
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) E n)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (actual : ∀ p, Ctx p) (s : ℝ) (v u : ι) (d : ℕ) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 =>
      physicalCoefficient (referenceChartedFamily F hφ s) ν e E actual v u d z.1 z.2) := by
  unfold physicalCoefficient
  exact Finset.measurable_sum _ (fun γ _ =>
    reference_constituentPhysical_joint_measurable F hc ν e E n hs hmeas hwmeas actual s v u γ d)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Literal scalar time derivatives of compact spacetime tests are smooth and compact. -/

theorem spacetime_time_partial_eq (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ 1 f)
    (t : ℝ) (x : Vec 2) :
    deriv (fun s => f (s, x)) t = fderiv ℝ f (t, x) (1, 0) := by
  have hp := (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hh := (hf.differentiable (by norm_num) (t, x)).hasFDerivAt.comp_hasDerivAt t hp
  exact hh.deriv

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual inherited constituent in common reference cell coordinates retains its native Piola array. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem weighted_reference_piece_cell_operator_natural_taylor_split
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (hν : ν ≠ 0) (he : 0 < e) (p : P') (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (r : ℕ) (hr : 1 ≤ r) (Ks : ℕ) (s : ℝ) (t : Set.Icc tS tZ) (yc z : Vec 2) :
    let Y := streamFlow φ hφ (F.piece p).anchor (yc + e • z) s
    let Yc := streamFlow φ hφ (F.piece p).anchor yc s
    let J := fun x => naturalPreparationJacobian hφ (F.piece p).anchor s (yc + e • x)
    let B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 :=
      fun d I => F.flux p c v u γ d I t (E⁻¹ • Y) (e⁻¹ • Y)
    let Bp : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 :=
      fun d I a => taylorSlow 0 Ks
        (fun X => F.flux p c v u γ d I t X (e⁻¹ • Y) a) (E⁻¹ • Yc) (E⁻¹ • (Y - Yc))
    ((e * (e ^ r)⁻¹) * ν⁻¹) • (F.weight p t • nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff
        (chartInvJacobian ⇑(pieceReferenceMaterial F hφ s p t).symm)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e E p c v u γ d I t
          ((pieceReferenceMaterial F hφ s p t).symm (yc + e • z))
          (e⁻¹ • (pieceReferenceMaterial F hφ s p t).symm (yc + e • z))) r A (yc + e • z) a)) =
    F.weight p t • nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff J (F.identity v u γ).maxOrder Bp r A z a) +
    F.weight p t • nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff J (F.identity v u γ).maxOrder
        (fun d I => B d I - Bp d I) r A z a) := by
  dsimp only
  rw [weighted_reference_piece_cell_operator_natural F hc ν e E hν he p c v u γ r hr s t yc z]
  rw [nativeArrayAssembly_transported_remainder_split
    (fun x => naturalPreparationJacobian hφ (F.piece p).anchor s (yc + e • x))
    (F.identity v u γ).maxOrder _ _ r (F.identity v u γ).map z, smul_add]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization Set AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! A fixed compact spatial test extends to a compact smooth spacetime test constant on the window. -/

def compactWindowScalarTest (τ : ℝ → ℝ) (q : Vec 2 → ℝ) : ℝ × Vec 2 → ℝ :=
  fun p => τ p.1 * q p.2

theorem compactWindowScalarTest_smooth (τ : ℝ → ℝ) (q : Vec 2 → ℝ)
    (hτ : ContDiff ℝ (⊤ : ℕ∞) τ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ContDiff ℝ (⊤ : ℕ∞) (compactWindowScalarTest τ q) :=
  (hτ.comp contDiff_fst).mul (hq.comp contDiff_snd)

theorem compactWindowScalarTest_compact (τ : ℝ → ℝ) (q : Vec 2 → ℝ)
    (hτ : HasCompactSupport τ) (hq : HasCompactSupport q) :
    HasCompactSupport (compactWindowScalarTest τ q) := by
  apply HasCompactSupport.of_support_subset_isCompact (hτ.isCompact.prod hq.isCompact)
  intro p hp
  have ht : τ p.1 ≠ 0 := by
    intro h
    exact hp (by simp only [compactWindowScalarTest, h, zero_mul])
  have hx : q p.2 ≠ 0 := by
    intro h
    exact hp (by simp only [compactWindowScalarTest, h, mul_zero])
  exact ⟨subset_tsupport τ ht, subset_tsupport q hx⟩

theorem exists_compact_spacetime_fixed_test (a b : ℝ) (q : Vec 2 → ℝ)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hcq : HasCompactSupport q) :
    ∃ η : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      ∀ t ∈ Icc a b, (∀ x, η (t, x) = q x) ∧
        ∀ x, deriv (fun r => η (r, x)) t = 0 := by
  obtain ⟨τ, hτ, hcτ, _, hτ1⟩ := exists_compact_time_cutoff a b
  refine ⟨compactWindowScalarTest τ q, compactWindowScalarTest_smooth τ q hτ hq,
    compactWindowScalarTest_compact τ q hcτ hcq, ?_⟩
  intro t ht
  refine ⟨fun x => by simp only [compactWindowScalarTest, (hτ1 t ht).1, one_mul], ?_⟩
  intro x
  have hd := ((hτ1 t ht).2.mul_const (q x)).deriv
  simpa only [compactWindowScalarTest, zero_mul] using hd

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleWords AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The slow Taylor remainder of the actual physical flow inherits the natural-cell jet budget. -/

section
variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem naturalPreparation_physical_remainder_uniform_jet_budget (K n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
    (_hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (_ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ),
    r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m →
    ∀ (e E : ℝ), 0 < e → ∀ (yc : Vec 2) (s ϖ ζ B : ℝ),
    0 < s → s ≤ ocEpsilon q Λ (m - 1) / e → 0 < ϖ → s * ϖ ≤ 1 →
    0 ≤ ζ → 0 ≤ B → e / E = ζ * ϖ → n ≤ Jchart + 1 →
    ∀ (f : Vec 2 → Vec 2 → ℝ),
    ContDiff ℝ (n + (K + 1) : ℕ) (Function.uncurry f) →
    (∀ a b : ℕ, a + b ≤ n → ∀ X z,
      s ^ (a + b) * |e / E| ^ a *
        ‖iteratedFDeriv ℝ (K + 1 + a) (fun X' => iteratedFDeriv ℝ b (f X') z) X‖ ≤ B) →
    ∀ z j, j ≤ n →
    let Y := fun x => streamFlow φ hφ r (yc + e • x) σ
    let Yc := streamFlow φ hφ r yc σ
    let D := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
    s ^ j * ‖iteratedFDeriv ℝ j (fun x =>
      f (E⁻¹ • Y x) (e⁻¹ • Y x) -
        taylorSlow 0 K (fun X => f X (e⁻¹ • Y x)) (E⁻¹ • Yc) (E⁻¹ • (Y x - Yc))) z‖ ≤
      (n.factorial : ℝ) * D ^ n * ((n + 1 : ℕ) * (C * B * ζ ^ (K + 1))) *
        (3 + max (Cchart 0) 0) ^ (K + 1) * polynomialMomentRoot ϖ z ^ (K + 1) := by
  obtain ⟨C, hC, hb⟩ := naturalPreparation_slow_remainder_uniform_jet_budget
    (α := α) (q := q) (Λ := Λ) (m := m) (φ := φ) (hφ := hφ)
    (tS := tS) (tZ := tZ) (Cpad := Cpad) (Cage := Cage)
    (Jchart := Jchart) (Cchart := Cchart) K n
  refine ⟨C, hC, ?_⟩
  intro hc ha r σ hr hσ hage e E he yc s ϖ ζ B hs hsE hϖ hscale hζ hB hδ hn f hf hjet z j hj
  let phase := e⁻¹ • streamFlow φ hφ r yc σ
  let g := fun X y => f X (y + phase)
  have hg : ContDiff ℝ (n + (K + 1) : ℕ) (Function.uncurry g) :=
    hf.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))
  have hgj (a b : ℕ) (hab : a + b ≤ n) (X y : Vec 2) :
      s ^ (a + b) * |e / E| ^ a *
        ‖iteratedFDeriv ℝ (K + 1 + a) (fun X' => iteratedFDeriv ℝ b (g X') y) X‖ ≤ B := by
    simp only [g, iteratedFDeriv_comp_add_right]
    exact hjet a b hab X (y + phase)
  have hh := hb hc ha r σ hr hσ hage e he yc
    (E⁻¹ • streamFlow φ hφ r yc σ) s ϖ (e / E) ζ B hs hsE hϖ hscale hζ hB hδ hn g hg hgj z j hj
  have heq := funext (fun x => naturalPreparation_slow_remainder_coordinates hφ r σ e E he.ne' yc x K f)
  dsimp only at heq ⊢ hh
  rw [heq]
  exact hh
end

/-! The slow Taylor remainder of the actual physical flow inherits the natural-cell jet budget. -/

section
variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem naturalPreparation_physical_remainder_fixed_price_jet_bound (K n : ℕ) :
    ∀
    (_hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (_ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ),
    r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m →
    ∀ (e E : ℝ), 0 < e → ∀ (yc : Vec 2) (s ϖ ζ B : ℝ),
    0 < s → s ≤ ocEpsilon q Λ (m - 1) / e → 0 < ϖ → s * ϖ ≤ 1 →
    0 ≤ ζ → 0 ≤ B → e / E = ζ * ϖ → n ≤ Jchart + 1 →
    ∀ (f : Vec 2 → Vec 2 → ℝ),
    ContDiff ℝ (n + (K + 1) : ℕ) (Function.uncurry f) →
    (∀ a b : ℕ, a + b ≤ n → ∀ X z,
      s ^ (a + b) * |e / E| ^ a *
        ‖iteratedFDeriv ℝ (K + 1 + a) (fun X' => iteratedFDeriv ℝ b (f X') z) X‖ ≤ B) →
    ∀ z j, j ≤ n →
    let Y := fun x => streamFlow φ hφ r (yc + e • x) σ
    let Yc := streamFlow φ hφ r yc σ
    let D := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
    s ^ j * ‖iteratedFDeriv ℝ j (fun x =>
      f (E⁻¹ • Y x) (e⁻¹ • Y x) -
        taylorSlow 0 K (fun X => f X (e⁻¹ • Y x)) (E⁻¹ • Yc) (E⁻¹ • (Y x - Yc))) z‖ ≤
      (n.factorial : ℝ) * D ^ n * ((n + 1 : ℕ) * (centeredSlowRemainderJetPrice K n * B * ζ ^ (K + 1))) *
        (3 + max (Cchart 0) 0) ^ (K + 1) * polynomialMomentRoot ϖ z ^ (K + 1) := by
  have hb := naturalPreparation_slow_remainder_fixed_price_jet_bound
    (α := α) (q := q) (Λ := Λ) (m := m) (φ := φ) (hφ := hφ)
    (tS := tS) (tZ := tZ) (Cpad := Cpad) (Cage := Cage)
    (Jchart := Jchart) (Cchart := Cchart) K n
  intro hc ha r σ hr hσ hage e E he yc s ϖ ζ B hs hsE hϖ hscale hζ hB hδ hn f hf hjet z j hj
  let phase := e⁻¹ • streamFlow φ hφ r yc σ
  let g := fun X y => f X (y + phase)
  have hg : ContDiff ℝ (n + (K + 1) : ℕ) (Function.uncurry g) :=
    hf.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))
  have hgj (a b : ℕ) (hab : a + b ≤ n) (X y : Vec 2) :
      s ^ (a + b) * |e / E| ^ a *
        ‖iteratedFDeriv ℝ (K + 1 + a) (fun X' => iteratedFDeriv ℝ b (g X') y) X‖ ≤ B := by
    simp only [g, iteratedFDeriv_comp_add_right]
    exact hjet a b hab X (y + phase)
  have hh := hb hc ha r σ hr hσ hage e he yc
    (E⁻¹ • streamFlow φ hφ r yc σ) s ϖ (e / E) ζ B hs hsE hϖ hscale hζ hB hδ hn g hg hgj z j hj
  have heq := funext (fun x => naturalPreparation_slow_remainder_coordinates hφ r σ e E he.ne' yc x K f)
  dsimp only at heq ⊢ hh
  rw [heq]
  exact hh
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleWords AVRegularity.Sobolev AVRegularity.ChartTransport
namespace AVRegularity.CycleJointProofs

/-! The slow Taylor remainder of the actual physical flow inherits the natural-cell jet budget. -/

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem naturalPreparation_physical_remainder_bounded_price_jet_bound (K n nMax : ℕ) (hnMax : n ≤ nMax) :
    ∀
    (_hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (_ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ),
    r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m →
    ∀ (e E : ℝ), 0 < e → ∀ (yc : Vec 2) (s ϖ ζ B : ℝ),
    0 < s → s ≤ ocEpsilon q Λ (m - 1) / e → 0 < ϖ → s * ϖ ≤ 1 →
    0 ≤ ζ → 0 ≤ B → e / E = ζ * ϖ → n ≤ Jchart + 1 →
    ∀ (f : Vec 2 → Vec 2 → ℝ),
    ContDiff ℝ (n + (K + 1) : ℕ) (Function.uncurry f) →
    (∀ a b : ℕ, a + b ≤ n → ∀ X z,
      s ^ (a + b) * |e / E| ^ a *
        ‖iteratedFDeriv ℝ (K + 1 + a) (fun X' => iteratedFDeriv ℝ b (f X') z) X‖ ≤ B) →
    ∀ z j, j ≤ n →
    let Y := fun x => streamFlow φ hφ r (yc + e • x) σ
    let Yc := streamFlow φ hφ r yc σ
    let D := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
    s ^ j * ‖iteratedFDeriv ℝ j (fun x =>
      f (E⁻¹ • Y x) (e⁻¹ • Y x) -
        taylorSlow 0 K (fun X => f X (e⁻¹ • Y x)) (E⁻¹ • Yc) (E⁻¹ • (Y x - Yc))) z‖ ≤
      (nMax.factorial : ℝ) * D ^ nMax * ((nMax + 1 : ℕ) * (centeredSlowRemainderBoundedJetPrice K nMax * B * ζ ^ (K + 1))) *
        (3 + max (Cchart 0) 0) ^ (K + 1) * polynomialMomentRoot ϖ z ^ (K + 1) := by
  intro hc ha r σ hr hσ hage e E he yc ρ ϖ ζ B hρ hρE hϖ hscale hζ hB hδ hn f hf hjet z j hj
  have hb := naturalPreparation_physical_remainder_fixed_price_jet_bound K n hc ha r σ
    hr hσ hage e E he yc ρ ϖ ζ B hρ hρE hϖ hscale hζ hB hδ hn f hf hjet z j hj
  let D := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
  let L := 3 + max (Cchart 0) 0
  let root := polynomialMomentRoot ϖ z ^ (K + 1)
  have hroot : 0 ≤ root := pow_nonneg
    (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) _
  have hfac := factorialChartPrice_mono hnMax
    (one_le_jetConst (preparationFlowJetConstant Cchart) (Jchart + 1))
  have hrest : centeredSlowRemainderJetPrice K n * B * ζ ^ (K + 1) * L ^ (K + 1) * root ≤
      centeredSlowRemainderBoundedJetPrice K nMax * B * ζ ^ (K + 1) * L ^ (K + 1) * root := by
    apply mul_le_mul_of_nonneg_right _ hroot
    apply mul_le_mul_of_nonneg_right _ (by dsimp only [L]; positivity)
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hζ _)
    exact mul_le_mul_of_nonneg_right (centeredSlowRemainderJetPrice_le_bounded K hnMax) hB
  have hnrest : 0 ≤ centeredSlowRemainderJetPrice K n * B * ζ ^ (K + 1) * L ^ (K + 1) * root := by
    have hC := centeredSlowRemainderJetPrice_nonneg K n
    dsimp only [L]
    positivity
  dsimp only at hb ⊢
  calc
    _ ≤ _ := hb
    _ = ((n.factorial : ℝ) * D ^ n * (n + 1 : ℕ)) *
        (centeredSlowRemainderJetPrice K n * B * ζ ^ (K + 1) * L ^ (K + 1) * root) := by
      dsimp only [D, L, root]
      ring
    _ ≤ ((nMax.factorial : ℝ) * D ^ nMax * (nMax + 1 : ℕ)) *
        (centeredSlowRemainderBoundedJetPrice K nMax * B * ζ ^ (K + 1) * L ^ (K + 1) * root) :=
      mul_le_mul hfac hrest hnrest (by dsimp only [D]; positivity)
    _ = _ := by dsimp only [D, L, root]; ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Weighted energy bounds for one literal admissible coupling term. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] in
/-- Each weighted coupling term consumes its coefficient budget and a finite full-lift reserve. -/
theorem planeCoupledFluxTerm_weighted_factorialEnergy_le (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (w : PlaneHk Set.univ (K i' + 1) (h i'))
    (q : Vec 2 → ℝ) (hq : Continuous q)
    (hD : JetMemL2On Set.univ (fun β x => q x • w.toFunction.jet β x))
    (hT : JetMemL2On Set.univ (fun β x => q x •
      (planePositiveDerivativeTensor (d.1 - 1) (admissibleOrders_reserve K D i i' d).1
        (admissibleOrders_reserve K D i i' d).2 w).toFunction.jet β x)) :
    storedChartFactorialEnergy ρ (fun x => q x ^ 2)
        (planeCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC w) ≤
      (ENNReal.ofReal ((coefficientSeminorm ρ (K i) a b A).toReal ^ 2) *
        ENNReal.ofReal ((derivativeReserveFactor ρ (K i) (d.1 - 1)) ^ 2)) *
        storedChartFactorialEnergy ρ (fun x => q x ^ 2) w := by
  have hc := planeMultiplyIntervalCoefficient_weighted_factorialEnergy_le
    ρ hρ (K i) a b A hA t ht hC
    (planePositiveDerivativeTensor (d.1 - 1) (admissibleOrders_reserve K D i i' d).1
      (admissibleOrders_reserve K D i i' d).2 w) q hT
  have hd := planePositiveDerivativeTensor_weighted_factorialEnergy_le ρ hρ (d.1 - 1)
    (admissibleOrders_reserve K D i i' d).1
    (admissibleOrders_reserve K D i i' d).2 w q hq hD
  have hh := mul_le_mul
    (le_refl (ENNReal.ofReal ((coefficientSeminorm ρ (K i) a b A).toReal ^ 2)))
    hd zero_le zero_le
  exact hc.trans (by simpa only [mul_assoc] using hh)

omit [Fintype ι] in
/-- Finite source energy supplies the integrability needed for the weighted coupling bound. -/
theorem planeCoupledFluxTerm_weighted_factorialEnergy_le_of_finite (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (w : PlaneHk Set.univ (K i' + 1) (h i'))
    (q : Vec 2 → ℝ) (hq : Continuous q)
    (he : storedChartFactorialEnergy ρ (fun x => q x ^ 2) w ≠ ⊤) :
    storedChartFactorialEnergy ρ (fun x => q x ^ 2)
        (planeCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC w) ≤
      (ENNReal.ofReal ((coefficientSeminorm ρ (K i) a b A).toReal ^ 2) *
        ENNReal.ofReal ((derivativeReserveFactor ρ (K i) (d.1 - 1)) ^ 2)) *
        storedChartFactorialEnergy ρ (fun x => q x ^ 2) w := by
  have hD := weighted_raw_jets_memL2On_of_stored_energy ρ hρ q hq w he
  let T := planePositiveDerivativeTensor (d.1 - 1)
    (admissibleOrders_reserve K D i i' d).1
    (admissibleOrders_reserve K D i i' d).2 w
  have hb := planePositiveDerivativeTensor_weighted_factorialEnergy_le ρ hρ (d.1 - 1)
    (admissibleOrders_reserve K D i i' d).1
    (admissibleOrders_reserve K D i i' d).2 w q hq hD
  have hTe : storedChartFactorialEnergy ρ (fun x => q x ^ 2) T ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top he) hb
  exact planeCoupledFluxTerm_weighted_factorialEnergy_le
    ρ hρ K D a b i i' d A hA t ht hC w q hq hD
    (weighted_raw_jets_memL2On_of_stored_energy ρ hρ q hq T hTe)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Reference transport retains the original independent spatial reserve. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem reference_constituentPhysical_spatial_smooth (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (hE : E ≠ 0) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u) (d : ℕ) (s t : ℝ)
    (ht : t ∈ Set.Icc a b) :
    ContDiff ℝ (n v : ℕ)
      (constituentPhysical (referenceChartedFamily F hφ s) ν e E actual v u γ d t) := by
  let g := fun p τ y => nativeArrayAssembly (d - 1) (F.identity v u γ).map
    (fun k A => transportedCoeff (naturalPreparationJacobian hφ (F.piece p).anchor s)
      (F.identity v u γ).maxOrder
      (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I τ
        (streamFlow φ hφ (F.piece p).anchor y s)
        (e⁻¹ • streamFlow φ hφ (F.piece p).anchor y s)) (d - 1) A y k)
  have he : constituentPhysical (referenceChartedFamily F hφ s) ν e E actual v u γ d t =
      fun y => ∑ᶠ p, F.weight p t • g p t y :=
    reference_constituentPhysical_eq_natural F hc ν e E actual v u γ d s ⟨t, ht⟩
  rw [he]
  apply piece_finsum_spatial_smooth_onWindow F a b
    (fun p τ y => F.weight p τ • g p τ y) (n v) _ _ t ht
  · intro p τ hτ
    by_cases hout : τ ∈ (F.piece p).output
    · have hg : ContDiff ℝ (n v : ℕ) (g p τ) :=
        natural_flow_constituent_operator_smooth F ν e E hE n _ hs p (actual p) v u γ
          (d - 1) φ hφ (F.piece p).anchor s τ (fun Y => ⟨⟨hout, hτ⟩, Set.mem_univ Y⟩)
      exact hg.const_smul _
    · have hz : (fun y => F.weight p τ • g p τ y) = fun _ => 0 := by
        funext y
        rw [F.weight_zero p τ hout]
        exact zero_smul ℝ (g p τ y)
      rw [hz]
      exact contDiff_const
  · intro p τ y hout
    rw [F.weight_zero p τ hout]
    exact zero_smul ℝ (g p τ y)

theorem reference_edgeCoefficient_spatial_smooth [Fintype ι]
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (hE : E ≠ 0) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (v u : ι) (d : admissibleOrders K D v u)
    (s t : ℝ) (ht : t ∈ Set.Icc a b) :
    ContDiff ℝ (n v : ℕ)
      (edgeCoefficient (referenceChartedFamily F hφ s) ν e E actual K v u d t) := by
  unfold edgeCoefficient physicalCoefficient
  exact ContDiff.sum (fun γ _ =>
    reference_constituentPhysical_spatial_smooth F hc ν e E hE n hs actual v u γ d.1 s t ht)

end AVRegularity.CycleJointProofs
end
end
