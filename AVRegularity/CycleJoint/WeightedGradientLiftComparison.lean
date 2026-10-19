-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlaneFluxChartPull
import AVRegularity.CoupledEnergyPlane.Variational.ResidualValueSource
public import AVRegularity.Weighted.WeightedZeroCarrier
import AVRegularity.Families.TorusCompatible.WeakStage
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Weak plane curves admit jointly L2 value and gradient fields preserving every trace. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakCurve_exists_joint_fields {a b : ℝ}
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk univ 1 E}
    (h : PlaneWeakHilbertCurve a b u slice dual) :
    ∃ θ : ℝ × Vec 2 → E, ∃ G : Fin 2 → ℝ × Vec 2 → E,
      MemLp θ 2 ((volume.restrict (Icc a b)).prod volume) ∧
      (∀ i, MemLp (G i) 2 ((volume.restrict (Icc a b)).prod volume)) ∧
      (∀ t, (u t : Vec 2 → E) =ᵐ[volume] fun x => θ (t, x)) ∧
      (∀ t i, (planeH1GradientOperator (slice t) i : Vec 2 → E)
        =ᵐ[volume] fun x => G i (t, x)) ∧
      ∀ᵐ t ∂volume.restrict (Icc a b), ∀ i e,
        HasWeakPartialDerivOn univ i (fun x => inner ℝ e (θ (t, x)))
          (fun x => inner ℝ e (G i (t, x))) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp E 2 (volume : Measure (Vec 2))) :=
    Lp.SecondCountableTopology
  have hu : MemLp u 2 (volume.restrict (Icc a b)) :=
    ((planeHkValueOperator (E := E) 1).comp_memLp' h.state).ae_eq
      (h.agrees.mono (fun _ ht => ht.symm))
  obtain ⟨θ, hθ, heθ⟩ := exists_bochner_joint_trace_realization
    (volume.restrict (Icc a b)) volume u hu
  let L := fun i => (PiLp.proj (𝕜 := ℝ) 2
    (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2))) i).comp
      (planeH1GradientOperator (E := E))
  have hex i := exists_bochner_joint_trace_realization
    (volume.restrict (Icc a b)) volume (fun t => L i (slice t))
      ((L i).comp_memLp' h.state)
  choose G hG heG using hex
  refine ⟨θ, G, hθ, hG, heθ, (fun t i => heG i t), ?_⟩
  filter_upwards [h.agrees] with t ht
  intro i e
  apply hasWeakPartialDerivOn_congr_ae _ _ (planeH1_value_gradient_weakPartial (slice t) i e)
  · apply ae_restrict_of_ae
    have he := heθ t
    rw [ht] at he
    exact he.fun_comp (fun y => inner ℝ e y)
  · apply ae_restrict_of_ae
    exact (heG i t).fun_comp (fun y => inner ℝ e y)

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Weighted AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Each component of the actual common-chart flux operator is its finite inverse-Jacobian multiplier row. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

def planeFluxChartComponentMultiplier {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) (k j : Fin 2) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
  planeScalarMultiplier (fun y => (chartJac hφ s t y)⁻¹ k j)
    (chartJac_inverse_entry_continuous_slice hφ s t k j)
    (streamFlow_jacMatrix_bounded hφ t s).choose_spec.1
    (fun y => unitDet_inverse_entry_bound (chartJac hφ s t y)
      (streamFlow_jacMatrix_det_one hφ t s y)
      (streamFlow_jacMatrix_bounded hφ t s).choose
      ((streamFlow_jacMatrix_bounded hφ t s).choose_spec.2 y) k j)

theorem planeFluxChartPull_component {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) (F : PlaneFluxL2 E) (k : Fin 2) :
    planeFluxChartPull hφ t s F k = ∑ j : Fin 2,
      planeFluxChartComponentMultiplier hφ t s k j
        (Lp.compMeasurePreservingₗᵢ ℝ (fun y => streamFlow φ hφ t y s)
          (streamFlow_measurePreserving hφ t s) (F j)) := by
  change (planeDiffusionRows (fun k j => planeFluxChartComponentMultiplier hφ t s k j)
    (planeFluxFlowPull hφ t s F)) k = _
  rw [planeDiffusionRows_apply]
  rfl

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! The finite Sobolev coupling row for a plane solution. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i i' d t))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))

/-- The Sobolev coupling row reads the raw coupling flux `planeRawCouplingFlux` at every physical
window time. -/
theorem planeCouplingFluxRow_raw_value_ae (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)
      (planeCouplingFluxRow hab ρ hρ K D A hA hc w i t) =ᵐ[volume]
      planeRawCouplingFlux K D t A (fun i => w i t) i := by
  have hclamp : (clampPoint a b hab t : ℝ) = t := by
    simp only [clampPoint, max_eq_right ht.1, min_eq_right ht.2]
  let term (i' : ι) (d : admissibleOrders K D i i') :=
    planeCoupledFluxTerm ρ hρ K D a b i i' d (A i i' d) (hA i i' d)
      (clampPoint a b hab t) (clampPoint a b hab t).property
      (hc i i' d _ (clampPoint a b hab t).property) (w i' t)
  let raw (i' : ι) (d : admissibleOrders K D i i') (x : Vec 2) :=
    A i i' d t x (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) =>
      (w i' t).toFunction.jet ⟨⟨d.1 - 1, by
        have hd := admissibleOrders_reserve K D i i' d; omega⟩, word⟩ x))
  have hterm (i' : ι) (d : admissibleOrders K D i i') :
      planeHkValueOperator (K i) (term i' d) =ᵐ[volume] raw i' d := by
    have he := planeCoupledFluxTerm_raw_value_ae ρ hρ K D a b i i' d
      (A i i' d) (hA i i' d) (clampPoint a b hab t)
      (clampPoint a b hab t).property (hc i i' d _ (clampPoint a b hab t).property)
      (w i' t)
    simpa only [term, raw, hclamp] using he
  have hrow (i' : ι) : planeHkValueOperator (K i) (∑ d, term i' d) =ᵐ[volume]
      fun x => ∑ d, raw i' d x := by
    rw [map_sum]
    apply (MeasureTheory.Lp.coeFn_fun_finsetSum _ _).trans
    have he := eventuallyEq_sum (s := Finset.univ) (fun d _ => hterm i' d)
    filter_upwards [he] with x hx
    simpa only [Finset.sum_apply] using hx
  unfold planeCouplingFluxRow planeRawCouplingFlux
  rw [map_sum]
  apply (MeasureTheory.Lp.coeFn_fun_finsetSum _ _).trans
  have he := eventuallyEq_sum (s := Finset.univ) (fun i' _ => hrow i')
  filter_upwards [he] with x hx
  simpa only [Finset.sum_apply] using hx

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Finite scalar-weighted raw jet arrays read the public stored factorial chart energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- A square-root-weighted L² jet array has exactly the corresponding chart factorial energy. -/
theorem storedChartFactorialEnergy_weighted_jet_readout {K : ℕ} (ρ : ℝ)
    (q : Vec 2 → ℝ) (U : PlaneHk Set.univ K E)
    (hD : JetMemL2On Set.univ (fun β x => q x • U.toFunction.jet β x)) :
    storedChartFactorialEnergy ρ (fun x => q x ^ 2) U =
      ENNReal.ofReal (factorialNormSq ρ
        (jetToL2 (fun β x => q x • U.toFunction.jet β x) hD)) := by
  let J := jetToL2 (fun β x => q x • U.toFunction.jet β x) hD
  have he (β : JetIndex2 K) :
      chartScalarEnergy (fun x => q x ^ 2) (planeJetReadoutOperator K β U) =
        ENNReal.ofReal (‖J β‖ ^ 2) := by
    have hr : univToPlane (J β) =ᵐ[volume] fun x => q x • planeJetReadoutOperator K β U x := by
      have hJ := (hD β).coeFn_toLp
      simp only [Measure.restrict_univ] at hJ
      filter_upwards [univToPlane_ae (J β), hJ, univToPlane_ae (U.val β)]
        with x hx hJx hUx
      change univToPlane (J β) x = q x • univToPlane (U.val β) x
      rw [hx, hUx]
      exact hJx
    have hn := chartScalarEnergy_eq_weighted_representative_norm q
      (planeJetReadoutOperator K β U) (univToPlane (J β)) hr
    simpa only [univToPlane.norm_map] using hn
  unfold storedChartFactorialEnergy
  rw [factorialNormSq_eq_sum_indices, ENNReal.ofReal_sum_of_nonneg
    (fun β _ => mul_nonneg (factorialWeight_nonneg ρ β.1.val) (sq_nonneg _))]
  apply Finset.sum_congr rfl
  intro β _
  rw [ENNReal.ofReal_mul (factorialWeight_nonneg ρ β.1.val)]
  exact congrArg (fun z => ENNReal.ofReal (factorialWeight ρ β.1.val) * z) (he β)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Support bounds on all actual jets control the complete stored factorial chart energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem storedChartFactorialEnergy_supported_bound {K : ℕ} (ρ : ℝ)
    (q : Vec 2 → ℝ) (U : PlaneHk Set.univ K E) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ a, ∀ᵐ x ∂volume, U.toFunction.jet a x ≠ 0 → q x ≤ C) :
    storedChartFactorialEnergy ρ q U ≤
      ENNReal.ofReal C * ENNReal.ofReal (factorialNormSq ρ U.val) := by
  have hi (a : JetIndex2 K) : chartScalarEnergy q (planeJetReadoutOperator K a U) ≤
      ENNReal.ofReal C * ENNReal.ofReal (‖U.val a‖ ^ 2) := by
    have hh := chartScalarEnergy_supported_bound q (planeJetReadoutOperator K a U) C hC
      (by
        filter_upwards [hb a, univToPlane_ae (U.val a)] with x hx he
        intro hn
        rw [planeJetReadoutOperator_apply, he] at hn
        exact hx hn)
    simpa only [planeJetReadoutOperator_apply, univToPlane.norm_map] using hh
  unfold storedChartFactorialEnergy
  rw [factorialNormSq_eq_sum_indices, ENNReal.ofReal_sum_of_nonneg
    (fun a _ => mul_nonneg (factorialWeight_nonneg ρ a.1.val) (sq_nonneg _)), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [ENNReal.ofReal_mul (factorialWeight_nonneg ρ a.1.val)]
  have hh := mul_le_mul_of_nonneg_left (hi a)
    (show 0 ≤ ENNReal.ofReal (factorialWeight ρ a.1.val) from zero_le)
  simpa only [mul_left_comm] using hh

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Truncation retains a subset of the nonnegative weighted factorial jet energy. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] [CompleteSpace E] in
/-- Dropping higher orders cannot increase the factorial square. -/
theorem factorialNormSq_truncateJet_le {μ : Measure (Vec 2)} {K L : ℕ}
    (hKL : K ≤ L) (ρ : ℝ) (D : JetL2 μ L E) :
    factorialNormSq ρ (truncateJet hKL D) ≤ factorialNormSq ρ D := by
  rw [factorialNormSq_eq_sum_indices, factorialNormSq_eq_sum_indices]
  exact sum_comp_le_sum_nonneg (truncateJetIndex hKL) (truncateJetIndex_injective hKL)
    (fun β => factorialWeight ρ β.1.val * ‖D β‖ ^ 2)
    (fun β => mul_nonneg (factorialWeight_nonneg ρ β.1.val) (sq_nonneg _))

/-- A scalar-weighted Sobolev truncation retains no more than the full stored energy. -/
theorem storedChartFactorialEnergy_weighted_truncate_le {K L : ℕ}
    (hKL : K ≤ L) (ρ : ℝ) (q : Vec 2 → ℝ) (U : PlaneHk Set.univ L E)
    (hD : JetMemL2On Set.univ (fun β x => q x • U.toFunction.jet β x)) :
    storedChartFactorialEnergy ρ (fun x => q x ^ 2) (truncatePlaneHk hKL U) ≤
      storedChartFactorialEnergy ρ (fun x => q x ^ 2) U := by
  have hT : JetMemL2On Set.univ
      (fun β x => q x • (truncatePlaneHk hKL U).toFunction.jet β x) :=
    fun β => hD (truncateJetIndex hKL β)
  rw [storedChartFactorialEnergy_weighted_jet_readout ρ q _ hT,
    storedChartFactorialEnergy_weighted_jet_readout ρ q U hD]
  exact ENNReal.ofReal_le_ofReal (factorialNormSq_truncateJet_le hKL ρ
    (jetToL2 (fun β x => q x • U.toFunction.jet β x) hD))
end

/-! Finite stored factorial energy supplies all weighted raw representatives. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- A positive-radius finite stored energy places every weighted raw jet in L². -/
theorem weighted_raw_jets_memL2On_of_stored_energy {K : ℕ}
    (ρ : ℝ) (hρ : 0 < ρ) (q : Vec 2 → ℝ) (hq : Continuous q)
    (U : PlaneHk Set.univ K E)
    (he : storedChartFactorialEnergy ρ (fun x => q x ^ 2) U ≠ ⊤) :
    JetMemL2On Set.univ (fun β x => q x • U.toFunction.jet β x) := by
  intro β
  exact weighted_raw_jet_memLp_of_energy q hq U β
    (storedChartFactorialEnergy_component_ne_top ρ hρ (fun x => q x ^ 2) U he β)
end

/-! A finite public mass energy gives genuine uniform and integrated budgets for each component. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem finite_geometry_energy_component (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (K : ι → ℕ) (n : ℕ) (ϖ : ℝ) (z : Vec 2) (ρ a b : ℝ)
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (he : geometryEnergyNorm π K n ϖ z ρ a b u w < ⊤) (i : ι) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ t ∈ Set.Icc a b, weightedFactorialNormSq n ϖ z ρ (K i) (u i t) ≤ ENNReal.ofReal C) ∧
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ z ρ (K i) (w i t)) ≠ ⊤ := by
  let A := fun i => (⨆ t ∈ Set.Icc a b, weightedFactorialNormSq n ϖ z ρ (K i) (u i t)) +
    ∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ z ρ (K i) (w i t)
  have hsum : (∑ i, ENNReal.ofReal ((π i)⁻¹) * A i) ≠ ⊤ := by
    intro hh
    have ht : geometryEnergyNorm π K n ϖ z ρ a b u w = ⊤ := by
      change (∑ i, ENNReal.ofReal ((π i)⁻¹) * A i) ^ (1 / 2 : ℝ) = ⊤
      rw [hh, ENNReal.top_rpow_of_pos (by norm_num)]
    exact he.ne ht
  have hi : A i ≠ ⊤ := finite_weighted_sum_component (fun i => (π i)⁻¹)
    (fun i => inv_pos.mpr (hπ i)) A hsum i
  have hs : (⨆ t ∈ Set.Icc a b, weightedFactorialNormSq n ϖ z ρ (K i) (u i t)) ≠ ⊤ :=
    ne_top_of_le_ne_top hi (le_add_right le_rfl)
  have hg : (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ z ρ (K i) (w i t)) ≠ ⊤ :=
    ne_top_of_le_ne_top hi (le_add_left le_rfl)
  refine ⟨(⨆ t ∈ Set.Icc a b, weightedFactorialNormSq n ϖ z ρ (K i) (u i t)).toReal,
    ENNReal.toReal_nonneg, ?_, hg⟩
  intro t ht
  rw [ENNReal.ofReal_toReal hs]
  exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.TorusCompatible
namespace AVRegularity.CycleJointProofs

/-! Torus compatibility gives spatial periodicity of every original and transported scalar native piece row. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem pieceDimensionalNativeJetArray_periodic
    (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (actual : ∀ p, Ctx p)
    (hT : IsTorusCompatible F actual E) {N : ℕ} (he : e⁻¹ = N)
    (p : P) (v u : ι) (γ : F.Γ v u) (t : ℝ)
    (r : ℕ) (I : DerivativeWord2 r) :
    IsZ2Periodic (pieceDimensionalNativeJetArray F ν e E p (actual p) v u γ t r I) := by
  intro n x
  exact hT.dimFlux_sample_periodic ν e he p v u γ (r + 1) I t n x

theorem pieceNativeSourceScalarJetCoefficient_periodic {J : ℕ}
    (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (actual : ∀ p, Ctx p)
    (hT : IsTorusCompatible F actual E) {N : ℕ} (he : e⁻¹ = N)
    (p : P) (v u : ι) (γ : F.Γ v u) (t : ℝ) (k : Fin 2) (j : JetIndex2 J) :
    IsZ2Periodic (nativeSourceScalarJetCoefficient (F.identity v u γ).maxOrder
      (pieceDimensionalNativeJetArray F ν e E p (actual p) v u γ t) k j) := by
  intro n x
  unfold nativeSourceScalarJetCoefficient
  rw [pieceDimensionalNativeJetArray_periodic F ν e E actual hT he p v u γ t j.1.val j.2 n x]

theorem pieceTransportedNativeScalarJetCoefficient_periodic
    (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (actual : ∀ p, Ctx p)
    (hT : IsTorusCompatible F actual E) {N : ℕ} (he : e⁻¹ = N)
    (p : P) (v u : ι) (γ : F.Γ v u) (t : ℝ) (J : ℕ) (k : Fin 2) (j : JetIndex2 J) :
    IsZ2Periodic (pieceTransportedNativeScalarJetCoefficient F ν e E p (actual p) v u γ t J k j) := by
  have hB : IsZ2Periodic (fun x : Vec 2 => fun d (I : DerivativeWord2 (d - 1)) =>
      pieceDimensionalNativeJetArray F ν e E p (actual p) v u γ t (d - 1) I
        (((F.piece p).material t).symm x)) := by
    intro n x
    funext d I
    dsimp only
    rw [hT.symm_equivariant p t n x]
    exact pieceDimensionalNativeJetArray_periodic F ν e E actual hT he p v u γ t
      (d - 1) I n _
  have hp := isZ2Periodic_transportedCoeff
    (isZ2Periodic_chartInvJacobian (hT.symm_equivariant p t))
    (F.identity v u γ).maxOrder hB j.1.val j.2
  intro n x
  unfold pieceTransportedNativeScalarJetCoefficient transportedNativeScalarJetCoefficient
  by_cases hj : 1 ≤ j.1.val ∧ j.1.val < (F.identity v u γ).maxOrder
  · simp only [ite_eq_left hj]
    exact congrArg (fun z : Vec 2 => z k) (hp n x)
  · simp only [ite_eq_right hj]

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! The finite Sobolev coupling row for a plane solution. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i i' d t))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))

/-- Each Hilbert flux component reads the exact coupling row on the time window. -/
theorem planeCouplingFluxRow_component_ae (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (k : Fin 2) :
    AVRegularity.Weighted.planeFluxValueOperator (E := h i) (K i)
      (planeCouplingFluxRow hab ρ hρ K D A hA hc w i t) k =ᵐ[volume]
      fun x => planeRawCouplingFlux K D t A (fun i => w i t) i x k := by
  have hr := planeCouplingFluxRow_raw_value_ae hab ρ hρ K D A hA hc w i t ht
  have hs := AVRegularity.Weighted.planeFluxSplitOperator_ae
    (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)
      (planeCouplingFluxRow hab ρ hρ K D A hA hc w i t)) k
  filter_upwards [hr, hs] with x hx hsx
  exact hsx.trans (congrArg (fun z => z k) hx)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Every finite weighted full-lift moment controls its gradient moment at the same positive radius. -/

theorem factorialWeight_gradient_shift_le (ρ : ℝ) (hρ : 0 < ρ) (K j : ℕ) (hj : j ≤ K) :
    factorialWeight ρ j ≤ (((K + 1 : ℕ) : ℝ) ^ 2 / ρ ^ 2) * factorialWeight ρ (j + 1) := by
  have he : factorialWeight ρ j = (((j + 1 : ℕ) : ℝ) ^ 2 / ρ ^ 2) *
      factorialWeight ρ (j + 1) := by
    unfold factorialWeight
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.mul_add, pow_add]
    push_cast
    field_simp
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (le_of_lt (Weighted.factorialWeight_pos_of_radius_pos ρ hρ _))
  apply div_le_div_of_nonneg_right _ (sq_nonneg ρ)
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hj 1) 2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weightedGradFactorialNormSq_le_full_lift {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (W : PlaneHk Set.univ (K + 1) E) :
    weightedGradFactorialNormSq n ϖ zc ρ K W ≤
      ENNReal.ofReal ((((K + 1 : ℕ) : ℝ) ^ 2 / ρ ^ 2)) *
        weightedFactorialNormSq n ϖ zc ρ (K + 1) W := by
  let X (j : ℕ) := ∫⁻ z, ENNReal.ofReal
    ((1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ n *
      ∑ w : DerivativeWord2 j, ‖planeJetOrder W j w z‖ ^ 2)
  change (∑ j ∈ Finset.range (K + 1), ENNReal.ofReal (factorialWeight ρ j) * X (j + 1)) ≤
    ENNReal.ofReal ((((K + 1 : ℕ) : ℝ) ^ 2 / ρ ^ 2)) *
      (∑ j ∈ Finset.range (K + 2), ENNReal.ofReal (factorialWeight ρ j) * X j)
  calc
    _ ≤ ∑ j ∈ Finset.range (K + 1),
        ENNReal.ofReal ((((K + 1 : ℕ) : ℝ) ^ 2 / ρ ^ 2)) *
          (ENNReal.ofReal (factorialWeight ρ (j + 1)) * X (j + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal
        (factorialWeight_gradient_shift_le ρ hρ K j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))) le_rfl
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      have hs : (∑ j ∈ Finset.range (K + 1),
          ENNReal.ofReal (factorialWeight ρ (j + 1)) * X (j + 1)) ≤
          ∑ j ∈ Finset.range (K + 2), ENNReal.ofReal (factorialWeight ρ j) * X j := by
        rw [show K + 2 = (K + 1) + 1 by omega,
          Finset.sum_range_succ' (fun j => ENNReal.ofReal (factorialWeight ρ j) * X j) (K + 1)]
        exact le_self_add
      exact mul_le_mul' le_rfl hs

theorem integrated_weightedGradFactorialNormSq_ne_top_of_lift {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (hρ : 0 < ρ) (μ : Measure ℝ)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (he : (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ (K + 1) (W t) ∂μ) ≠ ⊤) :
    (∫⁻ t, weightedGradFactorialNormSq n ϖ zc ρ K (W t) ∂μ) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (lintegral_mono
    (fun t => weightedGradFactorialNormSq_le_full_lift n ϖ zc ρ hρ (W t)))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top he

end AVRegularity.CycleJointProofs
end
