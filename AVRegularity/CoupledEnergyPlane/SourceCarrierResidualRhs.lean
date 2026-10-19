-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionPlane
import AVRegularity.CoupledEnergyPlane.SourceRawSpatialTimeIdentity
public import AVRegularity.CoupledEnergyPlane.SourceFixedBandUniformBound

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceNativePackAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceNativePackTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceNativeEquation_pack_weakSolution {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      W t j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (ν : ℝ) (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (hg : ∀ j, Integrable (g j) (volume.restrict (Set.Icc a b)))
    (f : ∀ j, PlaneHk Set.univ (K j) (h j))
    (U : ∀ j, C(Set.Icc a b, PlaneHk Set.univ (K j) (h j)))
    (hinit : ∀ j, U j ⟨a, le_rfl, hab⟩ = f j)
    (hUa : ∀ j, extendCurve hab (U j) =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      truncatePlaneHk (E := h j) (Nat.le_succ (K j)) (weakHighCarrier K a b W j t))
    (hid : let Cc := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf
      let hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
      ∀ j, ∀ t : Set.Icc a b, ∀ ψ : PlaneHk Set.univ 1 (h j),
        inner ℝ (planeHkValueOperator (E := h j) (K j) (U j t)) (planeHkValueOperator (E := h j) 1 ψ) =
          nativeRawTestValue ν (planeHkValueOperator (E := h j) (K j) (f j))
            (weakH1CarrierTimeCLM K a b j W) (limitDriftField hab Cc hc j W)
            (limitFluxField hab Cc hc W j
              ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h j)) (K j)).compLpL 2
                (volume.restrict (Set.Icc a b)) ((hF j).toLp (F j))))
            (fun s => planeHkValueOperator (E := h j) (K j) (g j s)) t ψ) :

    IsCoupledWeakSolutionPlane ν a b v D K A f F g
      (fun j => extendCurve hab (U j)) (weakHighCarrier K a b W) := by
  refine ⟨fun j => (continuous_extendCurve hab (U j)).continuousOn,
    fun j => weakHighCarrier_memLp K a b W j, fun j => (hUa j).symm, ?_, ?_⟩
  · intro j
    change extendCurve hab (U j) a = f j
    rw [extendCurve_eq_of_mem hab (U j) (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)]
    exact hinit j
  · intro i t ht ψ
    let Cc := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf
    let hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
    let Q := weakH1CarrierTimeCLM K a b i W
    let Df := limitDriftField hab Cc hc i W
    let Hf := limitFluxField hab Cc hc W i
      ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
        (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i)))
    let gval := fun s => planeHkValueOperator (E := h i) (K i) (g i s)
    let η : ℝ → ℝ := fun s =>
      -inner ℝ (Df s) (planeHkValueOperator (E := h i) 1 ψ) -
        ν * inner ℝ (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) 0
          (planeGradientTensor (E := h i) (Q s)))
          (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) 0 (planeGradientTensor (E := h i) ψ)) -
        inner ℝ (Hf s)
          (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) 0 (planeGradientTensor (E := h i) ψ)) +
        inner ℝ (gval s) (planeHkValueOperator (E := h i) 1 ψ)
    let L : ℝ → ℝ := fun s => ∫ x, planeRawSpatialRhs K D ν s v A F g
      (fun j => weakHighCarrier K a b W j s) i ψ x
    have hgg : Integrable gval (volume.restrict (Set.Icc a b)) :=
      (planeHkValueOperator (E := h i) (K i)).integrable_comp (hg i)
    have hn : Integrable η (volume.restrict (Set.Icc a b)) :=
      nativeRawTest_rhs_integrable ν Q Df Hf gval hgg ψ
    have hae := sourceRawSpatialRhs_time_ae_native hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
      Kmax hK strain B lam hstrain hB hlam hjets W hW i ν F hF g ψ
    change L =ᵐ[volume.restrict (Set.Icc a b)] η at hae
    have htime : Integrable L (volume.restrict (Set.Icc a b)) := hn.congr hae.symm
    have hs : Set.Ioc a t ⊆ Set.Icc a b := fun s hst => ⟨hst.1.le, hst.2.trans ht.2⟩
    have hleft := planeRawValue_pairing_integrable_and_integral (extendCurve hab (U i) t) ψ
    have hfirst := planeRawValue_pairing_integrable_and_integral (f i) ψ
    simp only [CoupledWeakIdentity, Measure.restrict_univ]
    change Integrable (fun x => inner ℝ ((extendCurve hab (U i) t).toFunction.jet (valueIndex2 (K i)) x)
        (ψ.toFunction.jet (valueIndex2 1) x)) volume ∧
      Integrable (fun x => inner ℝ ((f i).toFunction.jet (valueIndex2 (K i)) x)
        (ψ.toFunction.jet (valueIndex2 1) x)) volume ∧
      (∀ s ∈ Set.Ioc a t, Integrable (planeRawSpatialRhs K D ν s v A F g
        (fun j => weakHighCarrier K a b W j s) i ψ) volume) ∧
      IntegrableOn L (Set.Ioc a t) ∧
      (∫ x, inner ℝ ((extendCurve hab (U i) t).toFunction.jet (valueIndex2 (K i)) x)
        (ψ.toFunction.jet (valueIndex2 1) x)) -
      (∫ x, inner ℝ ((f i).toFunction.jet (valueIndex2 (K i)) x)
        (ψ.toFunction.jet (valueIndex2 1) x)) = ∫ s in Set.Ioc a t, L s
    refine ⟨hleft.1, hfirst.1, ?_, IntegrableOn.mono_set htime hs, ?_⟩
    · intro s hst
      exact planeRawSpatialRhs_integrable ρ hρ K D a b s ν (hs hst) v (hv s (hs hst)).continuous
        V (hbv s (hs hst)) A hAf (fun j j' d => hAc j j' d s (hs hst)) F g
        (fun j => weakHighCarrier K a b W j s) i ψ
    · have he : (∫ s in Set.Ioc a t, L s) = ∫ s in a..t, η s := by
        rw [intervalIntegral.integral_of_le ht.1]
        exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hs hae)
      rw [hleft.2, hfirst.2, he, extendCurve_eq_of_mem hab (U i) ht]
      have hi := hid i ⟨t, ht⟩ ψ
      change inner ℝ (planeHkValueOperator (E := h i) (K i) (U i ⟨t, ht⟩))
        (planeHkValueOperator (E := h i) 1 ψ) =
          inner ℝ (planeHkValueOperator (E := h i) (K i) (f i)) (planeHkValueOperator (E := h i) 1 ψ) +
            ∫ s in a..t, η s at hi
      simpa only [add_sub_cancel_left] using congrArg (fun r : ℝ => r -
        inner ℝ (planeHkValueOperator (E := h i) (K i) (f i)) (planeHkValueOperator (E := h i) 1 ψ)) hi
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance arbitraryNativeAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance arbitraryNativeTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem planeWeakSolution_native_equation {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (ν : ℝ) (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (hg : ∀ j, Integrable (g j) (volume.restrict (Set.Icc a b)))
    (f : ∀ j, PlaneHk Set.univ (K j) (h j))
    (u : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (w : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) :
    let W := planeCarrierHighTime K a b w hsol.2.1
    let Cc := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf
      let hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
      ∀ j, ∀ t : Set.Icc a b, ∀ ψ : PlaneHk Set.univ 1 (h j),
        inner ℝ (planeHkValueOperator (E := h j) (K j) (u j t)) (planeHkValueOperator (E := h j) 1 ψ) =
          nativeRawTestValue ν (planeHkValueOperator (E := h j) (K j) (f j))
            (weakH1CarrierTimeCLM K a b j W) (limitDriftField hab Cc hc j W)
            (limitFluxField hab Cc hc W j
              ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h j)) (K j)).compLpL 2
                (volume.restrict (Set.Icc a b)) ((hF j).toLp (F j))))
            (fun s => planeHkValueOperator (E := h j) (K j) (g j s)) t ψ := by
  let W := planeCarrierHighTime K a b w hsol.2.1
  have hW := planeCarrierHighTime_graph_ae K a b w hsol.2.1
  dsimp only
  intro i t ψ
  let Cc := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf
  let hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
  let Q := weakH1CarrierTimeCLM K a b i W
  let Df := limitDriftField hab Cc hc i W
  let Hf := limitFluxField hab Cc hc W i
    ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
    (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i)))
  let gval := fun s => planeHkValueOperator (E := h i) (K i) (g i s)
  have _hgg : Integrable gval (volume.restrict (Set.Icc a b)) :=
    (planeHkValueOperator (E := h i) (K i)).integrable_comp (hg i)
  let η : ℝ → ℝ := fun s =>
    -inner ℝ (Df s) (planeHkValueOperator (E := h i) 1 ψ) -
    ν * inner ℝ (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) 0
      (planeGradientTensor (E := h i) (Q s)))
      (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) 0 (planeGradientTensor (E := h i) ψ)) -
    inner ℝ (Hf s)
      (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) 0 (planeGradientTensor (E := h i) ψ)) +
    inner ℝ (gval s) (planeHkValueOperator (E := h i) 1 ψ)
  let L : ℝ → ℝ := fun s => ∫ x, planeRawSpatialRhs K D ν s v A F g
    (fun j => weakHighCarrier K a b W j s) i ψ x
  have hae := sourceRawSpatialRhs_time_ae_native hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets W hW i ν F hF g ψ
  change L =ᵐ[volume.restrict (Set.Icc a b)] η at hae
  have hr : L =ᵐ[volume.restrict (Set.Icc a b)] fun s => ∫ x,
      planeRawSpatialRhs K D ν s v A F g (fun j => w j s) i ψ x := by
    filter_upwards [ae_all_iff.mpr (fun j => planeCarrierHighTime_readout_ae K a b w hsol.2.1 j)] with s hs
    have he : (fun j => weakHighCarrier K a b W j s) = (fun j => w j s) := funext hs
    change (∫ x, planeRawSpatialRhs K D ν s v A F g
      (fun j => weakHighCarrier K a b W j s) i ψ x) = _
    rw [he]
  have hs : Set.Ioc a t.val ⊆ Set.Icc a b := fun s hst => ⟨hst.1.le, hst.2.trans t.property.2⟩
  have he : (∫ s in Set.Ioc a t.val, ∫ x,
      planeRawSpatialRhs K D ν s v A F g (fun j => w j s) i ψ x) = ∫ s in a..t.val, η s := by
    rw [intervalIntegral.integral_of_le t.property.1]
    exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hs (hr.symm.trans hae))
  have hi := (hsol.2.2.2.2 i t.val t.property ψ).2.2.2.2
  simp only [Measure.restrict_univ] at hi
  change (∫ x, inner ℝ ((u i t).toFunction.jet (valueIndex2 (K i)) x)
      (ψ.toFunction.jet (valueIndex2 1) x)) -
    (∫ x, inner ℝ ((f i).toFunction.jet (valueIndex2 (K i)) x)
      (ψ.toFunction.jet (valueIndex2 1) x)) = _ at hi
  rw [(planeRawValue_pairing_integrable_and_integral (u i t) ψ).2,
    (planeRawValue_pairing_integrable_and_integral (f i) ψ).2] at hi
  change inner ℝ (planeHkValueOperator (E := h i) (K i) (u i t)) (planeHkValueOperator 1 ψ) -
    inner ℝ (planeHkValueOperator (E := h i) (K i) (f i)) (planeHkValueOperator 1 ψ) =
      ∫ s in Set.Ioc a t.val, ∫ x,
        planeRawSpatialRhs K D ν s v A F g (fun j => w j s) i ψ x at hi
  rw [he] at hi
  change _ = inner ℝ (planeHkValueOperator (E := h i) (K i) (f i))
    (planeHkValueOperator (E := h i) 1 ψ) + ∫ s in a..t.val, η s
  exact (sub_eq_iff_eq_add.mp hi).trans (add_comm _ _)
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceNativeCarrierRhsAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceNativeCarrierRhsTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceFixedBandRhs_carrier_ae {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      W t j ∈ planeHkGraph (E := h j) Set.univ (K j + 1)) (i : ι)
    (ν : ℝ) (F : ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : MemLp F 2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → PlaneHk Set.univ (K i) (h i)) (N : ℕ) :
    let Cc := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf
    let hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
    fixedBandRhs (E := h i) N ν
      ((planeHkValueOperator (E := h i) 1).compLpL 2 (volume.restrict (Set.Icc a b))
        (weakH1CarrierTimeCLM K a b i W))
      (limitDriftField hab Cc hc i W)
      (limitFluxField hab Cc hc W i ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
        (volume.restrict (Set.Icc a b)) (hF.toLp F)))
      (fun s => planeHkValueOperator (E := h i) (K i) (g s)) =ᵐ[volume.restrict (Set.Icc a b)] fun s =>
      -hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i)
        (planeTransportCarrier (hK i) (v (clampPoint a b hab s))
          (hv _ (clampPoint a b hab s).property) V (hbv _ (clampPoint a b hab s).property)
          strain B lam (hjets _ (clampPoint a b hab s).property) (weakHighCarrier K a b W i s))) +
      ν • bandLaplacianOperator (E := h i) N
        (planeHkValueOperator (E := h i) (K i + 1) (weakHighCarrier K a b W i s)) +
      bandDivergenceOperator (E := h i) N
        (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)
          ((∑ j, ∑ d : admissibleOrders K D i j,
            planeCoupledFluxTerm ρ hρ K D a b i j d (A i j d) (hAf i j d)
              (clampPoint a b hab s) (clampPoint a b hab s).property
              (hAc i j d _ (clampPoint a b hab s).property) (weakHighCarrier K a b W j s)) + F s)) +
      hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i) (g s)) := by
  dsimp only
  have hrhs := sourceFixedBandSobolevRhs_ae hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets W hW i ν F hF g N
  have hs := sourceSobolevFlux_carrier_ae hab ρ hρ K D A hAc hAf hAm ν W i F hF
  have ht := weakTransportTimeCLM_ae hab K Kmax hK i v hvm hv V strain B lam
    hV hstrain hB hlam hbv hjets W
  let T : ℝ → PlaneHk Set.univ (K i) (h i) := fun s =>
    planeTransportCarrier (hK i) (v (clampPoint a b hab s))
      (hv _ (clampPoint a b hab s).property) V (hbv _ (clampPoint a b hab s).property)
      strain B lam (hjets _ (clampPoint a b hab s).property) (weakHighCarrier K a b W i s)
  let C : ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)) := fun s =>
    ∑ j, ∑ d : admissibleOrders K D i j,
      planeCoupledFluxTerm ρ hρ K D a b i j d (A i j d) (hAf i j d)
        (clampPoint a b hab s) (clampPoint a b hab s).property
        (hAc i j d _ (clampPoint a b hab s).property) (weakHighCarrier K a b W j s)
  exact bandCarrierFields_rhs_ae (E := h i) (volume.restrict (Set.Icc a b)) N (K i) ν _
    (fun _ => fixedBandRhs_projection (E := h i) N ν _ _ _ _ _)
    (sourceSobolevFlux hab ρ hρ K D A hAc hAf hAm ν W i F hF)
    (timeValueSource (weakTransportTimeCLM hab K Kmax hK i v hvm hv V strain B lam
      hV hstrain hB hlam hbv hjets W) g)
    (weakHighCarrier K a b W i) T g C F hrhs hs
    (timeValueSource_ae_sub_of_field _ g T ht)
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakNativeDifferenceAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakNativeDifferenceTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem planeWeakSolution_nativeDifference_equation {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (ν : ℝ) (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (hg : ∀ j, Integrable (g j) (volume.restrict (Set.Icc a b)))
    (f : ∀ j, PlaneHk Set.univ (K j) (h j))
    (u : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (w : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w)
    (u' : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (w' : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hsol' : IsCoupledWeakSolutionPlane ν a b v D K A f F g u' w') :
    let W := planeCarrierHighTime (h := h) K a b w hsol.2.1
    let W' := planeCarrierHighTime (h := h) K a b w' hsol'.2.1
    let Wd := W - W'
    let Cc := sourceProjectedCoefficients (h := h) a b ρ hρ v hv V hV hbv K D A hAc hAf
    let hc := sourceProjectedCoefficients_isMeasurable (h := h) a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
    ∀ i, ∀ t : Set.Icc a b, ∀ ψ : PlaneHk Set.univ 1 (h i),
      inner ℝ (planeHkValueOperator (E := h i) (K i) (u i t - u' i t))
        (planeHkValueOperator (E := h i) 1 ψ) =
      nativeRawTestValue (E := h i) ν 0 (weakH1CarrierTimeCLM (h := h) K a b i Wd)
        (limitDriftField (h := h) hab Cc hc i Wd) (limitFluxField (h := h) hab Cc hc Wd i 0)
        (fun _ => 0) t ψ := by
  intro W W' Wd Cc hc
  have hn := planeWeakSolution_native_equation (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets ν F hF g hg f u w hsol
  have hn' := planeWeakSolution_native_equation (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets ν F hF g hg f u' w' hsol'
  intro i t ψ
  let Fi := (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
    (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i))
  have hf := nativeDifferenceFields (h := h) hab Cc hc W W' i Fi
  have he := nativeRawTestDifference_identity_of_same_source (E := h i) t.property ν
    (planeHkValueOperator (E := h i) (K i) (f i))
    (weakH1CarrierTimeCLM (h := h) K a b i W) (weakH1CarrierTimeCLM (h := h) K a b i W')
    (limitDriftField (h := h) hab Cc hc i W) (limitDriftField (h := h) hab Cc hc i W')
    (limitFluxField (h := h) hab Cc hc W i Fi) (limitFluxField (h := h) hab Cc hc W' i Fi)
    (fun s => planeHkValueOperator (E := h i) (K i) (g i s))
    ((planeHkValueOperator (E := h i) (K i)).integrable_comp (hg i)) ψ
    (planeHkValueOperator (E := h i) (K i) (u i t))
    (planeHkValueOperator (E := h i) (K i) (u' i t)) (hn i t ψ) (hn' i t ψ)
  have hr := congrArg₂
    (fun (Q : Lp (PlaneHk Set.univ 1 (h i)) 2 (volume.restrict (Set.Icc a b)))
      (S : Lp (Lp (h i) 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)) ×
        Lp (Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b))) =>
      nativeRawTestValue (E := h i) (a := a) (b := b) ν 0 Q S.1 S.2 (fun _ => 0) t ψ)
    hf.1 (congrArg₂ (fun x y => (x, y)) hf.2.1 hf.2.2)
  have hl := congrArg (fun p : Lp (h i) 2 (volume : Measure (Vec 2)) =>
    inner ℝ p (planeHkValueOperator (E := h i) 1 ψ))
    ((planeHkValueOperator (E := h i) (K i)).toLinearMap.map_sub (u i t) (u' i t))
  exact hl.trans (he.trans hr.symm)
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakDifferencePackAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakDifferencePackTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem planeWeakSolution_difference_isWeakSolution {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (ν : ℝ) (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (hg : ∀ j, Integrable (g j) (volume.restrict (Set.Icc a b)))
    (f : ∀ j, PlaneHk Set.univ (K j) (h j))
    (u : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (w : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w)
    (u' : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (w' : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hsol' : IsCoupledWeakSolutionPlane ν a b v D K A f F g u' w') :
    let W := planeCarrierHighTime (h := h) K a b w hsol.2.1
    let W' := planeCarrierHighTime (h := h) K a b w' hsol'.2.1
    let U := planeWeakDifferenceCurve (h := h) K a b u u' hsol.1 hsol'.1
    IsCoupledWeakSolutionPlane ν a b v D K A (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0)
      (fun i => extendCurve hab (U i)) (weakHighCarrier (h := h) K a b (W - W')) := by
  intro W W' U
  have hWd := planeHighTime_sub_graph_ae (h := h) K a b W W'
    (planeCarrierHighTime_graph_ae (h := h) K a b w hsol.2.1)
    (planeCarrierHighTime_graph_ae (h := h) K a b w' hsol'.2.1)
  have hF0 (i : ι) : MemLp (fun _ : ℝ => (0 : PlaneHk Set.univ (K i)
      (PiLp 2 (fun _ : Fin 2 => h i)))) 2 (volume.restrict (Set.Icc a b)) :=
    timeMemLp_zero _ _
  have hg0 (i : ι) : Integrable (fun _ : ℝ => (0 : PlaneHk Set.univ (K i) (h i)))
      (volume.restrict (Set.Icc a b)) := timeIntegrable_zero _
  have hi (i : ι) : U i ⟨a, le_rfl, hab⟩ = 0 :=
    planeWeakDifferenceCurve_initial_zero (h := h) K hab u u' hsol.1 hsol'.1 f hsol.2.2.2.1 hsol'.2.2.2.1 i
  have ha (i : ι) := planeWeakDifferenceCurve_carrier_alignment_ae (h := h) K hab
    u u' hsol.1 hsol'.1 w w' hsol.2.1 hsol'.2.1 hsol.2.2.1 hsol'.2.2.1 i
  apply sourceNativeEquation_pack_weakSolution (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets (W - W') hWd ν (fun _ _ => 0) hF0
    (fun _ _ => 0) hg0 (fun _ => 0) U hi ha
  intro Cc hc i t ψ
  have he := planeWeakSolution_nativeDifference_equation (h := h) hab ρ hρ v hv V hV hbv
    K D A hAc hAf hvm hAm Kmax hK strain B lam hstrain hB hlam hjets
    ν F hF g hg f u w hsol u' w' hsol' i t ψ
  have hz : (hF0 i).toLp (fun _ => 0) = 0 := MemLp.toLp_zero (hF0 i)
  have hfz : (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
      (volume.restrict (Set.Icc a b)) ((hF0 i).toLp (fun _ => 0)) = 0 :=
    (congrArg ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
      (volume.restrict (Set.Icc a b))) hz).trans
      (((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
        (volume.restrict (Set.Icc a b))).toLinearMap.map_zero)
  simpa only [hfz, map_zero, U, planeWeakDifferenceCurve_apply] using he
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance arbitraryCutoffAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance arbitraryCutoffTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem planeWeakSolution_fixedBandPrimitive {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (ν : ℝ) (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (hg : ∀ j, Integrable (g j) (volume.restrict (Set.Icc a b)))
    (f : ∀ j, PlaneHk Set.univ (K j) (h j))
    (u : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (w : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w)     (i : ι) (N : ℕ) (t : Set.Icc a b) :
    sourceFixedBandPrimitive hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
      ν f F hF g hg (planeCarrierHighTime K a b w hsol.2.1) i N t =
        hilbertProjection N (planeHkValueOperator (E := h i) (K i) (u i t)) := by
  let W := planeCarrierHighTime K a b w hsol.2.1
  let Cc := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf
  let hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
  have hn := planeWeakSolution_native_equation hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets ν F hF g hg f u w hsol
  have he := fixedBandPrimitive_eq_cutoff_of_allTime_native_equation hab N ν
    (planeHkValueOperator (E := h i) (K i) (f i))
    (weakH1CarrierTimeCLM K a b i W) (limitDriftField hab Cc hc i W)
    (limitFluxField hab Cc hc W i ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
      (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i))))
    (fun s => planeHkValueOperator (E := h i) (K i) (g i s))
    ((planeHkValueOperator (E := h i) (K i)).integrable_comp (hg i))
    (fun s => planeHkValueOperator (E := h i) (K i) (u i s)) (fun s ψ => hn i s ψ) t
  exact he
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakFamilyCutoffAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakFamilyCutoffTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem planeWeakSolution_nativeFamily_component {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (ν : ℝ) (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (hg : ∀ j, Integrable (g j) (volume.restrict (Set.Icc a b)))
    (f : ∀ j, PlaneHk Set.univ (K j) (h j))
    (u : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (w : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) (N : ℕ) (t : Set.Icc a b) (i : ι) :
    sourceNativeFamilyPrimitive hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
      ν f F hF g hg (planeCarrierHighTime K a b w hsol.2.1) N t i = hilbertProjection N (planeHkValueOperator (E := h i) (K i) (u i t)) := by
  exact planeWeakSolution_fixedBandPrimitive hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets ν F hF g hg f u w hsol i N t

theorem planeWeakSolution_nativeFamily_alignment_ae {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (ν : ℝ) (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (hg : ∀ j, Integrable (g j) (volume.restrict (Set.Icc a b)))
    (f : ∀ j, PlaneHk Set.univ (K j) (h j))
    (u : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (w : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) (N : ℕ) (i : ι) :
    (fun t => extendCurve hab
      (sourceNativeFamilyPrimitive hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
      ν f F hF g hg (planeCarrierHighTime K a b w hsol.2.1) N) t i) =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i + 1)
          (weakHighCarrier K a b (planeCarrierHighTime K a b w hsol.2.1) i t)) := by
  have hw := planeCarrierHighTime_readout_ae K a b w hsol.2.1 i
  filter_upwards [hsol.2.2.1 i, hw, ae_restrict_mem measurableSet_Icc] with t ht hw htI
  rw [extendCurve_eq_of_mem hab _ htI]
  have he := planeWeakSolution_nativeFamily_component hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets ν F hF g hg f u w hsol N ⟨t, htI⟩ i
  rw [← ht, planeHkValueOperator_truncate] at he
  rw [hw]
  exact he
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakNativeBandIdentityAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakNativeBandIdentityTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem planeWeakSolution_nativeFamily_bandComponent {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (ν : ℝ) (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (hg : ∀ j, Integrable (g j) (volume.restrict (Set.Icc a b)))
    (f : ∀ j, PlaneHk Set.univ (K j) (h j))
    (u : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (w : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) (N : ℕ) (t : Set.Icc a b) (i : ι) :
    hilbertBandHk (E := h i) N (K i) (sourceNativeFamilyPrimitive (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
      ν f F hF g hg (planeCarrierHighTime (h := h) K a b w hsol.2.1) N t i) =
      planeHkCutoff (E := h i) N (K i) (u i t) := by
  have he := planeWeakSolution_nativeFamily_component (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets ν F hF g hg f u w hsol N t i
  rw [he]
  exact hilbertBandHk_projection (E := h i) N (K i) (planeHkValueOperator (E := h i) (K i) (u i t))

theorem planeWeakSolution_nativeFamily_massJets {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (ν : ℝ) (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (hg : ∀ j, Integrable (g j) (volume.restrict (Set.Icc a b)))
    (f : ∀ j, PlaneHk Set.univ (K j) (h j))
    (u : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (w : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) (N : ℕ) (t : Set.Icc a b) :
    (fun i => (hilbertBandHk (E := h i) N (K i) (sourceNativeFamilyPrimitive (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
      ν f F hF g hg (planeCarrierHighTime (h := h) K a b w hsol.2.1) N t i)).val) =
      fun i => (planeHkCutoff (E := h i) N (K i) (u i t)).val := by
  funext i
  exact congrArg Subtype.val (planeWeakSolution_nativeFamily_bandComponent (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets ν F hF g hg f u w hsol N t i)

theorem planeWeakSolution_nativeFamily_initialMassJets {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (ν : ℝ) (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (hg : ∀ j, Integrable (g j) (volume.restrict (Set.Icc a b)))
    (f : ∀ j, PlaneHk Set.univ (K j) (h j))
    (u : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (w : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) (N : ℕ) :
    (fun i => (hilbertBandHk (E := h i) N (K i) (sourceNativeFamilyPrimitive (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
      ν f F hF g hg (planeCarrierHighTime (h := h) K a b w hsol.2.1) N ⟨a, le_rfl, hab⟩ i)).val) =
      fun i => (planeHkCutoff (E := h i) N (K i) (f i)).val := by
  rw [planeWeakSolution_nativeFamily_massJets (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets ν F hF g hg f u w hsol N ⟨a, le_rfl, hab⟩]
  funext i
  rw [hsol.2.2.2.1 i]
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceResidualRhsAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceResidualRhsTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

local instance carrierResidualCachedFluxCarrierAdd (i : ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance carrierResidualCachedFluxCarrierTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance carrierResidualCachedFluxCarrierSpace (i : ι) (k : ℕ) :
    NormedSpace ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance carrierResidualCachedFluxCarrierModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  (carrierResidualCachedFluxCarrierSpace i k).toModule
local instance carrierResidualCachedFluxCarrierSmulZero (i : ι) (k : ℕ) :
    SMulWithZero ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance carrierResidualCachedFluxTimeSpace (i : ι) (k : ℕ) (a b : ℝ) :
    NormedSpace ℝ (Lp (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b))) := inferInstance
local instance carrierResidualCachedFluxTimeModule (i : ι) (k : ℕ) (a b : ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b))) := (carrierResidualCachedFluxTimeSpace i k a b).toModule

local instance carrierResidualCachedHighCarrierSpace (i : ι) (k : ℕ) :
    NormedSpace ℝ (PlaneHk Set.univ k (h i)) := inferInstance
local instance carrierResidualCachedHighTimeSpace (i : ι) (k : ℕ) (a b : ℝ) :
    NormedSpace ℝ (Lp (PlaneHk Set.univ k (h i)) 2 (volume.restrict (Set.Icc a b))) := inferInstance

theorem sourceCarrierRhs_residual_ae {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (W : PlaneHighTime (h := h) K a b)
    (i : ι)
    (ν : ℝ) (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j)) (N : ℕ)
    (q : ℝ → ProjectedFamily h)
    (hq : ∀ j, (fun t => q t j) =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      hilbertProjection (E := h j) N (planeHkValueOperator (E := h j) (K j + 1) (weakHighCarrier (h := h) K a b W j t))) :
    let Cc := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf
    let U := fun j => weakHighCarrierTimeCLM (h := h) K a b j W
    let Φ := fun j => (hF j).toLp (F j)
    let RF := fun j => (planeResidualFluxTime (h := h) hab ρ hρ K D A hAc hAf hAm U Φ N j :
      ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    let Rg := fun j => planeResidualValueSource hab (hK j) v hvm hv V strain B lam
      hV hstrain hB hlam hbv hjets (U j) (g j) N
    (fun s =>
      -hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i)
        (planeTransportCarrier (hK i) (v (clampPoint a b hab s))
          (hv _ (clampPoint a b hab s).property) V (hbv _ (clampPoint a b hab s).property)
          strain B lam (hjets _ (clampPoint a b hab s).property) (weakHighCarrier (h := h) K a b W i s))) +
      ν • bandLaplacianOperator (E := h i) N
        (planeHkValueOperator (E := h i) (K i + 1) (weakHighCarrier (h := h) K a b W i s)) +
      bandDivergenceOperator (E := h i) N
        (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)
          ((∑ j, ∑ d : admissibleOrders K D i j,
            planeCoupledFluxTerm ρ hρ K D a b i j d (A i j d) (hAf i j d)
              (clampPoint a b hab s) (clampPoint a b hab s).property
              (hAc i j d _ (clampPoint a b hab s).property) (weakHighCarrier (h := h) K a b W j s)) + F i s)) +
      hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i) (g i s))) =ᵐ[volume.restrict (Set.Icc a b)] fun s =>
        projectedOperator (Cc.reindex (clampPoint a b hab)) N ν s (q s) i + projectedSource N RF Rg s i := by
  intro Cc U Φ RF Rg
  have hf := sourceResidualFluxTime_ae (h := h) hab ρ hρ K D A hAc hAf hAm W F hF N i
  have hg := planeResidualValueSource_readout_ae hab (hK i) v hvm hv V strain B lam
    hV hstrain hB hlam hbv hjets (U i) (g i) N (weakHighCarrier (h := h) K a b W i)
    (weakHighCarrierTimeCLM_ae K a b i W)
  have hqall := ae_all_iff.mpr hq
  filter_upwards [hf, hg, hqall] with s hflux hvalue hqcut
  have hp := sourceProjectedRhs_cutoffCarrierResidual (h := h) K Kmax hK N (q s)
    ρ strain B lam ν hρ a b v hv V hV hbv (clampPoint a b hab s)
    (hjets _ (clampPoint a b hab s).property) D A hAf hAc i
    (fun j => weakHighCarrier (h := h) K a b W j s) hqcut (fun j => F j s) (fun j => g j s)
  dsimp only at hp
  rw [projectedSource_component] at hp
  rw [projectedOperator_reindex_apply, projectedSource_component]
  change _ = projectedOperator
      (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
      N ν (clampPoint a b hab s) (q s) i +
    (bandDivergenceOperator (E := h i) N (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) (RF i s)) +
      hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i) (Rg i s)))
  change RF i s = _ at hflux
  change Rg i s = _ at hvalue
  have hflux' := hflux.trans (add_comm _ _)
  rw [hflux', hvalue]
  exact hp.symm
end

end AVRegularity.CoupledEnergyPlane
end
