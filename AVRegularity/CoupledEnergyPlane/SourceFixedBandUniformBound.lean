-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.ResidualFluxTimeValue

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! The true diffusion, all admissible couplings, and external flux form a Sobolev time L² class. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem sourceResidualFluxTime_ae {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : admissibleOrders K D i j, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (W : PlaneHighTime (h := h) K a b)
    (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b))) (N : ℕ) (i : ι) :
    planeResidualFluxTime (h := h) hab ρ hρ K D A hAc hAf hAm
      (fun j => weakHighCarrierTimeCLM (h := h) K a b j W) (fun j => (hF j).toLp (F j)) N i
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        (∑ j, ∑ d : admissibleOrders K D i j,
          planeCoupledFluxTerm ρ hρ K D a b i j d (A i j d) (hAf i j d)
            (clampPoint a b hab t) (clampPoint a b hab t).property
            (hAc i j d _ (clampPoint a b hab t).property)
            (weakHighCarrier (h := h) K a b W j t - AVRegularity.CoupledEnergyPlane.Fourier.planeHkCutoff N (K j + 1) (weakHighCarrier (h := h) K a b W j t))) + F i t := by
  let U : ∀ j, Lp (PlaneHk Set.univ (K j + 1) (h j)) 2 (volume.restrict (Set.Icc a b)) :=
    fun j => weakHighCarrierTimeCLM (h := h) K a b j W
  let Φ : ∀ j, Lp (PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j))) 2
      (volume.restrict (Set.Icc a b)) := fun j => (hF j).toLp (F j)
  have he := planeResidualFluxTime_ae (h := h) hab ρ hρ K D A hAc hAf hAm
    U Φ N i
  have hu := ae_all_iff.mpr (fun j => weakHighCarrierTimeCLM_ae (h := h) K a b j W)
  filter_upwards [he, hu, (hF i).coeFn_toLp] with t ht hu hf
  exact ht.trans (residualFluxFields_congr
    (E := fun j => PlaneHk Set.univ (K j + 1) (h j))
    (G := PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (δ := fun j => admissibleOrders K D i j)
    (fun j => AVRegularity.CoupledEnergyPlane.Fourier.planeHkCutoff N (K j + 1))
    (fun j d p => planeCoupledFluxTerm ρ hρ K D a b i j d (A i j d) (hAf i j d)
      (clampPoint a b hab t) (clampPoint a b hab t).property
      (hAc i j d _ (clampPoint a b hab t).property) p)
    (fun j => weakHighCarrierTimeCLM (h := h) K a b j W t) (fun j => weakHighCarrier (h := h) K a b W j t)
    ((hF i).toLp (F i) t) (F i t) hu hf)
end

/-! The true diffusion, all admissible couplings, and external flux form a Sobolev time L² class. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance residualFluxBudgetCachedCarrierAdd (i : ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance residualFluxBudgetCachedCarrierTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance residualFluxBudgetCachedCarrierSpace (i : ι) (k : ℕ) :
    NormedSpace ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance residualFluxBudgetCachedCarrierModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  (residualFluxBudgetCachedCarrierSpace i k).toModule
local instance residualFluxBudgetCachedCarrierSmulZero (i : ι) (k : ℕ) :
    SMulWithZero ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance residualFluxBudgetCachedTimeSpace (i : ι) (k : ℕ) (a b : ℝ) :
    NormedSpace ℝ (Lp (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b))) := inferInstance
local instance residualFluxBudgetCachedTimeModule (i : ι) (k : ℕ) (a b : ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b))) := (residualFluxBudgetCachedTimeSpace i k a b).toModule

local instance residualFluxBudgetHighCarrierSpace (i : ι) (k : ℕ) :
    NormedSpace ℝ (PlaneHk Set.univ k (h i)) := inferInstance
local instance residualFluxBudgetHighTimeSpace (i : ι) (k : ℕ) (a b : ℝ) :
    NormedSpace ℝ (Lp (PlaneHk Set.univ k (h i)) 2 (volume.restrict (Set.Icc a b))) := inferInstance

theorem sourceResidualFlux_budget_tendsto {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : admissibleOrders K D i j, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (U : ∀ j, Lp (PlaneHk Set.univ (K j + 1) (h j)) 2 (volume.restrict (Set.Icc a b)))
    (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b))) (π : ι → ℝ) :
    Tendsto (fun N => ∫ t in Set.Icc a b, massNormSq ρ π
      (fun i => (planeResidualFluxTime hab ρ hρ K D A hAc hAf hAm U
        (fun j => (hF j).toLp (F j)) N i t).val)) atTop
      (𝓝 (∫ t in Set.Icc a b, massNormSq ρ π (fun i => (F i t).val))) := by
  have he := planeMassNormSq_timeLp_tendsto (E := fun i => PiLp 2 (fun _ : Fin 2 => h i))
    (volume.restrict (Set.Icc a b)) K ρ π
    (fun N i => planeResidualFluxTime hab ρ hρ K D A hAc hAf hAm U (fun j => (hF j).toLp (F j)) N i)
    (fun i => (hF i).toLp (F i))
    (fun i => tendsto_planeResidualFluxTime hab ρ hρ K D A hAc hAf hAm U (fun j => (hF j).toLp (F j)) i)
  have hFae := ae_all_iff.mpr (fun i => (hF i).coeFn_toLp)
  have hi : (∫ t in Set.Icc a b, massNormSq ρ π (fun i => ((hF i).toLp (F i) t).val)) =
      ∫ t in Set.Icc a b, massNormSq ρ π (fun i => (F i t).val) := by
    apply integral_congr_ae
    filter_upwards [hFae] with t ht
    have hj : (fun i => ((hF i).toLp (F i) t).val) = (fun i => (F i t).val) :=
      funext (fun i => congrArg Subtype.val (ht i))
    rw [hj]
  rw [hi] at he
  exact he
end

end AVRegularity.CoupledEnergyPlane
end

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

local instance sourceCoeffCarrierAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceCoeffCarrierTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem coefficientWeakTestValue_source_eq {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (W : PlaneHighTime (h := h) K a b) (i : ι) (t : Set.Icc a b)
    (ψ : PlaneHk Set.univ 1 (h i)) :
    coefficientWeakTestValue hab
      (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
      W i ν (planeHkValueOperator (K i) (f i))
      ((planeHkValueOperator (K i)).compLpL 2 (volume.restrict (Set.Icc a b))
        ((hF i).toLp (F i)))
      (fun s => planeHkValueOperator (K i) (g i s)) t ψ =
      sourceWeakTestValue K D a b v A ν f F g W i t ψ := by
  have hf := timeLpReadout_toLp_test_integral t.property
    (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i))
    (F i) (hF i) (planeHkValueOperator 0 (planeGradientTensor ψ))
  have hd := clampedTime_integral_eq hab t.property (fun q s => ∫ x, inner ℝ
    (driftFiberCoefficient (E := h i) (v q) x
      (((highGradientReadout (h := h) K i).compLpL 2
        (volume.restrict (Set.Icc a b)) W) s x)) (planeHkValueOperator 1 ψ x))
  have he (j : ι) (d : admissibleOrders K D i j) :=
    clampedTime_integral_eq hab t.property (fun q s => ∫ x, inner ℝ
      (A i j d q x (((highTensorReadout (h := h) K j (d.1 - 1)
        (by have hh := AVRegularity.CoupledEnergyPlane.Variational.admissibleOrders_reserve K D i j d; omega)).compLpL 2
          (volume.restrict (Set.Icc a b)) W) s x))
      (planeHkValueOperator 0 (planeGradientTensor ψ) x))
  unfold coefficientWeakTestValue sourceWeakTestValue
  dsimp only [sourceProjectedCoefficients]
  apply congrArg₂ (fun x y : ℝ => x + y)
  · apply congrArg₂ (fun x y : ℝ => x - y)
    · apply congrArg₂ (fun x y : ℝ => x - y)
      · apply congrArg₂ (fun x y : ℝ => x - y)
        · apply congrArg₂ (fun x y : ℝ => x - y)
          · rfl
          · exact hd
        · rfl
      · apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro d _
        exact he j d
    · exact hf
  · rfl
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceNativeCarrierAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceNativeCarrierTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceNativeRawTestValue_eq {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ j,
      W s j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (i : ι) (t : Set.Icc a b) (ψ : PlaneHk Set.univ 1 (h i)) :
    let C := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf
    let hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
    nativeRawTestValue ν (planeHkValueOperator (K i) (f i))
      (weakH1CarrierTimeCLM K a b i W) (limitDriftField hab C hc i W)
      (limitFluxField hab C hc W i ((planeHkValueOperator (K i)).compLpL 2
        (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i))))
      (fun s => planeHkValueOperator (K i) (g i s)) t ψ =
      sourceWeakTestValue K D a b v A ν f F g W i t ψ := by
  dsimp only
  have hgr := (planeHkValueOperator (E := h i) (K i)).integrable_comp (hg i)
  rw [nativeRawTestValue_eq_coefficientWeakTestValue hab _ _ W hW i ν _ _ _ hgr t ψ]
  exact coefficientWeakTestValue_source_eq hab ρ hρ v hv V hV hbv K D A hAc hAf
    ν f F hF g W i t ψ

theorem sourceNativeRawTestValue_eq_ae {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ j,
      W s j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (i : ι) (ψ : PlaneHk Set.univ 1 (h i)) :
    let Cc := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf
    let hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
    (fun t => nativeRawTestValue ν (planeHkValueOperator (K i) (f i))
      (weakH1CarrierTimeCLM K a b i W) (limitDriftField hab Cc hc i W)
      (limitFluxField hab Cc hc W i ((planeHkValueOperator (K i)).compLpL 2
        (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i))))
      (fun s => planeHkValueOperator (K i) (g i s)) t ψ)
      =ᵐ[volume.restrict (Set.Icc a b)] fun t => sourceWeakTestValue K D a b v A ν f F g W i t ψ := by
  dsimp only
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact sourceNativeRawTestValue_eq hab ρ hρ v hv V hV hbv K D A hAc hAf
    hvm hAm ν f F hF g hg W hW i ⟨t, ht⟩ ψ
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourcePrimitiveCarrierAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourcePrimitiveCarrierTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

def sourceFixedBandPrimitive {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (W : PlaneHighTime (h := h) K a b) (i : ι) (N : ℕ) :
    C(Set.Icc a b, Lp (h i) 2 (volume : Measure (Vec 2))) :=
  let Cc := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf
  let hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
  fixedBandPrimitive hab N ν (planeHkValueOperator (K i) (f i))
    ((planeHkValueOperator (E := h i) 1).compLpL 2 (volume.restrict (Set.Icc a b))
      (weakH1CarrierTimeCLM K a b i W))
    (limitDriftField hab Cc hc i W)
    (limitFluxField hab Cc hc W i ((planeHkValueOperator (K i)).compLpL 2
      (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i))))
    (fun s => planeHkValueOperator (K i) (g i s))
    ((planeHkValueOperator (E := h i) (K i)).integrable_comp (hg i))
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceSobolevPrimitiveCarrierAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceSobolevPrimitiveCarrierTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

def sourceFixedBandSobolevPrimitive {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (W : PlaneHighTime (h := h) K a b) (i : ι) (N : ℕ) :
    C(Set.Icc a b, PlaneHk Set.univ (K i) (h i)) :=
  let u := sourceFixedBandPrimitive hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm ν f F hF g hg W i N
  ⟨fun t => hilbertBandHkOperator (E := h i) N (K i) (u t),
    (hilbertBandHkOperator (E := h i) N (K i)).continuous.comp u.continuous⟩
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceBandTestAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceBandTestTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceFixedBandPrimitive_test_value {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ j,
      W s j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (i : ι) (t : Set.Icc a b) (N : ℕ)
    (z : Lp (h i) 2 (volume : Measure (Vec 2))) :
    inner ℝ (sourceFixedBandPrimitive hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
      ν f F hF g hg W i N t) z =
      sourceWeakTestValue K D a b v A ν f F g W i t (hilbertBandHk N 1 z) := by
  let Cc := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf
  let hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
  have hp := fixedBandPrimitive_eq_nativeRawTestValue hab N ν
    (planeHkValueOperator (K i) (f i)) (weakH1CarrierTimeCLM K a b i W)
    (limitDriftField hab Cc hc i W)
    (limitFluxField hab Cc hc W i ((planeHkValueOperator (K i)).compLpL 2
      (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i))))
    (fun s => planeHkValueOperator (K i) (g i s))
    ((planeHkValueOperator (E := h i) (K i)).integrable_comp (hg i)) t z
  exact hp.trans (sourceNativeRawTestValue_eq hab ρ hρ v hv V hV hbv K D A hAc hAf
    hvm hAm ν f F hF g hg W hW i t (hilbertBandHk N 1 z))
end

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! Pointwise convergence of every native weak test along the actual common Galerkin subsequence. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem sourceFixedBandPrimitive_test_tendsto {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h))
    (heq : ∀ N, ∀ t : Set.Icc a b, u N t = projectedInitial N f + ∫ s in a..t.1,
      projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf).reindex
          (clampPoint a b hab)) N ν s (extendCurve hab (u N) s) + projectedSource N F g s)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W)))
    (hW : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ j,
      W s j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (i : ι) (t : Set.Icc a b) (N : ℕ)
    (z : Lp (h i) 2 (volume : Measure (Vec 2))) :
    Tendsto (fun n => inner ℝ (hilbertProjection N (u (φ n) t i)) z)
      atTop (𝓝 (inner ℝ (sourceFixedBandPrimitive hab ρ hρ v hv V hV hbv K D A hAc hAf
        hvm hAm ν f F hF g hg W i N t) z)) := by
  have hp := sourceProjectedCurve_test_tendsto hab ρ hρ v hv V hV hbv K D A hAc hAf
    hvm hAm ν f F hF g hg u heq φ hφ W R hu hw i t (hilbertBandHk N 1 z)
  have hval : planeHkValueOperator 1 (hilbertBandHk N 1 z) = hilbertProjection N z :=
    planeHkValueOperator_hilbertBand N 1 z
  simp only [hval] at hp
  rw [sourceFixedBandPrimitive_test_value hab ρ hρ v hv V hV hbv K D A hAc hAf
    hvm hAm ν f F hF g hg W hW i t N z]
  exact hp.congr' (Eventually.of_forall (fun n =>
    (hilbertProjection_inner N (u (φ n) t i) z).symm))

end AVRegularity.CoupledEnergyPlane
end

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

local instance sourceFamilyPrimitiveAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceFamilyPrimitiveTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

def sourceNativeFamilyPrimitive {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (W : PlaneHighTime (h := h) K a b) (N : ℕ) : C(Set.Icc a b, ProjectedFamily h) :=
  finiteFamilyCurve (fun i => sourceFixedBandPrimitive hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    ν f F hF g hg W i N)
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceFamilyIdentityAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceFamilyIdentityTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceNativeFamilyPrimitive_eq_nativeFamily {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (W : PlaneHighTime (h := h) K a b) (N : ℕ) :
    let Cc := sourceProjectedCoefficients (h := h) a b ρ hρ v hv V hV hbv K D A hAc hAf
    let hc := sourceProjectedCoefficients_isMeasurable (h := h) a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
    sourceNativeFamilyPrimitive (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm ν f F hF g hg W N =
      nativeFamilyPrimitive (h := h) hab N ν
        (fun i => planeHkValueOperator (E := h i) (K i) (f i))
        (fun i => weakH1CarrierTimeCLM (h := h) K a b i W)
        (fun i => limitDriftField (h := h) hab Cc hc i W)
        (fun i => limitFluxField (h := h) hab Cc hc W i
          ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
            (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i))))
        (fun i s => planeHkValueOperator (E := h i) (K i) (g i s))
        (fun i => (planeHkValueOperator (E := h i) (K i)).integrable_comp (hg i)) := by
  rfl
end

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! Pointwise convergence of every native weak test along the actual common Galerkin subsequence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceWeakEquationAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceWeakEquationTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceWeakCarrier_native_equation {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h))
    (heq : ∀ N, ∀ t : Set.Icc a b, u N t = projectedInitial N f + ∫ s in a..t.1,
      projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf).reindex
          (clampPoint a b hab)) N ν s (extendCurve hab (u N) s) + projectedSource N F g s)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W)))
    (hrange : ∀ N t, familyProjection N (u N t) = u N t)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (C : ℝ)
    (hmass : ∀ N t, massNormSq ρ π
      (fun i => (hilbertBandHk N (K i) (u N t i)).val) ≤ C)
    (hW : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ j,
      W s j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (i : ι) (ψ : PlaneHk Set.univ 1 (h i)) :
    let Cc := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf
    let hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
    (fun t => inner ℝ (planeHkValueOperator 1 (weakH1CarrierTimeCLM K a b i W t))
      (planeHkValueOperator 1 ψ)) =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        nativeRawTestValue ν (planeHkValueOperator (K i) (f i))
          (weakH1CarrierTimeCLM K a b i W) (limitDriftField hab Cc hc i W)
          (limitFluxField hab Cc hc W i ((planeHkValueOperator (K i)).compLpL 2
            (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i))))
          (fun s => planeHkValueOperator (K i) (g i s)) t ψ := by
  dsimp only
  have ht := sourceWeakTestValue_eq_weakClass hab ρ hρ v hv V hV hbv K D A hAc hAf
    hvm hAm ν f F hF g hg u heq φ hφ W R hu hw hrange π hπ C hmass i ψ
  have hvv := weakH1CarrierTimeCLM_value_ae K a b i W hW
  have hvtest : (fun t => inner ℝ
      (planeHkValueOperator 1 (weakH1CarrierTimeCLM K a b i W t)) (planeHkValueOperator 1 ψ))
      =ᵐ[volume.restrict (Set.Icc a b)] fun t => inner ℝ
        (highJetReadout (h := h) K i (valueIndex2 (K i + 1)) (W t)) (planeHkValueOperator 1 ψ) := by
    filter_upwards [hvv] with t he
    exact congrArg (fun q : Lp (h i) 2 (volume : Measure (Vec 2)) =>
      inner ℝ q (planeHkValueOperator 1 ψ)) he
  exact hvtest.trans (ht.symm.trans
    (sourceNativeRawTestValue_eq_ae hab ρ hρ v hv V hV hbv K D A hAc hAf
      hvm hAm ν f F hF g hg W hW i ψ).symm)
end

/-! Pointwise convergence of every native weak test along the actual common Galerkin subsequence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceBandIdentificationAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceBandIdentificationTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceFixedBandPrimitive_ae_eq_cutoff {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h))
    (heq : ∀ N, ∀ t : Set.Icc a b, u N t = projectedInitial N f + ∫ s in a..t.1,
      projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf).reindex
          (clampPoint a b hab)) N ν s (extendCurve hab (u N) s) + projectedSource N F g s)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W)))
    (hrange : ∀ N t, familyProjection N (u N t) = u N t)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (C : ℝ)
    (hmass : ∀ N t, massNormSq ρ π
      (fun i => (hilbertBandHk N (K i) (u N t i)).val) ≤ C)
    (hW : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ j,
      W s j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (i : ι) (N : ℕ) :
    extendCurve hab (sourceFixedBandPrimitive hab ρ hρ v hv V hV hbv K D A hAc hAf
      hvm hAm ν f F hF g hg W i N) =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        hilbertProjection N (planeHkValueOperator 1 (weakH1CarrierTimeCLM K a b i W t)) := by
  exact fixedBandPrimitive_ae_eq_cutoff_of_native_equation hab N ν
    (planeHkValueOperator (K i) (f i)) (weakH1CarrierTimeCLM K a b i W) _ _ _
    ((planeHkValueOperator (E := h i) (K i)).integrable_comp (hg i))
    (fun ψ => sourceWeakCarrier_native_equation hab ρ hρ v hv V hV hbv K D A hAc hAf
      hvm hAm ν f F hF g hg u heq φ hφ W R hu hw hrange π hπ C hmass hW i ψ)
end

/-! Pointwise convergence of every native weak test along the actual common Galerkin subsequence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceContinuousEquationAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceContinuousEquationTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceContinuousCarrier_native_equation {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h))
    (heq : ∀ N, ∀ t : Set.Icc a b, u N t = projectedInitial N f + ∫ s in a..t.1,
      projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf).reindex
          (clampPoint a b hab)) N ν s (extendCurve hab (u N) s) + projectedSource N F g s)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W)))
    (hrange : ∀ N t, familyProjection N (u N t) = u N t)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (C : ℝ)
    (hmass : ∀ N t, massNormSq ρ π
      (fun i => (hilbertBandHk N (K i) (u N t i)).val) ≤ C)
    (hW : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ j,
      W s j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (i : ι) (U : C(Set.Icc a b, PlaneHk Set.univ (K i) (h i)))
    (hinit : U ⟨a, le_rfl, hab⟩ = f i)
    (hUa : extendCurve hab U =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      truncatePlaneHk (E := h i) (Nat.le_succ (K i)) (weakHighCarrier K a b W i t))
    (t : Set.Icc a b) (ψ : PlaneHk Set.univ 1 (h i)) :
    let Cc := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf
    let hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
    inner ℝ (planeHkValueOperator (E := h i) (K i) (U t)) (planeHkValueOperator (E := h i) 1 ψ) =
      nativeRawTestValue ν (planeHkValueOperator (E := h i) (K i) (f i))
        (weakH1CarrierTimeCLM K a b i W) (limitDriftField hab Cc hc i W)
        (limitFluxField hab Cc hc W i
          ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
            (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i))))
        (fun s => planeHkValueOperator (E := h i) (K i) (g i s)) t ψ := by
  have hvv : (fun s => planeHkValueOperator (E := h i) (K i) (extendCurve hab U s))
      =ᵐ[volume.restrict (Set.Icc a b)] fun s =>
        planeHkValueOperator (E := h i) 1 (weakH1CarrierTimeCLM K a b i W s) := by
    filter_upwards [hUa, weakLowerCarrierTimeCLM_ae K a b i W,
      weakLowerCarrierTimeCLM_value_eq_H1_ae K a b i W] with s hu hl hv
    exact (congrArg (planeHkValueOperator (E := h i) (K i)) (hu.trans hl.symm)).trans hv
  have he := sourceWeakCarrier_native_equation hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    ν f F hF g hg u heq φ hφ W R hu hw hrange π hπ C hmass hW i ψ
  exact nativeRawTestValue_eq_continuousCarrier_of_ae hab (K i) ν (f i) U hinit
    (weakH1CarrierTimeCLM K a b i W) _ _ _
    ((planeHkValueOperator (E := h i) (K i)).integrable_comp (hg i)) hvv ψ he t
end

/-! Pointwise convergence of every native weak test along the actual common Galerkin subsequence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceSobolevIdentificationAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceSobolevIdentificationTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceFixedBandSobolevPrimitive_ae_eq_cutoff {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h))
    (heq : ∀ N, ∀ t : Set.Icc a b, u N t = projectedInitial N f + ∫ s in a..t.1,
      projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf).reindex
          (clampPoint a b hab)) N ν s (extendCurve hab (u N) s) + projectedSource N F g s)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W)))
    (hrange : ∀ N t, familyProjection N (u N t) = u N t)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (C : ℝ)
    (hmass : ∀ N t, massNormSq ρ π
      (fun i => (hilbertBandHk N (K i) (u N t i)).val) ≤ C)
    (hW : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ j,
      W s j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (i : ι) (N : ℕ) :
    extendCurve hab (sourceFixedBandSobolevPrimitive hab ρ hρ v hv V hV hbv K D A hAc hAf
      hvm hAm ν f F hF g hg W i N) =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        planeHkCutoff N (K i) (weakLowerCarrierTimeCLM K a b i W t) := by
  have hp := sourceFixedBandPrimitive_ae_eq_cutoff hab ρ hρ v hv V hV hbv K D A hAc hAf
    hvm hAm ν f F hF g hg u heq φ hφ W R hu hw hrange π hπ C hmass hW i N
  have hvv := weakLowerCarrierTimeCLM_value_eq_H1_ae K a b i W
  filter_upwards [hp, hvv] with t ht hval
  change hilbertBandHkOperator N (K i)
    (extendCurve hab (sourceFixedBandPrimitive hab ρ hρ v hv V hV hbv K D A hAc hAf
      hvm hAm ν f F hF g hg W i N) t) = _
  rw [ht]
  change hilbertBandHk N (K i)
    (hilbertProjection N (planeHkValueOperator 1 (weakH1CarrierTimeCLM K a b i W t))) =
      hilbertBandHk N (K i) (planeHkValueOperator (K i) (weakLowerCarrierTimeCLM K a b i W t))
  rw [hilbertBandHk_projection, hval]
end

/-! Pointwise convergence of every native weak test along the actual common Galerkin subsequence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceBandBoundAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceBandBoundTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceFixedBandSobolevPrimitive_norm_le {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h))
    (heq : ∀ N, ∀ t : Set.Icc a b, u N t = projectedInitial N f + ∫ s in a..t.1,
      projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf).reindex
          (clampPoint a b hab)) N ν s (extendCurve hab (u N) s) + projectedSource N F g s)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W)))
    (hrange : ∀ N t, familyProjection N (u N t) = u N t)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (C : ℝ)
    (hmass : ∀ N t, massNormSq ρ π
      (fun i => (hilbertBandHk N (K i) (u N t i)).val) ≤ C)
    (hW : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ j,
      W s j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (i : ι) (N : ℕ) (t : Set.Icc a b) :
    ‖sourceFixedBandSobolevPrimitive hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
      ν f F hF g hg W i N t‖ ≤ Real.sqrt ((∑ j, π j / factorialWeightMin ρ (K j)) * C) := by
  have hQ : 0 ≤ ∑ j, π j / factorialWeightMin ρ (K j) :=
    Finset.sum_nonneg (fun j _ => div_nonneg (hπ j).le
      (factorialWeightMin_pos (K := K j) ρ hρ).le)
  have hroot (n : ℕ) : ‖lowerBandJetOperator (φ n) K (u (φ n) t)‖ ≤
      Real.sqrt ((∑ j, π j / factorialWeightMin ρ (K j)) * C) :=
    Real.le_sqrt_of_sq_le ((lowerBandJet_normSq_le (φ n) K ρ hρ π hπ (u (φ n) t)).trans
      (mul_le_mul_of_nonneg_left (hmass (φ n) t) hQ))
  change ‖hilbertBandHkOperator (E := h i) N (K i)
    (sourceFixedBandPrimitive hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
      ν f F hF g hg W i N t)‖ ≤ _
  apply norm_clm_le_of_tendsto_inner (hilbertBandHkOperator (E := h i) N (K i))
    (u := fun n => hilbertProjection N (u (φ n) t i))
  · intro n
    rw [hilbertBandHkOperator_apply, hilbertBandHk_projection]
    have hn : hilbertProjection (φ n) (u (φ n) t i) = u (φ n) t i := by
      simpa only [familyProjection_component] using
        congrArg (fun q : ProjectedFamily h => q i) (hrange (φ n) t)
    exact (hilbertBandHk_norm_le_of_range N (φ n) (K i) _ hn).trans
      ((PiLp.norm_apply_le (lowerBandJetOperator (φ n) K (u (φ n) t)) i).trans (hroot n))
  · intro z
    exact sourceFixedBandPrimitive_test_tendsto hab ρ hρ v hv V hV hbv K D A hAc hAf
      hvm hAm ν f F hF g hg u heq φ hφ W R hu hw hW i t N z
end

end AVRegularity.CoupledEnergyPlane
end
