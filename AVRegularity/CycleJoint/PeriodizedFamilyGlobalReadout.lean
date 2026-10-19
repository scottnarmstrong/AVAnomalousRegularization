-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.FamilyNaturalTimeRemainderReservedJets
import AVRegularity.CycleJoint.ReferencePhysicalSpatialSmooth
public import AVRegularity.CycleJoint.PlaneAllMomentNativeResidualBudget
import AVRegularity.CycleJoint.PlaneJetMultiplierSuperposition
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open AVenhance Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.ChartTransport AVRegularity.CycleReference
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The independent pointwise certificate bounds the actual native Piola operator before partition assembly. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem pointwise_molecular_native_flow_transport_uniform_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < ocEpsilon q Λ (m - 1))
    (hρE : ρ ≤ ocEpsilon q Λ (m - 1)) (ha : 0 ≤ ocA α q Λ (m - 1)) (hρ : 0 < ρ)
    (Cm : ℕ → ℝ) (Jm : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm b)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0)
    (p : P) (c : Ctx p)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (hnchart : K v ≤ Jchart + 1) (N : ℕ) (hN : N ≤ Jchart)
    (s t τ : ℝ)
    (hs : s ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (ht : t ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |s - t| ≤ 2 * Cage * ocTauPP α q Λ m)
    (hdom : ∀ Y : Vec 2, (τ, Y) ∈ dom p c)
    (n r : ℕ) (hn : n ≤ K v) (hr : 1 ≤ r)
    (hnN : n + (F.identity v u γ).maxOrder ≤ N) (hrD : r + 1 ≤ D) (x : Vec 2) :
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let CK := compConst Cflow N * Cflow
    let Bcost := (Kmax.factorial : ℝ) * Cflow ^ Kmax * ((Kmax + 1 : ℕ) *
      ((4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2))
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff (naturalPreparationJacobian hφ s t)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) p c v u γ d I τ
          (streamFlow φ hφ s y t) (e⁻¹ • streamFlow φ hφ s y t)) r A y a)) x‖ ≤
      ‖(F.identity v u γ).map‖ *
        ((2 : ℝ) ^ (D + 1) *
          (((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) ^ 2 * CK *
            (3 * (N + 1 : ℕ) * 2 ^ N * CK) ^ D) * Bcost) *
        (∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
          ∑ I : DerivativeWord2 (d - 1),
            (pointwiseMolecularJet ρ e (K v) 0 (fun z : F.Index => dom z.1 z.2)
              (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ d I)).toReal *
              (ocEpsilon q Λ (m - 1))⁻¹ ^ (d - 1 - r)) := by
  dsimp only
  let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
  let CK := compConst Cflow N * Cflow
  let Bcost := (Kmax.factorial : ℝ) * Cflow ^ Kmax * ((Kmax + 1 : ℕ) *
    ((4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2))
  let CT := (((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) ^ 2 * CK *
    (3 * (N + 1 : ℕ) * 2 ^ N * CK) ^ D)
  let M := fun d (I : DerivativeWord2 (d - 1)) =>
    (pointwiseMolecularJet ρ e (K v) 0 (fun z : F.Index => dom z.1 z.2)
      (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ d I)).toReal *
        (ocEpsilon q Λ (m - 1))⁻¹ ^ (d - 1 - r)
  have hh := pointwise_molecular_native_flow_transport_budget F π hπ K Kmax hK dom ν e ρ
    hν he hE hρE ha hρ Cm Jm b henv v u γ hγ p c hc hnchart N hN
    s t τ hs ht hage hdom n r hn hr hnN x
  have heq (d : ℕ) (I : DerivativeWord2 (d - 1)) :
      Bcost * (pointwiseMolecularJet ρ e (K v) 0 (fun z : F.Index => dom z.1 z.2)
        (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ d I)).toReal *
          (ocEpsilon q Λ (m - 1))⁻¹ ^ (d - 1 - r) = Bcost * M d I := by
    dsimp only [M]
    ring
  dsimp only at hh
  apply hh.trans
  rw [native_transport_direction_sum]
  dsimp only [Bcost, Cflow] at heq
  simp_rw [heq]
  simp_rw [← Finset.mul_sum]
  have hCflow : 1 ≤ Cflow := one_le_jetConst _ _
  have hCK : 1 ≤ CK := preparation_jacobian_constant_ge_one Jchart Cchart N
  have hpow : (2 : ℝ) ^ (r + 2) ≤ 2 ^ (D + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hsum : 0 ≤ ∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
      ∑ I : DerivativeWord2 (d - 1), M d I := by
    apply Finset.sum_nonneg
    intro d _
    apply Finset.sum_nonneg
    intro I _
    exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (inv_nonneg.mpr hE.le) _)
  have hnT : 0 ≤ CT := by dsimp [CT]; positivity
  have hnB : 0 ≤ Bcost := by dsimp [Bcost]; positivity
  have hp := mul_le_mul_of_nonneg_right hpow
    (mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg (F.identity v u γ).map) hnT) hnB) hsum)
  convert hp using 1 <;> ring
end

/-! The independent pointwise certificate bounds the actual native Piola operator before partition assembly. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem pointwise_molecular_native_transport_uniform_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < ocEpsilon q Λ (m - 1))
    (hρE : ρ ≤ ocEpsilon q Λ (m - 1)) (ha : 0 ≤ ocA α q Λ (m - 1)) (hρ : 0 < ρ)
    (Cm : ℕ → ℝ) (Jm : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm b)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0)
    (p : P) (c : Ctx p)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (hnchart : K v ≤ Jchart + 1) (N : ℕ) (hN : N ≤ Jchart)
    (s t : ℝ)
    (hs : s ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (ht : t ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |s - t| ≤ 2 * Cage * ocTauPP α q Λ m)
    (hdom : ∀ Y : Vec 2, (t, Y) ∈ dom p c)
    (n r : ℕ) (hn : n ≤ K v) (hr : 1 ≤ r)
    (hnN : n + (F.identity v u γ).maxOrder ≤ N) (hrD : r + 1 ≤ D) (x : Vec 2) :
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let CK := compConst Cflow N * Cflow
    let Bcost := (Kmax.factorial : ℝ) * Cflow ^ Kmax * ((Kmax + 1 : ℕ) *
      ((4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2))
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff (naturalPreparationJacobian hφ s t)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) p c v u γ d I t
          (streamFlow φ hφ s y t) (e⁻¹ • streamFlow φ hφ s y t)) r A y a)) x‖ ≤
      ‖(F.identity v u γ).map‖ *
        ((2 : ℝ) ^ (D + 1) *
          (((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) ^ 2 * CK *
            (3 * (N + 1 : ℕ) * 2 ^ N * CK) ^ D) * Bcost) *
        (∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
          ∑ I : DerivativeWord2 (d - 1),
            (pointwiseMolecularJet ρ e (K v) 0 (fun z : F.Index => dom z.1 z.2)
              (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ d I)).toReal *
              (ocEpsilon q Λ (m - 1))⁻¹ ^ (d - 1 - r)) := by
  dsimp only
  let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
  let CK := compConst Cflow N * Cflow
  let Bcost := (Kmax.factorial : ℝ) * Cflow ^ Kmax * ((Kmax + 1 : ℕ) *
    ((4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2))
  let CT := (((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) ^ 2 * CK *
    (3 * (N + 1 : ℕ) * 2 ^ N * CK) ^ D)
  let M := fun d (I : DerivativeWord2 (d - 1)) =>
    (pointwiseMolecularJet ρ e (K v) 0 (fun z : F.Index => dom z.1 z.2)
      (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ d I)).toReal *
        (ocEpsilon q Λ (m - 1))⁻¹ ^ (d - 1 - r)
  have hh := pointwise_molecular_native_transport_budget F π hπ K Kmax hK dom ν e ρ
    hν he hE hρE ha hρ Cm Jm b henv v u γ hγ p c hc hnchart N hN
    s t hs ht hage hdom n r hn hr hnN x
  have heq (d : ℕ) (I : DerivativeWord2 (d - 1)) :
      Bcost * (pointwiseMolecularJet ρ e (K v) 0 (fun z : F.Index => dom z.1 z.2)
        (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ d I)).toReal *
          (ocEpsilon q Λ (m - 1))⁻¹ ^ (d - 1 - r) = Bcost * M d I := by
    dsimp only [M]
    ring
  dsimp only at hh
  apply hh.trans
  rw [native_transport_direction_sum]
  dsimp only [Bcost, Cflow] at heq
  simp_rw [heq]
  simp_rw [← Finset.mul_sum]
  have hCflow : 1 ≤ Cflow := one_le_jetConst _ _
  have hCK : 1 ≤ CK := preparation_jacobian_constant_ge_one Jchart Cchart N
  have hpow : (2 : ℝ) ^ (r + 2) ≤ 2 ^ (D + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hsum : 0 ≤ ∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
      ∑ I : DerivativeWord2 (d - 1), M d I := by
    apply Finset.sum_nonneg
    intro d _
    apply Finset.sum_nonneg
    intro I _
    exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (inv_nonneg.mpr hE.le) _)
  have hnT : 0 ≤ CT := by dsimp [CT]; positivity
  have hnB : 0 ≤ Bcost := by dsimp [Bcost]; positivity
  have hp := mul_le_mul_of_nonneg_right hpow
    (mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg (F.identity v u γ).map) hnT) hnB) hsum)
  convert hp using 1 <;> ring
end

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Finite weighted source lift energy gives finite integrated coupling-term energy. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] in
/-- The actual clamped coefficient multiplier preserves finite integrated weighted lift energy. -/
theorem planeCoupledFluxTerm_weighted_time_energy_ne_top {a b : ℝ}
    (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hc : ∀ t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A t))
    (w : ℝ → PlaneHk Set.univ (K i' + 1) (h i'))
    (hw : MemLp w 2 (volume.restrict (Set.Icc a b)))
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (he : (∫⁻ t in Set.Icc a b, storedChartFactorialEnergy ρ (fun x => q x ^ 2) (w t)) ≠ ⊤) :
    (∫⁻ t in Set.Icc a b, storedChartFactorialEnergy ρ (fun x => q x ^ 2)
      (planeCoupledFluxTerm ρ hρ K D a b i i' d A hA
        (clampPoint a b hab t) (clampPoint a b hab t).property
        (hc _ (clampPoint a b hab t).property) (w t))) ≠ ⊤ := by
  let C := ENNReal.ofReal ((coefficientSeminorm ρ (K i) a b A).toReal ^ 2) *
    ENNReal.ofReal ((derivativeReserveFactor ρ (K i) (d.1 - 1)) ^ 2)
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hm := storedChartFactorialEnergy_time_aemeasurable ρ (fun x => q x ^ 2)
    (hq.pow 2) (fun x => sq_pos_of_pos (hq0 x)) _ w hw
  have hae := ae_lt_top' hm he
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hC he)
  calc
    _ ≤ ∫⁻ t in Set.Icc a b, C * storedChartFactorialEnergy ρ (fun x => q x ^ 2) (w t) := by
      apply lintegral_mono_ae
      filter_upwards [hae] with t ht
      exact planeCoupledFluxTerm_weighted_factorialEnergy_le_of_finite
        ρ hρ K D a b i i' d A hA _ (clampPoint a b hab t).property
        (hc _ (clampPoint a b hab t).property) (w t) q hq ht.ne
    _ = C * ∫⁻ t in Set.Icc a b, storedChartFactorialEnergy ρ (fun x => q x ^ 2) (w t) :=
      lintegral_const_mul' _ _ hC

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Component response certificates assemble actual scalar weak solutions on the original family. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
  (K : ι → ℕ) (a b ϖ ρ : ℝ)
  (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))

theorem planeComponentAllMomentResponse_assemble
    (hR : ∀ i, IsPlaneComponentAllMomentResponse (E := h i) M v (K i) a b ϖ ρ (R i))
    (f : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) :
    ∃ (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
      (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
        (fun _ _ => 0) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i) ∧
      ∀ i, PlaneTimeAllMomentRepresents (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b)) (f i) (F i) ∧
        PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)) (R i (f i)) (w i) := by
  classical
  choose F u w hs hf hw using fun i => hR i (f i)
  refine ⟨F, fun i => u i (), fun i => w i (), ?_, fun i => ⟨hf i, hw i⟩⟩
  apply scalarPlaneChain_of_components K a b v (fun t _ => M t)
    (fun _ => 0) F (fun i => u i ()) (fun i => w i ())
  intro i
  have hu : u i = fun _ => u i () := by funext x; cases x; rfl
  have hw' : w i = fun _ => w i () := by funext x; cases x; rfl
  have hi := hs i
  rw [hu, hw'] at hi
  exact hi

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The actual polynomial-weighted coupling flux has the original dissipative reserve norm price. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeCoupledFluxTerm_weighted_gradient_norm
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i u : ι) (d : admissibleOrders K D i u)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (U : PlaneHk Set.univ (K u + 1) (h u))
    (he : weightedGradFactorialNormSq n ϖ zc ρ (K u) U ≠ ⊤)
    (hD : JetMemL2On Set.univ (fun β x => planeMomentSquareRoot n ϖ zc x •
      (planeCoupledFluxTerm ρ hρ K D a b i u d A hA t ht hC U).toFunction.jet β x)) :
    ‖scalarWeightedFactorialJet ρ (planeMomentSquareRoot n ϖ zc)
      (planeCoupledFluxTerm ρ hρ K D a b i u d A hA t ht hC U) hD‖ ≤
      Real.sqrt (Fintype.card (DerivativeWord2 (d.1 - 1)) : ℝ) *
        (coefficientSeminorm ρ (K i) a b A).toReal *
          derivativeReserveFactor ρ (K i) (d.1 - 2) *
            ‖polynomialWeightedGradientJet n ϖ zc ρ hρ U he‖ := by
  have hb := planeCoupledFluxTerm_weighted_gradient_budget
    ρ hρ K D a b i u d A hA t ht hC n ϖ zc U he
  rw [← scalarWeightedFactorialJet_moment_normSq n ϖ zc ρ _ hD,
    ← polynomialWeightedGradientJet_normSq n ϖ zc ρ hρ U he] at hb
  have hr : 0 ≤ derivativeReserveFactor ρ (K i) (d.1 - 2) := by
    unfold derivativeReserveFactor
    positivity
  exact norm_le_of_ennreal_card_square_budget _ _ _ _ _ ENNReal.toReal_nonneg hr hb

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The actual terminal native forcing has one extra metric power at the selected initial moment reserve. -/

section
variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance terminalForcingGradientNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k
local instance terminalForcingGradientNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (E i)) := allMomentTimeNativeModule k

theorem planeAllMoment_terminal_forcing_energy_gain
    (K : ι → ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ)
    (M S : Module.End ℝ (∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 μ))
    (L : (∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 μ) →
      ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0 μ)
    (a b : ℕ → ℝ≥0∞) (C D η θ : ℝ≥0∞) (p N : ℕ)
    (hM : ∀ n, n + p ≤ N → ∀ W,
      planeAllMomentFamilyGradientEnergy (E := E) K n ϖ ρ μ π (M W) ≤
        a n * planeAllMomentFamilyGradientEnergy (E := E) K (n + p) ϖ ρ μ π W)
    (hS : ∀ n, n + p ≤ N → ∀ W,
      planeAllMomentFamilyGradientEnergy (E := E) K n ϖ ρ μ π (S W) ≤
        b n * planeAllMomentFamilyGradientEnergy (E := E) K (n + p) ϖ ρ μ π W)
    (ha : ∀ k ≤ N, a k ≤ C * η ^ 2) (hb : ∀ k ≤ N, b k ≤ C * θ ^ 2)
    (W : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 μ)
    (n J H : ℕ) (hN : n + p + (J + H) * p ≤ N)
    (hL : ∀ X, planeAllMomentFamilyEnergy (E := fun i => PiLp 2 (fun _ : Fin 2 => E i))
      K n ϖ ρ μ π (L X) ≤ (D * η ^ 2) *
        planeAllMomentFamilyGradientEnergy (E := E) K (n + p) ϖ ρ μ π X) :
    planeAllMomentFamilyEnergy (E := fun i => PiLp 2 (fun _ : Fin 2 => E i))
      K n ϖ ρ μ π (L (∑ h ∈ Finset.range (H + 1), finiteResponse 1 M S W J h)) ≤
      (D * terminalResponseEnergyPrice C θ J H) * η ^ (2 * (J + 1)) *
        planeAllMomentFamilyGradientEnergy (E := E) K N ϖ ρ μ π W := by
  exact finiteResponse_terminal_forcing_energy_gain M S
    (fun n X => planeAllMomentFamilyGradientEnergy (E := E) K n ϖ ρ μ π X)
    (planeAllMomentFamilyEnergy (E := fun i => PiLp 2 (fun _ : Fin 2 => E i)) K n ϖ ρ μ π)
    L a b C D η θ p N (fun n => planeAllMomentFamilyGradientEnergy_zero K n ϖ ρ μ π)
    (fun n X Y => planeAllMomentFamilyGradientEnergy_add_le K n ϖ ρ μ π X Y)
    hM hS ha hb W (planeAllMomentFamilyGradientEnergy (E := E) K N ϖ ρ μ π W)
    (fun k hk => planeAllMomentFamilyGradientEnergy_moment_mono K hk ϖ ρ μ π W)
    n J H hN hL
end

/-! The retained native family gradient has a fixed response price at one initial moment reserve. -/

section
variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance retainedGradientGainNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k
local instance retainedGradientGainNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (E i)) := allMomentTimeNativeModule k

theorem planeAllMoment_retained_gradient_energy_gain
    (K : ι → ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ)
    (M S : Module.End ℝ (∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 μ))
    (a b : ℕ → ℝ≥0∞) (C η θ : ℝ≥0∞) (p N : ℕ)
    (hM : ∀ n, n + p ≤ N → ∀ W,
      planeAllMomentFamilyGradientEnergy (E := E) K n ϖ ρ μ π (M W) ≤
        a n * planeAllMomentFamilyGradientEnergy (E := E) K (n + p) ϖ ρ μ π W)
    (hS : ∀ n, n + p ≤ N → ∀ W,
      planeAllMomentFamilyGradientEnergy (E := E) K n ϖ ρ μ π (S W) ≤
        b n * planeAllMomentFamilyGradientEnergy (E := E) K (n + p) ϖ ρ μ π W)
    (ha : ∀ k ≤ N, a k ≤ C * η ^ 2) (hb : ∀ k ≤ N, b k ≤ C * θ ^ 2) (hη : η ≤ 1)
    (W : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 μ)
    (n J H : ℕ) (hN : n + (J + H) * p ≤ N) :
    planeAllMomentFamilyGradientEnergy (E := E) K n ϖ ρ μ π
      (∑ j ∈ Finset.range (J + 1), ∑ h ∈ Finset.range (H + 1), finiteResponse 1 M S W j h) ≤
      retainedResponseEnergyPrice C θ J H *
        planeAllMomentFamilyGradientEnergy (E := E) K N ϖ ρ μ π W := by
  exact finiteResponse_retained_energy_gain M S
    (fun n X => planeAllMomentFamilyGradientEnergy (E := E) K n ϖ ρ μ π X)
    a b C η θ p N (fun n => planeAllMomentFamilyGradientEnergy_zero K n ϖ ρ μ π)
    (fun n X Y => planeAllMomentFamilyGradientEnergy_add_le K n ϖ ρ μ π X Y)
    hM hS ha hb hη W (planeAllMomentFamilyGradientEnergy (E := E) K N ϖ ρ μ π W)
    (fun k hk => planeAllMomentFamilyGradientEnergy_moment_mono K hk ϖ ρ μ π W)
    n J H hN
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Literal linear raw forcing constructions with every finite moment define native all-moment linear maps. -/

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [AddCommGroup X] [Module ℝ X]

def IsPlaneTimeAllMomentRawLinearMap (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (H : X → ℝ → Vec 2 → E)
    (T : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ) : Prop :=
  ∀ x, ∀ᵐ t ∂μ,
    planeValue (planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (T x) t) =ᵐ[volume] H x t

theorem exists_planeRaw_allMoment_linearMap
    (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ) (H : X → ℝ → Vec 2 → E)
    (hadd : ∀ x y, ∀ᵐ t ∂μ, H (x + y) t =ᵐ[volume] fun z => H x t z + H y t z)
    (hsmul : ∀ (c : ℝ) x, ∀ᵐ t ∂μ, H (c • x) t =ᵐ[volume] fun z => c • H x t z)
    (hex : ∀ x n, ∃ V : ℝ → PlaneHk Set.univ K E,
      MemLp V 2 μ ∧
      (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (V t) ∂μ) ≠ ⊤ ∧
      ∀ᵐ t ∂μ, planeValue (V t) =ᵐ[volume] H x t) :
    ∃ T : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ,
      IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ H T := by
  have hx (x : X) := planeForcing_exists_every_moment ϖ ρ zc μ (H x) (hex x)
  choose V hV he hread using hx
  obtain ⟨haddV, hsmulV⟩ := planeForcing_ae_linear_readout_superposition μ H V hadd hsmul hread
  obtain ⟨T, hT⟩ := planeTimeAllMoment_curve_linear_representation K ϖ ρ zc μ V hV haddV hsmulV he
  refine ⟨T, ?_⟩
  intro x
  filter_upwards [hT x, hread x] with t ht hr
  rw [ht]
  exact hr

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Polynomial energy periodizes both the continuous trajectory and its genuine L2 Sobolev lift. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem exists_polynomialCarrier_trace_lift
    (a b : ℝ) (u : ℝ → PlaneHk Set.univ K E) (w : ℝ → PlaneHk Set.univ (K + 1) E)
    (hu : ContinuousOn u (Set.Icc a b))
    (hw : MemLp w 2 (volume.restrict (Set.Icc a b)))
    (hlift : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), truncatePlaneHk (Nat.le_succ K) (w t) = u t)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t ∈ Set.Icc a b, weightedFactorialNormSq 4 ϖ z ρ K (u t) ≤ ENNReal.ofReal C)
    (he : (∫⁻ t in Set.Icc a b, weightedFactorialNormSq 4 ϖ z ρ (K + 1) (w t)) ≠ ⊤) :
    ∃ (U : ℝ → TorusHk K E) (W : ℝ → TorusHk (K + 1) E),
      ContinuousOn U (Set.Icc a b) ∧ MemLp W 2 (volume.restrict (Set.Icc a b)) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Icc a b)), truncateTorusHk (Nat.le_succ K) (W t) = U t) ∧
      (∀ t ∈ Set.Icc a b, ∀ α, (U t).val α =ᵐ[volume.restrict AVenhance.unitCube]
        periodizeRawJet (u t).toFunction.jet α) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Icc a b)), ∀ α, (W t).val α =ᵐ[volume.restrict AVenhance.unitCube]
        periodizeRawJet (w t).toFunction.jet α) := by
  let g := radialMomentGoodPart u z
  have hm (t : ℝ) : HasRadialPlaneMoments (g t) z := radialMomentGoodPart_hasMoments u z t
  have hg (t : ℝ) (ht : t ∈ Set.Icc a b) : g t = u t :=
    radialMomentGoodPart_eq u z t (hasRadialPlaneMoments_of_finite_polynomial (u t)
      ϖ hϖ z ρ hρ (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb t ht)))
  have hgc : ContinuousOn g (Set.Icc a b) := hu.congr hg
  let U := fun t => periodizeRadialPlaneCarrier (g t) z (hm t)
  have hUc : ContinuousOn U (Set.Icc a b) := by
    apply periodizeRadialPlaneCarrier_continuousOn g (Set.Icc a b) hgc z hm
      (polynomialPeriodizationMomentBudget K ϖ ρ C)
      (polynomialPeriodizationMomentBudget_nonneg K ϖ ρ C)
    intro t ht α
    rw [hg t ht]
    exact polynomial_energy_radial_component_budget (u t) ϖ hϖ z ρ hρ C hC (hb t ht) α
  obtain ⟨W, hW, hWr⟩ := exists_polynomialCarrier_periodization_time_memLp
    ϖ hϖ z ρ hρ (volume.restrict (Set.Icc a b)) w hw he
  have hlg : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), truncatePlaneHk (Nat.le_succ K) (w t) = g t := by
    filter_upwards [hlift, ae_restrict_mem measurableSet_Icc] with t ht hi
    exact ht.trans (hg t hi).symm
  refine ⟨U, W, hUc, hW, periodized_carrier_lift_ae _ (Nat.le_succ K) z g w hm hlg W hWr, ?_, hWr⟩
  intro t ht α
  have hr := periodizeRadialPlaneCarrier_component_ae (g t) z (hm t) α
  exact hr.trans (Filter.Eventually.of_forall (fun x =>
    congrArg (fun f : PlaneHk Set.univ K E => periodizeRawJet f.toFunction.jet α x) (hg t ht)))

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual regularity, lift compatibility, and raw readouts required by family periodization. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def IsPeriodizedFamilyPair (K : ι → ℕ) (a b : ℝ)
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (U : ∀ i, ℝ → TorusHk (K i) (h i))
    (W : ∀ i, ℝ → TorusHk (K i + 1) (h i)) : Prop :=
  (∀ i, ContinuousOn (U i) (Set.Icc a b)) ∧
  (∀ i, MemLp (W i) 2 (volume.restrict (Set.Icc a b))) ∧
  (∀ i, ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), truncateTorusHk (Nat.le_succ (K i)) (W i t) = U i t) ∧
  (∀ i, ∀ t ∈ Set.Icc a b, ∀ α, (U i t).val α =ᵐ[volume.restrict AVenhance.unitCube]
    periodizeRawJet (u i t).toFunction.jet α) ∧
  (∀ i, ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), ∀ α, (W i t).val α =ᵐ[volume.restrict AVenhance.unitCube]
    periodizeRawJet (w i t).toFunction.jet α)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! A native raw forcing map has the same actual curve as any independently constructed native forcing with its literal readout. -/

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [AddCommGroup X] [Module ℝ X]

theorem planeRaw_allMoment_map_represents
    (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ) (H : X → ℝ → Vec 2 → E)
    (T : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (hT : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ H T)
    (x : X) (V : ℝ → PlaneHk Set.univ K E)
    (hV : ∀ᵐ t ∂μ, planeValue (V t) =ᵐ[volume] H x t) :
    PlaneTimeAllMomentRepresents K ϖ ρ zc μ (T x) V := by
  filter_upwards [hT x, hV] with t ht hv
  exact planeHk_eq_of_planeValue_ae (ht.trans hv.symm)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Native forcing-map readouts depend only on their time window. -/

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [AddCommGroup X] [Module ℝ X]

theorem planeRaw_allMoment_linearMap_congr_ae
    (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (H H' : X → ℝ → Vec 2 → E)
    (T : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (hT : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ H T)
    (heq : ∀ x, ∀ᵐ t ∂μ, H' x t =ᵐ[volume] H x t) :
    IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ H' T := by
  intro x
  filter_upwards [hT x, heq x] with t ht he
  exact ht.trans he.symm

theorem planeRaw_allMoment_linearMap_window_congr
    (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (a b : ℝ)
    (H H' : X → ℝ → Vec 2 → E)
    (T : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc
      (volume.restrict (Set.Icc a b)))
    (hT : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc (volume.restrict (Set.Icc a b)) H T)
    (heq : ∀ x t, t ∈ Set.Icc a b → H' x t = H x t) :
    IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc (volume.restrict (Set.Icc a b)) H' T := by
  apply planeRaw_allMoment_linearMap_congr_ae K ϖ ρ zc _ H H' T hT
  intro x
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact Filter.Eventually.of_forall (congrFun (heq x t ht))

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Measurability of the inputs gives joint measurability of the actual retained inherited row after reference cell scaling. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparationReferenceCellSourceCoefficient_joint_measurable
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (hν : 0 < ν) (he : e ≠ 0) (K : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E K)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (actual : ∀ p, Ctx p) (s : ℝ) (yc : Vec 2) (v u : ι)
    (d : admissibleOrders K D v u) :
    Measurable (fun p : Set.Icc ((e⁻¹) ^ 2 * (ν * a)) ((e⁻¹) ^ 2 * (ν * b)) × Vec 2 =>
      preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc v u d p.1 p.2) := by
  have hσ : 0 < (e⁻¹) ^ 2 * ν := mul_pos (sq_pos_of_ne_zero (inv_ne_zero he)) hν
  have htime (t : ℝ) : ((e⁻¹) ^ 2 * ν)⁻¹ * t = ν⁻¹ * (e ^ 2 * t) := by
    rw [mul_inv_rev, inv_pow, inv_inv, mul_assoc]
  have hh := reference_physicalCoefficient_joint_measurable F hc ν e E K hs hmeas hwmeas
    actual s v u d.1
  have hi := affineTimeScaledCoefficient_joint_measurable a b ((e⁻¹) ^ 2 * ν)
    ((e * (e ^ (d.1 - 1))⁻¹) * ν⁻¹) e hσ yc
    (physicalCoefficient (referenceChartedFamily F hφ s) ν e E actual v u d.1) hh
  rw [show (e⁻¹) ^ 2 * (ν * a) = ((e⁻¹) ^ 2 * ν) * a by rw [mul_assoc],
    show (e⁻¹) ^ 2 * (ν * b) = ((e⁻¹) ^ 2 * ν) * b by rw [mul_assoc]]
  simpa only [htime, preparationReferenceCellSourceCoefficient, edgeCoefficient] using hi

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Finite weighted lift moments control the full actual finite coupling row. -/

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

/-- Finite weighted source curves give a finite weighted coupling-row time budget. -/
theorem planeCouplingFluxRow_weighted_time_energy_ne_top
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)))
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (he : ∀ i, (∫⁻ t in Set.Icc a b,
      storedChartFactorialEnergy ρ (fun x => q x ^ 2) (w i t)) ≠ ⊤) (i : ι) :
    (∫⁻ t in Set.Icc a b, storedChartFactorialEnergy ρ (fun x => q x ^ 2)
      (planeCouplingFluxRow hab ρ hρ K D A hA hc w i t)) ≠ ⊤ := by
  let term (i' : ι) (d : admissibleOrders K D i i') (t : ℝ) :=
    planeCoupledFluxTerm ρ hρ K D a b i i' d (A i i' d) (hA i i' d)
      (clampPoint a b hab t) (clampPoint a b hab t).property
      (hc i i' d _ (clampPoint a b hab t).property) (w i' t)
  have hterm (i' : ι) (d : admissibleOrders K D i i') :
      MemLp (term i' d) 2 (volume.restrict (Set.Icc a b)) :=
    planeCoupledFluxTerm_memLp hab ρ hρ K D i i' d (A i i' d)
      (hA i i' d) (hc i i' d) (hAm i i' d) (w i') (hw i')
  have ht (i' : ι) (d : admissibleOrders K D i i') :
      (∫⁻ t in Set.Icc a b, storedChartFactorialEnergy ρ (fun x => q x ^ 2) (term i' d t)) ≠ ⊤ :=
    planeCoupledFluxTerm_weighted_time_energy_ne_top hab ρ hρ K D i i' d
      (A i i' d) (hA i i' d) (hc i i' d) (w i') (hw i') q hq hq0 (he i')
  change (∫⁻ t in Set.Icc a b, storedChartFactorialEnergy ρ (fun x => q x ^ 2)
    (∑ i', ∑ d : admissibleOrders K D i i', term i' d t)) ≠ ⊤
  apply integrated_stored_energy_finite_sum_ne_top ρ hρ q hq hq0
  · intro i'
    exact memLp_fintype_sum (term i') (hterm i')
  · intro i'
    exact integrated_stored_energy_finite_sum_ne_top ρ hρ q hq hq0 _
      (term i') (hterm i') (ht i')

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Arithmetic of certified native forcing maps preserves their literal readouts. -/

variable {E X Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

local instance rawArithmeticNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  allMomentTimeNativeNormed k
local instance rawArithmeticModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) :=
  allMomentTimeNativeModule k

variable (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)

theorem planeRaw_allMoment_linearMap_comp
    (H : X → ℝ → Vec 2 → E)
    (T : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (hT : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ H T) (S : Y →ₗ[ℝ] X) :
    IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ (fun y => H (S y)) (T.comp S) :=
  fun y => hT (S y)

theorem planeRaw_allMoment_linearMap_add
    (H G : X → ℝ → Vec 2 → E)
    (T S : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (hT : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ H T)
    (hS : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ G S) :
    IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ
      (fun x t z => H x t z + G x t z) (T + S) := by
  intro x
  filter_upwards [planeTimeAllMomentCarrier_add K ϖ ρ zc μ (T x) (S x), hT x, hS x]
    with t ht htx hsx
  change planeValue (planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (T x + S x) t) =ᵐ[volume] _
  rw [ht]
  have ha := planeJetOrder_add_all_ae 0 (fun i => Fin.elim0 i)
    (planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (T x) t)
    (planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (S x) t)
  filter_upwards [ha, htx, hsx] with z hz htz hsz
  exact hz.trans (congrArg₂ (· + ·) htz hsz)

theorem planeRaw_allMoment_linearMap_smul
    (H : X → ℝ → Vec 2 → E)
    (T : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (hT : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ H T) (c : ℝ) :
    IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ
      (fun x t z => c • H x t z) (c • T) := by
  intro x
  filter_upwards [planeTimeAllMomentCarrier_smul K ϖ ρ zc μ c (T x), hT x]
    with t ht htx
  change planeValue (planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (c • T x) t) =ᵐ[volume] _
  rw [ht]
  have ha := planeJetOrder_smul_ae 0 (fun i => Fin.elim0 i) c
    (planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (T x) t)
  filter_upwards [ha, htx] with z hz htz
  exact hz.trans (congrArg (c • ·) htz)

theorem planeRaw_allMoment_linearMap_sub
    (H G : X → ℝ → Vec 2 → E)
    (T S : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (hT : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ H T)
    (hS : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ G S) :
    IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ
      (fun x t z => H x t z - G x t z) (T - S) := by
  have hn := planeRaw_allMoment_linearMap_smul K ϖ ρ zc μ G S hS (-1)
  simpa only [neg_one_smul, sub_eq_add_neg] using
    planeRaw_allMoment_linearMap_add K ϖ ρ zc μ H (fun x t z => (-1 : ℝ) • G x t z)
      T ((-1 : ℝ) • S) hT hn

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! The actual native coupling row reads the retained full array and preserves almost-everywhere linearity of its input lifts. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {a b : ℝ}

variable (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hC : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))

theorem planeCouplingFluxRow_planeValue_ae
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)) (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    planeValue (planeCouplingFluxRow hab ρ hρ K D A hA hC w i t) =ᵐ[volume]
      planeRawCouplingFlux K D t A (fun j => w j t) i := by
  rw [planeValue_eq_rawValue]
  exact (univToPlane_ae
    ((planeCouplingFluxRow hab ρ hρ K D A hA hC w i t).val (valueIndex2 (K i)))).symm.trans
    (planeCouplingFluxRow_raw_value_ae hab ρ hρ K D A hA hC w i t ht)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Spatial metric constructions, including Taylor jets, preserve native readouts
under equality on the time window. -/

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [AddCommGroup X] [Module ℝ X]

theorem planeMetric_raw_map_window_congr
    (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (a b : ℝ)
    (G G' : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (H : (Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) → X → ℝ → Vec 2 → E)
    (T : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc
      (volume.restrict (Set.Icc a b)))
    (hT : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc
      (volume.restrict (Set.Icc a b)) (fun x t => H (G t) x t) T)
    (heq : ∀ t ∈ Set.Icc a b, G' t = G t) :
    IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc
      (volume.restrict (Set.Icc a b)) (fun x t => H (G' t) x t) T := by
  exact planeRaw_allMoment_linearMap_window_congr K ϖ ρ zc a b
    (fun x t => H (G t) x t) (fun x t => H (G' t) x t) T hT
    (fun x t ht => congrArg (fun M => H M x t) (heq t ht))

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Zero raw sources are represented by the actual zero native forcing map. -/

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [AddCommGroup X] [Module ℝ X]

theorem planeRaw_allMoment_zero_map
    (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ) (H : X → ℝ → Vec 2 → E)
    (hH : ∀ x t z, H x t z = 0) :
    IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ H
      (0 : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ) := by
  intro x
  simp only [LinearMap.zero_apply]
  filter_upwards [planeTimeAllMomentCarrier_zero_representative (E := E) K ϖ ρ zc μ 0 rfl] with t ht
  rw [ht]
  have hzero : H x t = fun _ => 0 := funext (hH x t)
  rw [hzero]
  exact planeValue_zero_ae (E := E) K

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Finite weighted lift moments control the full actual finite coupling row. -/

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

/-- A triangular row needs weighted energy only from its strictly lower-depth sources. -/
theorem planeCouplingFluxRow_weighted_time_energy_ne_top_of_lower_depth
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)))
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (rank : ι → ℕ) (i : ι)
    (hz : ∀ i', ¬ rank i' < rank i → ∀ d t x, A i i' d t x = 0)
    (he : ∀ i', rank i' < rank i → (∫⁻ t in Set.Icc a b,
      storedChartFactorialEnergy ρ (fun x => q x ^ 2) (w i' t)) ≠ ⊤) :
    (∫⁻ t in Set.Icc a b, storedChartFactorialEnergy ρ (fun x => q x ^ 2)
      (planeCouplingFluxRow hab ρ hρ K D A hA hc w i t)) ≠ ⊤ := by
  let term (i' : ι) (d : admissibleOrders K D i i') (t : ℝ) :=
    planeCoupledFluxTerm ρ hρ K D a b i i' d (A i i' d) (hA i i' d)
      (clampPoint a b hab t) (clampPoint a b hab t).property
      (hc i i' d _ (clampPoint a b hab t).property) (w i' t)
  have hterm (i' : ι) (d : admissibleOrders K D i i') :
      MemLp (term i' d) 2 (volume.restrict (Set.Icc a b)) :=
    planeCoupledFluxTerm_memLp hab ρ hρ K D i i' d (A i i' d)
      (hA i i' d) (hc i i' d) (hAm i i' d) (w i') (hw i')
  have ht (i' : ι) (d : admissibleOrders K D i i') :
      (∫⁻ t in Set.Icc a b, storedChartFactorialEnergy ρ (fun x => q x ^ 2) (term i' d t)) ≠ ⊤ := by
    by_cases hlt : rank i' < rank i
    · exact planeCoupledFluxTerm_weighted_time_energy_ne_top hab ρ hρ K D i i' d
        (A i i' d) (hA i i' d) (hc i i' d) (w i') (hw i') q hq hq0 (he i' hlt)
    · have hzero (t : ℝ) : term i' d t = 0 := by
        apply planeMulCoefficient_eq_zero
        exact hz i' hlt d _
      simp only [hzero, storedChartFactorialEnergy, map_zero, chartScalarEnergy_zero,
        mul_zero, Finset.sum_const_zero, lintegral_zero, ne_eq, ENNReal.zero_ne_top,
        not_false_eq_true]
  change (∫⁻ t in Set.Icc a b, storedChartFactorialEnergy ρ (fun x => q x ^ 2)
    (∑ i', ∑ d : admissibleOrders K D i i', term i' d t)) ≠ ⊤
  apply integrated_stored_energy_finite_sum_ne_top ρ hρ q hq hq0
  · intro i'
    exact memLp_fintype_sum (term i') (hterm i')
  · intro i'
    exact integrated_stored_energy_finite_sum_ne_top ρ hρ q hq hq0 _
      (term i') (hterm i') (ht i')

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! A native raw forcing map vanishes when its literal source vanishes. -/

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [AddCommGroup X] [Module ℝ X]

theorem planeRaw_allMoment_map_eq_zero_of_ae
    (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ) (H : X → ℝ → Vec 2 → E)
    (T : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (hT : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ H T)
    (hH : ∀ x, ∀ᵐ t ∂μ, H x t =ᵐ[volume] (fun _ => 0)) : T = 0 := by
  ext x
  apply planeTimeAllMomentRepresents_zero K ϖ ρ zc μ (T x) (fun _ => 0)
  · apply planeRaw_allMoment_map_represents K ϖ ρ zc μ H T hT x (fun _ => 0)
    filter_upwards [hH x] with t ht
    exact (planeValue_zero_ae (E := E) K).trans ht.symm
  · exact Filter.Eventually.of_forall (fun _ => rfl)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Literal readouts identify native all-moment forcing maps without choosing pointwise time representatives. -/

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [AddCommGroup X] [Module ℝ X]

local instance rawMapUniquenessNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  allMomentTimeNativeNormed k

theorem planeRaw_allMoment_map_unique
    (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (H G : X → ℝ → Vec 2 → E)
    (T S : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (hT : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ H T)
    (hS : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ G S)
    (hHG : ∀ x, ∀ᵐ t ∂μ, H x t =ᵐ[volume] G x t) : T = S := by
  ext x
  have hrep : PlaneTimeAllMomentRepresents K ϖ ρ zc μ (T x)
      (fun t => planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (S x) t) := by
    apply planeRaw_allMoment_map_represents K ϖ ρ zc μ H T hT x
    filter_upwards [hS x, hHG x] with t hs he
    exact hs.trans he.symm
  exact planeTimeAllMomentRepresents_unique K ϖ ρ zc μ (T x) (S x) _ hrep
    (Filter.Eventually.of_forall (fun _ => rfl))

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The exact weighted production budget supplies the periodized trajectory and its L2 lift. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem exists_polynomialProduction_trace_lift
    (a b : ℝ) (u : ℝ → PlaneHk Set.univ K E) (w : ℝ → PlaneHk Set.univ (K + 1) E)
    (hu : ContinuousOn u (Set.Icc a b))
    (hw : MemLp w 2 (volume.restrict (Set.Icc a b)))
    (hlift : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), truncatePlaneHk (Nat.le_succ K) (w t) = u t)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t ∈ Set.Icc a b, weightedFactorialNormSq 4 ϖ z ρ K (u t) ≤ ENNReal.ofReal C)
    (hgrad : (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq 4 ϖ z ρ K (w t)) ≠ ⊤) :
    ∃ (U : ℝ → TorusHk K E) (W : ℝ → TorusHk (K + 1) E),
      ContinuousOn U (Set.Icc a b) ∧ MemLp W 2 (volume.restrict (Set.Icc a b)) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Icc a b)), truncateTorusHk (Nat.le_succ K) (W t) = U t) ∧
      (∀ t ∈ Set.Icc a b, ∀ α, (U t).val α =ᵐ[volume.restrict AVenhance.unitCube]
        periodizeRawJet (u t).toFunction.jet α) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Icc a b)), ∀ α, (W t).val α =ᵐ[volume.restrict AVenhance.unitCube]
        periodizeRawJet (w t).toFunction.jet α) := by
  have hbAE : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      weightedFactorialNormSq 4 ϖ z ρ K (u t) ≤ ENNReal.ofReal C :=
    (ae_restrict_mem measurableSet_Icc).mono (fun t ht => hb t ht)
  have he := polynomial_production_lift_energy_ne_top 4 ϖ z ρ hρ
    (volume.restrict (Set.Icc a b)) u w hw hlift C hbAE hgrad
  exact exists_polynomialCarrier_trace_lift a b u w hu hw hlift ϖ hϖ z ρ hρ C hC hb he

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A periodized family retains its actual global endpoint and almost-everywhere lift jets. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (K : ι → ℕ) (a b : ℝ)
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (U : ∀ i, ℝ → TorusHk (K i) (h i))
    (W : ∀ i, ℝ → TorusHk (K i + 1) (h i))

theorem periodizedFamily_trace_global_ae (hp : IsPeriodizedFamilyPair K a b u w U W)
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) (α : JetIndex2 (K i)) :
    (U i t).toFunction.jet α =ᵐ[volume] periodizeRawJet (u i t).toFunction.jet α :=
  periodizedCarrier_rawJet_ae (u i t) (U i t) α (hp.2.2.2.1 i t ht α)

theorem periodizedFamily_lift_global_ae (hp : IsPeriodizedFamilyPair K a b u w U W)
    (i : ι) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ α : JetIndex2 (K i + 1),
      (W i t).toFunction.jet α =ᵐ[volume] periodizeRawJet (w i t).toFunction.jet α := by
  filter_upwards [hp.2.2.2.2 i] with t ht
  intro α
  exact periodizedCarrier_rawJet_ae (w i t) (W i t) α (ht α)

end AVRegularity.CycleJointProofs
end
