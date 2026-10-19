-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PlaneJetMultiplierSuperposition
import AVRegularity.CycleJoint.PlaneWindowScalarDiffusion
public import AVRegularity.CycleJoint.PeriodizedCarrierRawReadout
public import AVRegularity.CycleJoint.InactiveTimeZeroFamilyPointwiseEnvelope
public import AVRegularity.Statements.Intermediate.CycleJoint.EdgeCoefficient
public import AVRegularity.EntryWeak.JointSourceCongruence
import AVRegularity.CycleWords.CellComplexH1Separability
import AVRegularity.CycleReference.TransitionTaylorBounds
public import AVRegularity.Statements.Intermediate.CycleJoint.JointOperator
public import AVRegularity.CycleReference.FluxFastDiscrepancy
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

section
/-! Compatibility import for the existing pointwise uniform molecular reserve. -/
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Dimension-independent spatial jet bounds for the native operator assembly. -/

section
variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem nativeArrayAssembly_jet_norm_le (r n : ℕ) (C : U →L[ℝ] V)
    (b : Vec 2 → Fin 2 → DerivativeWord2 r → ℝ)
    (hb : ∀ k A, ContDiff ℝ (n : ℕ) (fun x => b x k A)) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun y => nativeArrayAssembly r C (b y)) x‖ ≤
      ∑ k : Fin 2, ∑ A : DerivativeWord2 r,
        ‖C‖ * ‖iteratedFDeriv ℝ n (fun y => b y k A) x‖ := by
  classical
  let L := fun k A => (Weighted.fluxCoordinateInjection k C).comp
    (PiLp.proj 2 (fun _ : DerivativeWord2 r => U) A)
  have he : (fun y => nativeArrayAssembly r C (b y)) =
      (fun y => ∑ k : Fin 2, ∑ A : DerivativeWord2 r, b y k A • L k A) := by
    funext y
    exact nativeArrayAssembly_expansion r C (b y)
  rw [he]
  have hs k A : ContDiff ℝ (n : ℕ) (fun y => b y k A • L k A) :=
    (hb k A).smul contDiff_const
  apply (finite_jet_sum_norm_le _ n
    (fun k => ContDiff.sum (fun A _ => hs k A)) x).trans
  apply Finset.sum_le_sum
  intro k _
  apply (finite_jet_sum_norm_le _ n (hs k) x).trans
  apply Finset.sum_le_sum
  intro A _
  exact (scalar_fixed_vector_jet_norm_le _ n (hb k A) (L k A) x).trans
    (mul_le_mul_of_nonneg_right (native_coordinate_operator_norm_le r C k A) (norm_nonneg _))
end

/-! The real pointwise edge bound, with the original positive edge matrix. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem sampledEnvelope_edgeCoefficient_bound (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (actual : ∀ p, Ctx p)
    (t₀ t₁ ν e E ρ C : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (A : ι → ι → ℝ) (hA : ∀ v u, 0 ≤ A v u)
    (hfwd : IsSampledEnvelope F π K actual t₀ t₁ ν e E ρ C
      (fun v u => Real.sqrt (π u / π v) * A v u))
    (v u : ι) (d : admissibleOrders K D v u)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ t₁) (x : Vec 2) :
    ‖edgeCoefficient F ν e E actual K v u d t x‖ ≤
      C * (ν * ρ ^ (d.val - 2)) *
        ((K v).factorial : ℝ) / ((K v + d.val - 2).factorial : ℝ) * A v u := by
  have hw : 0 < Real.sqrt (π u / π v) := Real.sqrt_pos.2 (div_pos (hπ u) (hπ v))
  have hden : 0 < ν * ρ ^ (d.val - 2) := mul_pos hν (pow_pos hρ _)
  have hn : 0 < ((K v).factorial : ℝ) := by positivity
  have hf : 0 < ((K v + d.val - 2).factorial : ℝ) := by positivity
  have hb := sampledEnvelope_physicalCoefficient_normalized_bound F π K actual
    t₀ t₁ ν e E ρ C (fun v u => Real.sqrt (π u / π v) * A v u) hν hρ hfwd v u
    (mul_nonneg hC (mul_nonneg hw.le (hA v u))) d.val (Finset.mem_filter.mp d.property).1 t ht x
  have hbound := normalized_physical_budget (Real.sqrt (π u / π v))
    ‖physicalCoefficient F ν e E actual v u d.val t x‖ (ν * ρ ^ (d.val - 2))
    (((K v + d.val - 2).factorial : ℝ) / ((K v).factorial : ℝ)) C (A v u)
    hw hden (div_pos hf hn) hb
  change ‖physicalCoefficient F ν e E actual v u d.val t x‖ ≤ _
  convert hbound using 1
  field_simp [hn.ne', hf.ne']
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! All admissible source orders share one positive sampled-envelope budget. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem sampledEnvelope_admissible_edge_sum_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (actual : ∀ p, Ctx p)
    (a b ν e E ρ C : ℝ) (B : ι → ι → ℝ)
    (hs : IsSampledEnvelope F π K actual a b ν e E ρ C B) (v u : ι) :
    ENNReal.ofReal (Real.sqrt (π u / π v)) *
      (∑ d : admissibleOrders K D v u,
        coefficientSeminorm ρ (K v) a b (edgeCoefficient F ν e E actual K v u d) *
          (ENNReal.ofReal (ν * ρ ^ (d.1 - 2)))⁻¹ *
          ENNReal.ofReal (((K v + d.1 - 2).factorial : ℝ) / ((K v).factorial : ℝ))) ≤
      ENNReal.ofReal (C * B v u) := by
  classical
  let T := fun (γ : F.Γ v u) (d : ℕ) =>
    coefficientSeminorm ρ (K v) a b (constituentPhysical F ν e E actual v u γ d) *
      (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
      ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))
  apply le_trans _ (hs.2 v u)
  apply mul_le_mul_of_nonneg_left _ zero_le
  calc
    _ ≤ ∑ d : admissibleOrders K D v u, ∑ γ : F.Γ v u, T γ d.1 := by
      apply Finset.sum_le_sum
      intro d _
      have hcoef : coefficientSeminorm ρ (K v) a b (edgeCoefficient F ν e E actual K v u d) ≤
          ∑ γ : F.Γ v u, coefficientSeminorm ρ (K v) a b
            (constituentPhysical F ν e E actual v u γ d.1) :=
        coefficientSeminorm_sum_le Finset.univ
          (fun γ => constituentPhysical F ν e E actual v u γ d.1) ρ (K v) a b
          (fun γ _ t ht => hs.1 v u γ d.1 t ht)
      simpa only [T, Finset.sum_mul] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef zero_le) zero_le
    _ = ∑ γ : F.Γ v u, ∑ d : admissibleOrders K D v u, T γ d.1 := Finset.sum_comm
    _ ≤ ∑ γ : F.Γ v u, ∑ d ∈ Finset.Icc 2 D, T γ d := by
      apply Finset.sum_le_sum
      intro γ _
      rw [Finset.sum_coe_sort]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact (Finset.mem_filter.mp hd).1
      · intro d _ _
        exact zero_le
    _ = _ := rfl
end

/-! A sampled positive envelope makes every assembled edge seminorm finite. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

omit [Fintype ι] in
theorem sampledEnvelope_constituent_seminorm_ne_top (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (actual : ∀ p, Ctx p)
    (a b ν e E ρ C : ℝ) (_hν : 0 < ν) (_hρ : 0 < ρ) (B : ι → ι → ℝ)
    (hfwd : IsSampledEnvelope F π K actual a b ν e E ρ C B)
    (v u : ι) (γ : F.Γ v u) (d : ℕ) (hd : d ∈ Finset.Icc 2 D) :
    coefficientSeminorm ρ (K v) a b (constituentPhysical F ν e E actual v u γ d) ≠ ⊤ := by
  have hs := sampledEnvelope_order_budget F π K actual a b ν e E ρ C B hfwd v u d hd
  have hroot : ENNReal.ofReal (Real.sqrt (π u / π v)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (div_pos (hπ u) (hπ v)))).ne'
  have hinv : (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hfac : ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (div_pos (by positivity) (by positivity))).ne'
  have hh := (ENNReal.lt_top_of_mul_ne_top_right
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs) hroot).ne
  have hh' := (ENNReal.lt_top_of_mul_ne_top_left hh hfac).ne
  have hsum := (ENNReal.lt_top_of_mul_ne_top_left hh' hinv).ne
  exact ENNReal.sum_ne_top.mp hsum γ (Finset.mem_univ γ)

theorem sampledEnvelope_edge_seminorm_ne_top (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (actual : ∀ p, Ctx p)
    (a b ν e E ρ C : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (B : ι → ι → ℝ)
    (hfwd : IsSampledEnvelope F π K actual a b ν e E ρ C B)
    (v u : ι) (d : admissibleOrders K D v u) :
    coefficientSeminorm ρ (K v) a b (edgeCoefficient F ν e E actual K v u d) ≠ ⊤ := by
  exact coefficientSeminorm_sum_ne_top Finset.univ
    (fun γ => constituentPhysical F ν e E actual v u γ d.val) ρ (K v) a b
    (fun γ _ t ht => hfwd.1 v u γ d.val t ht)
    (fun γ _ => sampledEnvelope_constituent_seminorm_ne_top F π hπ K actual
      a b ν e E ρ C hν hρ B hfwd v u γ d.val (Finset.mem_filter.mp d.property).1)
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.EntryWeakProofs AVenhance.Infra.Classical
namespace AVRegularity.CycleJointProofs

/-! Constant vectors as genuine periodic Sobolev carriers at every finite order. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def torusConstantRawJet (K : ℕ) (c : E) : RawJet2 K E :=
  mapRawJet ((ContinuousLinearMap.id ℝ ℝ).smulRight c)
    (classicalFiniteJet K (fun _ => 1))

omit [MeasurableSpace E] [BorelSpace E] in
theorem torusConstantRawJet_hasPeriodicWeakJet (K : ℕ) (c : E) :
    HasPeriodicOrderedWeakJet (torusConstantRawJet K c) :=
  mapRawJet_hasPeriodicWeakJet _ _
    (classicalFiniteJet_periodicWeak K (fun _ => 1) contDiff_const (fun _ _ => rfl))

def torusConstantCarrier (K : ℕ) (c : E) : TorusHk K E :=
  TorusHkFunction.toHk ⟨torusConstantRawJet K c, torusConstantRawJet_hasPeriodicWeakJet K c⟩

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem torusConstantRawJet_value (K : ℕ) (c : E) (x : Vec 2) :
    torusConstantRawJet K c (valueIndex2 K) x = c := by
  simp only [torusConstantRawJet, mapRawJet, classicalFiniteJet, valueIndex2, valueIndex,
    Fin.val_zero, smoothLiftWord, classicalWordDerivative, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, one_smul]

theorem classicalWordDerivative_constant_succ (n : ℕ) (w : DerivativeWord2 (n + 1)) :
    classicalWordDerivative (smoothLiftWord (n + 1) w) (fun _ => (1 : ℝ)) = 0 := by
  induction n with
  | zero =>
    simp only [smoothLiftWord, classicalWordDerivative, AVenhance.spaceGrad,
      fderiv_const_apply, zero_apply]
    rfl
  | succ n ih =>
    rw [smoothLiftWord, classicalWordDerivative, ih]
    funext x
    change fderiv ℝ (fun _ : Vec 2 => (0 : ℝ)) x (basisVec _) = 0
    rw [fderiv_const_apply]
    rfl

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem torusConstantRawJet_positive (K : ℕ) (c : E) (a : JetIndex2 K) (ha : 0 < a.1.val)
    (x : Vec 2) : torusConstantRawJet K c a x = 0 := by
  obtain ⟨⟨n, hn⟩, w⟩ := a
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  simp only [torusConstantRawJet, mapRawJet, classicalFiniteJet,
    classicalWordDerivative_constant_succ, Pi.zero_apply, map_zero]

theorem torusConstantCarrier_jet_ae (K : ℕ) (c : E) (a : JetIndex2 K) :
    (torusConstantCarrier K c).val a =ᵐ[volume.restrict AVenhance.unitCube]
      torusConstantRawJet K c a :=
  torusJetToL2_ae _ (torusConstantRawJet_hasPeriodicWeakJet K c).2.1 a

variable [FiniteDimensional ℝ E]

theorem torusConstantCarrier_truncate (K L : ℕ) (hKL : K ≤ L) (c : E) :
    truncateTorusHk hKL (torusConstantCarrier L c) = torusConstantCarrier K c := by
  apply TorusHk.ext_value
  apply Lp.ext
  have ht := torusConstantCarrier_jet_ae L c (valueIndex2 L)
  have hs := torusConstantCarrier_jet_ae K c (valueIndex2 K)
  filter_upwards [ht, hs] with x hx hy
  change (torusConstantCarrier L c).val (valueIndex2 L) x = _
  rw [hx, hy, torusConstantRawJet_value, torusConstantRawJet_value]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The transition jet majorant retains every power spent in native order lowering. -/

theorem transitionT_scaled_jet_bound
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (N : ℕ) (C E : ℝ) (hC : 0 ≤ C) (hE : 0 < E)
    (hKC : ∀ a b j, j ≤ N → ∀ x,
      E ^ j * ‖iteratedFDeriv ℝ j (fun y => K y a b) x‖ ≤ C)
    (I A : List (Fin 2)) (n : ℕ) (hn : n + I.length ≤ N) (x : Vec 2) :
    E ^ ((n : ℤ) + (I.length : ℤ) - (A.length : ℤ)) *
      ‖iteratedFDeriv ℝ n (transitionT K I A) x‖ ≤
        (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ I.length := by
  let KE := fun y : Vec 2 => K (E • y)
  have hKE : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun y => KE y i j) :=
    fun i j => (hK i j).comp (contDiff_id.const_smul E)
  have hKEC : ∀ a b j, j ≤ N → ∀ y,
      ‖iteratedFDeriv ℝ j (fun z => KE z a b) y‖ ≤ C := by
    intro a b j hj y
    have he := AVRegularity.CycleWords.normalizedJet_rescaling_eq j
      ((hK a b).of_le (by simp)) 1 E y
    simp only [one_pow, one_mul, abs_of_pos hE] at he
    rw [he]
    exact hKC a b j hj (E • y)
  have hm := transitionT_uniform_jet_bound KE hKE N C hC hKEC I A n hn (E⁻¹ • x)
  have hT := transitionT_spatial_smooth K hK I A
  have heq : transitionT KE I A =
      (fun y => E ^ ((I.length : ℤ) - (A.length : ℤ)) * transitionT K I A (E • y)) :=
    funext (transitionT_spatial_rescaling K hK E hE I A)
  have hc : ContDiff ℝ (n : ℕ) (fun y : Vec 2 => transitionT K I A (E • y)) :=
    (hT.of_le (by simp)).comp (contDiff_id.const_smul E)
  rw [heq] at hm
  change ‖iteratedFDeriv ℝ n (fun y =>
    E ^ ((I.length : ℤ) - (A.length : ℤ)) • transitionT K I A (E • y)) (E⁻¹ • x)‖ ≤ _ at hm
  rw [iteratedFDeriv_const_smul_apply' hc.contDiffAt, norm_smul, Real.norm_eq_abs,
    abs_of_pos (zpow_pos hE _)] at hm
  have hs := AVRegularity.CycleWords.normalizedJet_rescaling_eq n
    (hT.of_le (by simp)) 1 E (E⁻¹ • x)
  simp only [one_pow, one_mul, abs_of_pos hE, smul_smul, mul_inv_cancel₀ hE.ne', one_smul] at hs
  rw [hs] at hm
  have hp : E ^ ((I.length : ℤ) - (A.length : ℤ)) * E ^ n =
      E ^ ((n : ℤ) + (I.length : ℤ) - (A.length : ℤ)) := by
    rw [← zpow_natCast E n, ← zpow_add₀ hE.ne']
    congr 1
    ring
  rw [← mul_assoc, hp] at hm
  exact hm

/-! A uniform operator jet budget controls the entire factorial-normalized coefficient seminorm. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem uniform_pointwise_coefficient_seminorm (ρ : ℝ) (hρ : 0 < ρ)
    (K Kmax : ℕ) (hK : K ≤ Kmax) (a b : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hA : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A t))
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ t ∈ Set.Icc a b, ∀ j, j ≤ K → ∀ x,
      ρ ^ j * ‖iteratedFDeriv ℝ j (A t) x‖ ≤ B) :
    coefficientSeminorm ρ K a b A ≤
      ENNReal.ofReal (((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) * B) := by
  have hh := pointwise_coefficient_seminorm_budget ρ hρ K a b A hA
    (fun _ => B) (fun _ => hB) hb
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have he : (∑ j ∈ Finset.range (K + 1), (2 : ℝ) ^ j * B / (j.factorial : ℝ)) =
      (∑ j ∈ Finset.range (K + 1), (2 : ℝ) ^ j / (j.factorial : ℝ)) * B := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (finite_jet_seminorm_constant K Kmax hK) hB
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Scalar cell coefficient jets retain the original molecular price under arbitrary fast phase. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem familyPointwiseMolecular_scalar_mixed_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (j : ℕ) (hj : j ≤ J) (p : P) (c : Ctx p) :
    ∀ t : ℝ, (∀ Y : Vec 2, (t, Y) ∈ dom p c) →
      ∀ (φ : Vec 2) (k : Fin 2) (a b : ℕ), a + b ≤ K v → ∀ X z,
      (ρ / e) ^ (a + b) * |e / E| ^ a *
        ‖iteratedFDeriv ℝ (j + a) (fun X' => iteratedFDeriv ℝ b
          (fun z' => F.flux p c v u γ d I t X' (z' + φ) k) z) X‖ ≤
        (Kmax.factorial : ℝ) ^ 2 * E ^ j *
          molecularRealPrice ν ρ (K v) (d - 2)
            (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
              (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) /
                derivativeReserveFactor (ρ / e) (K v) (d - 2) := by
  intro t hdom φ k a b hab X z
  have ht := familyPointwiseMolecular_uniform_reserve F π hπ K Kmax hK dom ν e E ρ
    hν he hE hρ C J b₀ henv v u γ hγ d hd I j hj p c t
  have hf : IsBoxSmooth (j + a) b (F.flux p c v u γ d I t) := by
    apply Weighted.isBoxSmooth_of_joint_contDiff
    have hh := molecular_joint_contDiff F dom E hE.ne' (fun v => K v + J)
      henv.1 p c t hdom v u γ d I
    exact hh.of_le (by exact_mod_cast (by omega : j + a + b ≤ K v + J))
  have hc := mixedJet_fast_shift_coordinate_norm_le (F.flux p c v u γ d I t) hf φ k X z
  have hR : 0 < derivativeReserveFactor (ρ / e) (K v) (d - 2) := by
    unfold derivativeReserveFactor
    positivity
  apply (le_div_iff₀ hR).mpr
  have hn := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc
      (mul_nonneg (pow_nonneg (div_pos hρ he).le (a + b))
        (pow_nonneg (abs_nonneg (e / E)) a))) hR.le
  exact hn.trans (by simpa only [abs_of_pos (div_pos he hE)] using ht hdom a b hab X (z + φ))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Frozen metric insertions have a fibre-dimension independent operator smallness bound. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

theorem metricFlux_norm_le_four_entries {a b : ι} (M : Matrix (Fin 2) (Fin 2) ℝ)
    (m : ℕ) (hab : a = b) (hm : m = 1) (g : ℝ) (hg : 0 ≤ g)
    (hM : ∀ i j, |M i j| ≤ g) :
    ‖metricFlux (h := h) M m hab hm‖ ≤ 4 * g := by
  rw [metricFlux_entry_expansion]
  exact fourEntry_smul_sum_norm_le M (metricWordEntry (h := h) m hab hm) g hg hM
    (fun i j => metricWordEntry_norm_le_one m hab hm i j)

theorem metricFlux_near_identity_norm_le {a b : ι} (M : Matrix (Fin 2) (Fin 2) ℝ)
    (m : ℕ) (hab : a = b) (hm : m = 1) (g : ℝ) (hg : 0 ≤ g) (hsym : M.IsSymm)
    (hquad : ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (M - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        g * ∑ i, ξ i ^ 2) :
    ‖metricFlux (h := h) (M - 1) m hab hm‖ ≤ 4 * g :=
  metricFlux_norm_le_four_entries (M - 1) m hab hm g hg
    (symmetricMetric_difference_entry_abs_le M g hsym hquad)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Every positive raw derivative of a constant Sobolev carrier vanishes. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torusConstantCarrier_raw_value_ae (K : ℕ) (c : E) :
    (torusConstantCarrier K c).toFunction.jet (valueIndex2 K)
      =ᵐ[volume.restrict AVenhance.unitCube] fun _ => c := by
  filter_upwards [periodicJetRepresentative_ae (torusConstantCarrier K c).val (valueIndex2 K),
    torusConstantCarrier_jet_ae K c (valueIndex2 K)] with x hx hy
  exact hx.trans (hy.trans (torusConstantRawJet_value K c x))

theorem torusConstantCarrier_positive_jet_zero (K : ℕ) (c : E)
    (a : JetIndex2 K) (ha : 0 < a.1.val) : (torusConstantCarrier K c).val a = 0 := by
  apply Lp.ext
  filter_upwards [torusConstantCarrier_jet_ae K c a,
    Lp.coeFn_zero E 2 (volume.restrict AVenhance.unitCube)] with x hx hz
  exact hx.trans ((torusConstantRawJet_positive K c a ha x).trans hz.symm)

theorem torusConstantCarrier_raw_positive_ae (K : ℕ) (c : E)
    (a : JetIndex2 K) (ha : 0 < a.1.val) :
    (torusConstantCarrier K c).toFunction.jet a
      =ᵐ[volume.restrict AVenhance.unitCube] fun _ => 0 := by
  have he := periodicJetRepresentative_ae (torusConstantCarrier K c).val a
  rw [torusConstantCarrier_positive_jet_zero K c a ha] at he
  exact he.trans (Lp.coeFn_zero E 2 (volume.restrict AVenhance.unitCube))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs

/-! Literal centres and native chart windows of the preparation cover, including its two padding charts. -/

def windowCoverChartCentre (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2) (i : Fin (P + 2)) : Vec 2 :=
  ocCellCentre α q Λ m φ hφ (l₀ - 1)
    (ocTransition α q Λ m φ hφ (l₀ - 1) l₀ y₀) i

def windowCoverChartWindow (α q : ℝ) (Λ m : ℕ) (ν tA tZ : ℝ) (l₀ : ℤ)
    (P : ℕ) (i : Fin (P + 2)) : Set ℝ :=
  Set.Icc (max tA ((((l₀ - 1 + i : ℤ) : ℝ) - 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
    (min tZ ((((l₀ - 1 + i : ℤ) : ℝ) + 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The positive spatial cutoffs define actual compact localization operators. -/

theorem spatialPatchCutoff_compact {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (k : Fin 2 → ℤ) :
    HasCompactSupport (spatialPatchCutoff ζ N k) := by
  apply HasCompactSupport.intro
    (isCompact_closedBall (spatialPatchCentre N k) ((2 / 3 : ℝ) / N))
  intro x hx
  by_contra hn
  exact hx (Metric.mem_closedBall.mpr (by
    rw [dist_eq_norm]
    exact spatialPatchCutoff_support_radius hζ N hN k x hn))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

def spatialPatchCoefficient (ζ : ℝ → ℝ) (N : ℕ) (k : Fin 2 → ℤ) :
    Vec 2 → E →L[ℝ] E := fun x => spatialPatchCutoff ζ N k x • ContinuousLinearMap.id ℝ E

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem spatialPatchCoefficient_smooth {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (k : Fin 2 → ℤ) (K : ℕ) :
    ContDiff ℝ (K : ℕ) (spatialPatchCoefficient (E := E) ζ N k) := by
  exact ((spatialPatchCutoff_smooth hζ N k).of_le (by simp)).smul contDiff_const

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem spatialPatchCoefficient_compact {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (k : Fin 2 → ℤ) :
    HasCompactSupport (spatialPatchCoefficient (E := E) ζ N k) := by
  exact (spatialPatchCutoff_compact hζ N hN k).smul_right
    (f' := fun _ => ContinuousLinearMap.id ℝ E)

def spatialPatchLocalization {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (k : Fin 2 → ℤ) (K : ℕ) :
    TorusHk K E →ₗ[ℝ] PlaneHk Set.univ K E :=
  localizeTorusLinear (spatialPatchCoefficient ζ N k)
    (spatialPatchCoefficient_smooth hζ N k K) (spatialPatchCoefficient_compact hζ N hN k)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A constant value trace identifies the entire genuine periodic Sobolev carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torusConstantCarrier_eq_of_raw_value (K : ℕ) (f : TorusHk K E) (c : E)
    (hf : f.toFunction.jet (valueIndex2 K)
      =ᵐ[volume.restrict AVenhance.unitCube] fun _ => c) :
    f = torusConstantCarrier K c := by
  apply TorusHk.ext_value
  apply Lp.ext
  filter_upwards [periodicJetRepresentative_ae f.val (valueIndex2 K), hf,
    torusConstantCarrier_jet_ae K c (valueIndex2 K)] with x hx hc hk
  exact hx.symm.trans (hc.trans ((torusConstantRawJet_value K c x).symm.trans hk.symm))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Native transition factors spend their order-lowering scale before molecular radius reduction. -/

theorem transitionT_molecular_jet_bound
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (N : ℕ) (C E ρ : ℝ) (hC : 0 ≤ C) (hE : 0 < E)
    (hρ : 0 ≤ ρ) (hρE : ρ ≤ E)
    (hKC : ∀ a b j, j ≤ N → ∀ x,
      E ^ j * ‖iteratedFDeriv ℝ j (fun y => K y a b) x‖ ≤ C)
    (I A : List (Fin 2)) (hA : A.length ≤ I.length)
    (n : ℕ) (hn : n + I.length ≤ N) (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (transitionT K I A) x‖ ≤
      (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ I.length * E⁻¹ ^ (I.length - A.length) := by
  have hh := transitionT_scaled_jet_bound K hK N C E hC hE hKC I A n hn x
  have he : (n : ℤ) + (I.length : ℤ) - (A.length : ℤ) =
      ((n + (I.length - A.length) : ℕ) : ℤ) := by omega
  rw [he, zpow_natCast] at hh
  exact radius_lowering_bound E ρ _ _ n (I.length - A.length) hE hρ hρE
    (by positivity) hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Analysis.Convolution
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Actual native plane value representatives have integrable pairings and their literal L2 readout. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHk_rawValuePairing_integrable {K J : ℕ}
    (U : PlaneHk Set.univ K E) (V : PlaneHk Set.univ J E) :
    Integrable (fun x => inner ℝ (U.toFunction.jet (valueIndex2 K) x)
      (V.toFunction.jet (valueIndex2 J) x)) volume := by
  apply (L2.integrable_inner (planeHkValueOperator K U) (planeHkValueOperator J V)).congr
  filter_upwards [univToPlane_ae (U.val (valueIndex2 K)),
    univToPlane_ae (V.val (valueIndex2 J))] with x hu hv
  change inner ℝ (univToPlane (U.val (valueIndex2 K)) x)
    (univToPlane (V.val (valueIndex2 J)) x) = _
  rw [hu, hv]
  rfl

theorem planeHk_rawValuePairing {K J : ℕ}
    (U : PlaneHk Set.univ K E) (V : PlaneHk Set.univ J E) :
    inner ℝ (planeHkValueOperator K U) (planeHkValueOperator J V) =
      ∫ x, inner ℝ (U.toFunction.jet (valueIndex2 K) x)
        (V.toFunction.jet (valueIndex2 J) x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [univToPlane_ae (U.val (valueIndex2 K)),
    univToPlane_ae (V.val (valueIndex2 J))] with x hu hv
  change inner ℝ (univToPlane (U.val (valueIndex2 K)) x)
    (univToPlane (V.val (valueIndex2 J)) x) = _
  rw [hu, hv]
  rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The sampled positive constituent budget bounds the full mass-weighted Schur matrix once. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem sampledEnvelope_schurMatrix_le (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (actual : ∀ p, Ctx p)
    (a b ν e E ρ C : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (B : ι → ι → ℝ)
    (hs : IsSampledEnvelope F π K actual a b ν e E ρ C B)
    (v u : ι) (hCb : 0 ≤ C * B v u) :
    schurMatrix ν ρ π K D a b (edgeCoefficient F ν e E actual K) v u ≤ C * B v u := by
  classical
  have hden (d : admissibleOrders K D v u) : 0 < ν * ρ ^ (d.1 - 2) :=
    mul_pos hν (pow_pos hρ _)
  have hfac (d : admissibleOrders K D v u) :
      0 ≤ ((K v + d.1 - 2).factorial : ℝ) / ((K v).factorial : ℝ) := by positivity
  have hfinite (d : admissibleOrders K D v u) :
      coefficientSeminorm ρ (K v) a b (edgeCoefficient F ν e E actual K v u d) *
        (ENNReal.ofReal (ν * ρ ^ (d.1 - 2)))⁻¹ *
        ENNReal.ofReal (((K v + d.1 - 2).factorial : ℝ) / ((K v).factorial : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (sampledEnvelope_edge_seminorm_ne_top F π hπ K actual a b ν e E ρ C hν hρ B hs v u d)
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (hden d)).ne')) ENNReal.ofReal_ne_top
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (sampledEnvelope_admissible_edge_sum_budget F π K actual a b ν e E ρ C B hs v u)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_sum (fun d _ => hfinite d), ENNReal.toReal_ofReal hCb] at hh
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (hden _).le, ENNReal.toReal_ofReal (hfac _)] at hh
  simpa only [schurMatrix, div_eq_mul_inv] using hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! A single compact reference cutoff controls every mesh and patch derivative. -/

theorem spatialPatchCutoff_iteratedFDeriv_scale {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N j : ℕ) (k : Fin 2 → ℤ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (spatialPatchCutoff ζ N k) x‖ = (N : ℝ) ^ j *
      ‖iteratedFDeriv ℝ j (spatialPatchCutoff ζ 1 0)
        ((N : ℝ) • x - AVenhance.latticeShift k)‖ := by
  let g : Vec 2 → ℝ := fun y => spatialPatchCutoff ζ 1 0 (y - AVenhance.latticeShift k)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    (spatialPatchCutoff_smooth hζ 1 0).comp (contDiff_id.sub contDiff_const)
  have he : spatialPatchCutoff ζ N k = fun y => g ((N : ℝ) • y) := by
    funext y
    simp only [spatialPatchCutoff, g, Nat.cast_one, one_mul, Pi.zero_apply, Int.cast_zero,
      sub_zero, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, AVenhance.latticeShift]
  rw [he, congrFun (iteratedFDeriv_comp_const_smul (N : ℝ)
      (hg.of_le (by simp) : ContDiff ℝ (j : ℕ∞) g)) x, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg N) j)]
  dsimp only [g]
  rw [iteratedFDeriv_comp_sub]

theorem spatialPatchCutoff_derivatives_uniform {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (K : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N j : ℕ, j ≤ K → ∀ (k : Fin 2 → ℤ) x,
      ‖iteratedFDeriv ℝ j (spatialPatchCutoff ζ N k) x‖ ≤ C * (N : ℝ) ^ j := by
  have hc := spatialPatchCutoff_compact hζ 1 (by norm_num) 0
  obtain ⟨C, hC, hb⟩ := hc.exists_bound_iteratedFDeriv
    (spatialPatchCutoff_smooth hζ 1 0) K
  refine ⟨C, hC, ?_⟩
  intro N j hj k x
  rw [spatialPatchCutoff_iteratedFDeriv_scale hζ]
  simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (hb j hj _)
    (pow_nonneg (Nat.cast_nonneg N) j)

end AVRegularity.CycleJointProofs
end
end

section
public section
open Homogenization AVenhance AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Explicit spatial slices of the jointly smooth inverse chart Jacobian. -/

theorem chartJac_inverse_entry_continuous_slice {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (i j : Fin 2) :
    Continuous (fun y : Vec 2 => (chartJac hφ s t y)⁻¹ i j) := by
  have hg : Continuous (fun y : Vec 2 => (t, y)) := continuous_const.prodMk continuous_id
  have hc := (chartJac_inverse_entry_smooth hφ s i j).continuous.comp hg
  exact hc

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization AVenhance AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Joint smoothness of every entry of the actual material chart metric. -/

theorem chartMetric_entry_smooth {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => chartMetric hφ s p.1 p.2 i j) := by
  have he : (fun p : ℝ × Vec 2 => chartMetric hφ s p.1 p.2 i j) =
      (fun p => (chartJac hφ s p.1 p.2)⁻¹ i 0 * (chartJac hφ s p.1 p.2)⁻¹ j 0 +
        (chartJac hφ s p.1 p.2)⁻¹ i 1 * (chartJac hφ s p.1 p.2)⁻¹ j 1) := by
    funext p
    simp only [chartMetric, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  rw [he]
  exact ((chartJac_inverse_entry_smooth hφ s i 0).mul
    (chartJac_inverse_entry_smooth hφ s j 0)).add
    ((chartJac_inverse_entry_smooth hφ s i 1).mul (chartJac_inverse_entry_smooth hφ s j 1))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! The native order-one plane norm is exactly the sum of value and gradient squares. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1_normSq_eq_value_gradient (u : PlaneHk univ 1 E) :
    ‖u‖ ^ 2 = ‖planeHkValueOperator 1 u‖ ^ 2 + ‖planeH1GradientOperator u‖ ^ 2 := by
  let : Unique (DerivativeWord2 0) :=
    { default := Fin.elim0, uniq := fun w => funext (fun z => Fin.elim0 z) }
  have h0 : derivativeNormSq u.val (0 : Fin 2) = ‖u.val (valueIndex2 1)‖ ^ 2 := by
    change (∑ w : DerivativeWord2 0, ‖u.val ⟨0, w⟩‖ ^ 2) = _
    rw [Fintype.sum_unique]
    rfl
  have h1 : derivativeNormSq u.val (1 : Fin 2) =
      ∑ k : Fin 2, ‖u.val ⟨⟨1, by omega⟩, fun _ => k⟩‖ ^ 2 := by
    change (∑ w : DerivativeWord2 1, ‖u.val ⟨1, w⟩‖ ^ 2) = _
    apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2))
    intro w
    have hw : w = (fun _ => w 0) := funext (fun z => congrArg w (Subsingleton.elim z 0))
    change ‖u.val ⟨1, w⟩‖ ^ 2 = ‖u.val ⟨1, fun _ => w 0⟩‖ ^ 2
    rw [hw]
    rfl
  change ‖u.val‖ ^ 2 = _
  rw [jet_norm_sq_eq_sum, Fin.sum_univ_two, h0, h1, planeHkValueOperator_apply,
    univToPlane.norm_map, PiLp.norm_sq_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [planeH1GradientOperator_apply, univToPlane.norm_map]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Every cutoff coefficient derivative remains in the original mesh patch. -/

theorem spatialPatchCutoff_tsupport_coordinate {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (k : Fin 2 → ℤ) (x : Vec 2) (hx : x ∈ tsupport (spatialPatchCutoff ζ N k))
    (i : Fin 2) : |(N : ℝ) * x i - k i| ≤ 2 / 3 := by
  have hs : Function.support (spatialPatchCutoff ζ N k) ⊆
      {y : Vec 2 | |(N : ℝ) * y i - k i| ≤ 2 / 3} := by
    intro y hy
    exact (spatialPatchCutoff_coordinate_support hζ N k y hy i).le
  have hc : IsClosed {y : Vec 2 | |(N : ℝ) * y i - k i| ≤ 2 / 3} :=
    isClosed_le (by fun_prop) continuous_const
  exact closure_minimal hs hc hx

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 theorem spatialPatchCoefficient_array_support {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N j : ℕ) (k : Fin 2 → ℤ) (x : Vec 2)
    (hn : coefficientDerivativeArray (spatialPatchCoefficient (E := E) ζ N k) j x ≠ 0)
    (i : Fin 2) : |(N : ℝ) * x i - k i| ≤ 2 / 3 := by
  have hx : x ∈ tsupport (spatialPatchCoefficient (E := E) ζ N k) := by
    by_contra hx
    exact hn (coefficientDerivativeArray_zero_of_not_tsupport _ j x hx)
  have hs : tsupport (spatialPatchCoefficient (E := E) ζ N k) ⊆
      tsupport (spatialPatchCutoff ζ N k) :=
    tsupport_smul_subset_left _ (fun _ => ContinuousLinearMap.id ℝ E)
  exact spatialPatchCutoff_tsupport_coordinate hζ N k x (hs hx) i

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The localized H1 torus test has the actual scalar cutoff product-rule gradient. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem spatialPatchCoefficient_derivative {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (j : Fin 2 → ℤ) (x v : Vec 2) (z : E) :
    fderiv ℝ (spatialPatchCoefficient (E := E) ζ N j) x v z =
      fderiv ℝ (spatialPatchCutoff ζ N j) x v • z := by
  unfold spatialPatchCoefficient
  have he := fderiv_smul_const (𝕜 := ℝ)
    ((spatialPatchCutoff_smooth hζ N j).differentiable (by simp) x)
    (ContinuousLinearMap.id ℝ E)
  exact congrArg (fun L : Vec 2 →L[ℝ] E →L[ℝ] E => L v z) he

theorem spatialPatchLocalization_value_ae {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → ℤ) (φ : TorusHk 1 E) :
    (spatialPatchLocalization hζ N hN j 1 φ).toFunction.jet (valueIndex2 1) =ᵐ[volume]
      fun x => spatialPatchCutoff ζ N j x • φ.toFunction.jet (valueIndex2 1) x := by
  exact localizeTorusCarrier_value_ae φ _ _ _

theorem spatialPatchLocalization_gradient_ae {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → ℤ) (φ : TorusHk 1 E) (k : Fin 2) :
    (spatialPatchLocalization hζ N hN j 1 φ).toFunction.jet
      ⟨⟨1, by decide⟩, fun _ => k⟩ =ᵐ[volume]
      fun x => fderiv ℝ (spatialPatchCutoff ζ N j) x (basisVec k) •
          φ.toFunction.jet (valueIndex2 1) x +
        spatialPatchCutoff ζ N j x • φ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩ x := by
  filter_upwards [localizeTorusCarrier_jet_ae φ (spatialPatchCoefficient ζ N j)
    (spatialPatchCoefficient_smooth hζ N j 1) (spatialPatchCoefficient_compact hζ N hN j)
    ⟨⟨1, by decide⟩, fun _ => k⟩] with x hx
  change (localizeTorusCarrier φ (spatialPatchCoefficient ζ N j)
    (spatialPatchCoefficient_smooth hζ N j 1) (spatialPatchCoefficient_compact hζ N hN j)).toFunction.jet
      ⟨⟨1, by decide⟩, fun _ => k⟩ x = _
  rw [hx, multiplicationRawJet_first, spatialPatchCoefficient_derivative hζ]
  exact add_comm _ _

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Diagonal normalization and annihilation by each positive source block fix every constant vector. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusJointOperator_fixes_constants (K : ι → ℕ) (Mout H : ℕ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (hd : ∀ v c, Pd v (torusConstantCarrier 0 c) = torusConstantCarrier (max Mout (K v)) c)
    (hg : ∀ n, 1 ≤ n → n ≤ H → ∀ v u c, Pg n v u (torusConstantCarrier 0 c) = 0)
    (f : ∀ u, TorusHk 0 (h u)) (c : ∀ v, h v)
    (hf : ∀ v, (f v).toFunction.jet (valueIndex2 0)
      =ᵐ[volume.restrict AVenhance.unitCube] fun _ => c v) (v : ι) :
    (jointOperator K Mout H Pd Pg f v).toFunction.jet (valueIndex2 (max Mout (K v)))
      =ᵐ[volume.restrict AVenhance.unitCube] fun _ => c v := by
  have he (u : ι) : f u = torusConstantCarrier 0 (c u) :=
    torusConstantCarrier_eq_of_raw_value 0 (f u) (c u) (hf u)
  have hz : (∑ n ∈ Finset.Icc 1 H, ∑ u, Pg n v u (f u)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    apply Finset.sum_eq_zero
    intro u _
    rw [he, hg n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2]
  have hj : jointOperator K Mout H Pd Pg f v = torusConstantCarrier (max Mout (K v)) (c v) := by
    rw [jointOperator, hz, add_zero, he, hd]
  rw [hj]
  exact torusConstantCarrier_raw_value_ae _ _

end AVRegularity.CycleJointProofs
end
end

section
public section
namespace AVRegularity.CycleJointProofs

/-! In two dimensions, determinant-one inverse entries have the same entry bound. -/

theorem unitDet_inverse_entry_bound (J : Matrix (Fin 2) (Fin 2) ℝ) (hJ : J.det = 1)
    (C : ℝ) (hb : ∀ i j, |J i j| ≤ C) (i j : Fin 2) : |J⁻¹ i j| ≤ C := by
  fin_cases i <;> fin_cases j
  · simpa [Matrix.inv_def, hJ, Matrix.adjugate_fin_two] using hb 1 1
  · simpa [Matrix.inv_def, hJ, Matrix.adjugate_fin_two, abs_neg] using hb 0 1
  · simpa [Matrix.inv_def, hJ, Matrix.adjugate_fin_two, abs_neg] using hb 1 0
  · simpa [Matrix.inv_def, hJ, Matrix.adjugate_fin_two] using hb 0 0

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The spatially frozen metric keeps its small coefficient price at every finite native reserve. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

theorem frozenMetric_coefficientSeminorm_le {u v : ι}
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (r : ℕ) (huv : u = v) (hr : r = 1)
    (ρ : ℝ) (K : ℕ) (a b g : ℝ) (hg : 0 ≤ g)
    (hsym : ∀ t ∈ Set.Icc a b, (M t).IsSymm)
    (hquad : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (M t - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        g * ∑ i, ξ i ^ 2) :
    coefficientSeminorm ρ K a b (fun t _ => metricFlux (h := h) (M t - 1) r huv hr) ≤
      ENNReal.ofReal (4 * g) :=
  coefficientSeminorm_spatial_const_le ρ K a b
    (fun t => metricFlux (h := h) (M t - 1) r huv hr) (4 * g)
    (fun t ht => metricFlux_near_identity_norm_le (M t) r huv hr g hg (hsym t ht) (hquad t ht))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A positive, radius-normalized bound for one exact native Piola/order-lowering summand. -/

theorem native_piola_summand_molecular_jet_bound
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (N : ℕ) (C E ρ : ℝ) (hC : 0 ≤ C) (hE : 0 < E)
    (hρ : 0 ≤ ρ) (hρE : ρ ≤ E)
    (hKC : ∀ a b j, j ≤ N → ∀ x,
      E ^ j * ‖iteratedFDeriv ℝ j (fun y => K y a b) x‖ ≤ C)
    (I A : List (Fin 2)) (hA : A.length ≤ I.length)
    (n : ℕ) (hn : n + I.length ≤ N)
    (B : Vec 2 → ℝ) (hB : ContDiff ℝ (n : ℕ) B) (MB : ℝ)
    (hBj : ∀ j, j ≤ n → ∀ y, ρ ^ j * ‖iteratedFDeriv ℝ j B y‖ ≤ MB)
    (a i : Fin 2) (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => K y a i * B y * transitionT K I A y) x‖ ≤
      ((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C * MB *
        ((3 * (N + 1 : ℕ) * 2 ^ N * C) ^ I.length * E⁻¹ ^ (I.length - A.length)) := by
  have hnn : n ≤ N := by omega
  apply triple_product_weighted_jet_bound _ _ _ x n
    ((hK a i).of_le (by simp)) hB
    ((transitionT_spatial_smooth K hK I A).of_le (by simp)) ρ C MB _ hρ
  · intro j hj
    have hh := hKC a i j (hj.trans hnn) x
    have hb := radius_lowering_bound E ρ C _ j 0 hE hρ hρE hC
      (by simpa only [Nat.add_zero] using hh)
    simpa only [pow_zero, mul_one] using hb
  · intro j hj
    exact hBj j hj x
  · intro j hj
    exact transitionT_molecular_jet_bound K hK N C E ρ hC hE hρ hρE hKC I A hA
      j (by omega) x

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! The native plane H1 norm controls its value and gradient and is controlled by their sum. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1_norm_le_value_add_gradient (u : PlaneHk univ 1 E) :
    ‖u‖ ≤ ‖planeHkValueOperator 1 u‖ + ‖planeH1GradientOperator u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [planeH1_normSq_eq_value_gradient]
  calc
    _ ≤ ‖planeHkValueOperator 1 u‖ ^ 2 + ‖planeH1GradientOperator u‖ ^ 2 +
        2 * (‖planeHkValueOperator 1 u‖ * ‖planeH1GradientOperator u‖) :=
      le_add_of_nonneg_right (mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = _ := by ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! Bochner L2 value and gradient readouts determine the native H1 time class. -/

variable {E T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [MeasurableSpace T]

theorem planeH1_time_memLp_of_readouts (μ : Measure T) (u : T → PlaneHk univ 1 E)
    (hv : MemLp (fun t => planeHkValueOperator 1 (u t)) 2 μ)
    (hG : ∀ i, MemLp (fun t => planeH1GradientOperator (u t) i) 2 μ) : MemLp u 2 μ := by
  apply closedSubspace_memLp (planeHkGraph (E := E) univ 1) μ u
  apply memLp_piLp_iff.mpr
  rintro ⟨j, w⟩
  fin_cases j
  · have hw : w = Fin.elim0 := funext (fun z => Fin.elim0 z)
    rw [hw]
    have hp := planeToUniv.toContinuousLinearMap.comp_memLp' hv
    change MemLp (fun t => planeToUniv (planeHkValueOperator 1 (u t))) 2 μ at hp
    simp_rw [planeHkValueOperator_apply, planeToUniv_univToPlane] at hp
    exact hp
  · have hw : w = (fun _ => w 0) := funext (fun z => congrArg w (Subsingleton.elim z 0))
    have hp := planeToUniv.toContinuousLinearMap.comp_memLp' (hG (w 0))
    change MemLp (fun t => planeToUniv (planeH1GradientOperator (u t) (w 0))) 2 μ at hp
    simp_rw [planeH1GradientOperator_apply, planeToUniv_univToPlane] at hp
    rw [hw]
    exact hp

end AVRegularity.CycleJointProofs
end
end
