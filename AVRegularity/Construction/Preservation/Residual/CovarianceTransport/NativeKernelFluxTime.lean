-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.NativeClassicalCurves
public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.LiftResidual
public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.NativeContextRegularity
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
import AVRegularity.EntryWeakAssembly.NativeFamilyLiftUniqueness
import AVRegularity.IterationPassage.Passage.Profiles.ClausesStatement
public import AVRegularity.KernelEnergy.PlaneFluxTerm
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.CycleComparison.LiftMeanEntrywise.Letter
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
import AVRegularity.Families.TorusCompatible.WeakStage

/-! The actual higher kernel input already belongs to time L² in the solution
class. Its coefficient flux therefore has the reserved Sobolev time integrability
without a Schur smallness assumption or an additional kernel construction. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter
open AVRegularity.KernelEnergy AVRegularity.CoupledEnergy.Galerkin
open scoped Topology
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
attribute [local instance] nativeTorusHkNormed nativeTorusHkInner nativeTorusHkNormedSpace
variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
variable {K r : ℕ} {a b ρ : ℝ} (hρ : 0 < ρ)
  (A : ℝ → Vec 2 → (PiLp 2 (fun _ : DerivativeWord2 r => G)) →L[ℝ]
    PiLp 2 (fun _ : Fin 2 => H))
  (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
  (hC : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (A t))
  (hp : ∀ t ∈ Icc a b, AVenhance.IsZ2Periodic (A t))

/-- Coefficient multiplication after the actual ordered derivative tensor. -/
def nativeKernelFluxCLM (t : Icc a b) :
    TorusHk (K + r) G →L[ℝ] TorusHk K (PiLp 2 (fun _ : Fin 2 => H)) :=
  (torusMultiplierCLM (A t) (hC t t.property) (hp t t.property)
    (fun l : Fin (K + 1) => (coefficientOrderSup a b A l.val).toReal)
    (fun l x => coefficientOrderSup_derivative_bound ρ hρ K a b A hA l.val
      (Nat.le_of_lt_succ l.isLt) t t.property x) ρ hρ).comp
    (torusKernelDerivativeTensorCLM K r)

/-- The flux map has exactly the literal weak coefficient and ordered jets. -/
theorem native_kernel_flux_value_ae (t : Icc a b) (Y : TorusHk (K + r) G) :
    (nativeKernelFluxCLM hρ A hA hC hp t Y).toFunction.jet (valueIndex2 K) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x =>
        A t x (WithLp.toLp 2 fun w : DerivativeWord2 r =>
          Y.toFunction.jet (prefixJetIndex w (valueIndex2 K)) x) := by
  have hm := torusMulCoefficient_toFunction_value_ae
    (torusDerivativeTensor (K := K) (r := r) Y) (A t) (hC t t.property) (hp t t.property)
    (fun l x => coefficientOrderSup_derivative_bound ρ hρ K a b A hA l.val
      (Nat.le_of_lt_succ l.isLt) t t.property x)
  have hd := torusDerivativeTensor_base_ae (K := K) (r := r) Y
  change (torusMultiplierCLM _ _ _ _ _ ρ hρ
    (torusKernelDerivativeTensorCLM K r Y)).toFunction.jet _ =ᵐ[_] _
  simp only [torusKernelDerivativeTensorCLM_apply]
  filter_upwards [hm, hd] with x hm hd
  exact hm.trans (congrArg (A t x) hd)

/-- Only measurability of the coefficient values is needed for the native flux. -/
theorem native_kernel_flux_fixed_stronglyMeasurable
    (hm : Measurable (fun z : Icc a b × Vec 2 => A z.1 z.2))
    (Y : TorusHk (K + r) G) :
    StronglyMeasurable (fun t => nativeKernelFluxCLM hρ A hA hC hp t Y) := by
  exact torusMultiplier_time_stronglyMeasurable ρ hρ (fun t : Icc a b => A t) hm
    (fun t => hC t t.property) (fun t => hp t t.property)
    (fun l : Fin (K + 1) => (coefficientOrderSup a b A l.val).toReal)
    (fun t l x => coefficientOrderSup_derivative_bound ρ hρ K a b A hA l.val
      (Nat.le_of_lt_succ l.isLt) t t.property x)
    (fun _ => torusKernelDerivativeTensorCLM K r Y) stronglyMeasurable_const

/-- A finite coefficient budget bounds the map uniformly in time. -/
theorem native_kernel_flux_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : Icc a b, ‖nativeKernelFluxCLM hρ A hA hC hp t‖ ≤ C := by
  let L : ℝ := (∑ l : Fin (K + 1), factorialRootWeight ρ l.val *
    (coefficientOrderSup a b A l.val).toReal) *
      Real.sqrt (factorialWeightMax ρ K) / Real.sqrt (factorialWeightMin ρ K)
  refine ⟨|L| * ‖torusKernelDerivativeTensorCLM (E := G) K r‖,
    mul_nonneg (abs_nonneg L) (norm_nonneg (torusKernelDerivativeTensorCLM (E := G) K r)), ?_⟩
  intro t
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg L) (norm_nonneg (torusKernelDerivativeTensorCLM (E := G) K r)))
  intro Y
  have hb := torusMultiplier_norm_bound (A t) (hC t t.property) (hp t t.property)
    (fun l : Fin (K + 1) => (coefficientOrderSup a b A l.val).toReal)
    (fun l x => coefficientOrderSup_derivative_bound ρ hρ K a b A hA l.val
      (Nat.le_of_lt_succ l.isLt) t t.property x) ρ hρ
    (torusKernelDerivativeTensorCLM K r Y)
  exact hb.trans ((mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)).trans
    ((mul_le_mul_of_nonneg_left ((torusKernelDerivativeTensorCLM (E := G) K r).le_opNorm Y)
      (abs_nonneg L)).trans_eq (mul_assoc _ _ _).symm))

/-- Clamp only the coefficient time; the input is the original solution time. -/
def nativeKernelFluxPath (hab : a ≤ b) (Y : ℝ → TorusHk (K + r) G) :
    ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => H)) := fun t =>
  nativeKernelFluxCLM hρ A hA hC hp (projIcc a b hab t) (Y t)

/-- Higher kernel jets already present in the solution give time L² fluxes. -/
theorem native_kernel_flux_memLp (hab : a ≤ b)
    (hm : Measurable (fun z : Icc a b × Vec 2 => A z.1 z.2))
    (Y : ℝ → TorusHk (K + r) G)
    (hY : MemLp Y 2 (volume.restrict (Icc a b))) :
    MemLp (nativeKernelFluxPath hρ A hA hC hp hab Y) 2 (volume.restrict (Icc a b)) := by
  obtain ⟨C, hC0, hb⟩ := native_kernel_flux_uniform_bound (G := G) (H := H) (K := K) (r := r) hρ A hA hC hp
  exact memLp_operator_action (H := TorusHk (K + r) G)
    (G := TorusHk K (PiLp 2 (fun _ : Fin 2 => H))) (volume.restrict (Icc a b))
    (fun t => nativeKernelFluxCLM hρ A hA hC hp (projIcc a b hab t))
    (fun Y => (native_kernel_flux_fixed_stronglyMeasurable hρ A hA hC hp hm Y).comp_measurable
      (continuous_projIcc (a := a) (b := b) (h := hab)).measurable)
    C hC0 (fun t => hb _) hY

/-- A joint coefficient's spatial chain term is its finite fast and slow
partial sum, in the same word coordinates as the local reserve API. -/
theorem native_joint_derivative_partial_sum
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Vec 2 → Vec 2 → V) (hf : ContDiff ℝ 1 (Function.uncurry f))
    (X U : Vec 2 × Vec 2) :
    fderiv ℝ (Function.uncurry f) X U =
      (∑ i : Fin 2, U.1 i • orderedDerivative (fun _ : Fin 1 => i) (fun z => f z X.2) X.1) +
      ∑ i : Fin 2, U.2 i • orderedDerivative (fun _ : Fin 1 => i) (f X.1) X.2 := by
  have hfast : HasFDerivAt (fun z => f z X.2) (fderiv ℝ (fun z => f z X.2) X.1) X.1 :=
    ((hf.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero X.1).hasFDerivAt
  have hslow : HasFDerivAt (f X.1) (fderiv ℝ (f X.1) X.2) X.2 :=
    ((hf.comp (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero X.2).hasFDerivAt
  rw [EntryWeakProofs.joint_fderiv_apply_of_slice_derivatives 2 f X _ _
    (hf.differentiable one_ne_zero X) hfast hslow U]
  have hword (g : Vec 2 → V) (x : Vec 2) (i : Fin 2) :
      orderedDerivative (fun _ : Fin 1 => i) g x = fderiv ℝ g x (basisVec i) := by
    rw [orderedDerivative_succ, orderedDerivative_zero]
  simp_rw [hword]
  conv_lhs =>
    arg 1
    arg 2
    rw [AVRegularity.vec_eq_sum_basis U.1]
  conv_lhs =>
    arg 2
    arg 2
    rw [AVRegularity.vec_eq_sum_basis U.2]
  simp only [map_sum, map_smul]

/-- Local coefficient reserves alone control sampling in a smooth physical chart.
No temporal derivative or primitive is needed for these spatial budgets. -/
theorem native_local_reserve_sample_spatial_budget
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    {a b : ℝ} {f : ℝ → Vec 2 → Vec 2 → V} (R : ℕ)
    (hmodel : ∀ Y : Vec 2, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = f t z Z)
    (Γ : ℝ → Vec 2 → Vec 2 × Vec 2)
    (hΓ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Γ)) (X : Set (Vec 2)) (hX : IsCompact X) :
    NativeCompactSpatialBudget a b R X (fun t x => f t (Γ t x).1 (Γ t x).2) := by
  refine ⟨?_, native_local_reserve_sample_jet_bound R hmodel Γ hΓ X hX⟩
  intro t ht
  have hs := (native_local_reserve_joint_data (Ω := univ) R f (fun Y _ => hmodel Y)).1 t ht
  rw [univ_prod_univ] at hs
  exact (contDiffOn_univ.mp hs).comp
    ((hΓ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp))

/-- Local native reserve models give joint measurability after zero extension of
the literal window values. The fast and slow labels remain independent. -/
theorem native_local_reserve_joint_zero_extension_measurable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} (f : ℝ → Vec 2 → Vec 2 → V)
    (hmodel : ∀ Y : Vec 2, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve 0 g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = f t z Z) :
    Measurable (fun p : ℝ × (Vec 2 × Vec 2) =>
      if p.1 ∈ Icc a b then f p.1 p.2.1 p.2.2 else 0) := by
  classical
  obtain ⟨hfc, _⟩ := native_local_reserve_joint_data (Ω := univ) 0 f (fun Y _ => hmodel Y)
  obtain ⟨_, hfm, _⟩ := native_local_reserve_window_data f (fun Y _ => hmodel Y)
  let g := fun t (X : Vec 2 × Vec 2) => if t ∈ Icc a b then f t X.1 X.2 else 0
  have hc (t : ℝ) : Continuous (g t) := by
    by_cases ht : t ∈ Icc a b
    · have hh := hfc t ht
      rw [univ_prod_univ] at hh
      simpa only [g, ite_eq_left ht] using (contDiffOn_univ.mp hh).continuous
    · simpa only [g, ite_eq_right ht] using
        (continuous_const : Continuous (fun _ : Vec 2 × Vec 2 => (0 : V)))
  have hm (X : Vec 2 × Vec 2) : Measurable (fun t => g t X) :=
    (hfm X.2 (mem_univ _)).comp (measurable_id.prodMk (measurable_const (a := X.1)))
  exact (measurable_uncurry_of_continuous_of_measurable hc hm).comp measurable_swap

/-- A local coefficient reserve suffices for joint measurability of its
literal sample on the closed time window. -/
theorem native_local_reserve_sample_measurable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} {f : ℝ → Vec 2 → Vec 2 → V}
    (hmodel : ∀ Y : Vec 2, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve 0 g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = f t z Z)
    (Γ : ℝ → Vec 2 → Vec 2 × Vec 2) (hΓ : Measurable (Function.uncurry Γ)) :
    Measurable (fun p : {p : ℝ × Vec 2 // p.1 ∈ Icc a b} =>
      f p.1.1 (Γ p.1.1 p.1.2).1 (Γ p.1.1 p.1.2).2) := by
  have hm : Measurable (fun p : {p : ℝ × Vec 2 // p.1 ∈ Icc a b} =>
      if p.1.1 ∈ Icc a b then f p.1.1 (Γ p.1.1 p.1.2).1 (Γ p.1.1 p.1.2).2 else 0) :=
    (native_local_reserve_joint_zero_extension_measurable f hmodel).comp
    ((measurable_fst.comp measurable_subtype_coe).prodMk (hΓ.comp measurable_subtype_coe))
  convert hm using 1
  funext p
  exact (ite_eq_left p.2).symm

/-- Sampling a native coefficient in a smooth moving chart has one literal time
RHS with uniform compact spatial budgets at every finite order. -/
theorem NativeLocalTimeData.sample_time_rhs
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
    {a b : ℝ} (hab : a ≤ b) {f df : ℝ → Vec 2 → Vec 2 → V}
    (Q : NativeLocalTimeData a b univ f df) (Γ : ℝ → Vec 2 → Vec 2 × Vec 2)
    (hΓ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Γ)) :
    ∃ D : ℝ → Vec 2 → V,
      (∀ᵐ t ∂volume.restrict (Icc a b), ∀ x,
        HasDerivAt (fun s => f s (Γ s x).1 (Γ s x).2) (D t x) t) ∧
      (∀ R X, IsCompact X → NativeCompactSpatialBudget a b R X D) ∧
      Measurable (fun p : {p : ℝ × Vec 2 // p.1 ∈ Icc a b} => D p.1.1 p.1.2) := by
  classical
  let dotΓ := fun t x => deriv (fun s => Γ s x) t
  let Cf := fun (i : Fin 2) t z Y => orderedDerivative (fun _ : Fin 1 => i) (fun w => f t w Y) z
  let Cs := fun (i : Fin 2) t z Y => orderedDerivative (fun _ : Fin 1 => i) (fun Z => f t z Z) Y
  let D := fun t x => df t (Γ t x).1 (Γ t x).2 +
    (∑ i : Fin 2, (dotΓ t x).1 i • Cf i t (Γ t x).1 (Γ t x).2) +
    ∑ i : Fin 2, (dotΓ t x).2 i • Cs i t (Γ t x).1 (Γ t x).2
  have hDot : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry dotΓ) := native_smooth_time_partial Γ hΓ
  have hFast (i : Fin 2) := Q.mixed hab isOpen_univ 1 (fun _ => i) 0 Fin.elim0
  have hSlow (i : Fin 2) := Q.mixed hab isOpen_univ 0 Fin.elim0 1 (fun _ => i)
  have hCf (i : Fin 2) (R : ℕ) (X : Set (Vec 2)) (hX : IsCompact X) :
      NativeCompactSpatialBudget a b R X (fun t x => Cf i t (Γ t x).1 (Γ t x).2) := by
    simpa only [Cf, orderedDerivative_zero] using native_local_reserve_sample_spatial_budget R
      (fun Y => (hFast i).coefficient R Y (mem_univ _)) Γ hΓ X hX
  have hCs (i : Fin 2) (R : ℕ) (X : Set (Vec 2)) (hX : IsCompact X) :
      NativeCompactSpatialBudget a b R X (fun t x => Cs i t (Γ t x).1 (Γ t x).2) := by
    simpa only [Cs, orderedDerivative_zero] using native_local_reserve_sample_spatial_budget R
      (fun Y => (hSlow i).coefficient R Y (mem_univ _)) Γ hΓ X hX
  have hvFast (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => (dotΓ p.1 p.2).1 i) :=
    (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ).contDiff.comp hDot.fst
  have hvSlow (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => (dotΓ p.1 p.2).2 i) :=
    (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ).contDiff.comp hDot.snd
  have hproduct (A : ℝ → Vec 2 → ℝ)
      (hA : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry A)) (B : ℝ → Vec 2 → V)
      (hB : ∀ R X, IsCompact X → NativeCompactSpatialBudget a b R X B)
      (R : ℕ) (X : Set (Vec 2)) (hX : IsCompact X) :
      NativeCompactSpatialBudget a b R X (fun t x => A t x • B t x) := by
    have hAt (t : ℝ) : ContDiff ℝ (R : ℕ∞) (A t) :=
      (hA.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
    refine ⟨fun t ht => (hAt t).smul ((hB R X hX).smooth t ht), ?_⟩
    apply native_uniform_bilinear_jet_bound
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V) R X A B
      (fun t _ => hAt t) (hB R X hX).smooth
    · intro k _hk
      obtain ⟨C, hC, hc⟩ := native_smooth_chart_compact_jet_bounds A hA
        (fun _ x => x) contDiff_snd a b X hX k
      exact ⟨C, le_trans zero_le_one hC, fun t ht x hx => hc k le_rfl t ht x hx⟩
    · intro k _hk
      exact (hB k X hX).bound
  refine ⟨D, ?_, ?_, ?_⟩
  · have hs := (native_local_reserve_joint_data (Ω := univ) 1 f (Q.coefficient 1)).1
    filter_upwards [Q.moving_chain_rule hab, ae_restrict_mem measurableSet_Icc] with t ht hmem
    intro x
    have hγ : HasDerivAt (fun s => Γ s x) (dotΓ t x) t :=
      ((hΓ.comp (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable (by simp) t).hasDerivAt
    have hh := ht (fun s => Γ s x) (dotΓ t x) hγ
    have hft := hs t hmem
    rw [univ_prod_univ] at hft
    have he := native_joint_derivative_partial_sum (fun z Y => f t z Y)
      (contDiffOn_univ.mp hft) (Γ t x) (dotΓ t x)
    have he' : fderiv ℝ (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2) (Γ t x) (dotΓ t x) =
        (∑ i : Fin 2, (dotΓ t x).1 i • Cf i t (Γ t x).1 (Γ t x).2) +
        ∑ i : Fin 2, (dotΓ t x).2 i • Cs i t (Γ t x).1 (Γ t x).2 := he
    rw [he'] at hh
    simpa only [D, Cf, Cs, add_assoc] using hh
  · intro R X hX
    exact (((native_local_reserve_sample_spatial_budget R
      (fun Y => Q.rhs R Y (mem_univ _)) Γ hΓ X hX)).add
      (NativeCompactSpatialBudget.sum Finset.univ _ (fun i _ =>
        hproduct (fun t x => (dotΓ t x).1 i) (hvFast i) _ (hCf i) R X hX))).add
      (NativeCompactSpatialBudget.sum Finset.univ _ (fun i _ =>
        hproduct (fun t x => (dotΓ t x).2 i) (hvSlow i) _ (hCs i) R X hX))
  · have hBase := native_local_reserve_sample_measurable
      (fun Y => Q.rhs 0 Y (mem_univ _)) Γ hΓ.continuous.measurable
    have hfMeas (i : Fin 2) : Measurable (fun p : {p : ℝ × Vec 2 // p.1 ∈ Icc a b} =>
        Cf i p.1.1 (Γ p.1.1 p.1.2).1 (Γ p.1.1 p.1.2).2) := by
      simpa only [Cf, orderedDerivative_zero] using native_local_reserve_sample_measurable
        (fun Y => (hFast i).coefficient 0 Y (mem_univ _)) Γ hΓ.continuous.measurable
    have hsMeas (i : Fin 2) : Measurable (fun p : {p : ℝ × Vec 2 // p.1 ∈ Icc a b} =>
        Cs i p.1.1 (Γ p.1.1 p.1.2).1 (Γ p.1.1 p.1.2).2) := by
      simpa only [Cs, orderedDerivative_zero] using native_local_reserve_sample_measurable
        (fun Y => (hSlow i).coefficient 0 Y (mem_univ _)) Γ hΓ.continuous.measurable
    exact (hBase.add (Finset.measurable_sum _ (fun i _ =>
      ((hvFast i).continuous.measurable.comp measurable_subtype_coe).smul (hfMeas i)))).add
      (Finset.measurable_sum _ (fun i _ =>
        ((hvSlow i).continuous.measurable.comp measurable_subtype_coe).smul (hsMeas i)))

/-- A native time curve with uniform spatial budgets at every finite order on
compact sets. The derivative is selected before spatial points and tests. -/
structure NativeUniformTimeData {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] (a b : ℝ) (f df : ℝ → Vec 2 → V) : Prop where
  spatial : ∀ R X, IsCompact X → NativeCompactSpatialBudget a b R X f
  derivativeSpatial : ∀ R X, IsCompact X → NativeCompactSpatialBudget a b R X df
  measurable : Measurable (fun p : {p : ℝ × Vec 2 // p.1 ∈ Icc a b} => f p.1.1 p.1.2)
  derivativeMeasurable : Measurable (fun p : {p : ℝ × Vec 2 // p.1 ∈ Icc a b} => df p.1.1 p.1.2)
  derivative : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ x,
    HasDerivAt (fun s => f s x) (df t x) t

/-- Native local coefficient data supply this compact spatial time package after
sampling in the actual smooth physical chart. -/
theorem NativeLocalTimeData.sample_uniform_time
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
    {a b : ℝ} (hab : a ≤ b) {f df : ℝ → Vec 2 → Vec 2 → V}
    (Q : NativeLocalTimeData a b univ f df) (Γ : ℝ → Vec 2 → Vec 2 × Vec 2)
    (hΓ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Γ)) :
    ∃ D : ℝ → Vec 2 → V,
      NativeUniformTimeData a b (fun t x => f t (Γ t x).1 (Γ t x).2) D := by
  obtain ⟨D, hd, hD, hDm⟩ := Q.sample_time_rhs hab Γ hΓ
  exact ⟨D, fun R X hX => native_local_reserve_sample_spatial_budget R
      (fun Y => Q.coefficient R Y (mem_univ _)) Γ hΓ X hX, hD,
    native_local_reserve_sample_measurable
      (fun Y => Q.coefficient 0 Y (mem_univ _)) Γ hΓ.continuous.measurable, hDm, hd⟩

/-- A jointly smooth chart factor has uniform time/spatial budgets on every
compact window and compact spatial set. -/
theorem native_smooth_uniform_time_data
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] {a b : ℝ}
    (f : ℝ → Vec 2 → V) (hf : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f)) :
    NativeUniformTimeData a b f (fun t x => deriv (fun s => f s x) t) := by
  have hd := native_smooth_time_partial f hf
  have hbudget (g : ℝ → Vec 2 → V) (hg : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry g))
      (R : ℕ) (X : Set (Vec 2)) (hX : IsCompact X) : NativeCompactSpatialBudget a b R X g := by
    obtain ⟨B, hB, hb⟩ := native_smooth_chart_compact_jet_bounds g hg
      (fun _ x => x) contDiff_snd a b X hX R
    exact ⟨fun t _ => (hg.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp),
      B, le_trans zero_le_one hB, fun t ht x hx => hb R le_rfl t ht x hx⟩
  refine ⟨hbudget f hf, hbudget _ hd,
    hf.continuous.measurable.comp measurable_subtype_coe,
    hd.continuous.measurable.comp measurable_subtype_coe, ?_⟩
  exact ae_of_all _ (fun t x =>
    ((hf.comp (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable (by simp) t).hasDerivAt)

/-- Uniform compact spatial reserves are closed under a fixed bilinear map.
No time derivative is required for this spatial part of the product rule. -/
theorem native_uniform_bilinear_spatial_budget
    {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {a b : ℝ} {f : ℝ → Vec 2 → V} {g : ℝ → Vec 2 → W}
    (L : V →L[ℝ] W →L[ℝ] Z)
    (hF : ∀ R X, IsCompact X → NativeCompactSpatialBudget a b R X f)
    (hG : ∀ R X, IsCompact X → NativeCompactSpatialBudget a b R X g)
    (R : ℕ) (X : Set (Vec 2)) (hX : IsCompact X) :
    NativeCompactSpatialBudget a b R X (fun t x => L (f t x) (g t x)) := by
  refine ⟨fun t ht => (L.contDiff.comp ((hF R X hX).smooth t ht)).clm_apply
    ((hG R X hX).smooth t ht), ?_⟩
  exact native_uniform_bilinear_jet_bound L R X f g
    (hF R X hX).smooth (hG R X hX).smooth
    (fun k _ => (hF k X hX).bound) (fun k _ => (hG k X hX).bound)

/-- Fixed bilinear operations preserve the common-time spatial package and its
literal product-rule derivative. -/
theorem NativeUniformTimeData.bilinear
    {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    [MeasurableSpace Z] [BorelSpace Z]
    [SecondCountableTopology V] [SecondCountableTopology W] [SecondCountableTopology Z]
    {a b : ℝ} {f df : ℝ → Vec 2 → V} {g dg : ℝ → Vec 2 → W}
    (Qf : NativeUniformTimeData a b f df) (Qg : NativeUniformTimeData a b g dg)
    (L : V →L[ℝ] W →L[ℝ] Z) :
    NativeUniformTimeData a b (fun t x => L (f t x) (g t x))
      (fun t x => L (df t x) (g t x) + L (f t x) (dg t x)) := by
  have hmeas (F : {p : ℝ × Vec 2 // p.1 ∈ Icc a b} → V)
      (G : {p : ℝ × Vec 2 // p.1 ∈ Icc a b} → W)
      (hF : Measurable F) (hG : Measurable G) : Measurable (fun p => L (F p) (G p)) :=
    ((L.continuous.comp continuous_fst).clm_apply continuous_snd).measurable.comp
      (hF.prodMk hG)
  refine ⟨native_uniform_bilinear_spatial_budget L Qf.spatial Qg.spatial,
    fun R X hX => (native_uniform_bilinear_spatial_budget L Qf.derivativeSpatial Qg.spatial R X hX).add
      (native_uniform_bilinear_spatial_budget L Qf.spatial Qg.derivativeSpatial R X hX),
    hmeas _ _ Qf.measurable Qg.measurable,
    (hmeas _ _ Qf.derivativeMeasurable Qg.measurable).add
      (hmeas _ _ Qf.measurable Qg.derivativeMeasurable), ?_⟩
  filter_upwards [Qf.derivative, Qg.derivative] with t hf hg
  intro x
  simpa only [Function.comp_def, add_comm] using (L.hasFDerivAt.comp_hasDerivAt t (hf x)).clm_apply (hg x)

/-- Uniform spatial operator budgets multiply integrable spatial source budgets
without imposing time smoothness or a uniform-in-time source bound. -/
theorem native_integrable_bilinear_jet_bound
    {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (L : V →L[ℝ] W →L[ℝ] Z) {a b : ℝ} (R : ℕ) (X : Set (Vec 2))
    (f : ℝ → Vec 2 → V) (g : ℝ → Vec 2 → W)
    (hf : ∀ t ∈ Icc a b, ContDiff ℝ (R : ℕ∞) (f t))
    (hg : ∀ t ∈ Icc a b, ContDiff ℝ (R : ℕ∞) (g t))
    (hfb : ∀ k ≤ R, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x ∈ X,
      ‖iteratedFDeriv ℝ k (f t) x‖ ≤ C)
    (hgb : ∀ k ≤ R, ∃ B : ℝ → ℝ, IntegrableOn B (Icc a b) ∧
      ∀ t ∈ Icc a b, ∀ x ∈ X, ‖iteratedFDeriv ℝ k (g t) x‖ ≤ B t) :
    ∃ B : ℝ → ℝ, IntegrableOn B (Icc a b) ∧ ∀ t ∈ Icc a b, ∀ x ∈ X,
      ‖iteratedFDeriv ℝ R (fun y => L (f t y) (g t y)) x‖ ≤ B t := by
  classical
  choose C hC hc using fun k : Fin (R + 1) => hfb k.1 (by omega)
  choose D hD hd using fun k : Fin (R + 1) => hgb k.1 (by omega)
  let Csum := ∑ k : Fin (R + 1), C k
  let Dsum := fun t => ∑ k : Fin (R + 1), |D k t|
  have hCsum : 0 ≤ Csum := Finset.sum_nonneg (fun k _ => hC k)
  have hDint : IntegrableOn Dsum (Icc a b) := integrable_finsetSum _ (fun k _ => (hD k).norm)
  let B := fun t => ‖L‖ * ∑ k ∈ Finset.range (R + 1), (R.choose k : ℝ) * Csum * Dsum t
  refine ⟨B, (integrable_finsetSum _ (fun k _ => hDint.const_mul _)).const_mul ‖L‖, ?_⟩
  intro t ht x hx
  apply (L.norm_iteratedFDeriv_le_of_bilinear (hf t ht) (hg t ht) x (by simp)).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg L)
  apply Finset.sum_le_sum
  intro k hk
  have hkR : k < R + 1 := Finset.mem_range.mp hk
  have hcf := (hc ⟨k, hkR⟩ t ht x hx).trans
    (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ _))
  have hcg := ((hd ⟨R - k, by omega⟩ t ht x hx).trans (le_abs_self _)).trans
    (Finset.single_le_sum (fun i _ => abs_nonneg (D i t)) (Finset.mem_univ _))
  exact mul_le_mul (mul_le_mul_of_nonneg_left hcf (Nat.cast_nonneg _))
    hcg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hCsum)

/-- A derivative representative with genuine spatial budgets can be selected
periodic at every time. It is changed only on a measurable null set of times;
periodicity on the good set follows from uniqueness of the time derivative. -/
theorem native_periodic_derivative_with_window_budgets
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] {a b : ℝ} {K : ℕ}
    (f df : ℝ → Vec 2 → V)
    (hp : ∀ t ∈ Icc a b, AVenhance.IsZ2Periodic (f t))
    (hd : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ x,
      HasDerivAt (fun s => f s x) (df t x) t)
    (hs : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (df t))
    (hm : Measurable (fun z : {z : ℝ × Vec 2 // z.1 ∈ Icc a b} => df z.1.1 z.1.2))
    (hb : ∀ n ≤ K, ∀ w : DerivativeWord2 n, ∃ B : ℝ → ℝ,
      IntegrableOn B (Icc a b) ∧ ∀ t ∈ Icc a b, ∀ x ∈ AVenhance.unitCube,
        ‖orderedDerivative w (df t) x‖ ≤ B t) :
    ∃ g : ℝ → Vec 2 → V, ClassicalWindowBound a b K g ∧
      ∀ᵐ t ∂volume.restrict (Icc a b), ∀ x,
        HasDerivAt (fun s => f s x) (g t x) t := by
  classical
  have hi : ∀ᵐ t ∂volume.restrict (Icc a b), t ∈ Ioo a b := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
    exact ae_restrict_mem measurableSet_Ioo
  have hg := hi.and hd
  obtain ⟨G, hG, hgood, hGa⟩ := Weighted.exists_measurable_good_times
    (volume.restrict (Icc a b)) _ hg
  let g := fun t x => if t ∈ G then df t x else 0
  refine ⟨g, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro t ht
    by_cases htG : t ∈ G
    · simpa only [g, ite_eq_left htG] using hs t ht
    · simpa only [g, ite_eq_right htG] using
        (contDiff_const : ContDiff ℝ (K : ℕ) (fun _ : Vec 2 => (0 : V)))
  · intro t _ht k x
    by_cases htG : t ∈ G
    · have hdg := (hgood t htG).2
      have he : (fun s => f s (x + AVenhance.latticeShift k)) =ᶠ[𝓝 t] fun s => f s x := by
        filter_upwards [isOpen_Ioo.mem_nhds (hgood t htG).1] with s hs
        exact hp s (Ioo_subset_Icc_self hs) k x
      have heq := (hdg (x + AVenhance.latticeShift k)).unique
        ((hdg x).congr_of_eventuallyEq he)
      simpa only [g, ite_eq_left htG] using heq
    · simp only [g, ite_eq_right htG]
  · exact hm.ite (hG.preimage (measurable_fst.comp measurable_subtype_coe)) measurable_const
  · intro n hn w
    obtain ⟨B, hB, hbd⟩ := hb n hn w
    refine ⟨fun t => |B t|, hB.norm, fun t ht x hx => ?_⟩
    by_cases htG : t ∈ G
    · have he : g t = df t := by funext y; exact ite_eq_left htG
      rw [he]
      exact (hbd t ht x hx).trans (le_abs_self _)
    · have he : g t = fun _ => 0 := by funext y; exact ite_eq_right htG
      rw [he, AVRegularity.orderedDerivative_const_zero]
      simpa only [norm_zero] using (abs_nonneg (B t))
  · filter_upwards [hGa, hd] with t ht hdt
    intro x
    simpa only [g, ite_eq_left ht] using hdt x

/-- The periodic word budgets also bound a full spatial jet uniformly in space,
with a genuine integrable time bound. -/
theorem ClassicalWindowBound.full_jet_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] {a b : ℝ} {K : ℕ}
    {f : ℝ → Vec 2 → V} (Q : ClassicalWindowBound a b K f)
    (r : ℕ) (hr : r ≤ K) :
    ∃ B : ℝ → ℝ, IntegrableOn B (Icc a b) ∧ ∀ t ∈ Icc a b, ∀ x,
      ‖iteratedFDeriv ℝ r (f t) x‖ ≤ B t := by
  classical
  choose B hB hb using fun w : DerivativeWord2 r => Q.global_bound r hr w
  refine ⟨fun t => ∑ w, |B w t|, integrable_finsetSum _ (fun w _ => (hB w).norm), ?_⟩
  intro t ht x
  exact (ChartTransport.norm_iteratedFDeriv_le_sum_words
    ((Q.smooth t ht).of_le (Nat.cast_le.mpr hr)) x).trans
    (Finset.sum_le_sum (fun w _ => (hb w t ht x).trans (le_abs_self _)))

/-- A common-time derivative with finite spatial reserve and integrable full
jet budgets. Periodicity is imposed only after the complete pulse sum is formed. -/
structure NativeTimeDerivativeBudget {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] (a b : ℝ) (K : ℕ) (f df : ℝ → Vec 2 → V) : Prop where
  derivative : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ x,
    HasDerivAt (fun s => f s x) (df t x) t
  smooth : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ∞) (df t)
  measurable : Measurable (fun p : {p : ℝ × Vec 2 // p.1 ∈ Icc a b} => df p.1.1 p.1.2)
  bound : ∀ r ≤ K, ∃ B : ℝ → ℝ, IntegrableOn B (Icc a b) ∧
    ∀ t ∈ Icc a b, ∀ x ∈ AVenhance.unitCube, ‖iteratedFDeriv ℝ r (df t) x‖ ≤ B t

/-- Adding two common-time derivatives adds their actual integrable budgets. -/
theorem NativeTimeDerivativeBudget.add
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] {a b : ℝ} {K : ℕ} {f df g dg : ℝ → Vec 2 → V}
    (Q : NativeTimeDerivativeBudget a b K f df) (R : NativeTimeDerivativeBudget a b K g dg) :
    NativeTimeDerivativeBudget a b K (fun t x => f t x + g t x) (fun t x => df t x + dg t x) := by
  refine ⟨?_, fun t ht => (Q.smooth t ht).add (R.smooth t ht), Q.measurable.add R.measurable, ?_⟩
  · filter_upwards [Q.derivative, R.derivative] with t hq hr
    exact fun x => (hq x).add (hr x)
  · intro r hr
    obtain ⟨B, hB, hb⟩ := Q.bound r hr
    obtain ⟨C, hC, hc⟩ := R.bound r hr
    refine ⟨fun t => B t + C t, hB.add hC, fun t ht x hx => ?_⟩
    rw [show (fun y => df t y + dg t y) = df t + dg t by rfl,
      iteratedFDeriv_add_apply ((Q.smooth t ht).of_le (Nat.cast_le.mpr hr)).contDiffAt
        ((R.smooth t ht).of_le (Nat.cast_le.mpr hr)).contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add (hb t ht x hx) (hc t ht x hx))

/-- Constant scalar weights preserve the derivative's finite reserve. -/
theorem NativeTimeDerivativeBudget.const_smul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] {a b : ℝ} {K : ℕ} {f df : ℝ → Vec 2 → V}
    (Q : NativeTimeDerivativeBudget a b K f df) (c : ℝ) :
    NativeTimeDerivativeBudget a b K (fun t x => c • f t x) (fun t x => c • df t x) := by
  refine ⟨?_, fun t ht => (Q.smooth t ht).const_smul c, measurable_const.smul Q.measurable, ?_⟩
  · filter_upwards [Q.derivative] with t ht
    exact fun x => (ht x).const_smul c
  · intro r hr
    obtain ⟨B, hB, hb⟩ := Q.bound r hr
    refine ⟨fun t => ‖c‖ * B t, hB.const_mul _, fun t ht x hx => ?_⟩
    rw [iteratedFDeriv_const_smul_apply' ((Q.smooth t ht).of_le (Nat.cast_le.mpr hr)).contDiffAt,
      norm_smul]
    exact mul_le_mul_of_nonneg_left (hb t ht x hx) (norm_nonneg c)

/-- Finite pulse and partition sums preserve the common-time derivative package. -/
theorem NativeTimeDerivativeBudget.sum
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] {ι : Type*} (S : Finset ι) {a b : ℝ} {K : ℕ}
    (f df : ι → ℝ → Vec 2 → V) (Q : ∀ i ∈ S, NativeTimeDerivativeBudget a b K (f i) (df i)) :
    NativeTimeDerivativeBudget a b K (fun t x => ∑ i ∈ S, f i t x) (fun t x => ∑ i ∈ S, df i t x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨ae_of_all _ (fun t x => hasDerivAt_const t 0), fun _ _ => contDiff_const,
      measurable_const, fun r _ => ⟨fun _ => 0, integrableOn_zero, fun _ _ _ _ => by
        simpa only [AVRegularity.orderedDerivative_const_zero, norm_zero, Finset.sum_const_zero] using
          ChartTransport.norm_iteratedFDeriv_le_sum_words
            (contDiff_const : ContDiff ℝ (r : ℕ∞) (fun _ : Vec 2 => (0 : V))) _⟩⟩
  | @insert i S hi ih =>
    have h := (Q i (Finset.mem_insert_self i S)).add
      (ih (fun j hj => Q j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using h

/-- Equality on the closed window transports a derivative on its full-measure
interior without requiring any equality outside that window. -/
theorem NativeTimeDerivativeBudget.congr_window
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    {a b : ℝ} {K : ℕ} {f df g : ℝ → Vec 2 → V}
    (Q : NativeTimeDerivativeBudget a b K f df)
    (he : ∀ t ∈ Icc a b, ∀ x, f t x = g t x) :
    NativeTimeDerivativeBudget a b K g df := by
  refine ⟨?_, Q.smooth, Q.measurable, Q.bound⟩
  have hi : ∀ᵐ t ∂volume.restrict (Icc a b), t ∈ Ioo a b := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hi, Q.derivative] with t ht hd
  intro x
  apply (hd x).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact (he s (Ioo_subset_Icc_self hs) x).symm

/-- For a periodic complete lift, its common-time derivative can be made
periodic at every time while retaining all integrable spatial budgets. -/
theorem NativeTimeDerivativeBudget.periodic_selection
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] {a b : ℝ} {K : ℕ} {f df : ℝ → Vec 2 → V}
    (Q : NativeTimeDerivativeBudget a b K f df)
    (hp : ∀ t ∈ Icc a b, AVenhance.IsZ2Periodic (f t)) :
    ∃ g : ℝ → Vec 2 → V, ClassicalWindowBound a b K g ∧
      ∀ᵐ t ∂volume.restrict (Icc a b), ∀ x, HasDerivAt (fun s => f s x) (g t x) t := by
  apply native_periodic_derivative_with_window_budgets f df hp Q.derivative Q.smooth Q.measurable
  intro n hn w
  obtain ⟨B, hB, hb⟩ := Q.bound n hn
  refine ⟨B, hB, fun t ht x hx => ?_⟩
  exact (ChartTransport.norm_orderedDerivative_le
    ((Q.smooth t ht).of_le (Nat.cast_le.mpr hn)) w x).trans (hb t ht x hx)

/-- Choose derivative witnesses before assembling a finite pulse or letter sum. -/
theorem NativeTimeDerivativeBudget.exists_sum
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] {ι : Type*} (S : Finset ι) {a b : ℝ} {K : ℕ}
    (f : ι → ℝ → Vec 2 → V)
    (Q : ∀ i ∈ S, ∃ df, NativeTimeDerivativeBudget a b K (f i) df) :
    ∃ df, NativeTimeDerivativeBudget a b K (fun t x => ∑ i ∈ S, f i t x) df := by
  classical
  let df := fun i => if hi : i ∈ S then (Q i hi).choose else fun _ _ => 0
  refine ⟨fun t x => ∑ i ∈ S, df i t x, NativeTimeDerivativeBudget.sum S f df ?_⟩
  intro i hi
  simpa only [df, dite_eq_left hi] using (Q i hi).choose_spec

/-- An actual native operator acts on a stationary prepared full jet with the
literal product derivative and finite integrable spatial budgets. -/
theorem native_uniform_operator_prepared_jet_time
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (F : Frame D hr Dm bw j₀) {K n R : ℕ} {f df : F.Field}
    (Q : ClassicalTimeCurve F K f df) (hn : n + R + 4 ≤ K) (hab : F.tp ≤ F.tf)
    (v : CompIn F.G.comps) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    (L dL : ℝ → Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) (hr v.1.root) →L[ℝ] V)
    (hL : NativeUniformTimeData F.tp F.tf L dL) :
    NativeTimeDerivativeBudget F.tp F.tf R
      (fun t x => L t x (iteratedFDeriv ℝ n (fun y => f t y v) x))
      (fun t x => dL t x (iteratedFDeriv ℝ n (fun y => f t y v) x) +
        L t x (iteratedFDeriv ℝ n (fun y => df t y v) x)) := by
  let nativePreparedActionJetMeasurable : MeasurableSpace
      (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) (hr v.1.root)) := borel _
  let nativePreparedActionJetBorel : BorelSpace
      (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) (hr v.1.root)) := ⟨rfl⟩
  have hf := (Q.field v).spatial_jet (n := n) (L := R) (by omega)
  have hd := (Q.derivativeBound v).spatial_jet (n := n) (L := R) (by omega)
  have hs1 (t : ℝ) (ht : t ∈ Icc F.tp F.tf) : ContDiff ℝ (R : ℕ∞)
      (fun x => dL t x (iteratedFDeriv ℝ n (fun y => f t y v) x)) :=
    ((hL.derivativeSpatial R (Icc (0 : Vec 2) 1) isCompact_Icc).smooth t ht).clm_apply
      (hf.smooth t ht)
  have hs2 (t : ℝ) (ht : t ∈ Icc F.tp F.tf) : ContDiff ℝ (R : ℕ∞)
      (fun x => L t x (iteratedFDeriv ℝ n (fun y => df t y v) x)) :=
    ((hL.spatial R (Icc (0 : Vec 2) 1) isCompact_Icc).smooth t ht).clm_apply
      (hd.smooth t ht)
  refine ⟨?_, fun t ht => (hs1 t ht).add (hs2 t ht),
    (((continuous_fst.clm_apply continuous_snd).measurable.comp
      (hL.derivativeMeasurable.prodMk hf.measurable))).add
      ((continuous_fst.clm_apply continuous_snd).measurable.comp
        (hL.measurable.prodMk hd.measurable)), ?_⟩
  · filter_upwards [hL.derivative, native_classical_curve_spatial_jet_moving F (n := n) Q hab (by omega) v]
      with t ht hj
    intro x
    have hA : HasDerivAt (fun s => iteratedFDeriv ℝ n (fun y => f s y v) x)
        (iteratedFDeriv ℝ n (fun y => df t y v) x) t := by
      simpa only [map_zero, add_zero] using hj (fun _ => x) 0 (hasDerivAt_const t x)
    simpa only [add_comm] using (ht x).clm_apply hA
  · intro r hRle
    have hrf (t : ℝ) (ht : t ∈ Icc F.tp F.tf) := (hf.smooth t ht).of_le (Nat.cast_le.mpr hRle)
    have hrd (t : ℝ) (ht : t ∈ Icc F.tp F.tf) := (hd.smooth t ht).of_le (Nat.cast_le.mpr hRle)
    let A := ((ContinuousLinearMap.apply ℝ V).flip :
      (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) (hr v.1.root) →L[ℝ] V) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) (hr v.1.root) →L[ℝ] V)
    obtain ⟨B, hB, hb⟩ := native_integrable_bilinear_jet_bound A r (Icc (0 : Vec 2) 1)
      dL (fun t x => iteratedFDeriv ℝ n (fun y => f t y v) x)
      (hL.derivativeSpatial r (Icc (0 : Vec 2) 1) isCompact_Icc).smooth hrf
      (fun k _ => (hL.derivativeSpatial k (Icc (0 : Vec 2) 1) isCompact_Icc).bound)
      (fun k hk => by
        obtain ⟨C, hC, hc⟩ := hf.full_jet_bound k (hk.trans hRle)
        exact ⟨C, hC, fun t ht x _ => hc t ht x⟩)
    obtain ⟨C, hC, hc⟩ := native_integrable_bilinear_jet_bound A r (Icc (0 : Vec 2) 1)
      L (fun t x => iteratedFDeriv ℝ n (fun y => df t y v) x)
      (hL.spatial r (Icc (0 : Vec 2) 1) isCompact_Icc).smooth hrd
      (fun k _ => (hL.spatial k (Icc (0 : Vec 2) 1) isCompact_Icc).bound)
      (fun k hk => by
        obtain ⟨C, hC, hc⟩ := hd.full_jet_bound k (hk.trans hRle)
        exact ⟨C, hC, fun t ht x _ => hc t ht x⟩)
    refine ⟨fun t => B t + C t, hB.add hC, fun t ht x hx => ?_⟩
    rw [show (fun y => dL t y (iteratedFDeriv ℝ n (fun z => f t z v) y) +
        L t y (iteratedFDeriv ℝ n (fun z => df t z v) y)) =
        (fun y => dL t y (iteratedFDeriv ℝ n (fun z => f t z v) y)) +
        (fun y => L t y (iteratedFDeriv ℝ n (fun z => df t z v) y)) by rfl,
      iteratedFDeriv_add_apply ((hs1 t ht).of_le (Nat.cast_le.mpr hRle)).contDiffAt
        ((hs2 t ht).of_le (Nat.cast_le.mpr hRle)).contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add (hb t ht x ⟨fun i => (hx i (mem_univ _)).1.le, fun i => (hx i (mem_univ _)).2.le⟩)
      (hc t ht x ⟨fun i => (hx i (mem_univ _)).1.le, fun i => (hx i (mem_univ _)).2.le⟩))

/-- Zero coefficients have the local all-order time package on any window. -/
theorem NativeLocalTimeData.zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    {a b : ℝ} : NativeLocalTimeData a b univ
      (fun _ _ _ => (0 : V)) (fun _ _ _ => (0 : V)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro R Y _
    exact ⟨univ, fun _ _ _ => 0, isOpen_univ, mem_univ Y,
      ⟨EntryWeakProofs.IndependentParameterSourceReserve.zero R⟩, fun _ _ _ _ _ => rfl⟩
  · intro R Y _
    exact ⟨univ, fun _ _ _ => 0, isOpen_univ, mem_univ Y,
      ⟨EntryWeakProofs.IndependentParameterSourceReserve.zero R⟩, fun _ _ _ _ _ => rfl⟩
  · intro t _ Y _ z
    simp only [sub_self, integral_zero]

/-- Positive chart jets are invariant under an affine lattice translation. -/
theorem native_quasiperiodic_positive_jet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Vec 2 → V) (δ : Vec 2) (v : V)
    (hf : ∀ y, f (y + δ) = f y + v) (n : ℕ) (hn : 0 < n) (x : Vec 2) :
    iteratedFDeriv ℝ n f (x + δ) = iteratedFDeriv ℝ n f x := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [← iteratedFDeriv_comp_add_right]
  have he : (fun y => f (y + δ)) = fun y => f y + v := funext hf
  rw [he, iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  have hd : (fun y => fderiv ℝ (fun z => f z + v) y) = fun y => fderiv ℝ f y := by
    funext y
    exact fderiv_add_const v
  rw [hd]

/-- Compact all-order native spatial budgets become global coefficient budgets by
periodicity; the coefficient constant is uniform over the full closed time window. -/
theorem native_uniform_coeff_of_spatial_data
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace V] [MeasurableSpace W]
    {a b : ℝ} {A : ℝ → Vec 2 → V →L[ℝ] W}
    (Q : ∀ R X, IsCompact X → NativeCompactSpatialBudget a b R X A)
    (hA : Measurable (fun p : {p : ℝ × Vec 2 // p.1 ∈ Icc a b} => A p.1.1 p.1.2))
    (hp : ∀ t ∈ Icc a b, AVenhance.IsZ2Periodic (A t)) (K : ℕ) :
    NativeUniformCoeff a b K A := by
  refine ⟨fun t ht => (Q K ∅ isCompact_empty).smooth t ht,
    hp, hA, fun n _hn => ?_⟩
  obtain ⟨B, _hB, hb⟩ := (Q n (Icc (0 : Vec 2) 1) isCompact_Icc).bound
  refine ⟨B, fun t ht x => ?_⟩
  have hs : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) (A t) :=
    (Q (n + 1) (Icc (0 : Vec 2) 1) isCompact_Icc).smooth t ht
  have hper : AVenhance.IsZ2Periodic (iteratedFDeriv ℝ n (A t)) := by
    intro l y
    rw [← iteratedFDeriv_comp_add_right]
    have he : (fun z => A t (z + AVenhance.latticeShift l)) = A t :=
      funext (hp t ht l)
    rw [he]
  exact native_periodic_norm_le_of_cube _
    (hs.continuous_iteratedFDeriv (by exact_mod_cast Nat.le_succ n)) hper B
    (fun y hy => hb t ht y (by
      constructor
      · intro i; exact (hy i (Set.mem_univ i)).1.le
      · intro i; exact (hy i (Set.mem_univ i)).2.le)) x

local instance nativeKernelMultilinearMeasurableSpace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) :
    MeasurableSpace (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) V) := borel _
local instance nativeKernelMultilinearBorelSpace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) :
    BorelSpace (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) V) := ⟨rfl⟩
section ActualNativeCoefficients
open AVRegularity.CycleComparison.Coarse
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {F : Frame D hr Dm bw j₀}

/-- The stored Hilbert coefficient sequence is the same native path sum on its
entire cell window, at the menu's own length and all stored degrees. -/
theorem native_input_coefficients_eq_paths (hi : NativeInput F) (p : OddSlot) :
    ∀ g ≤ F.depth, ∀ n, Uniqueness.CoeffEq (F.CcT p.1)
      (nativeStagePathCandidate hi.stage F.depth p)
      (D.slotStart F.G.level p.1 / D.cellScaleSq F.G.level)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.G.level) /
        D.cellScaleSq F.G.level) g n := by
  have hc := F.lift.1 p.1 p.2
  rw [← hi.level, ← hi.menuN] at hc
  have hA : (F.G.actual p).1 = nativeChain F.G.level p.1 := hi.stage.natural.2.2.1 p
  rw [← hA] at hc
  have hX : F.Mn.N + 2 + Dm ≤ F.sX := by
    rw [hi.menuN]
    have := Nat.le_max_left (F.N + 2) (2 * F.p)
    have := hi.slow
    omega
  have hZ : F.Mn.N + 2 + Dm ≤ F.sZ := by
    rw [hi.menuN]
    have := Nat.le_max_left (F.N + 2) (2 * F.p)
    have := hi.fast
    omega
  exact native_stage_path_decomposition hi.stage p F.depth F.sX F.sZ hX hZ (F.CcT p.1) hc

/-- The literal complete lift has the spatial reserve supplied by its prepared
input. All coefficient orders are taken at the actual menu length. -/
theorem native_input_lifted_spatial_contDiff (hi : NativeInput F)
    (r : ℕ) (hr : r + F.N ≤ F.Naux - 2 * F.p)
    (t : ℝ) (ht : t ∈ Icc F.tp F.tf) (v : CompIn F.G.comps) :
    ContDiff ℝ (r : ℕ∞) (fun x => F.uh t x v) := by
  classical
  have hc : 0 < D.cellScaleSq F.m := EntryWeakProofs.weakData_cellScaleSq_pos
    D hi.stage.base hi.stage.profile hi.stage.band F.m
  have hclock : D.cellScaleSq F.m * ((D.cellScaleSq F.m)⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  have ha : ContDiff ℝ ((r + F.N : ℕ) : ℕ∞) (F.aRep t) := by
    apply contDiff_pi.mpr
    intro u
    exact (F.lift.2.1 u t ht).2.2.1.of_le (Nat.cast_le.mpr hr)
  unfold Frame.uh menuLiftedRep gluedLift
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply ContDiff.sum
  intro j hj
  by_cases hw : ocCutoff D.α D.q D.Λ F.m j t = 0
  · simp only [hw, zero_smul]
    exact contDiff_const
  have hjodd : Odd j := (Finset.mem_filter.mp hj).2.1
  have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero
    (Construction.Stream.ocTau_pos hi.stage.base : 0 < ocTau D.α D.q D.Λ F.m) hw
  have htcell : (D.cellScaleSq F.m)⁻¹ * t ∈
      Icc (D.slotStart F.m j / D.cellScaleSq F.m)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m) := by
    rw [inv_mul_eq_div]
    exact ⟨div_le_div_of_nonneg_right htw.1 hc.le,
      div_le_div_of_nonneg_right htw.2 hc.le⟩
  apply ContDiff.const_smul
  rw [FullLift.pulsePhysicalLift_freeze_time, hclock]
  apply FullLift.pulsePhysicalLift_static_contDiff_of_boxes _ _ _ _ _ _ _ _ _ _ _ _ ha
    ((CycleReference.streamFlow_spatial_smooth (D.hΦ (F.m - 1))
      t (D.slotAnchor F.m j)).of_le (by simp))
    ((CycleReference.streamFlow_spatial_smooth (D.hΦ (F.m - 1))
      (D.slotAnchor F.m j) t).of_le (by simp))
  intro hh hhh n _hn m _hm α u w
  have he := native_input_coefficients_eq_paths hi ⟨j, hjodd⟩ hh hhh n
  rw [hi.level] at he
  have heq : (fun X z => F.CcT j hh n m α ((D.cellScaleSq F.m)⁻¹ * t) X z u w) =
      fun X z => nativeStagePathCandidate hi.stage F.depth ⟨j, hjodd⟩
        hh n m α ((D.cellScaleSq F.m)⁻¹ * t) X z u w := by
    funext X z
    exact congrFun (congrFun (congrFun (congrFun (he _ htcell m α) X) z) u) w
  rw [heq]
  apply Weighted.isBoxSmooth_of_joint_contDiff
  apply native_stage_path_candidate_joint_contDiff hi.stage F.depth ⟨j, hjodd⟩
    (r + r) hh hhh n m α u w
  rw [hi.level]
  exact htcell

/-- The stored full sequence inherits its physical slow lattice from the native
metric and sources by qualitative uniqueness on the whole slow space. -/
theorem native_input_coefficient_slow_shift (hi : NativeInput F) (p : OddSlot)
    (hρ : F.Mn.lenFactor * liftLength D F.m ≠ 0)
    (l : Fin 2 → ℤ) (hh : ℕ) (hhh : hh ≤ F.depth) (n m : ℕ)
    (α : DerivativeWord2 m) (t : ℝ)
    (ht : t ∈ Icc (D.slotStart F.m p.1 / D.cellScaleSq F.m)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m))
    (X z : Vec 2) (v u : CompIn F.G.comps) :
    F.CcT p.1 hh n m α t (X + (F.Mn.lenFactor * liftLength D F.m)⁻¹ •
      AVenhance.latticeShift l) z v u = F.CcT p.1 hh n m α t X z v u := by
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let a := D.slotStart F.m p.1 / D.cellScaleSq F.m
  let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m
  let Q := familyLiftData D F.m p.1 (nativeChain F.m p.1) ρ
    (F.G.fam.fiber p (F.G.actual p))
  let T := ρ⁻¹ • AVenhance.latticeShift l
  have hs : IsLiftSequence Q F.sX F.sZ a b F.N F.depth (F.CcT p.1) := F.lift.1 p.1 p.2
  have hlevel : 1 ≤ F.m := by have := hi.stage.level; rw [hi.level] at this; omega
  have hmetric : ∀ s Y i j, Q.G s (Y + T) i j = Q.G s Y i j := by
    intro s Y i j
    exact congrFun (congrFun (FullLift.native_familyLiftData_metric_shift D F.m hlevel p.1
      hρ (F.G.fam.fiber p (F.G.actual p)) l s Y) i) j
  have htorus := GenStage.isTorusCompatible_of_shiftInvariant hi.stage.natural hi.shift
  have hedge : ∀ v' u' d, ∀ γ ∈ Q.edge v' u' d, ∀ β s Y w,
      γ.coeff β s (Y + T) w = γ.coeff β s Y w := by
    intro v' u' d γ hγ β s Y w
    have hγ' : γ ∈ (familyLiftData D F.G.level p.1 (nativeChain F.G.level p.1) ρ
        (F.G.fam.fiber p (F.G.actual p))).edge v' u' d := by
      simpa only [Q, hi.level] using hγ
    exact FullLift.native_familyLiftData_edge_coeff_shift F.G htorus p hρ l
      v' u' d γ hγ' β s Y w
  have hshift := CycleComparison.LiftMeanEntrywise.isLiftSequence_slowShift Q
    F.sX F.sZ a b F.N F.depth (F.CcT p.1) hs T hmetric hedge
  have hu := WeakEntryProofs.native_family_lift_coefficients_unique D hi.stage.profile F.m
    p.1 p.2 (nativeChain F.m p.1) ρ (F.G.fam.fiber p (F.G.actual p))
    univ isOpen_univ a b
    (EntryWeakProofs.weakData_lift_window_strict D hi.stage.base hi.stage.profile
      hi.stage.band F.m p.1).le F.N F.depth F.sX F.sZ F.sX F.sZ
    (F.CcT p.1) (CycleComparison.LiftMeanEntrywise.slowShiftSequence T (F.CcT p.1))
    (WeakEntryProofs.liftSequenceOn_of_global univ Q _ _ _ _ _ _ _ hs)
    (WeakEntryProofs.liftSequenceOn_of_global univ Q _ _ _ _ _ _ _ hshift)
  exact (hu hh hhh n m α t ht X (mem_univ X) z v u).symm

/-- The actual-menu complete lift is periodic on its closed observation window.
The period is proved globally, rather than inferred from its cube representative. -/
theorem native_input_lifted_periodic (hi : NativeInput F)
    (t : ℝ) (ht : t ∈ Icc F.tp F.tf) : AVenhance.IsZ2Periodic (F.uh t) := by
  classical
  have hc : 0 < D.cellScaleSq F.m := EntryWeakProofs.weakData_cellScaleSq_pos
    D hi.stage.base hi.stage.profile hi.stage.band F.m
  have hclock : D.cellScaleSq F.m * ((D.cellScaleSq F.m)⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  have htop : F.m - 1 ≤ D.term := by have := hi.stage.top; rw [hi.level] at this; omega
  have hρ : F.Mn.lenFactor * liftLength D F.m ≠ 0 :=
    (mul_pos hi.stage.length_factor (Real.sqrt_pos.mpr
      (mul_pos (CycleReference.bandChain_pos hi.stage.base hi.stage.profile hi.stage.band htop)
        (Construction.Stream.ocTauPP_pos hi.stage.base)))).ne'
  have ha : AVenhance.IsZ2Periodic (F.aRep t) := by
    intro l x
    funext v
    exact (F.lift.2.1 v t ht).2.2.2.1 l x
  obtain ⟨J, hJ⟩ := TorusCompatible.ocEpsilon_inv_natCast D.q D.Λ F.m
  intro l x
  unfold Frame.uh menuLiftedRep gluedLift
  refine Finset.sum_congr rfl fun j hj => ?_
  by_cases hw : ocCutoff D.α D.q D.Λ F.m j t = 0
  · simp only [hw, zero_smul]
  apply congrArg (fun y => ocCutoff D.α D.q D.Λ F.m j t • y)
  have hjodd : Odd j := (Finset.mem_filter.mp hj).2.1
  have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero
    (Construction.Stream.ocTau_pos hi.stage.base : 0 < ocTau D.α D.q D.Λ F.m) hw
  have htcell : (D.cellScaleSq F.m)⁻¹ * t ∈
      Icc (D.slotStart F.m j / D.cellScaleSq F.m)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m) := by
    rw [inv_mul_eq_div]
    exact ⟨div_le_div_of_nonneg_right htw.1 hc.le,
      div_le_div_of_nonneg_right htw.2 hc.le⟩
  rw [FullLift.pulsePhysicalLift_freeze_time, FullLift.pulsePhysicalLift_freeze_time, hclock]
  apply FullLift.pulsePhysicalLift_static_periodic _ _ _ _ _ _ _ _ _ _ _ hρ hJ
    (fun p Y => FullLift.native_flow_latticeShift D _ _ _ p Y)
    (fun p Y => FullLift.native_flow_latticeShift D _ _ _ p Y) ha _ _ l x
  · intro hh hhh n _hn m _hm α p Y z v u
    exact native_input_coefficient_slow_shift hi ⟨j, hjodd⟩ hρ p hh hhh n m α _ htcell Y z v u
  · intro hh hhh n _hn m _hm α Y v u
    exact ((F.lift.1 j hjodd).2.2.2.2.2.1 hh hhh n m α v u _ htcell).2 Y

/-- The literal kernel fields preserve every spatial reserve available to the
complete lift, for arbitrary stage and menu. -/
theorem native_input_lifted_kernel_contDiff (hi : NativeInput F)
    (r : ℕ) (hr : r + F.N ≤ F.Naux - 2 * F.p)
    (v u : CompIn F.G.comps) (γ : F.G.fam.Γ v u)
    (t : ℝ) (ht : t ∈ Icc F.tp F.tf) :
    ContDiff ℝ (r : ℕ∞) ((F.G.kernelOf F.P F.seedK F.freshK v u γ).applyClassical
      F.φ₀ t (fun y => F.uh t y u)) := by
  exact (IterationPassage.Passage.regularKernel_contDiff_periodic hi.smooth hi.support _ t
    (native_input_lifted_spatial_contDiff hi r hr t ht u)
    (fun l x => congrFun (native_input_lifted_periodic hi t ht l x) u)).1

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- On an actual native history the canonical scalar path array needs no
carrier extension: every slow offset is admissible, at the menu's own length. -/
theorem native_stage_path_family_eq_inverse {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G)
    {h : ℕ} (π : StagePath G h) (p : OddSlot) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let A := (G.actual p).1
    let edge := pathEdges G π p (G.actual p)
    let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let Q := familyLiftData D G.level p.1 A ρ edge
    let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ :=
      fun Y => WeakEntryProofs.nativeWindowResponseLinear D hi.profile G.level
        p.1 p.2 A ρ edge 1 le_rfl a b
        (EntryWeakProofs.weakData_lift_window_strict D hi.base hi.profile hi.band G.level p.1).le Y
    StageSuccessor.pathLiftFamily hi.base hi.profile hi.band ρ Mn.N π p.1 A =
      WeakEntryProofs.weakLiftInverseCoefficients Q inv Mn.N := by
  classical
  dsimp only
  have hA : IsAdmissibleChain D bw j₀ G.level p.1 (G.actual p).1 ∧ Odd p.1 :=
    ⟨(G.actual p).2, p.2⟩
  simp only [StageSuccessor.pathLiftFamily, dite_eq_left hA,
    native_actual_ladderOmega_eq_univ hi p]
  funext hh n m α t Y z v u
  simp only [WeakEntryProofs.weakLiftCarrierRestriction, mem_univ, or_true, ite_true]

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- Every used scalar path entry has local time data on the whole slow space.
Degree zero is the fixed initial block; positive degrees use the literal cell RHS. -/
theorem native_stage_path_family_time_data {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G)
    {h : ℕ} (π : StagePath G h) (p : OddSlot)
    (hh n m : ℕ) (hhh : hh ≤ h) (hnN : n ≤ Mn.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : Fin (h + 1)) :
    let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let c := fun t z Y => StageSuccessor.pathLiftFamily hi.base hi.profile hi.band
      (Mn.lenFactor * liftLength D G.level) Mn.N π p.1 (G.actual p).1 hh n m α t Y z v u 1
    ∃ df : ℝ → Vec 2 → Vec 2 → ℝ, NativeLocalTimeData a b univ c df := by
  classical
  dsimp only
  let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
  let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  rw [native_stage_path_family_eq_inverse hi π p]
  by_cases hn : n = 0
  · subst n
    let c₀ : ℝ := (if hh = 0 ∧ m = 0 then
      CycleComparison.Lift.blockIdentityEntry (fun _ : Fin (h + 1) => ℝ) v u else 0) 1
    simp only [WeakEntryProofs.weakLiftInverseCoefficients_zero_degree]
    change ∃ df : ℝ → Vec 2 → Vec 2 → ℝ,
      NativeLocalTimeData a b univ (fun _ _ _ => c₀) df
    refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
    · intro R Y _hY
      exact ⟨univ, fun _ _ _ => c₀, isOpen_univ, mem_univ Y,
        ⟨EntryWeakProofs.IndependentParameterSourceReserve.const R c₀⟩, fun _ _ _ _ _ => rfl⟩
    · intro R Y _hY
      exact ⟨univ, fun _ _ _ => 0, isOpen_univ, mem_univ Y,
        ⟨EntryWeakProofs.IndependentParameterSourceReserve.zero R⟩, fun _ _ _ _ _ => rfl⟩
    · intro t _ht Y _hY z
      simp only [sub_self, integral_zero]
  · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hA : IsAdmissibleChain D bw j₀ G.level p.1 (G.actual p).1 ∧ Odd p.1 :=
      ⟨(G.actual p).2, p.2⟩
    have hd := native_path_coefficient_time_data hi π p.1 (G.actual p).1 hA
      hh n m hhh hn' hnN hm α v u
    dsimp only at hd
    rw [native_actual_ladderOmega_eq_univ hi p] at hd
    exact ⟨_, hd⟩

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] in
/-- The actual full candidate inherits all-order local time data from its finite
scalar paths, with values in the original component operator spaces. -/
theorem native_stage_path_candidate_time_data {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G)
    (H : ℕ) (p : OddSlot) (g : ℕ) (hg : g ≤ H) (n : ℕ) (hn : n ≤ Mn.N)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : CompIn G.comps) :
    let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    ∃ df : ℝ → Vec 2 → Vec 2 → (hr u.1.root →L[ℝ] hr v.1.root),
      NativeLocalTimeData a b univ
        (fun t z Y => nativeStagePathCandidate hi H p g n m α t Y z v u) df := by
  classical
  dsimp only
  let ρ := Mn.lenFactor * liftLength D G.level
  let lam := ρ / D.eps (G.level - 1)
  let F := Providers.PathDecomp.stageFam G (D.cellScaleSq G.level) lam p (G.actual p)
  let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily
    hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
  let Lift := Providers.PathDecomp.stLift G (D.cellScaleSq G.level) lam p (G.actual p) H Cp
  let Arise := Providers.PathDecomp.stArise G (D.cellScaleSq G.level) lam p (G.actual p) H
  let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
  let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let c (q : F.Walk g u v) := fun t z Y =>
    Providers.PathDecomp.topOf Lift Arise g (F.walkDat q) n m α t Y z
  have hc (q : F.Walk g u v) : ∃ df : ℝ → Vec 2 → Vec 2 → ℝ,
      NativeLocalTimeData a b univ (c q) df := by
    have hA : Arise g (F.walkDat q) := ⟨hg, Providers.PathDecomp.stage_walk_path q⟩
    have hA' : Providers.PathDecomp.stArise G (D.cellScaleSq G.level)
        (ρ / D.eps (G.level - 1)) p (G.actual p) H g (F.walkDat q) := hA
    have heL : Lift g (F.walkDat q) = Cp g (Classical.choose hA.2) := by
      simp only [Lift, lam, Providers.PathDecomp.stLift, dite_eq_left hA']
    simp only [c, Providers.PathDecomp.topOf, ite_eq_left hA, Providers.PathDecomp.topArr]
    rw [heL]
    exact native_stage_path_family_time_data hi (Classical.choose hA.2) p
      g n m le_rfl hn hm α (Fin.last g) 0
  choose df hdf using hc
  let L (q : F.Walk g u v) : ℝ →L[ℝ] (hr u.1.root →L[ℝ] hr v.1.root) :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (F.compMap q)
  have hs := NativeLocalTimeData.sum (fun q => (hdf q).map (L q))
  change ∃ df : ℝ → Vec 2 → Vec 2 → (hr u.1.root →L[ℝ] hr v.1.root),
    NativeLocalTimeData a b univ (fun t z Y => ∑ q : F.Walk g u v, c q t z Y • F.compMap q) df
  exact ⟨_, hs⟩

/-- The stored full Hilbert array itself inherits the local all-order time
calculus. Only its values on its own cell window are compared with the paths. -/
theorem native_input_coefficient_time_data (hi : NativeInput F) (p : OddSlot)
    (g n m : ℕ) (hg : g ≤ F.depth) (hn : n ≤ F.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : CompIn F.G.comps) :
    let a := D.slotStart F.m p.1 / D.cellScaleSq F.m
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m
    ∃ df : ℝ → Vec 2 → Vec 2 → (hr u.1.root →L[ℝ] hr v.1.root),
      NativeLocalTimeData a b univ (fun t z Y => F.CcT p.1 g n m α t Y z v u) df := by
  obtain ⟨df, hdf⟩ := native_stage_path_candidate_time_data hi.stage F.depth p g hg
    n (by rw [hi.menuN]; exact hn) m hm α v u
  have he := native_input_coefficients_eq_paths hi p g hg n
  rw [hi.level] at hdf he
  exact ⟨df, hdf.congr_window (fun t ht z Y =>
    (congrFun (congrFun (congrFun (congrFun (he t ht m α) Y) z) v) u).symm)
    (fun _ _ _ _ => rfl)⟩

/-- Physical time data for the stored native coefficient array. The cell-clock
factor is part of the chosen derivative, at the menu's actual cell scale. -/
theorem native_input_coefficient_physical_time_data (hi : NativeInput F) (p : OddSlot)
    (g n m : ℕ) (hg : g ≤ F.depth) (hn : n ≤ F.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : CompIn F.G.comps) :
    let a := D.slotStart F.m p.1
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m)
    ∃ df : ℝ → Vec 2 → Vec 2 → (hr u.1.root →L[ℝ] hr v.1.root),
      NativeLocalTimeData a b univ
        (fun t z Y => F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * t) Y z v u) df := by
  obtain ⟨df, hdf⟩ := native_input_coefficient_time_data hi p g n m hg hn hm α v u
  have hc : 0 < D.cellScaleSq F.m := EntryWeakProofs.weakData_cellScaleSq_pos
    D hi.stage.base hi.stage.profile hi.stage.band F.m
  dsimp only at hdf ⊢
  rw [div_eq_inv_mul, div_eq_inv_mul] at hdf
  exact ⟨_, hdf.time_scale (inv_pos.mpr hc)⟩

/-- All mixed jets of a stored coefficient have one common moving-chart time
rule and are jointly continuous on the closed physical pulse window. -/
theorem native_input_coefficient_mixed_time (hi : NativeInput F) (p : OddSlot)
    (g n m : ℕ) (hg : g ≤ F.depth) (hn : n ≤ F.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : CompIn F.G.comps) :
    let a := D.slotStart F.m p.1
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m)
    let c := fun t z Y => F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * t) Y z v u
    ∃ df : ℝ → Vec 2 → Vec 2 → (hr u.1.root →L[ℝ] hr v.1.root),
      NativeLocalTimeData a b univ c df ∧
      (∀ q (β : DerivativeWord2 q) r (σ : DerivativeWord2 r),
        Continuous (fun p : Icc a b × (Vec 2 × Vec 2) => orderedDerivative σ
          (fun Y => orderedDerivative β (fun z => c p.1 z Y) p.2.1) p.2.2)) ∧
      ∀ᵐ t ∂volume.restrict (Icc a b), ∀ q (β : DerivativeWord2 q) r (σ : DerivativeWord2 r),
        let cw := fun s z Y => orderedDerivative σ (fun Z => orderedDerivative β (fun w => c s w Z) z) Y
        let dw := fun s z Y => orderedDerivative σ (fun Z => orderedDerivative β (fun w => df s w Z) z) Y
        ∀ γ : ℝ → Vec 2 × Vec 2, ∀ V : Vec 2 × Vec 2, HasDerivAt γ V t →
          HasDerivAt (fun s => cw s (γ s).1 (γ s).2)
            (dw t (γ t).1 (γ t).2 +
              fderiv ℝ (fun Z : Vec 2 × Vec 2 => cw t Z.1 Z.2) (γ t) V) t := by
  classical
  dsimp only
  obtain ⟨df, hdf⟩ := native_input_coefficient_physical_time_data hi p g n m hg hn hm α v u
  have hab : D.slotStart F.m p.1 ≤
      (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) := by
    have hw := EntryWeakProofs.weakData_lift_window_strict
      D hi.stage.base hi.stage.profile hi.stage.band F.m p.1
    have hc := EntryWeakProofs.weakData_cellScaleSq_pos
      D hi.stage.base hi.stage.profile hi.stage.band F.m
    exact (div_le_div_iff_of_pos_right hc).mp hw.le
  refine ⟨df, hdf, ?_, ?_⟩
  · intro q β r σ
    exact (hdf.mixed hab isOpen_univ q β r σ).continuous_window hab
  · apply ae_all_iff.mpr
    intro q
    apply ae_all_iff.mpr
    intro β
    apply ae_all_iff.mpr
    intro r
    apply ae_all_iff.mpr
    intro σ
    exact (hdf.mixed hab isOpen_univ q β r σ).moving_chain_rule hab

/-- Each coefficient/chart factor of a physical pulse is an operator on one
stationary full prepared jet, with a common-time derivative and all spatial budgets. -/
theorem native_input_pulse_word_operator_time (hi : NativeInput F) (p : OddSlot)
    (g n m : ℕ) (hg : g ≤ F.depth) (hn : n ≤ F.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (c : OrderedFinpartition m) (v u : CompIn F.G.comps)
    (chart label : ℝ → Vec 2 → Vec 2)
    (hchart : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry chart))
    (hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label)) :
    let ρ := F.Mn.lenFactor * liftLength D F.m
    ∃ L dL : ℝ → Vec 2 →
        ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) (hr u.1.root) →L[ℝ] hr v.1.root,
      NativeUniformTimeData F.tp F.tf L dL ∧
      ∀ t ∈ Icc F.tp F.tf, ∀ x A,
        L t x A = ocCutoff D.α D.q D.Λ F.m p.1 t •
          F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * t)
            (ρ⁻¹ • label t x) ((D.eps F.m)⁻¹ • label t x) v u
            ((c.compAlongOrderedFinpartition A
              (fun i => iteratedFDeriv ℝ (c.partSize i) (fun Y => chart t (ρ • Y))
                (ρ⁻¹ • label t x))) (fun i => basisVec (α (Fin.rev i)))) := by
  classical
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let a := D.slotStart F.m p.1
  let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m)
  have hab : a ≤ b := by
    have hw := EntryWeakProofs.weakData_lift_window_strict
      D hi.stage.base hi.stage.profile hi.stage.band F.m p.1
    have hc := EntryWeakProofs.weakData_cellScaleSq_pos
      D hi.stage.base hi.stage.profile hi.stage.band F.m
    exact (div_le_div_iff_of_pos_right hc).mp hw.le
  obtain ⟨dc, hc⟩ := native_input_coefficient_physical_time_data hi p g n m hg hn hm α v u
  let Γ := fun t x => (((D.eps F.m)⁻¹ • label t x), (ρ⁻¹ • label t x))
  have hΓ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Γ) :=
    ((contDiff_const (c := (D.eps F.m)⁻¹)).smul hlabel).prodMk
      ((contDiff_const (c := ρ⁻¹)).smul hlabel)
  obtain ⟨dC, hC⟩ := (hc.time_clamp hab F.tp F.tf).sample_uniform_time hi.window Γ hΓ
  let C := fun t x => F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * projIcc a b hab t)
    (Γ t x).2 (Γ t x).1 v u
  have hC' : NativeUniformTimeData F.tp F.tf C dC := hC
  let Φ := fun t Y => chart t (ρ • Y)
  let Ψ := fun t x => ρ⁻¹ • label t x
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Φ) :=
    hchart.comp (contDiff_fst.prodMk ((contDiff_const (c := ρ)).smul contDiff_snd))
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Ψ) := (contDiff_const (c := ρ⁻¹)).smul hlabel
  obtain ⟨J, hJ, heJ⟩ := native_pullback_word_smooth_operator (V := hr u.1.root) α c Φ Ψ hΦ hΨ
  have hJt := native_smooth_uniform_time_data J hJ (a := F.tp) (b := F.tf)
  have hComp := hC'.bilinear hJt
    (Z := ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) (hr u.1.root) →L[ℝ] hr v.1.root)
    (ContinuousLinearMap.compL ℝ
    (ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) (hr u.1.root))
    (hr u.1.root) (hr v.1.root))
  let cut := fun t (_x : Vec 2) => ocCutoff D.α D.q D.Λ F.m p.1 t
  have hcut : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry cut) :=
    (CycleReference.ocCutoff_contDiff hi.stage.base p.1).comp contDiff_fst
  let nativePulseOperatorNormedSpace : NormedSpace ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) (hr u.1.root) →L[ℝ] hr v.1.root) := inferInstance
  let nativePulseOperatorBoundedSMul : IsBoundedSMul ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) (hr u.1.root) →L[ℝ] hr v.1.root) :=
    IsBoundedSMul.of_norm_smul_le (α := ℝ)
      (β := ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) (hr u.1.root) →L[ℝ] hr v.1.root)
      (fun r x => NormedSpace.norm_smul_le r x)
  have hw := (native_smooth_uniform_time_data cut hcut (a := F.tp) (b := F.tf)).bilinear hComp
    (Z := ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) (hr u.1.root) →L[ℝ] hr v.1.root)
    (ContinuousLinearMap.lsmul (E := ContinuousMultilinearMap ℝ
      (fun _ : Fin c.length => Vec 2) (hr u.1.root) →L[ℝ] hr v.1.root) ℝ ℝ)
  refine ⟨_, _, hw, ?_⟩
  intro t ht x A
  simp only [ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, smul_apply]
  change ocCutoff D.α D.q D.Λ F.m p.1 t • C t x (J t x A) = _
  by_cases hz : ocCutoff D.α D.q D.Λ F.m p.1 t = 0
  · simp only [hz, zero_smul]
  · have htw : t ∈ Icc a b := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero
      (Construction.Stream.ocTau_pos hi.stage.base) hz
    rw [heJ]
    dsimp only [C, Γ, Φ, Ψ]
    rw [projIcc_of_mem hab htw]

/-- A pulse's stationary-jet operator has global periodic coefficient budgets. -/
theorem native_input_pulse_word_operator_coeff (hi : NativeInput F) (p : OddSlot)
    (g n m : ℕ) (hg : g ≤ F.depth) (hn : n ≤ F.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (c : OrderedFinpartition m) (v u : CompIn F.G.comps)
    (chart label : ℝ → Vec 2 → Vec 2)
    (hchart : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry chart))
    (hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label))
    (hcper : ∀ t l y, chart t (y + AVenhance.latticeShift l) = chart t y + AVenhance.latticeShift l)
    (hlper : ∀ t l y, label t (y + AVenhance.latticeShift l) = label t y + AVenhance.latticeShift l) :
    let ρ := F.Mn.lenFactor * liftLength D F.m
    ∃ L : ℝ → Vec 2 →
        ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) (hr u.1.root) →L[ℝ] hr v.1.root,
      (∀ K, NativeUniformCoeff F.tp F.tf K L) ∧
      ∀ t ∈ Icc F.tp F.tf, ∀ x A,
        L t x A = ocCutoff D.α D.q D.Λ F.m p.1 t •
          F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * t)
            (ρ⁻¹ • label t x) ((D.eps F.m)⁻¹ • label t x) v u
            ((c.compAlongOrderedFinpartition A
              (fun i => iteratedFDeriv ℝ (c.partSize i) (fun Y => chart t (ρ • Y))
                (ρ⁻¹ • label t x))) (fun i => basisVec (α (Fin.rev i)))) := by
  classical
  let ρ := F.Mn.lenFactor * liftLength D F.m
  have htop : F.m - 1 ≤ D.term := by have := hi.stage.top; rw [hi.level] at this; omega
  have hρ : ρ ≠ 0 :=
    (mul_pos hi.stage.length_factor (Real.sqrt_pos.mpr
      (mul_pos (CycleReference.bandChain_pos hi.stage.base hi.stage.profile hi.stage.band htop)
        (Construction.Stream.ocTauPP_pos hi.stage.base)))).ne'
  obtain ⟨L, dL, hL, heL⟩ := native_input_pulse_word_operator_time hi p g n m hg hn hm α c v u
    chart label hchart hlabel
  have hper : ∀ t ∈ Icc F.tp F.tf, AVenhance.IsZ2Periodic (L t) := by
    intro t ht l x
    ext A
    rw [heL t ht, heL t ht]
    by_cases hz : ocCutoff D.α D.q D.Λ F.m p.1 t = 0
    · simp only [hz, zero_smul]
    have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero
      (Construction.Stream.ocTau_pos hi.stage.base : 0 < ocTau D.α D.q D.Λ F.m) hz
    have hclock := EntryWeakProofs.weakData_cellScaleSq_pos
      D hi.stage.base hi.stage.profile hi.stage.band F.m
    have htcell : (D.cellScaleSq F.m)⁻¹ * t ∈
        Icc (D.slotStart F.m p.1 / D.cellScaleSq F.m)
          ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m) := by
      rw [inv_mul_eq_div]
      exact ⟨div_le_div_of_nonneg_right htw.1 hclock.le,
        div_le_div_of_nonneg_right htw.2 hclock.le⟩
    have hj (i : Fin c.length) :
        iteratedFDeriv ℝ (c.partSize i) (fun Y => chart t (ρ • Y))
          (ρ⁻¹ • label t x + ρ⁻¹ • AVenhance.latticeShift l) =
        iteratedFDeriv ℝ (c.partSize i) (fun Y => chart t (ρ • Y)) (ρ⁻¹ • label t x) := by
      apply native_quasiperiodic_positive_jet _ _ (AVenhance.latticeShift l)
      · intro Y
        rw [CycleComparison.Assembly.smul_add_inv_smul hρ, hcper]
      · exact c.partSize_pos i
    obtain ⟨J, hJ⟩ := TorusCompatible.ocEpsilon_inv_natCast D.q D.Λ F.m
    rw [hlper, smul_add, smul_add]
    dsimp only [ρ] at hj
    simp_rw [hj]
    rw [native_input_coefficient_slow_shift hi p hρ l g hg n m α _ htcell]
    change (D.eps F.m)⁻¹ = (J : ℝ) at hJ
    rw [hJ, TorusCompatible.natCast_smul_latticeShift]
    have hfast := ((F.lift.1 p.1 p.2).2.2.2.2.2.1 g hg n m α v u _ htcell).2
      (ρ⁻¹ • label t x) (fun i => (J : ℤ) * l i) ((J : ℝ) • label t x)
    dsimp only [ρ] at hfast
    rw [hfast]
  exact ⟨L, fun K => native_uniform_coeff_of_spatial_data hL.spatial hL.measurable hper K, heL⟩

end ActualNativeCoefficients

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
