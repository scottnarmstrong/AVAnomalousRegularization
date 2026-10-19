-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleReference.TransitionZero
import AVRegularity.CycleJoint.CoupledWeakIdentityIntegralImageAssembly
public import AVRegularity.CycleEvolution.TimeEnergy
import AVRegularity.Velocity.ExistsLimitVelocity
import AVRegularity.Construction.Preservation.Buffer.DoubleCauchyAngleIntegral
import AVRegularity.CycleReference.MeanEnhancementScale
import AVRegularity.CycleComparison.Lift.TruncatedMeanCoefficientRegularity
import AVRegularity.CycleWords.NormalizedProductSquare
import AVRegularity.CycleReference.CoreFlux
public import AVRegularity.Definitions.Construction.Gen.ParShift
public import AVRegularity.CoupledEnergy.Variational.TorusCoupledFluxValue
import AVRegularity.CoupledEnergy.Galerkin.PlainTestedIntegralEquation
public import AVRegularity.CoupledEnergy.Galerkin.IntervalCoefficientSub
public import AVRegularity.CycleComparison.Lift.TransverseModeFactor
public import AVRegularity.KernelEnergy.TorusMultiplierTime
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDimFlux
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsSmoothOn
public import AVenhance.Infra.FaaDiBruno.Seminorm
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Countable
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! The molecular buffer's adjacent-order factorial energy estimate. -/

theorem factorialWeight_succ_mul (ρ : ℝ) (j : ℕ) :
    factorialWeight ρ (j + 1) * ((j + 1 : ℕ) : ℝ) ^ 2 =
      ρ ^ 2 * factorialWeight ρ j := by
  unfold factorialWeight
  rw [Nat.factorial_succ, Nat.cast_mul, mul_pow, show 2 * (j + 1) = 2 * j + 2 by omega,
    pow_add]
  field_simp

theorem factorialWeight_succ_le (ρ : ℝ) (j : ℕ) :
    factorialWeight ρ (j + 1) ≤ ρ ^ 2 * factorialWeight ρ j := by
  rw [← factorialWeight_succ_mul ρ j]
  exact le_mul_of_one_le_right (factorialWeight_nonneg ρ _) (by
    have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
    exact one_le_pow₀ hj)

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  {μ : Measure (Vec 2)} {K : ℕ}

theorem factorialNormSq_zero_eq_derivative (ρ : ℝ) (D : JetL2 μ 0 E) :
    factorialNormSq ρ D = derivativeNormSq D 0 := by
  unfold factorialNormSq
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, factorialWeight, Nat.mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, one_pow, div_one, one_mul, Fin.sum_univ_zero, add_zero]

theorem factorialNormSq_le_value_add_grad (ρ : ℝ) (D : JetL2 μ (K + 1) E) :
    factorialNormSq ρ D ≤ derivativeNormSq D 0 + ρ ^ 2 * gradFactorialNormSq ρ D := by
  unfold factorialNormSq
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, factorialWeight, Nat.mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, one_pow, div_one, one_mul]
  refine add_le_add (le_refl _) ?_
  unfold gradFactorialNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  change factorialWeight ρ (j.val + 1) * derivativeNormSq D j.succ ≤
    ρ ^ 2 * (factorialWeight ρ j.val * derivativeNormSq D j.succ)
  exact (mul_le_mul_of_nonneg_right (factorialWeight_succ_le ρ j.val)
    (derivativeNormSq_nonneg D j.succ)).trans_eq (mul_assoc _ _ _)

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, MeasurableSpace (h i)]

theorem massNormSq_le_value_add_grad (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 ≤ π i)
    (D : ∀ i, JetL2 μ (K + 1) (h i)) :
    massNormSq ρ π D ≤
      (∑ i, (π i)⁻¹ * derivativeNormSq (D i) 0) + ρ ^ 2 * massGradNormSq ρ π D := by
  unfold massNormSq massGradNormSq
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  exact (mul_le_mul_of_nonneg_left (factorialNormSq_le_value_add_grad ρ (D i))
    (inv_nonneg.mpr (hπ i))).trans_eq (by ring)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.Buffer

/-! The finest wavelength decays faster than the enhanced preparation radius. -/

theorem preparation_radius_gap_pos {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) : 0 < q - (1 + ocC α q) := by
  have h := Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq
  rw [show q - (1 + ocC α q) = q - 1 - ocC α q by ring,
    CycleReference.prepared_radius_exponent_identity hq.1]
  exact add_pos (mul_pos (lt_trans (by norm_num) hq.1) h.1)
    (mul_pos (by norm_num) h.2.1)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Buffer

/-! Birth-law component masses and markers are strictly positive at the actual scales. -/

theorem birth_compMass_pos {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (law : BirthLaw) (c : Comp) : 0 < compMass q Λ law c := by
  apply mul_pos (law.rootMass_pos c.root)
  apply List.prod_pos
  intro x hx
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
  exact mul_pos (div_pos law.cH_pos (by exact_mod_cast law.wordCount_pos))
    (Real.rpow_pos_of_pos (Scales.epsilon_basic (m := e.scale) hq hΛ).1 _)

theorem birth_compMarker_pos {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (law : BirthLaw) (c : Comp) : 0 < compMarker q Λ law c := by
  apply Finset.prod_pos
  intro j _
  exact Real.rpow_pos_of_pos (Scales.epsilon_basic (m := j) hq hΛ).1 _

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
open Filter Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! Preparation error and incoming kernel prices are small at one deep-level threshold. -/

theorem preparation_parent_power_tendsto_zero {q p : ℝ} {Λ : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hp : 0 < p) :
    Tendsto (fun m : ℕ => ocEpsilon q Λ (m - 1) ^ p) atTop (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.comp
    (CycleReference.epsilon_parent_tendsto_zero hq hΛ)
  simpa only [Function.comp_def, Real.zero_rpow hp.ne'] using h

theorem preparation_parameters_eventually_small {q Q τ : ℝ} {Λ : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hQ : 0 < Q) (hτ : 0 < τ) (CQ CI : ℝ) :
    ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      CQ * ocEpsilon q Λ (m - 1) ^ Q ≤ 1 / 8 ∧
      CI * ocEpsilon q Λ (m - 1) ^ τ ≤ 1 / 8 := by
  have herror : Tendsto (fun m : ℕ => CQ * ocEpsilon q Λ (m - 1) ^ Q)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (preparation_parent_power_tendsto_zero hq hΛ hQ)
  have hkernel : Tendsto (fun m : ℕ => CI * ocEpsilon q Λ (m - 1) ^ τ)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (preparation_parent_power_tendsto_zero hq hΛ hτ)
  obtain ⟨n, hn⟩ := eventually_atTop.1
    ((herror.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 8))).and
      (hkernel.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 8))))
  exact ⟨max 2 n, le_max_left _ _, fun m hm => hn m ((le_max_right _ _).trans hm)⟩

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! The actual regularizer hypotheses restrict to a smaller time window. -/

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]

theorem spatialRegularizerTorus_time_restrict {ρ a b c d r : ℝ} {k D : ℕ}
    {C : ℕ → ℝ}
    {S : ℝ → (Lp G 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      Lp G 2 (volume.restrict AVenhance.unitCube)}
    (hS : IsSpatialRegularizerTorus ρ k D a b C r S)
    (hsub : Set.Icc c d ⊆ Set.Icc a b) :
    IsSpatialRegularizerTorus ρ k D c d C r S := by
  refine ⟨?_, fun t ht => hS.2.1 t (hsub ht), hS.2.2.1,
    fun t ht => hS.2.2.2 t (hsub ht)⟩
  intro z
  exact (hS.1 z).comp_measurable
    (measurable_subtype_coe.subtype_mk (h := fun t : Set.Icc c d => hsub t.property))

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Reuse kernel factorial contraction for the variational constant-fiber map. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem variational_mapTorusHk_eq_kernel {K : ℕ} (L : E →L[ℝ] F) (U : TorusHk K E) :
    CoupledEnergy.Variational.mapTorusHk L U = KernelEnergy.mapTorusHk L U := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  rw [CoupledEnergy.Variational.mapTorusHk_jet_eq_compLp,
    KernelEnergy.mapTorusHk_jet_eq_compLp]

theorem variational_map_factorialRoot_le {K : ℕ} (ρ : ℝ) (L : E →L[ℝ] F) (U : TorusHk K E) :
    Real.sqrt (factorialNormSq ρ (CoupledEnergy.Variational.mapTorusHk L U).val) ≤
      ‖L‖ * Real.sqrt (factorialNormSq ρ U.val) := by
  rw [variational_mapTorusHk_eq_kernel]
  have h := Real.sqrt_le_sqrt (KernelEnergy.mapTorusHk_factorialNormSq_le ρ L U)
  simpa only [Real.sqrt_mul (sq_nonneg ‖L‖), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg L)] using h

theorem variational_map_raw_jet_ae {K : ℕ} (L : E →L[ℝ] F) (U : TorusHk K E)
    (a : JetIndex2 K) :
    (CoupledEnergy.Variational.mapTorusHk L U).toFunction.jet a
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => L (U.toFunction.jet a x) := by
  have ho := periodicJetRepresentative_ae (CoupledEnergy.Variational.mapTorusHk L U).val a
  have hm := CoupledEnergy.Variational.mapTorusHk_jet_ae L U a
  have hi := periodicJetRepresentative_ae U.val a
  filter_upwards [ho, hm, hi] with x hx hmx hix
  exact hx.trans (hmx.trans (congrArg L hix.symm))

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Read the first scalar derivative tensor directly from the actual factorial energy. -/

theorem scalar_first_jet_square_integral {K : ℕ} (hK : 1 ≤ K) (U : TorusHk K ℝ) :
    (∑ i : Fin 2, ∫ x in unitCube,
      U.toFunction.jet ⟨⟨1, Nat.lt_succ_of_le hK⟩, fun _ : Fin 1 => i⟩ x ^ 2) =
      derivativeNormSq U.val ⟨1, Nat.lt_succ_of_le hK⟩ := by
  let e : DerivativeWord2 1 ≃ Fin 2 :=
    { toFun := fun a => a 0
      invFun := fun i _ => i
      left_inv := fun a => by funext t; fin_cases t; rfl
      right_inv := fun _ => rfl }
  unfold derivativeNormSq
  rw [Fintype.sum_equiv e _ (fun i : Fin 2 =>
    ‖U.val ⟨⟨1, Nat.lt_succ_of_le hK⟩, fun _ : Fin 1 => i⟩‖ ^ 2)
    (fun a => by
      have he : a = fun _ : Fin 1 => e a := by funext t; fin_cases t; rfl
      exact congrArg (fun w => ‖U.val ⟨⟨1, Nat.lt_succ_of_le hK⟩, w⟩‖ ^ 2) he)]
  apply Finset.sum_congr rfl
  intro i _
  rw [CycleEvolution.lpTwoHilbert_normSq_integral]
  apply integral_congr_ae
  filter_upwards [periodicJetRepresentative_ae U.val
    ⟨⟨1, Nat.lt_succ_of_le hK⟩, fun _ : Fin 1 => i⟩] with x hx
  change periodicJetRepresentative U.val _ x ^ 2 = _
  rw [hx, Real.norm_eq_abs, sq_abs]

theorem scalar_first_jet_scaled_energy {K : ℕ} (hK : 1 ≤ K) (U : TorusHk K ℝ) (ρ : ℝ) :
    ρ ^ 2 * (∑ i : Fin 2, ∫ x in unitCube,
      U.toFunction.jet ⟨⟨1, Nat.lt_succ_of_le hK⟩, fun _ : Fin 1 => i⟩ x ^ 2) ≤
      factorialNormSq ρ U.val := by
  rw [scalar_first_jet_square_integral hK U]
  have h := CycleJointProofs.factorial_component_energy_le ρ U.val
    (⟨1, Nat.lt_succ_of_le hK⟩ : Fin (K + 1))
  simpa only [factorialWeight, Nat.mul_one, Nat.factorial_one, Nat.cast_one, one_pow,
    div_one] using h

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.Buffer

/-! The literal OC stream has a velocity jet budget with constants independent of the order. -/

theorem actual_stream_drift_snorm
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 1 ≤ m)
    (t : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    FaaDiBruno.snorm (streamVel (Φ m) t) j (256 * (ocEpsilon q Λ m)⁻¹) ≤
      ENNReal.ofReal (8192 * ocA α q Λ m * ocEpsilon q Λ m) := by
  obtain ⟨C, _hC, hreg⟩ := Velocity.stream_regularity α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ
  have hφ := Velocity.streamSeq_admissible hζ hΛ hΦ m
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) :=
    hφ.1.comp (contDiff_const.prodMk contDiff_id)
  have he : 0 < ocEpsilon q Λ m := (Scales.epsilon_basic hq.1 hΛ).1
  have ha : 0 < ocA α q Λ m := Real.rpow_pos_of_pos he _
  have hb := (hreg m hm t).2.1 (j + 1) (by omega)
  rw [Velocity.Port.ExplicitBarNorm.barNorm_eq_snorm (hslice.of_le (by simp))] at hb
  have hinput : FaaDiBruno.snorm (Φ m t) (j + 1) (256 * (ocEpsilon q Λ m)⁻¹) ≤
      ENNReal.ofReal ((2097152 * ocA α q Λ m) *
        (256 * (ocEpsilon q Λ m)⁻¹)⁻¹ ^ 2 *
        (((j : ℝ) + 3) ^ 2 / ((j : ℝ) + 2) ^ 3)) := by
    convert hb using 1
    · norm_num
    · rw [← stream_jet_scale_conversion _ _ _ he.ne']
      norm_num [Nat.cast_add, Nat.cast_one, add_assoc]
  have hv := Velocity.Port.AppB2FieldBounds.streamVel_snorm_le_from_induction (Φ m)
    hφ.1 t j (mul_pos (by norm_num) (inv_pos.mpr he))
    (mul_pos (by norm_num) ha) hinput
  convert hv using 1
  congr 1
  field_simp
  ring

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Fourier forcing coordinates pair only the value carrier, at every Sobolev order. -/

open CoupledEnergy.Galerkin
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] in
theorem plainFluxForcing_truncate (N : ℕ) (r : CoupledFourierModeIndex (h := h) N)
    (i : ι) {k l : ℕ} (hkl : k ≤ l) (f : TorusHk l (PiLp 2 (fun _ : Fin 2 => h i))) :
    plainFluxForcingCLM N r i k (truncateTorusHk hkl f) =
      plainFluxForcingCLM N r i l f := rfl

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory
open AVenhance.Infra.Parabolic.FourierGalerkin AVenhance.Infra.Classical
namespace AVRegularity.Construction.Preservation.Buffer

/-! Reuse normalized real Fourier modes and their exact paired primitive. -/

theorem realFourierModeAmbient_cell_square (N : ℕ) (a : RealFourierIndex N) :
    (∫ x in unitCube, realFourierModeAmbient N a x ^ 2) = 1 := by
  have h := CoupledEnergy.Galerkin.plainScalarMode_cell_orthonormal N
    (realFourierIndexEquivFin N a) (realFourierIndexEquivFin N a)
  simpa only [Equiv.symm_apply_apply, ite_true, pow_two] using h

theorem realFourier_sine_primitive (N : ℕ)
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) (i : Fin 2) (x : Vec 2) :
    spaceGrad (realFourierModeAmbient N (some (p, true))) x i =
      (2 * Real.pi * (representativeFrequency p i : ℝ)) *
        realFourierModeAmbient N (some (p, false)) x := by
  simpa only [realFourierModeIndexSwap] using
    spaceGrad_realFourierModeAmbient N (some (p, true)) i x

/-! A normalized cosine and its sine primitive at any positive integer frequency. -/

def axisFrequency (N : ℕ) (hN : 1 ≤ N) :
    {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N} := by
  refine ⟨((N : ℤ), 0), ?_⟩
  simp only [positiveFrequencyRepresentatives, Finset.mem_filter, symmetricFrequencyBox,
    Finset.mem_product, Finset.mem_Icc, positiveFrequencyPair]
  constructor
  · omega
  · left
    omega

def axisCosine (N : ℕ) (hN : 1 ≤ N) : Vec 2 → ℝ :=
  realFourierModeAmbient N (some (axisFrequency N hN, false))

def axisSine (N : ℕ) (hN : 1 ≤ N) : Vec 2 → ℝ :=
  realFourierModeAmbient N (some (axisFrequency N hN, true))

theorem axisSine_primitive (N : ℕ) (hN : 1 ≤ N) (x : Vec 2) :
    spaceGrad (axisSine N hN) x 0 = (2 * Real.pi * (N : ℝ)) * axisCosine N hN x := by
  simpa [axisSine, axisCosine, representativeFrequency, axisFrequency, pairFrequency] using
    realFourier_sine_primitive N (axisFrequency N hN) 0 x

theorem axisCosine_cell_square (N : ℕ) (hN : 1 ≤ N) :
    (∫ x in unitCube, axisCosine N hN x ^ 2) = 1 :=
  realFourierModeAmbient_cell_square N _

theorem axisSine_cell_square (N : ℕ) (hN : 1 ≤ N) :
    (∫ x in unitCube, axisSine N hN x ^ 2) = 1 :=
  realFourierModeAmbient_cell_square N _

theorem realFourierModeAmbient_abs_le_sqrt_two (N : ℕ)
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) (sine : Bool) (x : Vec 2) :
    |realFourierModeAmbient N (some (p, sine)) x| ≤ Real.sqrt 2 := by
  have hc : ‖Infra.Torus.torusCharacter (-representativeFrequency p) x‖ = 1 := by
    simp [Infra.Torus.torusCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      Infra.Torus.toUnitTorus, Complex.norm_exp, Complex.mul_re]
  cases sine
  · change |Real.sqrt 2 * (Infra.Torus.torusCharacter (-representativeFrequency p) x).re| ≤ _
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans_eq hc)
      (Real.sqrt_nonneg _)).trans_eq (mul_one _)
  · change |Real.sqrt 2 * (Infra.Torus.torusCharacter (-representativeFrequency p) x).im| ≤ _
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans_eq hc)
      (Real.sqrt_nonneg _)).trans_eq (mul_one _)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
open AVenhance.Infra.Parabolic.FourierGalerkin AVenhance.Infra.Classical
namespace AVRegularity.Construction.Preservation.Buffer

/-! The normalized axis cosine has a spatial derivative bound proportional to its frequency. -/

theorem axisCosine_gradient_zero (N : ℕ) (hN : 1 ≤ N) (x : Vec 2) :
    spaceGrad (axisCosine N hN) x 0 = -(2 * Real.pi * (N : ℝ)) * axisSine N hN x := by
  simpa [axisCosine, axisSine, representativeFrequency, axisFrequency, pairFrequency,
    realFourierModeIndexSwap] using
    spaceGrad_realFourierModeAmbient N (some (axisFrequency N hN, false)) 0 x

theorem axisCosine_gradient_one (N : ℕ) (hN : 1 ≤ N) (x : Vec 2) :
    spaceGrad (axisCosine N hN) x 1 = 0 := by
  simpa [axisCosine, representativeFrequency, axisFrequency, pairFrequency] using
    spaceGrad_realFourierModeAmbient N (some (axisFrequency N hN, false)) 1 x

theorem axisCosine_fderiv_norm_le (N : ℕ) (hN : 1 ≤ N) (x : Vec 2) :
    ‖fderiv ℝ (axisCosine N hN) x‖ ≤ (2 * Real.pi * (N : ℝ)) * Real.sqrt 2 := by
  have hell : 0 ≤ 2 * Real.pi * (N : ℝ) := by positivity
  have hg : |spaceGrad (axisCosine N hN) x 0| ≤ (2 * Real.pi * (N : ℝ)) * Real.sqrt 2 := by
    rw [axisCosine_gradient_zero, abs_mul, abs_neg, abs_of_nonneg hell]
    exact mul_le_mul_of_nonneg_left (realFourierModeAmbient_abs_le_sqrt_two N
      (axisFrequency N hN) true x) hell
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hell (Real.sqrt_nonneg _))
  intro w
  have hw : w = w 0 • basisVec 0 + w 1 • basisVec 1 := by
    funext i
    fin_cases i <;> simp [basisVec]
  have hd : fderiv ℝ (axisCosine N hN) x w = w 0 * spaceGrad (axisCosine N hN) x 0 := by
    conv_lhs => rw [hw]
    rw [map_add, map_smul, map_smul]
    change w 0 * spaceGrad (axisCosine N hN) x 0 +
      w 1 * spaceGrad (axisCosine N hN) x 1 = _
    rw [axisCosine_gradient_one, mul_zero, add_zero]
  rw [hd, Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul (norm_le_pi_norm w 0) hg (abs_nonneg _)
    (norm_nonneg w)).trans_eq (mul_comm _ _)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
open AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVRegularity.Construction.Preservation.Buffer

/-! Smooth periodic normalized axis modes are literal admissible material-test profiles. -/

theorem axisCosine_smooth (N : ℕ) (hN : 1 ≤ N) :
    ContDiff ℝ (⊤ : ℕ∞) (axisCosine N hN) :=
  (realFourierModeAmbient_contDiff N _).of_le le_top

theorem axisSine_smooth (N : ℕ) (hN : 1 ≤ N) :
    ContDiff ℝ (⊤ : ℕ∞) (axisSine N hN) :=
  (realFourierModeAmbient_contDiff N _).of_le le_top

theorem axisCosine_periodic (N : ℕ) (hN : 1 ≤ N) :
    IsZ2Periodic (axisCosine N hN) := realFourierModeAmbient_periodic N _

theorem axisSine_periodic (N : ℕ) (hN : 1 ≤ N) :
    IsZ2Periodic (axisSine N hN) := realFourierModeAmbient_periodic N _

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Copy-adapt the existing closed-graph time calculus to the periodic carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torusHk_strong_time_of_jets {K : ℕ} {a b : ℝ}
    (z dz : ℝ → TorusHk K E)
    (h : ∀ α : JetIndex2 K, CycleEvolution.StrongTimeRegularity a b
      (fun t => (z t).val α) (fun t => (dz t).val α)) :
    CycleEvolution.StrongTimeRegularity a b z dz := by
  apply CycleJointProofs.closedSubspace_strong_time (torusHkGraph (E := E) K) z dz
  have hp := CycleJointProofs.strongTime_piLp (fun α t => (z t).val α)
    (fun α t => (dz t).val α) h
  simpa only [WithLp.toLp_ofLp] using hp

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.Buffer

/-! Smooth periodic spacetime fields have uniform spatial jets on compact time windows. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem periodic_compact_time_spatial_jet_bound
    (F : ℝ × Vec 2 → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hper : ∀ t x k, F (t, x + latticeShift k) = F (t, x))
    (T : Set ℝ) (hT : IsCompact T) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ T, ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => F (t, y)) x‖ ≤ C := by
  have hc : Continuous (iteratedFDeriv ℝ j F) :=
    hF.continuous_iteratedFDeriv (by simp)
  have hp (t : ℝ) (x : Vec 2) (k : Fin 2 → ℤ) :
      iteratedFDeriv ℝ j F (t, x + latticeShift k) = iteratedFDeriv ℝ j F (t, x) := by
    have he : (fun y : ℝ × Vec 2 => F ((0, latticeShift k) + y)) = F := by
      funext ⟨t, x⟩
      simpa only [Prod.mk_add_mk, zero_add, add_comm (latticeShift k)] using
        hper t x k
    have hd := congrArg (fun f => iteratedFDeriv ℝ j f (t, x)) he
    rw [iteratedFDeriv_comp_add_left] at hd
    simpa only [Prod.mk_add_mk, zero_add, add_comm (latticeShift k)] using hd
  obtain ⟨C, hC, hb⟩ := CycleReference.spatial_periodic_bound_on_compact_time
    (fun tx => iteratedFDeriv ℝ j F tx) hc hp T hT
  exact ⟨C, hC, fun t ht x =>
    (joint_slice_iteratedFDeriv_norm_le F hF t x j).trans (hb t ht x)⟩

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVenhance.Infra.Flow
open AVRegularity.CycleReference
namespace AVRegularity.Construction.Preservation.Buffer

/-! Actual periodic flows have uniform positive spatial jets on compact time windows. -/

theorem streamFlow_compact_time_positive_jet_bound {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (T : Set ℝ) (hT : IsCompact T) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ T, ∀ x,
      ‖iteratedFDeriv ℝ (j + 1) (fun y => streamFlow φ hφ s y t) x‖ ≤ C := by
  let F : ℝ × Vec 2 → Vec 2 := fun tx => streamFlow φ hφ s tx.2 tx.1
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := (streamFlow_joint_smooth hφ).comp
    (contDiff_const.prodMk (contDiff_snd.prodMk contDiff_fst))
  let H : ℝ × Vec 2 → (Vec 2 →L[ℝ] Vec 2) := fun tx =>
    fderiv ℝ (fun y => F (tx.1, y)) tx.2
  have hH : ContDiff ℝ (⊤ : ℕ∞) H :=
    Velocity.Port.Section2FlowRegularityCore.partialFDeriv_joint_contDiff F hF
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hp : ∀ r, IsZ2Periodic (streamVel φ r) := by
    intro r k y
    simpa using hb.periodic 0 k r y
  have hflow := flow_isFlow _ hφ.vel_continuous hφ.vel_lipschitz
  have hper (t : ℝ) (x : Vec 2) (k : Fin 2 → ℤ) :
      H (t, x + latticeShift k) = H (t, x) := by
    have he : (fun y => streamFlow φ hφ s (y + latticeShift k) t) =
        (fun y => streamFlow φ hφ s y t + latticeShift k) := by
      funext y
      exact flow_lattice_equivariant _ hφ.vel_lipschitz hp hflow y t s k
    have hd := congrArg (fun f : Vec 2 → Vec 2 => fderiv ℝ f x) he
    rw [fderiv_comp_add_right (𝕜 := ℝ)
      (f := fun y => streamFlow φ hφ s y t) (x := x) (latticeShift k),
      fderiv_add_const (𝕜 := ℝ)
      (f := fun y => streamFlow φ hφ s y t) (x := x) (latticeShift k)] at hd
    exact hd
  obtain ⟨C, hC, hbound⟩ := periodic_compact_time_spatial_jet_bound H hH hper T hT j
  refine ⟨C, hC, ?_⟩
  intro t ht x
  have hh := hbound t ht x
  change ‖iteratedFDeriv ℝ j (fderiv ℝ (fun y => streamFlow φ hφ s y t)) x‖ ≤ C at hh
  rw [norm_iteratedFDeriv_fderiv] at hh
  exact hh

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleReference
namespace AVRegularity.Construction.Preservation.Buffer

/-! Uniform coefficient jets remain bounded after the actual natural flow sampling. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem native_flow_pullback_jet_bounds {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (T : Set ℝ) (hT : IsCompact T)
    (A : Set ℝ) (hAT : A ⊆ T) (n : ℕ) (g : ℝ → Vec 2 → V)
    (hg : ∀ t ∈ A, ContDiff ℝ (n : ℕ∞) (g t))
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hb : ∀ t ∈ A, ∀ j ≤ n, ∀ y, ‖iteratedFDeriv ℝ j (g t) y‖ ≤ C j) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧ ∀ t ∈ A, ∀ j ≤ n, ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => g t (streamFlow φ hφ s y t)) x‖ ≤ B j := by
  have hex (j : ℕ) := streamFlow_compact_time_positive_jet_bound hφ s T hT j
  choose D hD hbound using hex
  have hflow (t : ℝ) : ContDiff ℝ (n : ℕ∞) (fun y => streamFlow φ hφ s y t) :=
    ((streamFlow_joint_smooth hφ).comp
      (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))).of_le (by simp)
  exact uniform_composition_jet_bounds A n g (fun t y => streamFlow φ hφ s y t)
    hg (fun t _ => hflow t) C (fun j => D (j - 1)) hC (fun j => hD (j - 1)) hb
    (fun t ht j hj _ x => by
      have hh := hbound (j - 1) t (hAT ht) x
      have he : j - 1 + 1 = j := by omega
      rw [he] at hh
      exact hh)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.Buffer

/-! The actual exponential mode budget pays for every finite fast Fourier derivative. -/

open CycleComparison.Lift

theorem exponential_mode_fourier_jet_budget
    (c : ℤ → ℂ) (a : ℝ) (ha : 0 < a) (M : ℝ)
    (hm : (∑' n : ℤ, ENNReal.ofReal (Real.exp (a * |(n : ℝ)|)) * ‖c n‖ₑ) ≤
      ENNReal.ofReal M) (j : ℕ) :
    (∑' n : ℤ, ‖profileFourierFrequency n ^ j * c n‖ₑ) ≤
      ENNReal.ofReal (((j.factorial : ℝ) * (2 * Real.pi / a) ^ j) * M) := by
  let C := (j.factorial : ℝ) * (2 * Real.pi / a) ^ j
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb (n : ℤ) : ‖profileFourierFrequency n ^ j * c n‖ₑ ≤
      ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (a * |(n : ℝ)|)) * ‖c n‖ₑ) := by
    have hn : ‖profileFourierFrequency n‖ = 2 * Real.pi * |(n : ℝ)| := by
      simp only [profileFourierFrequency, norm_mul, Complex.norm_two, Complex.norm_real,
        Complex.norm_I, Complex.norm_intCast, mul_one, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    have he := frequency_pow_le_exp_weight j (2 * Real.pi) a |(n : ℝ)|
      (by positivity) ha (abs_nonneg _)
    calc
      ‖profileFourierFrequency n ^ j * c n‖ₑ =
          ENNReal.ofReal ((2 * Real.pi * |(n : ℝ)|) ^ j * ‖c n‖) := by
        rw [← ofReal_norm, norm_mul, norm_pow, hn]
      _ ≤ ENNReal.ofReal ((C * Real.exp (a * |(n : ℝ)|)) * ‖c n‖) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right he (norm_nonneg _))
      _ = ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (a * |(n : ℝ)|)) * ‖c n‖ₑ) := by
        rw [mul_assoc, ENNReal.ofReal_mul hC,
          ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_norm]
  have hh := ENNReal.tsum_le_tsum hb
  rw [ENNReal.tsum_mul_left] at hh
  exact hh.trans ((mul_le_mul_right hm (ENNReal.ofReal C)).trans_eq
    (ENNReal.ofReal_mul hC).symm)

theorem exponential_mode_fourier_jet_summable
    (c : ℤ → ℂ) (a : ℝ) (ha : 0 < a) (M : ℝ)
    (hm : (∑' n : ℤ, ENNReal.ofReal (Real.exp (a * |(n : ℝ)|)) * ‖c n‖ₑ) ≤
      ENNReal.ofReal M) (j : ℕ) :
    Summable (fun n : ℤ => profileFourierFrequency n ^ j * c n) := by
  apply Summable.of_norm
  apply tsum_enorm_ne_top_iff_summable_norm.mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (exponential_mode_fourier_jet_budget c a ha M hm j)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CycleReference
namespace AVRegularity.Construction.Preservation.Buffer

/-! A genuine whole native domain slice gives dimensional diagonal regularity. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ} {P : Type*} {Ctx : P → Type*}

theorem dimensional_flux_diagonal_contDiff
    (F : ChartedFamily ι h Dm P Ctx) (dom : F.Domain) (ν e E : ℝ) (hE : E ≠ 0)
    (N : ι → ℕ) (hs : F.IsSmoothOn dom E N) (p : P) (ctx : Ctx p) (t : ℝ)
    (ht : ∀ Y : Vec 2, (t, Y) ∈ dom p ctx)
    (v u : ι) (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) :
    ContDiff ℝ (N v : ℕ) (fun X : Vec 2 => F.dimFlux ν e E p ctx v u γ d I t X (e⁻¹ • X) c) := by
  have hraw := CycleWords.molecular_joint_contDiff F dom E hE N hs p ctx t ht v u γ d I
  have hh := (hraw.comp ((contDiff_id.const_smul E⁻¹).prodMk
    (contDiff_id.const_smul e⁻¹))).const_smul (ν * e ^ (d - 2))
  exact (ContinuousLinearMap.proj c : Vec 2 →L[ℝ] ℝ).contDiff.comp hh

theorem dimensional_flux_flow_sample_contDiff
    (F : ChartedFamily ι h Dm P Ctx) (dom : F.Domain) (ν e E : ℝ) (hE : E ≠ 0)
    (N : ι → ℕ) (hs : F.IsSmoothOn dom E N) (p : P) (ctx : Ctx p) (t : ℝ)
    (ht : ∀ Y : Vec 2, (t, Y) ∈ dom p ctx)
    (v u : ι) (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (s : ℝ) :
    ContDiff ℝ (N v : ℕ) (fun X : Vec 2 => F.dimFlux ν e E p ctx v u γ d I t
      (streamFlow φ hφ s X t) (e⁻¹ • streamFlow φ hφ s X t) c) := by
  have hflow : ContDiff ℝ (N v : ℕ) (fun X : Vec 2 => streamFlow φ hφ s X t) :=
    ((streamFlow_joint_smooth hφ).comp
      (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))).of_le (by simp)
  exact (dimensional_flux_diagonal_contDiff F dom ν e E hE N hs p ctx t ht
    v u γ d I c).comp hflow

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Buffer

/-! Exponential mode budgets control actual classical fast jets at every finite order. -/

open CycleComparison.Lift

theorem exponential_profile_series_jet_norm_le
    (c : ℤ → ℂ) (a : ℝ) (ha : 0 < a) (M : ℝ) (hM : 0 ≤ M)
    (hm : (∑' n : ℤ, ENNReal.ofReal (Real.exp (a * |(n : ℝ)|)) * ‖c n‖ₑ) ≤
      ENNReal.ofReal M) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (profileFourierSeries c) x‖ ≤
      ((j.factorial : ℝ) * (2 * Real.pi / a) ^ j) * M := by
  have hs (k : ℕ) := exponential_mode_fourier_jet_summable c a ha M hm k
  rw [profileFourierSeries_iteratedDeriv j c (fun k _ => hs k)]
  have hsum : (∑' n : ℤ, ‖profileFourierFrequency n ^ j * c n‖) ≤
      ((j.factorial : ℝ) * (2 * Real.pi / a) ^ j) * M := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) (hs j).norm]
    simpa only [ofReal_norm] using exponential_mode_fourier_jet_budget c a ha M hm j
  apply le_trans _ hsum
  exact (by
    simpa only [profileFourierSeries, norm_mul, fourier_apply, Circle.norm_coe, one_mul] using
      norm_tsum_le_tsum_norm
        (profileFourierSeries_term_summable (fun n => profileFourierFrequency n ^ j * c n)
          (hs j) x).norm)

theorem exponential_profile_regular_and_jet_bound
    (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1)
    (a : ℝ) (ha : 0 < a) (M : ℝ) (hM : 0 ≤ M)
    (hm : (∑' n : ℤ, ENNReal.ofReal (Real.exp (a * |(n : ℝ)|)) *
      ‖unitProfileFourierCoeff f n‖ₑ) ≤ ENNReal.ofReal M) (q : ℕ) :
    ContDiff ℝ q f ∧ ∀ j : ℕ, j ≤ q → ∀ x : ℝ,
      ‖iteratedDeriv j f x‖ ≤ ((j.factorial : ℝ) * (2 * Real.pi / a) ^ j) * M := by
  have hs (k : ℕ) := exponential_mode_fourier_jet_summable
    (unitProfileFourierCoeff f) a ha M hm k
  have hzero : Summable (unitProfileFourierCoeff f) := by
    simpa only [pow_zero, one_mul] using hs 0
  have he := profileFourierSeries_reconstruct f hf hp hzero
  rw [← he]
  refine ⟨profileFourierSeries_contDiff q _ (fun k _ => hs k), ?_⟩
  exact fun j _ x => exponential_profile_series_jet_norm_le _ a ha M hM hm j x

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.Buffer

/-! The certified context size bounds each literal final-phase Fourier coefficient. -/

theorem finalPhaseCoeff_enorm_le_ctxModeSup
    (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ)
    (F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ) (mres : ℝ) (h : ℤ)
    (dd : ChainData) (n : ℕ)
    (hdd : ∃ ch : RealChain, IsAdmissibleChain D b j₀ i p ch ∧
      ch.data = dd ∧ ch.children.length = n)
    (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p)
    (x : ChainParamsC n) (hx : x ∈ carrierC D b dd n mres)
    (hreal : ∀ a, (x.2.2 a).im = 0) :
    ‖finalPhaseCoeff (transverseIndex p) (F dd n t) x h‖ₑ ≤
      ctxModeSup D b j₀ i p F mres h := by
  unfold ctxModeSup
  exact le_iSup_of_le dd (le_iSup_of_le n (le_iSup_of_le hdd
    (le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le x
      (le_iSup_of_le hx (le_iSup_of_le hreal le_rfl)))))))

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.Construction.Preservation.Buffer

/-! Use the incoming context certificate's measurable extension on a fixed admissible chain. -/

theorem holExtension_time_measurable {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ}
    {f : GenSort.Sem .ctx}
    {F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ}
    (hF : IsHolExtension D b j₀ i p f F)
    (ch : RealChain) (hch : IsAdmissibleChain D b j₀ i p ch) (ζ : Vec 2) :
    Measurable (fun t : ocPulseWindow D.α D.q D.Λ i p => f t ch ζ) := by
  have hm := Complex.continuous_re.measurable.comp
    (hF.2.1.1 ch.data ch.children.length (ch.paramsC ζ))
  have he : (fun t : ocPulseWindow D.α D.q D.Λ i p =>
      (F ch.data ch.children.length t (ch.paramsC ζ)).re) =
      (fun t : ocPulseWindow D.α D.q D.Λ i p => f t ch ζ) := by
    funext t
    exact congrArg Complex.re (hF.2.2 ch t t.property ζ hch)
  change Measurable (fun t : ocPulseWindow D.α D.q D.Λ i p =>
    (F ch.data ch.children.length t (ch.paramsC ζ)).re) at hm
  rw [he] at hm
  exact hm

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.Buffer

/-! The actual Hilbert drift contraction has a dimension-independent coefficient budget. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem driftFiberCoefficient_eq_sum (v : Vec 2 → Vec 2) (x : Vec 2) :
    driftFiberCoefficient (E := E) v x =
      ∑ k : Fin 2, v x k • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k := by
  ext z
  simp [driftFiberCoefficient_apply]

theorem driftFiberCoefficient_norm_le (v : Vec 2 → Vec 2) {V : ℝ} (hV : 0 ≤ V)
    (hb : ∀ x, ‖v x‖ ≤ V) (x : Vec 2) :
    ‖driftFiberCoefficient (E := E) v x‖ ≤ 2 * V := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hV)
  intro z
  rw [driftFiberCoefficient_apply]
  calc
    _ ≤ ∑ k : Fin 2, ‖v x k • z k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin 2, V * ‖z‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul]
      exact mul_le_mul ((norm_le_pi_norm (v x) k).trans (hb x))
        (PiLp.norm_apply_le z k) (norm_nonneg _) hV
    _ = (2 * V) * ‖z‖ := by simp; ring

theorem driftFiberCoefficient_continuous (v : Vec 2 → Vec 2) (hv : Continuous v) :
    Continuous (driftFiberCoefficient (E := E) v) := by
  change Continuous (fun x => driftFiberCoefficient (E := E) v x)
  simp only [driftFiberCoefficient_eq_sum]
  apply continuous_finsetSum
  intro k _
  exact ((continuous_apply k).comp hv).smul continuous_const

theorem driftFiberCoefficient_joint_continuous {v : ℝ → Vec 2 → Vec 2}
    (hv : Continuous (Function.uncurry v)) :
    Continuous (fun p : ℝ × Vec 2 => driftFiberCoefficient (E := E) (v p.1) p.2) := by
  simp only [driftFiberCoefficient_eq_sum]
  apply continuous_finsetSum
  intro k _
  exact ((continuous_apply k).comp hv).smul continuous_const

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.Buffer

/-! Identify the context's final-phase coefficient with Mathlib's periodic Fourier coefficient. -/

theorem finalPhaseCoeff_eq_fourierCoeffOn
    {n : ℕ} (q : Fin 2) (G : ChainParamsC n → ℂ) (x : ChainParamsC n) (h : ℤ) :
    finalPhaseCoeff q G x h =
      fourierCoeffOn (show (0 : ℝ) < 1 from zero_lt_one)
        (fun s => G (x.1, x.2.1, x.2.2 + fun a => if a = q then (s : ℂ) else 0)) h := by
  rw [finalPhaseCoeff, fourierCoeffOn_eq_integral]
  norm_num only [sub_zero, div_one, one_smul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [fourier_coe_apply]
  simp only [sub_zero, Complex.ofReal_one, div_one, smul_eq_mul, Int.cast_neg]
  rw [mul_comm]
  congr 1
  congr 1
  ring

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.Buffer

/-! The diffusion carrier's value is the same physical gradient readout used by weak tests. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem gradientTensor_value_eq_test_gradient (U : TorusHk 1 E) :
    torusHkValueCLM (torusGradientTensor U) = torusH1GradientL2CLM (E := E) U := by
  apply Lp.ext
  have ht := torusFamilyTensor_value_ae (fun i : Fin 2 => derivativeTorusHk (fun _ : Fin 1 => i) U)
  have hval (i : Fin 2) :
      (derivativeTorusHk (fun _ : Fin 1 => i) U).val (valueIndex2 0) =
        U.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ := by
    rw [derivativeTorusHk_apply]
    have hi : prefixJetIndex (fun _ : Fin 1 => i) (valueIndex2 0) =
        (⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ : JetIndex2 1) := by
      simp [prefixJetIndex, valueIndex2, valueIndex, Fin.append_elim0]
    rw [hi]
  filter_upwards [ht, torusH1GradientL2CLM_ae U] with x hx hg
  change (torusFamilyTensor (fun i : Fin 2 => derivativeTorusHk (fun _ : Fin 1 => i) U)).val
    (valueIndex2 0) x = _
  rw [hx, hg]
  apply PiLp.ext
  intro i
  exact congrArg (fun f : ComponentL2 (volume.restrict unitCube) E => f x) (hval i)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! Native complex base-label slices use the literal holomorphic carrier certificate. -/

theorem native_holomorphic_base_slice
    (D : OCData) (b : ℝ) (hb : 0 < b) (j₀ i : ℕ) (p : ℤ)
    (f : GenSort.Sem .ctx)
    (F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ)
    (hF : IsHolExtension D b j₀ i p f F)
    (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) (z : Fin 2 → ℂ) (hreal : ∀ a, (z a).im = 0) :
    DifferentiableOn ℂ
      (fun Z : Fin 2 → ℂ => F ⟨i - 1, [p]⟩ 0 t
        (Z, (fun k : Fin 0 => Fin.elim0 k), z))
      {Z : Fin 2 → ℂ | (∑ a, |(Z a).im|) <
        (1 + (2 : ℝ) / 4) * (1 / 100) * D.eps (i - 1)} := by
  let g : (Fin 2 → ℂ) → ChainParamsC 0 := fun Z =>
    (Z, (fun k : Fin 0 => Fin.elim0 k), z)
  have hg : Differentiable ℂ g := by
    dsimp [g]
    fun_prop
  have hm : MapsTo g
      {Z : Fin 2 → ℂ | (∑ a, |(Z a).im|) <
        (1 + (2 : ℝ) / 4) * (1 / 100) * D.eps (i - 1)}
      (carrierC D b ⟨i - 1, [p]⟩ 0 2) := by
    intro Z hZ
    refine ⟨hZ, ?_, ?_⟩
    · intro k
      exact Fin.elim0 k
    · change |(z (transverseIndex p)).im| < (3 + (2 : ℝ) / 4) * b
      rw [hreal, abs_zero]
      positivity
  exact (hF.1 ⟨i - 1, [p]⟩ 0 t ht).comp hg.differentiableOn hm

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.Buffer

/-! The final coordinate line is the literal real-chain phase parameter line. -/

theorem native_paramsC_phase_line
    (i : ℕ) (p : ℤ) (Y z : Vec 2) (q : Fin 2) (s : ℝ) :
    (⟨i - 1, [p], Y, []⟩ : RealChain).paramsC (z + s • basisVec q) =
      ((fun a => (Y a : ℂ)), (fun k : Fin 0 => Fin.elim0 k),
        (fun a => (z a : ℂ)) + fun a => if a = q then (s : ℂ) else 0) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext k
      exact Fin.elim0 k
    · funext a
      change ((z + s • basisVec q) a : ℂ) = (z a : ℂ) +
        (if a = q then (s : ℂ) else 0)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add]
      by_cases ha : a = q
      · subst a
        simp only [basisVec_apply, ite_true, mul_one]
      · simp only [basisVec_apply, ite_eq_right ha, mul_zero, Complex.ofReal_zero, add_zero]

/-! Literal slot directions and the affine transverse profile reduction. -/

theorem transverseIndex_eq_slotParallel_rev (p : ℤ) :
    transverseIndex p = (slotParallel p).rev := by
  unfold transverseIndex slotParallel
  split_ifs <;> rfl

theorem complex_real_phase_shift (z : Vec 2) (q : Fin 2) (s : ℝ) :
    (fun a => ((z + s • basisVec q) a : ℂ)) =
      (fun a => (z a : ℂ)) + fun a => if a = q then (s : ℂ) else 0 := by
  funext a
  by_cases ha : a = q
  · subst a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVec_apply,
      ite_true, mul_one, Complex.ofReal_add]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVec_apply,
      ha, ite_false, mul_zero, add_zero]

theorem parallel_invariant_affine_profile {E : Type*}
    (par : Fin 2) (f : Vec 2 → E)
    (hp : ∀ z : Vec 2, ∀ s : ℝ, f (z + s • basisVec par) = f z)
    (z X : Vec 2) (lam : ℝ) :
    f (z + lam • X) = f (z + (lam * X par.rev) • basisVec par.rev) := by
  have he : (z + (lam * X par.rev) • basisVec par.rev) +
      (lam * X par) • basisVec par = z + lam • X := by
    fin_cases par <;> ext a <;> fin_cases a <;>
      simp [basisVec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hh := hp (z + (lam * X par.rev) • basisVec par.rev) (lam * X par)
  rw [he] at hh
  exact hh

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! The rough initial datum controls the finite evolution at its actual starting time. -/

section
open CoupledEnergy.Galerkin AVenhance.Infra.ODE
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem finite_rough_initial_mass_le (N : ℕ) (ρ : ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (f : ∀ i, TorusHk 0 (h i)) {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → CoupledPlainCoefficients (h := h) N →L[ℝ]
      CoupledPlainCoefficients (h := h) N)
    (g y : ℝ → CoupledPlainCoefficients (h := h) N)
    (hy : IsLinearIntegralSolution A g (plainInitialCoefficients N (fun _ => 0) f) a b y) :
    massNormSq ρ π (fun i => (coupledPlainSynthesis N i 0 (y a)).val) ≤
      massNormSq ρ π (fun i => (f i).val) := by
  have ha : y a = plainInitialCoefficients N (fun _ => 0) f := by
    simpa only [intervalIntegral.integral_same, add_zero] using hy a ⟨le_rfl, hab⟩
  rw [ha]
  exact plainInitialCoefficients_mass_le (h := h) N (fun _ => 0) ρ π hπ f
end

/-! The kernel flux is independent of the Sobolev order used to construct its carrier. -/

section
open AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
    {a b ρ ν : ℝ} {k l D : ℕ}

theorem kernelInput_truncate
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
    (Q : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν l D)
    (hkl : k ≤ l) (hC : P.C = Q.C) (hS : P.S = Q.S)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, TorusHk (l + 1) (h i))
    (i j : ι) (α : Γ i j) :
    truncateTorusHk (by omega : k + D - 1 ≤ l + D - 1) (Q.lift t ht V i j α) =
      P.lift t ht (fun i => truncateTorusHk (Nat.add_le_add_right hkl 1) (V i)) i j α := by
  apply TorusHk.ext_value
  change (Q.lift t ht V i j α).val (valueIndex2 (l + D - 1)) = _
  rw [Q.lift_value, P.lift_value, hC, hS]
  rfl

theorem kernelFlux_truncate
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
    (Q : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν l D)
    (hkl : k ≤ l) (hB : P.B = Q.B) (hC : P.C = Q.C) (hS : P.S = Q.S)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, TorusHk (l + 1) (h i)) (i : ι) :
    truncateTorusHk hkl (Q.flux t ht V i) =
      P.flux t ht (fun i => truncateTorusHk (Nat.add_le_add_right hkl 1) (V i)) i := by
  classical
  let Vlo : ∀ i, TorusHk (k + 1) (h i) :=
    fun i => truncateTorusHk (Nat.add_le_add_right hkl 1) (V i)
  have hj : ∀ᵐ x ∂volume.restrict AVenhance.unitCube,
      ∀ j (α : Γ i j) (d : ↥(Finset.Icc 2 D)) (word : DerivativeWord2 (d.1 - 1)),
        (P.lift t ht Vlo i j α).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x =
        (Q.lift t ht V i j α).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro α
    apply ae_all_iff.mpr
    intro d
    apply ae_all_iff.mpr
    intro word
    rw [← kernelInput_truncate P Q hkl hC hS t ht V i j α]
    exact truncateTorusHk_toFunction_jet_ae _ _ _
  have hraw : P.rawFlux t ht Vlo i =ᵐ[volume.restrict AVenhance.unitCube]
      Q.rawFlux t ht V i := by
    filter_upwards [hj] with x hx
    unfold TorusKernelOperator.rawFlux
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro d _
    rw [hB]
    exact congrArg (Q.B i j α d t x) (PiLp.ext (fun word => hx j α d word))
  apply torusCarrier_eq_of_value_ae
  exact (truncateTorusHk_toFunction_jet_ae hkl (Q.flux t ht V i) (valueIndex2 k)).trans
    ((Q.flux_raw t ht V i).trans (hraw.symm.trans (P.flux_raw t ht Vlo i).symm))
end

end AVRegularity.Construction.Preservation.Buffer
end
end
