-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.FamilyMolecularMixedReserve
import AVRegularity.Velocity.ExistsLimitVelocity
import AVRegularity.CycleJoint.PlaneScalarDiffusionDeviationReadout
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleWords.PlaneScalarBlochSurjective
import AVRegularity.CycleEvolution.CellDriftSmoothEnergy
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.CycleReference.TransitionZero
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.CycleEvolution.FibreScalarSeriesHighIncrementBound
public import AVenhance.Statements.Construction.BarNorm
import Homogenization.Sobolev.H1.BasicLemmas
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The bounded slot gives a uniform mixed-jet constant for each positive molecular price. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem familyMolecular_ae_uniform_reserve (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (j : ℕ) (hj : j ≤ J) (p : P) (c : Ctx p) :
    ∀ᵐ t ∂volume, (∀ Y : Vec 2, (t, Y) ∈ dom p c) →
      ∀ a b : ℕ, a + b ≤ K v → ∀ X z,
      (ρ / e) ^ (a + b) * (e / E) ^ a *
        ‖iteratedFDeriv ℝ (j + a) (fun X' =>
          iteratedFDeriv ℝ b (F.flux p c v u γ d I t X') z) X‖ *
          derivativeReserveFactor (ρ / e) (K v) (d - 2) ≤
        (Kmax.factorial : ℝ) ^ 2 * E ^ j *
          molecularRealPrice ν ρ (K v) (d - 2)
            (molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
              (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) := by
  filter_upwards [familyMolecular_ae_mixed_reserve F π hπ K dom ν e E ρ hν he hE hρ
    C J b₀ henv v u γ hγ d hd I j hj p c] with t ht
  intro hdom a b hab X z
  have hh := ht a b hab hdom X z
  have hKv := hK v
  have ha : (a.factorial : ℝ) ≤ (Kmax.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : a ≤ Kmax)
  have hb : (b.factorial : ℝ) ≤ (Kmax.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : b ≤ Kmax)
  have habf : (a.factorial : ℝ) * (b.factorial : ℝ) ≤ (Kmax.factorial : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_le_mul ha hb (by positivity) (by positivity)
  have hid := molecularRealPrice_div_identity ν ρ hν hρ (K v) (d - 2)
    (molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
      (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
  have heq : ((a.factorial : ℝ) * (b.factorial : ℝ) * E ^ j /
      ((ν * ρ ^ (d - 2)) *
        (((K v).factorial : ℝ) / ((K v + (d - 2)).factorial : ℝ)))) *
      (molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)).toReal =
      (a.factorial : ℝ) * (b.factorial : ℝ) * E ^ j *
        molecularRealPrice ν ρ (K v) (d - 2)
          (molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) := by
    rw [← hid]
    ring
  rw [heq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right habf (pow_pos hE j).le)
    (molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! The polynomial moment root controls every scaled displacement. -/

def polynomialMomentRoot (ϖ : ℝ) (z : Vec 2) : ℝ :=
  Real.sqrt (1 + ϖ ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2))

theorem polynomialMomentRoot_one_le (ϖ : ℝ) (z : Vec 2) : 1 ≤ polynomialMomentRoot ϖ z := by
  unfold polynomialMomentRoot
  apply Real.one_le_sqrt.mpr
  exact le_add_of_nonneg_right (by positivity)

theorem scaledNorm_le_polynomialMomentRoot {ϖ : ℝ} (hϖ : 0 ≤ ϖ) (z : Vec 2) :
    ϖ * ‖z‖ ≤ polynomialMomentRoot ϖ z := by
  have hn := AVRegularity.Velocity.velocity_norm_le_vecEuclidean z
  have hs := (sq_le_sq₀ (norm_nonneg z) (Real.sqrt_nonneg _)).mpr hn
  rw [Real.sq_sqrt (vecNormSq_nonneg z)] at hs
  have hsq := mul_le_mul_of_nonneg_left hs (sq_nonneg ϖ)
  unfold polynomialMomentRoot
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  simp only [vecNormSq, vecDot, Fin.sum_univ_two, mul_pow] at hsq ⊢
  nlinarith only [hsq]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Scalar cell coefficient jets retain the original molecular price under arbitrary fast phase. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem familyMolecular_ae_scalar_mixed_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (j : ℕ) (hj : j ≤ J) (p : P) (c : Ctx p) :
    ∀ᵐ t ∂volume, (∀ Y : Vec 2, (t, Y) ∈ dom p c) →
      ∀ (φ : Vec 2) (k : Fin 2) (a b : ℕ), a + b ≤ K v → ∀ X z,
      (ρ / e) ^ (a + b) * |e / E| ^ a *
        ‖iteratedFDeriv ℝ (j + a) (fun X' => iteratedFDeriv ℝ b
          (fun z' => F.flux p c v u γ d I t X' (z' + φ) k) z) X‖ ≤
        (Kmax.factorial : ℝ) ^ 2 * E ^ j *
          molecularRealPrice ν ρ (K v) (d - 2)
            (molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
              (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) /
                derivativeReserveFactor (ρ / e) (K v) (d - 2) := by
  filter_upwards [familyMolecular_ae_uniform_reserve F π hπ K Kmax hK dom ν e E ρ
    hν he hE hρ C J b₀ henv v u γ hγ d hd I j hj p c] with t ht
  intro hdom φ k a b hab X z
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

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Weak derivatives vanish on every open region where the value vanishes. -/

theorem orderedWeakJet_zero_on_open {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {K : ℕ}
    {D : RawJet2 K E} (hD : JetMemL2On Set.univ D)
    (hw : HasOrderedWeakJetOn Set.univ D) {U : Set (Vec 2)} (hU : IsOpen U)
    (h0 : D (valueIndex2 K) =ᵐ[volume.restrict U] 0) :
    ∀ a, D a =ᵐ[volume.restrict U] 0 := by
  have hDU : JetMemL2On U D := by
    intro a
    simpa only [Measure.restrict_univ] using
      (hD a).mono_measure (Measure.restrict_mono (Set.subset_univ U) le_rfl)
  have hz : HasOrderedWeakJetOn U (fun _ : JetIndex2 K => (0 : Vec 2 → E)) := by
    intro j w i e φ hφ hc hs
    simp
  exact orderedWeakJet_unique hU hDU (fun _ => by simp)
    (CycleJointProofs.orderedWeakJet_restrict hw U) hz h0

theorem orderedWeakJet_supported_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {K : ℕ}
    {D : RawJet2 K E} (hD : JetMemL2On Set.univ D)
    (hw : HasOrderedWeakJetOn Set.univ D) {A : Set (Vec 2)} (hA : IsClosed A)
    (h0 : ∀ᵐ x ∂volume, x ∉ A → D (valueIndex2 K) x = 0)
    (q : Vec 2 → ℝ) (C : ℝ) (hq : ∀ x ∈ A, q x ≤ C) :
    ∀ a, ∀ᵐ x ∂volume, D a x ≠ 0 → q x ≤ C := by
  have h0U : D (valueIndex2 K) =ᵐ[volume.restrict Aᶜ] 0 := by
    change ∀ᵐ x ∂volume.restrict Aᶜ, D (valueIndex2 K) x = 0
    rw [ae_restrict_iff' hA.measurableSet.compl]
    exact h0
  have hj := orderedWeakJet_zero_on_open hD hw hA.isOpen_compl h0U
  intro a
  have ha : ∀ᵐ x ∂volume, x ∈ Aᶜ → D a x = 0 :=
    (ae_restrict_iff' hA.measurableSet.compl).mp (hj a)
  filter_upwards [ha] with x hx
  intro hn
  apply hq x
  by_contra hnA
  exact hn (hx hnA)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! A normalized physical radius controls every jet after rescaling a growing profile. -/

theorem polynomialJet_rescaling_le (r j : ℕ) {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (j : ℕ) f) {ϖ ρ A : ℝ}
    (hϖ : 0 ≤ ϖ) (hρ : 0 ≤ ρ) (hscale : ρ * ϖ ≤ 1) (hA : 0 ≤ A)
    (hb : ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A * (1 + ‖x‖) ^ r) (z : Vec 2) :
    ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => f (ϖ • z)) z‖ ≤
      2 ^ r * A * polynomialMomentRoot ϖ z ^ r := by
  have hd := congrFun (iteratedFDeriv_comp_const_smul ϖ hf) z
  rw [hd, norm_smul, Real.norm_of_nonneg (pow_nonneg hϖ j)]
  have hrad : (ρ * ϖ) ^ j ≤ 1 := pow_le_one₀ (mul_nonneg hρ hϖ) hscale
  have hroot : 1 + ‖ϖ • z‖ ≤ 2 * polynomialMomentRoot ϖ z := by
    rw [norm_smul, Real.norm_of_nonneg hϖ]
    linarith [polynomialMomentRoot_one_le ϖ z, scaledNorm_le_polynomialMomentRoot hϖ z]
  calc
    _ = (ρ * ϖ) ^ j * ‖iteratedFDeriv ℝ j f (ϖ • z)‖ := by rw [mul_pow]; ring
    _ ≤ ‖iteratedFDeriv ℝ j f (ϖ • z)‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hrad (norm_nonneg _)
    _ ≤ A * (1 + ‖ϖ • z‖) ^ r := hb _
    _ ≤ A * (2 * polynomialMomentRoot ϖ z) ^ r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hroot r) hA
    _ = _ := by rw [mul_pow]; ring

/-! A polynomial growth majorant used only to justify parameter differentiation. -/

theorem polynomialMomentRoot_growth_le (ϖ : ℝ) (z : Vec 2) :
    polynomialMomentRoot ϖ z ≤ (1 + 2 * |ϖ|) * (1 + ‖z‖) := by
  have h0 := norm_le_pi_norm z (0 : Fin 2)
  have h1 := norm_le_pi_norm z (1 : Fin 2)
  rw [Real.norm_eq_abs] at h0 h1
  have h0sq := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg z)).mpr h0
  have h1sq := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg z)).mpr h1
  rw [sq_abs] at h0sq h1sq
  unfold polynomialMomentRoot
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hs := mul_le_mul_of_nonneg_left (add_le_add h0sq h1sq) (sq_nonneg ϖ)
  rw [← sq_abs ϖ] at hs
  have hpos : 0 ≤ |ϖ| * ‖z‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hsquare : 1 + ϖ ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2) ≤
      (1 + 2 * |ϖ| * ‖z‖) ^ 2 := by
    rw [← sq_abs ϖ]
    nlinarith only [hs, hpos, sq_nonneg (|ϖ| * ‖z‖)]
  have hlin : 1 + 2 * |ϖ| * ‖z‖ ≤ (1 + 2 * |ϖ|) * (1 + ‖z‖) := by
    nlinarith only [abs_nonneg ϖ, norm_nonneg z]
  exact hsquare.trans (pow_le_pow_left₀ (by positivity) hlin 2)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleWords

/-! A smooth representative of a native torus value has the same ordered jets on the cell. -/

theorem torusHigher_smooth_local_readout {K : ℕ} (U : TorusHk K ℂ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (K : ℕ∞) f)
    (hvalue : (torusHkValueCLM U : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f) :
    ∀ a : JetIndex2 K, U.val a =ᵐ[volume.restrict AVenhance.unitCube] orderedDerivative a.2 f := by
  have ho : IsOpen AVenhance.unitCube := by
    simpa only [AVenhance.unitCube] using
      (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo))
  have hmem : JetMemL2On AVenhance.unitCube (smoothPlaneRawJet K f) := by
    intro a
    exact continuous_cell_memLp _ (orderedDerivative_contDiff a.2 0 f
      (hf.of_le (by exact_mod_cast (by omega : 0 + a.1.val ≤ K)))).continuous
  have hweak : HasOrderedWeakJetOn AVenhance.unitCube (smoothPlaneRawJet K f) := by
    intro j w i e
    exact (smoothPlaneRawJet_hasWeakJet_finite K hf j w i e).restrict ho (Set.subset_univ _)
  have h0 : U.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      smoothPlaneRawJet K f (valueIndex2 K) := by
    have h := (periodicJetRepresentative_ae U.val (valueIndex2 K)).trans hvalue
    change periodicJetRepresentative U.val (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      orderedDerivative (Fin.elim0 : DerivativeWord2 0) f
    simpa only [orderedDerivative_zero] using h
  have hall := orderedWeakJet_unique ho U.toFunction.hasPeriodicWeakJet.2.1 hmem
    U.toFunction.hasPeriodicWeakJet.hasWeakJetOn_cell hweak h0
  intro a
  exact (periodicJetRepresentative_ae U.val a).symm.trans (hall a)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! Positive radius converts a finite normalized jet budget into a qualitative growth bound. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalizedPolynomialJet_growth (K p : ℕ) (ρ ϖ A : ℝ)
    (hρ : 0 < ρ) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (f : Vec 2 → E),
      (∀ j ≤ K, ∀ x, ρ ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤
        A * polynomialMomentRoot ϖ x ^ p) →
      ∀ j ≤ K, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B * (1 + ‖x‖) ^ p := by
  classical
  let S : ℝ := ∑ j ∈ Finset.range (K + 1), (ρ ^ j)⁻¹
  let B := A * (1 + 2 * |ϖ|) ^ p * S
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => inv_nonneg.mpr (pow_pos hρ j).le)
  refine ⟨B, mul_nonneg (mul_nonneg hA (by positivity)) hS, ?_⟩
  intro f hf j hj x
  have hs : (ρ ^ j)⁻¹ ≤ S := Finset.single_le_sum
    (fun k _ => inv_nonneg.mpr (pow_pos hρ k).le)
    (Finset.mem_range.mpr (by omega))
  have hp := pow_le_pow_left₀ (zero_le_one.trans (polynomialMomentRoot_one_le ϖ x))
    (polynomialMomentRoot_growth_le ϖ x) p
  have hh : ‖iteratedFDeriv ℝ j f x‖ ≤
      (A * polynomialMomentRoot ϖ x ^ p) / ρ ^ j :=
    (le_div_iff₀ (pow_pos hρ j)).mpr (by simpa only [mul_comm] using hf j hj x)
  calc
    _ ≤ (A * ((1 + 2 * |ϖ|) * (1 + ‖x‖)) ^ p) / ρ ^ j :=
      hh.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hA) (pow_pos hρ j).le)
    _ ≤ B * (1 + ‖x‖) ^ p := by
      rw [div_eq_mul_inv, mul_pow]
      dsimp only [B]
      have hn : 0 ≤ A * (1 + 2 * |ϖ|) ^ p * (1 + ‖x‖) ^ p := by positivity
      convert mul_le_mul_of_nonneg_left hs hn using 1 <;> ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus
namespace AVRegularity.CycleWords

/-! The actual Bloch transform intertwines all continuous periodic scalar multipliers. -/

local instance planeBlochContinuousMultiplierMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

def planeBlochSymbolLeft (a : Vec 2) (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    C(UnitAddTorus (Fin 2), ℂ) →L[ℂ] Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a 1)) :=
  (planeScalarBlochComplexIsometry a 1 (by norm_num)).toContinuousLinearMap.comp
    ((ContinuousLinearMap.apply ℂ (Lp ℂ 2 (volume : Measure (Vec 2))) f).comp
      planePeriodicSymbolMultiplication)

def planeBlochSymbolRight (a : Vec 2) (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    C(UnitAddTorus (Fin 2), ℂ) →L[ℂ] Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a 1)) :=
  (ContinuousLinearMap.apply ℂ
    (Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a 1)))
    (planeScalarBlochTransform a 1 (by norm_num) f)).comp
      (scalarTorusSymbolMultiplication.compLpL₂ 2 (volume.restrict (planeFrequencyCell a 1)))

theorem planeBloch_continuousMultiplier (a : Vec 2)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) (b : C(UnitAddTorus (Fin 2), ℂ)) :
    planeScalarBlochTransform a 1 (by norm_num) (planePeriodicSymbolMultiplication b f) =
      (scalarTorusSymbolMultiplication b).compLp
        (planeScalarBlochTransform a 1 (by norm_num) f) := by
  have hmaps : planeBlochSymbolLeft a f = planeBlochSymbolRight a f := by
    apply scalarTorusFourierModeCLM_ext
    intro m
    change planeScalarBlochTransform a 1 (by norm_num)
      (planePeriodicSymbolMultiplication (mFourier m) f) =
      (scalarTorusSymbolMultiplication (mFourier m)).compLp
        (planeScalarBlochTransform a 1 (by norm_num) f)
    rw [planePeriodicSymbolMultiplication_mode]
    apply Lp.ext
    filter_upwards [planeBloch_integerModulation_ae a m f,
      (scalarTorusSymbolMultiplication (mFourier m)).coeFn_compLp
        (planeScalarBlochTransform a 1 (by norm_num) f)] with θ h₁ h₂
    rw [h₂, scalarTorusSymbolMultiplication_mode]
    exact h₁
  exact congrArg (fun L => L b) hmaps

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Measurable full-measure extensions enforce actual normalized jet budgets at every time. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]

theorem normalizedCoefficient_measurable_extension (K p : ℕ) (ρ ϖ A : ℝ)
    (hρ : 0 < ρ) (hA : 0 ≤ A) (μ : Measure ℝ)
    (c : ℝ → Vec 2 → E) (hm : ∀ x, Measurable (fun t => c t x))
    (hc : ∀ t, ContDiff ℝ (K : ℕ) (c t))
    (hb : ∀ᵐ t ∂μ, ∀ j ≤ K, ∀ x, ρ ^ j * ‖iteratedFDeriv ℝ j (c t) x‖ ≤
      A * polynomialMomentRoot ϖ x ^ p) :
    ∃ c' : ℝ → Vec 2 → E,
      (∀ x, Measurable (fun t => c' t x)) ∧
      (∀ t, ContDiff ℝ (K : ℕ) (c' t)) ∧
      (∀ t j, j ≤ K → ∀ x, ρ ^ j * ‖iteratedFDeriv ℝ j (c' t) x‖ ≤
        A * polynomialMomentRoot ϖ x ^ p) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ t j, j ≤ K → ∀ x,
        ‖iteratedFDeriv ℝ j (c' t) x‖ ≤ B * (1 + ‖x‖) ^ p) ∧
      ∀ᵐ t ∂μ, c' t = c t := by
  classical
  obtain ⟨s, hs, hsg, hsae⟩ := Weighted.exists_measurable_good_times μ
    (fun t => ∀ j ≤ K, ∀ x, ρ ^ j * ‖iteratedFDeriv ℝ j (c t) x‖ ≤
      A * polynomialMomentRoot ϖ x ^ p) hb
  let c' := fun t x => if t ∈ s then c t x else 0
  have hb' : ∀ t j, j ≤ K → ∀ x, ρ ^ j * ‖iteratedFDeriv ℝ j (c' t) x‖ ≤
      A * polynomialMomentRoot ϖ x ^ p := by
    intro t j hj x
    by_cases ht : t ∈ s
    · simpa only [c', ite_eq_left ht] using hsg t ht j hj x
    · simp only [c', ite_eq_right ht]
      simpa using (show ρ ^ j * ‖iteratedFDeriv ℝ j (fun _ : Vec 2 => (0 : E)) x‖ ≤
        A * polynomialMomentRoot ϖ x ^ p by
          simp; exact mul_nonneg hA (pow_nonneg
            (zero_le_one.trans (polynomialMomentRoot_one_le ϖ x)) p))
  refine ⟨c', fun x => (hm x).piecewise hs measurable_const, ?_, hb', ?_, ?_⟩
  · intro t
    by_cases ht : t ∈ s
    · simpa only [c', ite_eq_left ht] using hc t
    · simpa only [c', ite_eq_right ht] using
        (contDiff_const : ContDiff ℝ (K : ℕ) (fun _ : Vec 2 => (0 : E)))
  · obtain ⟨B, hB, hBg⟩ := normalizedPolynomialJet_growth (E := E) K p ρ ϖ A hρ hA
    exact ⟨B, hB, fun t => hBg (c' t) (hb' t)⟩
  · filter_upwards [hsae] with t ht
    funext x
    simp only [c', ite_eq_left ht]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The literal Bloch quadratic mass has a contrast-independent frequency-square bound. -/

theorem scaledMetricQuad_norm_le (η : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (ξ : Fin 2 → ℂ) (t : ℝ) :
    ‖∑ j : Fin 2, ∑ k : Fin 2, (G t j k : ℂ) * ((Real.sqrt η : ℂ) * ξ j) *
      ((Real.sqrt η : ℂ) * ξ k)‖ ≤ 8 * fibreNorm ξ ^ 2 := by
  rw [fibreBloch_metric_quadratic η hη0 (G t) ξ, norm_mul]
  have hηn : ‖(η : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη0] using hη
  exact (mul_le_mul hηn (fibreQuad_norm_le_eight (G t)
    (fun j k => cellMetric_entry_bound hG t 0 j k) ξ) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! A single, level-independent Jacobian seminorm budget for adjacent renewal charts. -/

theorem transition_uniform_jacobian_bar (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (m : ℕ) (hm : 1 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (l₁ l₂ : ℤ) (hl : l₂ = l₁ + 1 ∨ l₁ = l₂ + 1) :
    ∀ n i a, barNorm n (2 ^ 11 * (ocEpsilon q Λ (m - 1))⁻¹)
      (fun x => jacMatrix (ocTransition α q Λ m (Φ (m - 1)) hφ l₁ l₂) x i a -
        (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) ≤ ENNReal.ofReal (2 ^ 23) := by
  by_cases hm1 : m = 1
  · subst m
    rw [CycleReference.ocTransition_level_one hseq hφ l₁ l₂]
    intro n i a
    simp only [CycleReference.jacMatrix_identity, sub_self]
    rw [CycleReference.zero_barNorm]
    exact bot_le
  · have hb := CycleReference.transition_jacobian_bar_bounds α s hα₀ hα₁ hs₀ hs₁ q hq
      ζ hζ Λ hΛ Φ hseq m (by omega) hφ l₁ l₂ hl
    have ha := transition_amplitude_le_one hα₀ hα₁ hs₀ hs₁ hq hΛ hm
    intro n i a
    apply (hb n i a).trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ (2 : ℝ) ^ 23)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The next native ordered tensor is exactly the sum of gradients of the preceding words. -/

theorem torusOrdered_gradient_coordinate {r : ℕ} (w : DerivativeWord2 r)
    (i : Fin 2) (U : TorusHk (1 + r) ℂ) :
    cellDerivativeCLM i (derivativeTorusHk (K := 1) w U) =
      U.val ⟨⟨r + 1, by omega⟩, Fin.snoc w i⟩ := by
  change U.val (prefixJetIndex w ⟨⟨1, by decide⟩, fun _ => i⟩) = _
  simp only [prefixJetIndex, Fin.append_right_eq_snoc]

theorem torusOrdered_gradient_tensor_sq {r : ℕ} (U : TorusHk (1 + r) ℂ) :
    derivativeNormSq U.val ⟨r + 1, by omega⟩ =
      ∑ w : DerivativeWord2 r, ∑ i : Fin 2,
        ‖cellDerivativeCLM i (derivativeTorusHk (K := 1) w U)‖ ^ 2 := by
  unfold derivativeNormSq
  have he := (wordInitLastEquiv 2 r).symm.sum_comp
    (fun w : DerivativeWord2 (r + 1) => ‖U.val ⟨⟨r + 1, by omega⟩, w⟩‖ ^ 2)
  rw [Fintype.sum_prod_type] at he
  simpa only [wordInitLastEquiv, Equiv.coe_fn_symm_mk, torusOrdered_gradient_coordinate] using he.symm

end AVRegularity.CycleWords
end
end
