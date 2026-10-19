-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.ProfileModeHilbertJets
import AVRegularity.CycleComparison.Lift.SettingAmbientCrossTestTransverse
public import AVRegularity.CycleComparison.Lift.CellScalarSourceSeries
import AVRegularity.CycleComparison.CleanupChain
import AVRegularity.CycleComparison.Lift.CellInverseZero
import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
import AVRegularity.CycleComparison.Lift.LiftApplyFiniteVectorSynthesis
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Algebra.Ring.IsFormallyReal

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite calibration recovers clamped scalar time measurability without assumptions outside the window. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftCoefficient_applied_dual_measurable_of_finite_tests
    (n m : ℕ) (hm : m ≤ n) (c : LiftCoeff ι h) (lam : ℝ) (hlam : lam ≠ 0)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (a b : ℝ) (hab : a ≤ b) (X z : Vec 2)
    (v u : ι) (ξ : h u) (l : h v →L[ℝ] ℝ)
    (htest : ∀ j : Fin (m + 1), ∀ s : Fin (n + 1), Measurable (fun t =>
      l ((Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) X))⁻¹ •
        liftApply n c
          (fun _ Y => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y) •
            Pi.single u ξ) (Set.projIcc a b hab t) X z v))) :
    Measurable (fun t => l (c m α (Set.projIcc a b hab t) X z v u ξ)) := by
  have he : (fun t => l (c m α (Set.projIcc a b hab t) X z v u ξ)) = fun t =>
      (lam ^ m)⁻¹ *
        ((Fintype.card {β : DerivativeWord2 m // wordZeroMultiplicity β = wordZeroMultiplicity α} : ℝ)⁻¹ *
          ∑ j : Fin (m + 1), polynomialExtractionWeight m (wordZeroMultiplicity α) j *
            ∑ s : Fin (n + 1), polynomialExtractionWeight n m s *
              l ((Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) X))⁻¹ •
                liftApply n c
                  (fun _ Y => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y) •
                    Pi.single u ξ) (Set.projIcc a b hab t) X z v)) := by
    funext t
    rw [← symmetric_lift_coefficient_scaled_calibration n m hm c lam hlam hc α
      (Set.projIcc a b hab t) X z v u ξ]
    simp only [map_smul, map_sum, smul_eq_mul]
  rw [he]
  apply measurable_const.mul
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro j _
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro s _
  exact measurable_const.mul (htest j s)

theorem liftCoefficient_dual_measurable_of_finite_tests
    (n m : ℕ) (hm : m ≤ n) (c : LiftCoeff ι h) (lam : ℝ) (hlam : lam ≠ 0)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (a b : ℝ) (hab : a ≤ b) (X z : Vec 2)
    (v u : ι) [FiniteDimensional ℝ (h u)] (l : (h u →L[ℝ] h v) →L[ℝ] ℝ)
    (htest : ∀ ξ : h u, ∀ l : h v →L[ℝ] ℝ,
      ∀ j : Fin (m + 1), ∀ s : Fin (n + 1), Measurable (fun t =>
        l ((Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) X))⁻¹ •
          liftApply n c
            (fun _ Y => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y) •
              Pi.single u ξ) (Set.projIcc a b hab t) X z v))) :
    Measurable (fun t => l (c m α (Set.projIcc a b hab t) X z v u)) := by
  apply operator_dual_measurable_of_applied_duals _ _ l
  intro ξ l'
  exact liftCoefficient_applied_dual_measurable_of_finite_tests n m hm c lam hlam hc α
    a b hab X z v u ξ l' (htest ξ l')

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Centered coefficients give a centered tested field before any lift sequence is available. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, CompleteSpace (h i)]

theorem liftApply_centered_field_of_coefficients
    (n r : ℕ) (c : LiftCoeff ι h) (f : Vec 2 → ∀ i, h i)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ)
    (hbox : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u,
      IsBoxSmooth r r (fun X z => c m α t X z v u))
    (hper : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u, ∀ X,
      AVenhance.IsZ2Periodic (fun z => c m α t X z v u))
    (hm : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u, ∀ X, ∀ ξ : h u,
      fieldCellMean (fun z => c m α t X z v u ξ) = 0) :
    CoefField True r (liftApply n c (fun _ => f) t) := by
  have hg := liftApply_goodField_of_coefficients r n c f hf t hbox
    (fun X m hm α v u => hper m hm α v u X)
  refine ⟨hg, fun _ X => ?_⟩
  ext v
  rw [← fieldCellMean_pi_apply _ (hg.continuous_slice X) v]
  exact liftApply_component_mean_zero_of_centered_coefficients n c (fun _ => f) t X v
    (fun m hmn α u => ((hbox m hmn α v u).1 X).continuous)
    (fun m hmn α u ξ => hm m hmn α v u X ξ)
end

/-! The finite calibration separates the dimensional scale from its fixed weights. -/

theorem liftCalibrationWeight_abs_scale (n m : ℕ) (α : DerivativeWord2 m)
    (lam : ℝ) (hlam : 0 < lam) (j : Fin (m + 1) × Fin (n + 1)) :
    |liftCalibrationWeight n m α lam j| =
      (lam ^ m)⁻¹ * |liftCalibrationWeight n m α 1 j| := by
  unfold liftCalibrationWeight
  simp only [one_pow, inv_one, one_mul, abs_mul, abs_inv,
    abs_of_pos (pow_pos hlam m), mul_assoc]

theorem inverse_power_mul_graded_power (lam : ℝ) (hlam : lam ≠ 0)
    (n m r : ℕ) (hm : m ≤ n) :
    (lam ^ m)⁻¹ * lam ^ (n + r) = lam ^ (n - m + r) := by
  have he : n + r = m + (n - m + r) := by omega
  rw [he, pow_add, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero m hlam), one_mul]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Nonzero Fourier modes need no centering assumption for derivative decay. -/

theorem nonzero_weightedProfileFourierCoeff_parameter_data (p r j : ℕ) (hr : r ≤ p)
    (f : Vec 2 → ℝ → ℂ) (hf : ∀ X, ContDiff ℝ (j : ℕ∞) (f X))
    (hper : ∀ X, Function.Periodic (f X) 1)
    (hs : ∀ z, ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (f X) z))
    (C : ℕ → ℝ) (hb : ∀ q ≤ p, ∀ z X,
      ‖iteratedFDeriv ℝ q (fun Y => iteratedDeriv j (f Y) z) X‖ ≤ C q)
    (m : ℤ) (hm : m ≠ 0) :
    ContDiff ℝ (p : ℕ∞) (fun X => profileFourierFrequency m ^ j * unitProfileFourierCoeff (f X) m) ∧
    ∀ X, ‖iteratedFDeriv ℝ r
      (fun Y => profileFourierFrequency m ^ j * unitProfileFourierCoeff (f Y) m) X‖ ≤
      (2 : ℝ) ^ r * C r := by
  have he : (fun X => profileFourierFrequency m ^ j * unitProfileFourierCoeff (f X) m) =
      fun X => unitProfileFourierCoeff (iteratedDeriv j (f X)) m := by
    funext X
    simpa only [profileFourierFrequency] using
      (unitProfileFourierCoeff_iteratedDeriv j (f X) (hf X) (hper X) m hm).symm
  rw [he]
  have hme : ∀ X, Measurable (iteratedDeriv j (f X)) :=
    fun X => ((hf X).continuous_iteratedDeriv j le_rfl).measurable
  exact ⟨unitProfileFourierCoeff_parameter_contDiff p _ hme hs C hb m,
    fun X => unitProfileFourierCoeff_parameter_jet_norm_le p r hr _ hme hs C hb m X⟩

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Mixed source and metric slow derivatives have a common damping majorant. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem transverseModeKernel_source_scaled_jet (n q : ℕ) (hq : q ≤ n)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (g t))
    (M lam rate a b : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam)
    (hrate : 0 ≤ rate) (hab : a ≤ b)
    (hb : ∀ j ≤ n, ∀ t X, ‖iteratedFDeriv ℝ j (g t) X‖ ≤ M * lam ^ j)
    (f : Vec 2 → E) (hf : ContDiff ℝ (n : ℕ∞) f) (S : ℕ → ℝ)
    (hS : ∀ j ≤ n, 0 ≤ S j)
    (hfB : ∀ j ≤ n, ∀ X, ‖iteratedFDeriv ℝ j f X‖ ≤ S j * lam ^ j) (X : Vec 2) :
    ‖iteratedFDeriv ℝ q
      (fun Y => transverseModeKernel rate (fun t => g t Y) a b • f Y) X‖ ≤
      (∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * j.factorial * S (q - j)) *
        transverseModeKernel rate (fun t => g t X) a b *
        (max 1 ((2 : ℝ) ^ n * M * rate * (b - a))) ^ q * lam ^ q := by
  have hk : ContDiff ℝ (q : ℕ∞)
      (fun Y => transverseModeKernel rate (fun t => g t Y) a b) :=
    (transverseModeKernel_parameter_contDiff n g hm hs (fun j => M * lam ^ j)
      hb rate a b).of_le (by exact_mod_cast hq)
  apply norm_iteratedFDeriv_smul_damped_le q _ f hk
    (hf.of_le (by exact_mod_cast hq)) X lam
    (transverseModeKernel rate (fun t => g t X) a b)
    (max 1 ((2 : ℝ) ^ n * M * rate * (b - a))) hlam
    (transverseModeKernel_pos _ _ _ _).le (le_max_left _ _)
    (fun j => (j.factorial : ℝ)) S
  · intro j _
    exact Nat.cast_nonneg _
  · intro j hj
    exact hS j (hj.trans hq)
  · intro j hj
    exact transverseModeKernel_parameter_scaled_jet n j (hj.trans hq) g hm hs
      M lam rate a b hM hlam hrate hab hb X
  · intro j hj
    exact hfB j (hj.trans hq) X

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite normalized tests recover transverse geometry of the actual symmetric coefficient array. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftCoefficient_transverse_of_finite_tests (par : Fin 2) (I : Set ℝ)
    (n m : ℕ) (hm : m ≤ n) (c : LiftCoeff ι h) (lam : ℝ) (hlam : lam ≠ 0)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (v u : ι)
    (htest : ∀ ξ : h u, ∀ j : Fin (m + 1), ∀ s : Fin (n + 1),
      IsTransverseOn par I (fun t X z =>
        (Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) X))⁻¹ •
          liftApply n c
            (fun _ Y => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y) •
              Pi.single u ξ) t X z v)) :
    IsTransverseOn par I (fun t X z => c m α t X z v u) := by
  intro t ht X z r
  ext ξ
  rw [← symmetric_lift_coefficient_scaled_calibration n m hm c lam hlam hc α t X
    (z + r • basisVec par) v u ξ,
    ← symmetric_lift_coefficient_scaled_calibration n m hm c lam hlam hc α t X z v u ξ]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact congrArg (fun x => polynomialExtractionWeight n m s • x)
    (htest ξ j s t ht X z r)

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Cell solutions depend only on coefficients on their own time window. -/

theorem cellSolution_coefficients_congr {a b : ℝ}
    (G G' : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v v' : ℝ → Vec 2 → Vec 2)
    (hG : ∀ t ∈ Icc a b, G' t = G t) (hv : ∀ t ∈ Icc a b, v' t = v t)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) ⟨G, v, 0, 0⟩ src F D) :
    IsCellSolution (Icc a b) ⟨G', v', 0, 0⟩ src F D := by
  refine ⟨hD.1, hD.2.1, hD.2.2.1, hD.2.2.2.1, hD.2.2.2.2.1,
    hD.2.2.2.2.2.1, ?_⟩
  intro s hs t ht hst ψ
  have hw := hD.2.2.2.2.2.2 s hs t ht hst ψ
  let R := fun τ => cellLiteralRHS ⟨G, v, 0, 0⟩ τ (cellValue D τ)
    (fun j => cellGradComp (D τ) j) (ψ.jet (valueIndex2 1))
    (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) (src τ) (F τ)
  let R' := fun τ => cellLiteralRHS ⟨G', v', 0, 0⟩ τ (cellValue D τ)
    (fun j => cellGradComp (D τ) j) (ψ.jet (valueIndex2 1))
    (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) (src τ) (F τ)
  have he : R' =ᵐ[volume.restrict (Ioc s t)] R := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hrI : r ∈ Icc a b := ⟨hs.1.trans hr.1.le, hr.2.trans ht.2⟩
    funext x
    simp only [R', R, cellLiteralRHS, hG r hrI, hv r hrI]
  change Integrable (fun x => cellValue D t x * ψ.jet (valueIndex2 1) x)
      (volume.restrict AVenhance.unitCube) ∧
    Integrable (fun x => cellValue D s x * ψ.jet (valueIndex2 1) x)
      (volume.restrict AVenhance.unitCube) ∧
    (∀ᵐ τ ∂volume.restrict (Ioc s t), Integrable (R τ) (volume.restrict AVenhance.unitCube)) ∧
    IntegrableOn (fun τ => ∫ x in AVenhance.unitCube, R τ x) (Ioc s t) ∧
    (∫ x in AVenhance.unitCube, cellValue D t x * ψ.jet (valueIndex2 1) x) -
      (∫ x in AVenhance.unitCube, cellValue D s x * ψ.jet (valueIndex2 1) x) =
        ∫ τ in Ioc s t, ∫ x in AVenhance.unitCube, R τ x at hw
  change _ ∧ _ ∧
    (∀ᵐ τ ∂volume.restrict (Ioc s t), Integrable (R' τ) (volume.restrict AVenhance.unitCube)) ∧
    IntegrableOn (fun τ => ∫ x in AVenhance.unitCube, R' τ x) (Ioc s t) ∧ _
  have hi : (fun τ => ∫ x in AVenhance.unitCube, R' τ x) =ᵐ[volume.restrict (Ioc s t)]
      (fun τ => ∫ x in AVenhance.unitCube, R τ x) := he.fun_comp _
  refine ⟨hw.1, hw.2.1, ?_, hw.2.2.2.1.congr hi.symm, ?_⟩
  · filter_upwards [hw.2.2.1, he] with r hr heq
    exact heq ▸ hr
  · exact hw.2.2.2.2.trans (integral_congr_ae hi).symm

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Entrywise Fourier source data for the slow-dependent inverse. -/

def weightedParameterSource (f : ℝ → Vec 2 → ℝ → ℂ) (j : ℕ) : ℤ → ℝ → Vec 2 → ℂ :=
  fun m t X => profileFourierFrequency m ^ j * unitProfileFourierCoeff (f t X) m

theorem weightedParameterSource_data (p j : ℕ) (f : ℝ → Vec 2 → ℝ → ℂ)
    (hm : ∀ X, Measurable (Function.uncurry (fun t z => f t X z)))
    (hf : ∀ t X, ContDiff ℝ (j : ℕ∞) (f t X))
    (hper : ∀ t X, Function.Periodic (f t X) 1)
    (hs : ∀ t z, ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (f t X) z))
    (S : ℕ → ℝ) (lam : ℝ)
    (hb : ∀ r ≤ p, ∀ t z X,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedDeriv j (f t Y) z) X‖ ≤ S r * lam ^ r)
    (hcenter : ∀ t X, unitProfileFourierCoeff (f t X) 0 = 0) :
    (∀ m X, Measurable (fun t => weightedParameterSource f j m t X)) ∧
    (∀ m t, ContDiff ℝ (p : ℕ∞) (weightedParameterSource f j m t)) ∧
    (∀ r ≤ p, ∀ m t X, ‖iteratedFDeriv ℝ r (weightedParameterSource f j m t) X‖ ≤
      ((2 : ℝ) ^ r * S r) * lam ^ r) ∧
    ∀ t X, weightedParameterSource f j 0 t X = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m X
    exact measurable_const.mul (unitProfileFourierCoeff_time_measurable _ (hm X) m)
  · intro m t
    exact (weightedProfileFourierCoeff_parameter_data p 0 j (Nat.zero_le p)
      (f t) (hf t) (hper t) (hs t) (fun r => S r * lam ^ r)
      (fun r hr => hb r hr t) (hcenter t) m).1
  · intro r hr m t X
    have hh := (weightedProfileFourierCoeff_parameter_data p r j hr
      (f t) (hf t) (hper t) (hs t) (fun r => S r * lam ^ r)
      (fun r hr => hb r hr t) (hcenter t) m).2 X
    simpa only [weightedParameterSource, mul_assoc] using! hh
  · intro t X
    simp only [weightedParameterSource, hcenter, mul_zero]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The actual source acting on a lift polynomial has the recurrence's finite convolution. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ}

theorem sourceFlux_polynomial_input_coefficient (edge : ConstituentEdges D h) (hD : 1 ≤ D)
    (η t : ℝ) (N j : ℕ) (k : Fin 2) (P : ℕ → Vec 2 → Vec 2 → ∀ i, h i)
    (hP : ∀ i, GoodField D (P i)) (hz : ∀ i, N < i → P i = fun _ _ => 0)
    (X z : Vec 2) :
    ((j.factorial : ℝ)⁻¹) • iteratedDeriv j
      (fun ε : ℝ => sourceFlux edge η ε t
        (fun Y y => ∑ i ∈ Finset.range (N + 1), ε ^ i • P i Y y) k X z) 0 =
      ∑ l ∈ Finset.range (min (D - 1) j + 1), sourceFluxCoefficientArray edge η t (P (j - l)) k l X z := by
  have he : (fun ε : ℝ => sourceFlux edge η ε t
      (fun Y y => ∑ i ∈ Finset.range (N + 1), ε ^ i • P i Y y) k X z) =
      fun ε => ∑ i ∈ Finset.range (N + 1), ∑ l ∈ Finset.range ((D - 1) + 1),
        ε ^ (i + l) • sourceFluxCoefficientArray edge η t (P i) k l X z := by
    funext ε
    rw [congrFun (congrFun (sourceFlux_finset_sum_smul edge η ε t
      (Finset.range (N + 1)) (fun i => ε ^ i) P (fun i _ => hP i) k) X) z]
    simp_rw [sourceFlux_polynomial_identity edge η ε t _ (hP _) k]
    rw [Nat.sub_add_cancel hD]
    simp only [Finset.smul_sum, smul_smul, pow_add]
  rw [he, normalized_polynomial_convolution N (D - 1) j]
  intro i hi l
  rw [hz i hi]
  rw [← sourceFluxCoefficientArray_normalized edge hD η t _ GoodField.zero k l X z]
  simp only [sourceFlux_const_eq_zero, Pi.zero_apply]
  simp

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! One finite synthesis map commutes with the literal cross operator. -/

section
variable {J E : Type*} [Fintype J] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellB1_finite_synthesis (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (w : J → ℝ) (f : J → Vec 2 → Vec 2 → E)
    (hf : ∀ j, IsBoxSmooth 1 1 (f j))
    (hG : ∀ i j, IsBoxSmooth 1 0 (fun X (_ : Vec 2) => G t X i j)) (X z : Vec 2) :
    cellB1 η G v t (fun Y y => ∑ j, w j • f j Y y) X z =
      ∑ j, w j • cellB1 η G v t (f j) X z := by
  let F : Vec 2 → Vec 2 → J → E := fun Y y j => f j Y y
  let L : (J → E) →L[ℝ] E := ∑ j, w j • ContinuousLinearMap.proj j
  have hF : IsBoxSmooth 1 1 F := isBoxSmooth_pi _ _ F hf
  have hL (u : J → E) : L u = ∑ j, w j • u j := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply]
  have hcomp : (fun Y y => L (F Y y)) = fun Y y => ∑ j, w j • f j Y y := by
    funext Y y
    exact hL (F Y y)
  rw [← hcomp, cellB1_postcomposition L η G v t F hF hG X z, hL]
  apply Finset.sum_congr rfl
  intro j _
  have he := cellB1_postcomposition (ContinuousLinearMap.proj j : (J → E) →L[ℝ] E)
    η G v t F hF hG X z
  exact congrArg (fun u => w j • u) he.symm
end

/-! One finite synthesis map commutes with the literal cross operator. -/

section
variable {J E : Type*} [Fintype J] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellB2_finite_synthesis (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (t : ℝ) (w : J → ℝ) (f : J → Vec 2 → Vec 2 → E)
    (hf : ∀ j, IsBoxSmooth 2 0 (f j))
    (hG : ∀ i j, IsBoxSmooth 1 0 (fun X (_ : Vec 2) => G t X i j)) (X z : Vec 2) :
    cellB2 η G t (fun Y y => ∑ j, w j • f j Y y) X z =
      ∑ j, w j • cellB2 η G t (f j) X z := by
  let F : Vec 2 → Vec 2 → J → E := fun Y y j => f j Y y
  let L : (J → E) →L[ℝ] E := ∑ j, w j • ContinuousLinearMap.proj j
  have hF : IsBoxSmooth 2 0 F := isBoxSmooth_pi _ _ F hf
  have hL (u : J → E) : L u = ∑ j, w j • u j := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply]
  have hcomp : (fun Y y => L (F Y y)) = fun Y y => ∑ j, w j • f j Y y := by
    funext Y y
    exact hL (F Y y)
  rw [← hcomp, cellB2_postcomposition L η G t F hF hG X z, hL]
  apply Finset.sum_congr rfl
  intro j _
  have he := cellB2_postcomposition (ContinuousLinearMap.proj j : (J → E) →L[ℝ] E)
    η G t F hF hG X z
  exact congrArg (fun u => w j • u) he.symm
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Rectangular regularity of finitely many normalized coarse tests recovers operator coefficients. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

theorem liftCoefficient_box_reserve_of_finite_tests (p q n m : ℕ) (hm : m ≤ n)
    (c : LiftCoeff ι h) (lam : ℝ) (hlam : lam ≠ 0)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (t : ℝ) (v u : ι)
    (htest : ∀ ξ : h u, ∀ j : Fin (m + 1), ∀ s : Fin (n + 1),
      IsBoxSmooth p q (fun X z =>
        (Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) X))⁻¹ •
          liftApply n c
            (fun _ Y => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y) • Pi.single u ξ)
            t X z v)) : IsBoxSmooth p q (fun X z => c m α t X z v u) := by
  apply isBoxSmooth_clm_of_apply
  intro ξ
  have he : (fun X z => (lam ^ m)⁻¹ •
      ((Fintype.card {β : DerivativeWord2 m // wordZeroMultiplicity β = wordZeroMultiplicity α} : ℝ)⁻¹ •
        (∑ j : Fin (m + 1), polynomialExtractionWeight m (wordZeroMultiplicity α) j •
          ∑ s : Fin (n + 1), polynomialExtractionWeight n m s •
            ((Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) X))⁻¹ •
              liftApply n c
                (fun _ Y => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y) • Pi.single u ξ)
                t X z v)))) = fun X z => c m α t X z v u ξ := by
    funext X z
    exact symmetric_lift_coefficient_scaled_calibration n m hm c lam hlam hc α t X z v u ξ
  rw [← he]
  apply IsBoxSmooth.const_smul
  apply IsBoxSmooth.const_smul
  apply IsBoxSmooth.sum Finset.univ
  intro j _
  apply IsBoxSmooth.const_smul
  apply IsBoxSmooth.sum Finset.univ
  intro s _
  exact (htest ξ j s).const_smul (polynomialExtractionWeight n m s)

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Slow primitive jets on the fast unit interval have order-dependent, component-free bounds. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem parameter_centeredIntervalPrimitive_slow_norm_le
    (n : ℕ) (f : ℝ → Vec 2 → E)
    (hf : ∀ X, Continuous (fun y => f y X))
    (hs : ∀ y, ContDiff ℝ (n : ℕ∞) (f y))
    (C : ℕ → ℝ) (hb : ∀ j ≤ n, ∀ y X, ‖iteratedFDeriv ℝ j (f y) X‖ ≤ C j)
    (q : ℕ) (hq : q ≤ n) (X : Vec 2) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ‖iteratedFDeriv ℝ q (fun Y => centeredIntervalPrimitive (fun y => f y Y) r) X‖ ≤
      (2 : ℝ) ^ q * (2 * C q) := by
  have hC : 0 ≤ C q := (norm_nonneg _).trans (hb q hq 0 0)
  have hcp : ContDiff ℝ (q : ℕ∞)
      (fun Y => centeredIntervalPrimitive (fun y => f y Y) r) :=
    (parameter_centeredIntervalPrimitive_contDiff n f hf hs C hb r).of_le
      (by exact_mod_cast hq)
  have hw (α : DerivativeWord2 q) :
      ‖orderedDerivative α (fun Y => centeredIntervalPrimitive (fun y => f y Y) r) X‖ ≤
        2 * C q := by
    rw [orderedDerivative_parameter_centeredIntervalPrimitive n f hf hs C hb q hq α r]
    exact centeredIntervalPrimitive_unit_norm_le _ (C q) hC
      (fun y => (AVRegularity.ChartTransport.norm_orderedDerivative_le
        ((hs y).of_le (by exact_mod_cast hq)) α X).trans (hb q hq y X)) r hr
  calc
    _ ≤ ∑ α : DerivativeWord2 q,
        ‖orderedDerivative α (fun Y => centeredIntervalPrimitive (fun y => f y Y) r) X‖ :=
      AVRegularity.ChartTransport.norm_iteratedFDeriv_le_sum_words hcp X
    _ ≤ ∑ _α : DerivativeWord2 q, 2 * C q := Finset.sum_le_sum (fun α _ => hw α)
    _ = (2 : ℝ) ^ q * (2 * C q) := by
      rw [Finset.sum_const, AVRegularity.ChartTransport.card_derivativeWord2]
      simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Centered actual coarse tests identify centered symmetric coefficient entries. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem symmetric_lift_coefficient_centered_of_tests
    (n m : ℕ) (hm : m ≤ n) (c : LiftCoeff ι h)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (t : ℝ) (X : Vec 2) (v u : ι) (ξ : h u)
    (hcont : ∀ A : Vec 2 →L[ℝ] ℝ,
      Continuous (fun z => normalizedLiftTestField c n A u v ξ t X z))
    (hmean : ∀ A : Vec 2 →L[ℝ] ℝ,
      fieldCellMean (fun z => normalizedLiftTestField c n A u v ξ t X z) = 0) :
    fieldCellMean (fun z => c m α t X z v u ξ) = 0 := by
  have he (z : Vec 2) := liftCalibration_synthesis n m hm c 1 one_ne_zero hc α t X z v u ξ
  have hf : (fun z => c m α t X z v u ξ) =
      fun z => ∑ p : Fin (m + 1) × Fin (n + 1), liftCalibrationWeight n m α 1 p •
        normalizedLiftTestField c n
          ( (1 : ℝ) • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) u v ξ t X z := by
    funext z
    exact (he z).symm
  rw [hf]
  apply fieldCellMean_finset_sum_zero Finset.univ
  · intro p _
    exact (hcont _).const_smul _
  · intro p _
    rw [fieldCellMean_smul, hmean, smul_zero]

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Copy-adapt the proved weak-source congruence to classical representatives of the same weak state. -/

/-- Null changes in the states preserve the integrated weak identity. -/
theorem cellWeakIdentity_state_congr_sections (C : CellCoefficients) (s t : ℝ)
    (u0 u1 ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (u : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ)
    (u0' u1' : Vec 2 → ℂ) (u' : ℝ → Vec 2 → ℂ)
    (du' : ℝ → Fin 2 → Vec 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (h0 : u0 =ᵐ[volume.restrict AVenhance.unitCube] u0')
    (h1 : u1 =ᵐ[volume.restrict AVenhance.unitCube] u1')
    (hu : ∀ᵐ r ∂volume.restrict (Ioc s t),
      u r =ᵐ[volume.restrict AVenhance.unitCube] u' r)
    (hd : ∀ᵐ r ∂volume.restrict (Ioc s t), ∀ j,
      du r j =ᵐ[volume.restrict AVenhance.unitCube] du' r j)
    (h : CellWeakIdentity C s t u0 u1 ψ dψ u du src F) :
    CellWeakIdentity C s t u0' u1' ψ dψ u' du' src F := by
  let μ := volume.restrict AVenhance.unitCube
  let R := fun r => cellLiteralRHS C r (u r) (du r) ψ dψ (src r) (F r)
  let R' := fun r => cellLiteralRHS C r (u' r) (du' r) ψ dψ (src r) (F r)
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R r) μ) ∧
    Integrable (fun r => ∫ x, R r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R r x ∂μ at h
  change Integrable (fun x => u1' x * ψ x) μ ∧ Integrable (fun x => u0' x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R' r) μ) ∧
    Integrable (fun r => ∫ x, R' r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1' x * ψ x ∂μ) - (∫ x, u0' x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R' r x ∂μ
  have he : ∀ᵐ r ∂volume.restrict (Ioc s t), R r =ᵐ[μ] R' r := by
    filter_upwards [hu, hd] with r hur hdr
    have hdall := ae_all_iff.mpr hdr
    filter_upwards [hur, hdall] with x hx hdx
    simp only [R, R', cellLiteralRHS, hx]
    simp_rw [hdx]
  have he0 : (fun x => u0 x * ψ x) =ᵐ[μ] fun x => u0' x * ψ x :=
    h0.mono (fun x hx => congrArg (fun w => w * ψ x) hx)
  have he1 : (fun x => u1 x * ψ x) =ᵐ[μ] fun x => u1' x * ψ x :=
    h1.mono (fun x hx => congrArg (fun w => w * ψ x) hx)
  have hint : (fun r => ∫ x, R r x ∂μ) =ᵐ[volume.restrict (Ioc s t)]
      fun r => ∫ x, R' r x ∂μ := he.mono fun r hr => integral_congr_ae hr
  refine ⟨h.1.congr he1, h.2.1.congr he0, ?_, h.2.2.2.1.congr hint, ?_⟩
  · filter_upwards [h.2.2.1, he] with r hr her
    exact hr.congr her
  · rw [← integral_congr_ae he1, ← integral_congr_ae he0, ← integral_congr_ae hint]
    exact h.2.2.2.2

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Slow primitive jets are jointly continuous in position and endpoint, using fixed finite jet coordinates. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem parameter_centeredIntervalPrimitive_slow_joint_jets
    (n : ℕ) (f : ℝ → Vec 2 → E)
    (hf : Continuous (Function.uncurry f))
    (hs : ∀ y, ContDiff ℝ (n : ℕ∞) (f y))
    (C : ℕ → ℝ) (hb : ∀ j ≤ n, ∀ y X, ‖iteratedFDeriv ℝ j (f y) X‖ ≤ C j)
    (hjet : ∀ j ≤ n,
      Continuous (fun p : Vec 2 × ℝ => iteratedFDeriv ℝ j (f p.2) p.1))
    (q : ℕ) (hq : q ≤ n) :
    Continuous (fun p : Vec 2 × ℝ => iteratedFDeriv ℝ q
      (fun X => centeredIntervalPrimitive (fun y => f y X) p.2) p.1) := by
  have hfast (X : Vec 2) : Continuous (fun y => f y X) :=
    hf.comp (continuous_id.prodMk continuous_const)
  have hcp (r : ℝ) : ContDiff ℝ (q : ℕ∞)
      (fun X => centeredIntervalPrimitive (fun y => f y X) r) :=
    (parameter_centeredIntervalPrimitive_contDiff n f hfast hs C hb r).of_le
      (by exact_mod_cast hq)
  apply continuous_multilinear_of_basis_coordinates q
  intro w
  let α : DerivativeWord2 q := fun i => w (Fin.rev i)
  let g := fun y X => orderedDerivative α (f y) X
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) E
    (fun i => basisVec (α (Fin.rev i)))
  have hg : Continuous (Function.uncurry g) := by
    have hc := L.continuous.comp ((hjet q hq).comp (continuous_snd.prodMk continuous_fst))
    apply hc.congr
    intro p
    exact (congrFun (orderedDerivative_eq_iteratedFDeriv α
      ((hs p.1).of_le (by exact_mod_cast hq))) p.2).symm
  have hgb : ∀ y X, ‖g y X‖ ≤ C q := fun y X =>
    (AVRegularity.ChartTransport.norm_orderedDerivative_le
      ((hs y).of_le (by exact_mod_cast hq)) α X).trans (hb q hq y X)
  have hc := parameter_centeredIntervalPrimitive_joint_continuous g hg (C q) hgb
  apply hc.congr
  intro p
  have he := congrFun (orderedDerivative_eq_iteratedFDeriv α (hcp p.2)) p.1
  have hcomm := congrFun (orderedDerivative_parameter_centeredIntervalPrimitive n f hfast hs C hb
    q hq α p.2) p.1
  have he' : orderedDerivative α (fun X => centeredIntervalPrimitive (fun y => f y X) p.2) p.1 =
      iteratedFDeriv ℝ q (fun X => centeredIntervalPrimitive (fun y => f y X) p.2) p.1
        (fun i => basisVec (w i)) := by
    simpa only [α, Fin.rev_rev] using he
  exact (he'.symm.trans hcomm).symm

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! The original rectangular mixed-jet majorants control the literal cell energy norm. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rectangular_mixed_fieldEnergyNorm_le (I : Set ℝ) (hI : MeasurableSet I)
    (f : ℝ → Vec 2 → Vec 2 → E) (r j : ℕ) (X : Vec 2)
    (hf : ∀ t ∈ I, IsBoxSmooth r (j + 1) (f t))
    (B₀ B₁ : ℝ) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hb₀ : ∀ t ∈ I, ∀ z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤ B₀)
    (hb₁ : ∀ t ∈ I, ∀ z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ (j + 1) (f t Y) z) X‖ ≤ B₁) :
    fieldEnergyNorm I (fun t z =>
      iteratedFDeriv ℝ j (fun y => iteratedFDeriv ℝ r (fun Y => f t Y y) X) z) ≤
      ENNReal.ofReal (2 ^ r * (B₀ + B₁)) := by
  have hpow : (0 : ℝ) ≤ 2 ^ r := by positivity
  have he := mixed_jet_fieldEnergyNorm_le I hI f r j X hf
    (2 ^ r * B₀) (2 ^ r * B₁) (mul_nonneg hpow hB₀) (mul_nonneg hpow hB₁)
    (fun t ht z => (fast_slow_mixed_jet_norm_le
      ((hf t ht).mono le_rfl (Nat.le_succ j)) X z).trans
      (mul_le_mul_of_nonneg_left (hb₀ t ht z) hpow))
    (fun t ht z => (fast_slow_mixed_jet_norm_le (hf t ht) X z).trans
      (mul_le_mul_of_nonneg_left (hb₁ t ht z) hpow))
  simpa only [mul_add] using he

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite coarse-test calibration preserves periodicity and transverse coefficient geometry. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem symmetric_lift_coefficient_periodic_of_tests
    (n m : ℕ) (hm : m ≤ n) (c : LiftCoeff ι h)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (t : ℝ) (X : Vec 2) (v u : ι)
    (hp : ∀ (A : Vec 2 →L[ℝ] ℝ) (ξ : h u),
      AVenhance.IsZ2Periodic (fun z => normalizedLiftTestField c n A u v ξ t X z)) :
    AVenhance.IsZ2Periodic (fun z => c m α t X z v u) := by
  intro k z
  ext ξ
  rw [← liftCalibration_synthesis n m hm c 1 one_ne_zero hc α t X
      (z + AVenhance.latticeShift k) v u ξ,
    ← liftCalibration_synthesis n m hm c 1 one_ne_zero hc α t X z v u ξ]
  apply Finset.sum_congr rfl
  intro p _
  exact congrArg (fun y => liftCalibrationWeight n m α 1 p • y)
    (hp ((1 : ℝ) • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) ξ k z)

theorem symmetric_lift_coefficient_transverse_of_tests
    (par : Fin 2) (I : Set ℝ) (n m : ℕ) (hm : m ≤ n) (c : LiftCoeff ι h)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (v u : ι)
    (hp : ∀ (A : Vec 2 →L[ℝ] ℝ) (ξ : h u),
      IsTransverseOn par I (normalizedLiftTestField c n A u v ξ)) :
    IsTransverseOn par I (fun t X z => c m α t X z v u) := by
  intro t ht X z s
  ext ξ
  rw [← liftCalibration_synthesis n m hm c 1 one_ne_zero hc α t X
      (z + s • basisVec par) v u ξ,
    ← liftCalibration_synthesis n m hm c 1 one_ne_zero hc α t X z v u ξ]
  apply Finset.sum_congr rfl
  intro p _
  exact congrArg (fun y => liftCalibrationWeight n m α 1 p • y)
    (hp ((1 : ℝ) • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) ξ t ht X z s)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Literal cross operators commute with differences at their exact rectangular regularity costs. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellB1_field_sub (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (f g : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth 1 1 f) (hg : IsBoxSmooth 1 1 g)
    (hG : ∀ i j, IsBoxSmooth 1 0 (fun X (_ : Vec 2) => G t X i j)) (X z : Vec 2) :
    cellB1 η G v t (fun Y y => f Y y - g Y y) X z =
      cellB1 η G v t f X z - cellB1 η G v t g X z := by
  let F : Fin 2 → Vec 2 → Vec 2 → E := fun i => if i = 0 then f else g
  let w : Fin 2 → ℝ := fun i => if i = 0 then 1 else -1
  have hF (i : Fin 2) : IsBoxSmooth 1 1 (F i) := by
    dsimp only [F]
    split <;> assumption
  have hh := cellB1_finite_synthesis η G v t w F hF hG X z
  simpa [F, w, Fin.sum_univ_two, sub_eq_add_neg] using hh

theorem cellB2_field_sub (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (f g : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth 2 0 f) (hg : IsBoxSmooth 2 0 g)
    (hG : ∀ i j, IsBoxSmooth 1 0 (fun X (_ : Vec 2) => G t X i j)) (X z : Vec 2) :
    cellB2 η G t (fun Y y => f Y y - g Y y) X z =
      cellB2 η G t f X z - cellB2 η G t g X z := by
  let F : Fin 2 → Vec 2 → Vec 2 → E := fun i => if i = 0 then f else g
  let w : Fin 2 → ℝ := fun i => if i = 0 then 1 else -1
  have hF (i : Fin 2) : IsBoxSmooth 2 0 (F i) := by
    dsimp only [F]
    split <;> assumption
  have hh := cellB2_finite_synthesis η G t w F hF hG X z
  simpa [F, w, Fin.sum_univ_two, sub_eq_add_neg] using hh

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The literal zero trajectory satisfies the cell relation for arbitrary coefficients on an interval. -/

theorem cellSolution_zero_field (I : Set ℝ) (hI : I.OrdConnected) (C : CellCoefficients) :
    IsCellSolution I C 0 0 0 := by
  have hj : HasPeriodicOrderedWeakJet (0 : RawJet2 1 ℂ) := by
    refine ⟨?_, fun _ => MemLp.zero, ?_⟩
    · intro α n z
      rfl
    · intro j w i e φ _ _ _
      simp
  have hg : cellGradient (0 : RawJet2 1 ℂ) = 0 := by
    funext x
    apply PiLp.ext
    intro j
    rfl
  refine ⟨hI, Filter.Eventually.of_forall (fun _ => hj), ?_, ?_, ?_, ?_, ?_⟩
  · intro t _
    exact ⟨MemLp.zero, fun _ _ => rfl⟩
  · intro α
    exact aestronglyMeasurable_const
  · intro t _
    simpa only [cellValue, Pi.zero_apply, sub_self, enorm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      lintegral_zero] using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ENNReal)) _ _)
  · intro a _ b _
    simp [hg, cellL2Norm]
  · intro s _ t _ _ ψ
    simp [CellWeakIdentity, cellValue, cellGradComp]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The literal covariant polynomial recursion has a finite left-term representation. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def covariantLeftTermStep (η : ℝ) (k : Fin 2) (P : ℕ → List (LeftTerm E F))
    (j : ℕ) : List (LeftTerm E F) :=
  (P j).map (fun c => c.fastDerivative k) ++ if j = 0 then [] else
    ((P (j - 1)).flatMap (fun c => c.slowDerivativeTerms k)).map
      (fun c => c.smul (Real.sqrt η))

theorem covariantLeftTermStep_apply (η : ℝ) (k : Fin 2) (P : ℕ → List (LeftTerm E F))
    (j : ℕ) (hfast : ∀ c ∈ P j, IsBoxSmooth 0 1 c.coeff)
    (hslow : j ≠ 0 → ∀ c ∈ P (j - 1), IsBoxSmooth 1 0 c.coeff)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    leftTermsApply (covariantLeftTermStep η k P j) f =
      covariantCoefficientStep η k (fun i => leftTermsApply (P i) f) j := by
  by_cases hj : j = 0
  · rw [covariantLeftTermStep, ite_eq_left hj, leftTermsApply_append, leftTermsApply_nil,
      ← leftTermsApply_fastPartial (P j) k hfast f hf]
    funext X z
    simp only [covariantCoefficientStep, ite_eq_left hj, add_zero]
  · rw [covariantLeftTermStep, ite_eq_right hj, leftTermsApply_append, leftTermsApply_map_smul,
      ← leftTermsApply_fastPartial (P j) k hfast f hf,
      ← leftTermsApply_slowPartial (P (j - 1)) k (hslow hj) f hf]
    funext X z
    simp only [covariantCoefficientStep, ite_eq_right hj]
end

/-! Each polynomial step spends one fast or one slow coefficient derivative, exactly. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem covariantLeftTermStep_box (η : ℝ) (k : Fin 2) (P : ℕ → List (LeftTerm E F))
    (j p q : ℕ) (hfast : ∀ c ∈ P j, IsBoxSmooth p (q + 1) c.coeff)
    (hslow : j ≠ 0 → ∀ c ∈ P (j - 1), IsBoxSmooth (p + 1) q c.coeff) :
    ∀ c ∈ covariantLeftTermStep η k P j, IsBoxSmooth p q c.coeff := by
  intro c hc
  rw [covariantLeftTermStep] at hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact d.fastDerivative_box p q (hfast d hd) k
  · by_cases hj : j = 0
    · simp only [ite_eq_left hj, List.not_mem_nil] at hc
    · rw [ite_eq_right hj] at hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      obtain ⟨a, ha, hd⟩ := List.mem_flatMap.mp hd
      apply d.smul_box p q
      simp only [LeftTerm.slowDerivativeTerms, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact a.slowCoefficientDerivative_box p q (hslow hj a ha) k
      · exact (hslow hj a ha).mono (Nat.le_succ p) le_rfl

theorem covariantLeftTermStep_order (η : ℝ) (k : Fin 2) (P : ℕ → List (LeftTerm E F))
    (j n : ℕ) (hfast : ∀ c ∈ P j, c.order ≤ n + j)
    (hslow : j ≠ 0 → ∀ c ∈ P (j - 1), c.order ≤ n + (j - 1)) :
    ∀ c ∈ covariantLeftTermStep η k P j, c.order ≤ n + j := by
  intro c hc
  rw [covariantLeftTermStep] at hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact hfast d hd
  · by_cases hj : j = 0
    · simp only [ite_eq_left hj, List.not_mem_nil] at hc
    · rw [ite_eq_right hj] at hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      obtain ⟨a, ha, hd⟩ := List.mem_flatMap.mp hd
      have hb := hslow hj a ha
      simp only [LeftTerm.slowDerivativeTerms, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact hb.trans (by omega)
      · change a.order + 1 ≤ n + j
        omega
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Source-product slow jets admit a uniform, integrable exponential majorant. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem transverseModeKernel_source_scaled_jet_decay (n q : ℕ) (hq : q ≤ n)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (g t))
    (M lam rate κ a b : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam)
    (hrate : 0 ≤ rate) (hκ : 0 < κ) (hab : a ≤ b)
    (hb : ∀ j ≤ n, ∀ t X, ‖iteratedFDeriv ℝ j (g t) X‖ ≤ M * lam ^ j)
    (hgl : ∀ t ∈ Icc a b, ∀ X, κ ≤ g t X)
    (f : Vec 2 → E) (hf : ContDiff ℝ (n : ℕ∞) f) (S : ℕ → ℝ)
    (hS : ∀ j ≤ n, 0 ≤ S j)
    (hfB : ∀ j ≤ n, ∀ X, ‖iteratedFDeriv ℝ j f X‖ ≤ S j * lam ^ j) (X : Vec 2) :
    ‖iteratedFDeriv ℝ q
      (fun Y => transverseModeKernel rate (fun t => g t Y) a b • f Y) X‖ ≤
      (∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * j.factorial * S (q - j)) *
        (1 + q.factorial * (2 * ((2 : ℝ) ^ n * M) / κ) ^ q) *
        Real.exp (-(rate * κ / 2) * (b - a)) * lam ^ q := by
  let A := ∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * j.factorial * S (q - j)
  have hA : 0 ≤ A := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (hS (q - j) ((Nat.sub_le q j).trans hq))
  have hi : IntegrableOn (fun t => g t X) (Icc a b) := by
    apply (integrable_const M).mono' (hm X).aestronglyMeasurable
    exact ae_of_all _ (fun t => by simpa using hb 0 (by omega) t X)
  have hi' : IntegrableOn (fun t => g t X) (uIcc a b) := by
    simpa [uIcc_of_le hab] using hi
  have hk := transverseModeKernel_le_exp rate κ hrate (fun t => g t X) a b hab
    hi'.intervalIntegrable (fun t ht => hgl t ht X)
  have hw := weighted_decayKernel_pointwise q ((2 : ℝ) ^ n * M) rate κ (b - a)
    (mul_nonneg (pow_nonneg (by norm_num) n) hM) hrate hκ (sub_nonneg.mpr hab)
  have hj := transverseModeKernel_source_scaled_jet n q hq g hm hs M lam rate a b
    hM hlam hrate hab hb f hf S hS hfB X
  apply hj.trans
  have hh : (max 1 ((2 : ℝ) ^ n * M * rate * (b - a))) ^ q *
      transverseModeKernel rate (fun t => g t X) a b ≤
      (1 + q.factorial * (2 * ((2 : ℝ) ^ n * M) / κ) ^ q) *
        Real.exp (-(rate * κ / 2) * (b - a)) := by
    exact (mul_le_mul_of_nonneg_left hk
      (pow_nonneg (zero_le_one.trans (le_max_left 1 _)) q)).trans hw
  calc
    _ = A * ((max 1 ((2 : ℝ) ^ n * M * rate * (b - a))) ^ q *
        transverseModeKernel rate (fun t => g t X) a b) * lam ^ q := by dsimp [A]; ring
    _ ≤ A * ((1 + q.factorial * (2 * ((2 : ℝ) ^ n * M) / κ) ^ q) *
        Real.exp (-(rate * κ / 2) * (b - a))) * lam ^ q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hA) (pow_nonneg hlam q)
    _ = _ := by dsimp [A]; ring
end

/-! The finite-past Duhamel integrand has uniform slow jets after clamping its time argument. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem clamped_duhamel_uniform_jet_bound (n : ℕ)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (g t))
    (M lam rate κ a b : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam)
    (hrate : 0 ≤ rate) (hκ : 0 < κ) (hab : a ≤ b)
    (hb : ∀ j ≤ n, ∀ t X, ‖iteratedFDeriv ℝ j (g t) X‖ ≤ M * lam ^ j)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : ℝ → Vec 2 → E) (hf : ∀ t, ContDiff ℝ (n : ℕ∞) (f t))
    (S : ℕ → ℝ) (hS : ∀ j ≤ n, 0 ≤ S j)
    (hfB : ∀ j ≤ n, ∀ t X, ‖iteratedFDeriv ℝ j (f t) X‖ ≤ S j * lam ^ j)
    (q : ℕ) (hq : q ≤ n) (s : ℝ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ q (fun Y =>
      transverseModeKernel rate (fun t => g t Y) (projIcc a b hab s) b •
        f (projIcc a b hab s) Y) X‖ ≤
      ((∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * j.factorial * S (q - j)) *
        (1 + q.factorial * (2 * ((2 : ℝ) ^ n * M) / κ) ^ q)) * lam ^ q := by
  let r := (projIcc a b hab s : ℝ)
  have hr : r ≤ b := (projIcc a b hab s).2.2
  have hh := transverseModeKernel_source_scaled_jet_decay n q hq g hm hs
    M lam rate κ r b hM hlam hrate hκ hr hb (fun t _ X => hgl t X)
    (f r) (hf r) S hS (fun j hj X => hfB j hj r X) X
  have he : Real.exp (-(rate * κ / 2) * (b - r)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sub_nonneg.mpr hr)
  have hA : 0 ≤ ∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * j.factorial * S (q - j) := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (hS (q - j) ((Nat.sub_le q j).trans hq))
  apply hh.trans
  have hB : 0 ≤ 1 + (q.factorial : ℝ) * (2 * ((2 : ℝ) ^ n * M) / κ) ^ q := by positivity
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (mul_nonneg hA hB)) (pow_nonneg hlam q)).trans_eq
      (by ring)
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Real-dual profiles of the first diagonal forcing have the full original fast reserve. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_first_diagonal_profile_jets (c : ℝ) :
    ∃ C : ℕ → ℝ, (∀ j ≤ qf, 0 ≤ C j) ∧
      ∀ j ≤ qf, ∀ t ∈ Set.Icc a b, ∀ x : ℝ,
        ‖iteratedDeriv j (fun y => ((-(Real.sqrt Q.η * V t y) * c : ℝ) : ℂ)) x‖ ≤ C j := by
  let line : ℝ →L[ℝ] Vec 2 := (ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec par.rev)
  let A : Vec 2 →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj par : Vec 2 →L[ℝ] ℝ).smulRight ((-c : ℝ) : ℂ)
  have he (t : ℝ) : (fun y => ((-(Real.sqrt Q.η * V t y) * c : ℝ) : ℂ)) =
      fun y => A (Real.sqrt Q.η • Q.v t (line y)) := by
    funext y
    simp [A, line, P.v_shear, basisVec_apply]
    ring
  obtain ⟨C, hC, hb⟩ := setting_normalized_drift_profile_jets_bounded P line A
  refine ⟨C, hC, ?_⟩
  intro j hj t ht x
  rw [he t]
  exact hb j hj t ht x

end AVRegularity.CycleComparison.Lift
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Explicit finite left terms for each coefficient of an ordered covariant word. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def covariantLeftTermList (η : ℝ) (w : List (Fin 2)) (l : List (LeftTerm E F)) :
    ℕ → List (LeftTerm E F) :=
  w.foldl (fun P k => covariantLeftTermStep η k P) (fun j => if j = 0 then l else [])

theorem covariantLeftTermList_nil (η : ℝ) (l : List (LeftTerm E F)) :
    covariantLeftTermList η [] l = fun j => if j = 0 then l else [] := rfl

theorem covariantLeftTermList_append_singleton (η : ℝ) (w : List (Fin 2))
    (k : Fin 2) (l : List (LeftTerm E F)) :
    covariantLeftTermList η (w ++ [k]) l = covariantLeftTermStep η k (covariantLeftTermList η w l) := by
  simp only [covariantLeftTermList, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem covariantLeftTermList_above_degree (η : ℝ) (w : List (Fin 2))
    (l : List (LeftTerm E F)) : ∀ j, w.length < j → covariantLeftTermList η w l j = [] := by
  induction w using List.reverseRecOn with
  | nil =>
    intro j hj
    simp only [covariantLeftTermList_nil, ite_eq_right (show j ≠ 0 by simpa using Nat.ne_of_gt hj)]
  | append_singleton w k ih =>
    intro j hj
    have hj' : w.length + 1 < j := by simpa using hj
    rw [covariantLeftTermList_append_singleton, covariantLeftTermStep,
      ih j (by omega), ih (j - 1) (by omega)]
    simp only [List.map_nil, List.flatMap_nil, ite_self, List.nil_append]

theorem covariantLeftTermList_order (η : ℝ) (w : List (Fin 2))
    (l : List (LeftTerm E F)) (n : ℕ) (hl : ∀ c ∈ l, c.order ≤ n) :
    ∀ j c, c ∈ covariantLeftTermList η w l j → c.order ≤ n + j := by
  induction w using List.reverseRecOn with
  | nil =>
    intro j c hc
    rw [covariantLeftTermList_nil] at hc
    by_cases hj : j = 0
    · subst j
      exact hl c (by simpa only [ite_true] using hc)
    · simp only [ite_eq_right hj, List.not_mem_nil] at hc
  | append_singleton w k ih =>
    intro j c hc
    rw [covariantLeftTermList_append_singleton] at hc
    exact covariantLeftTermStep_order η k _ j n (ih j) (fun _ => ih (j - 1)) c hc

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The compiled finite synthesis maps apply to finite sets of classical cell fields. -/

variable {J E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellOperator_finset_synthesis (S : Finset J) (G : Fin 2 → Fin 2 → ℝ)
    (v : Vec 2 → Vec 2) (w : J → ℝ) (f : J → Vec 2 → E)
    (hf : ∀ j ∈ S, ContDiff ℝ 2 (f j)) (z : Vec 2) :
    cellOperator G v (fun y => ∑ j ∈ S, w j • f j y) z =
      ∑ j ∈ S, w j • cellOperator G v (f j) z := by
  classical
  have he := cellOperator_finite_synthesis G v (fun j : S => w j.val)
    (fun j : S => f j.val) (fun j => hf j.val j.property) z
  have hfield : (fun y => ∑ j : S, w j.val • f j.val y) =
      fun y => ∑ j ∈ S, w j • f j y := by
    funext y
    exact Finset.sum_coe_sort S (fun j => w j • f j y)
  have hout : (∑ j : S, w j.val • cellOperator G v (f j.val) z) =
      ∑ j ∈ S, w j • cellOperator G v (f j) z :=
    Finset.sum_coe_sort S (fun j => w j • cellOperator G v (f j) z)
  rw [hfield, hout] at he
  exact he

theorem cellB1_finset_synthesis (S : Finset J) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (t : ℝ) (w : J → ℝ) (f : J → Vec 2 → Vec 2 → E)
    (hf : ∀ j ∈ S, IsBoxSmooth 1 1 (f j))
    (hG : ∀ i j, IsBoxSmooth 1 0 (fun X (_ : Vec 2) => G t X i j)) (X z : Vec 2) :
    cellB1 η G v t (fun Y y => ∑ j ∈ S, w j • f j Y y) X z =
      ∑ j ∈ S, w j • cellB1 η G v t (f j) X z := by
  classical
  have he := cellB1_finite_synthesis η G v t (fun j : S => w j.val)
    (fun j : S => f j.val) (fun j => hf j.val j.property) hG X z
  have hfield : (fun Y y => ∑ j : S, w j.val • f j.val Y y) =
      fun Y y => ∑ j ∈ S, w j • f j Y y := by
    funext Y y
    exact Finset.sum_coe_sort S (fun j => w j • f j Y y)
  have hout : (∑ j : S, w j.val • cellB1 η G v t (f j.val) X z) =
      ∑ j ∈ S, w j • cellB1 η G v t (f j) X z :=
    Finset.sum_coe_sort S (fun j => w j • cellB1 η G v t (f j) X z)
  rw [hfield, hout] at he
  exact he

theorem cellB2_finset_synthesis (S : Finset J) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ) (w : J → ℝ)
    (f : J → Vec 2 → Vec 2 → E) (hf : ∀ j ∈ S, IsBoxSmooth 2 0 (f j))
    (hG : ∀ i j, IsBoxSmooth 1 0 (fun X (_ : Vec 2) => G t X i j)) (X z : Vec 2) :
    cellB2 η G t (fun Y y => ∑ j ∈ S, w j • f j Y y) X z =
      ∑ j ∈ S, w j • cellB2 η G t (f j) X z := by
  classical
  have he := cellB2_finite_synthesis η G t (fun j : S => w j.val)
    (fun j : S => f j.val) (fun j => hf j.val j.property) hG X z
  have hfield : (fun Y y => ∑ j : S, w j.val • f j.val Y y) =
      fun Y y => ∑ j ∈ S, w j • f j Y y := by
    funext Y y
    exact Finset.sum_coe_sort S (fun j => w j • f j Y y)
  have hout : (∑ j : S, w j.val • cellB2 η G t (f j.val) X z) =
      ∑ j ∈ S, w j • cellB2 η G t (f j) X z :=
    Finset.sum_coe_sort S (fun j => w j • cellB2 η G t (f j) X z)
  rw [hfield, hout] at he
  exact he

theorem cellOperator_const (G : Fin 2 → Fin 2 → ℝ) (v : Vec 2 → Vec 2) (c : E) :
    cellOperator G v (fun _ => c) = 0 := by
  funext z
  simp [cellOperator]

end AVRegularity.CycleComparison.Lift
end
end
