-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
public import AVRegularity.EntryWeak.IndependentScaledDifferenceSegmentDerivativeJets
import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
import AVRegularity.Construction.Preservation.FullLift.LiftCellSourceEffectiveAllDegrees
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
public import AVRegularity.Construction.Preservation.FullLift.FactorialWordEnergySum
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Construction.FreshAxes.RefFluxContinuous
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! The independent slow and fast blocks have norm at most one in the finite Pi carrier. -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem independent_scaled_mixed_jet_norm_le (r q : ℕ) (f : Vec (2 + 2) → F)
    (hf : ContDiff ℝ (r + q : ℕ∞) f) (lam B : ℝ) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (hbound : ∀ W, ‖iteratedFDeriv ℝ (r + q) f W‖ ≤ B) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q
      (fun w => f (EntryWeakProofs.independentIntrinsicParameterPacking 2 (lam • Y) w)) z) X‖ ≤
      B * lam ^ r := by
  let Lslow := lam • EntryWeakProofs.independentIntrinsicSlowEmbedding 2
  let Lfast := EntryWeakProofs.independentStoredParameterEmbedding 2
  have hs : ‖Lslow‖ ≤ lam := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]
    exact (mul_le_mul_of_nonneg_left
      (EntryWeakProofs.independentIntrinsicSlowEmbedding_norm_le 2) hlam).trans_eq (mul_one _)
  have he (Y w : Vec 2) : Lslow Y + Lfast w =
      EntryWeakProofs.independentIntrinsicParameterPacking 2 (lam • Y) w := by
    rw [EntryWeakProofs.independentStoredParameterEmbedding_eq_packing]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Lslow, EntryWeakProofs.independentIntrinsicSlowEmbedding,
        EntryWeakProofs.independentIntrinsicParameterPacking, smul_apply,
        ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, Pi.add_apply,
        Pi.smul_apply, Pi.zero_apply, Fin.addCases_left, add_zero]
    · simp only [Lslow, EntryWeakProofs.independentIntrinsicSlowEmbedding,
        EntryWeakProofs.independentIntrinsicParameterPacking, smul_apply,
        ContinuousLinearMap.pi_apply, Pi.add_apply, Pi.smul_apply, Fin.addCases_right,
        zero_apply, smul_zero, zero_add]
  have hn := scaled_mixed_parameter_jet_norm_le r q f hf Lslow Lfast lam B hlam hB hs
    (EntryWeakProofs.independentStoredParameterEmbedding_norm_le 2) hbound X z
  simpa only [he] using hn

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.CycleReference AVRegularity.EntryWeakProofs
namespace AVRegularity.Construction.Preservation.FullLift

/-! Balanced molecular drift jets have constants fixed before the band chain and all pulse times. -/

theorem balancedPulseDrift_vector_fast_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν B C : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hζ : IsFastProfile ζ)
    {slot : ℤ} (hslot : Odd slot) (K n : ℕ) (hn : n ≤ K)
    (hamp : Real.sqrt (ν / B) * (ocEpsilon q Λ m ^ (1 + α) / ν) ≤ C)
    (t : ℝ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun w => Real.sqrt (ν / B) •
      ocPulseCellDrift α q Λ ζ m ν slot t w) z‖ ≤ C * pulseFastDerivativeConstant K := by
  have hr : ContDiff ℝ (n : ℕ∞) (ocPulseCellDrift α q Λ ζ m ν slot t) :=
    (normalizedPulseDrift_contDiff hΛ hν hslot t).of_le
    (show (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)
  rw [iteratedFDeriv_const_smul_apply' hr.contDiffAt, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt (ν / B) * ((ocEpsilon q Λ m ^ (1 + α) / ν) * pulseFastDerivativeConstant K) :=
      mul_le_mul_of_nonneg_left
        (normalizedPulseDrift_vector_fast_bound hΛ hν hζ hslot K n hn t z) (Real.sqrt_nonneg _)
    _ = (Real.sqrt (ν / B) * (ocEpsilon q Λ m ^ (1 + α) / ν)) * pulseFastDerivativeConstant K :=
      (mul_assoc _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hamp (pulseFastDerivativeConstant_nonneg K)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! The literal native lift drift satisfies its balanced uniform jet supremum. -/

section
open AVRegularity.EntryWeakProofs
theorem uniform_native_lift_balanced_drift_sup_all_carriers {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Cw : ℕ → ℝ, (∀ n, 0 ≤ Cw n) ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧
      ∀ (ι : Type*) (h : ι → Type*) [∀ i, NormedAddCommGroup (h i)]
      [∀ i, NormedSpace ℝ (h i)] (Dm : ℕ), ∀ (D : OCData), D.α = α → D.q = q → Λ₀ ≤ D.Λ → D.ζ = ζ →
      IsOCBandChain α q D.Λ ζ D.term D.κ →
      ∀ m, 2 ≤ m → m < D.term → ∀ slot : ℤ, Odd slot →
      ∀ (A : RealChain) (ρ : ℝ) (edge : ConstituentEdges Dm h) (a b : ℝ),
      ∀ n : ℕ,
        (⨆ t ∈ Set.Icc a b, ⨆ z : Vec 2,
          ‖iteratedFDeriv ℝ n (fun w =>
            Real.sqrt (familyLiftData D m slot A ρ edge).η •
              (familyLiftData D m slot A ρ edge).v t w) z‖ₑ) ≤ ENNReal.ofReal (Cw n) := by
  obtain ⟨C, hC, Λ₀, hΛ₀, hbound⟩ :=
    bandChain_balanced_peclet_bound hα0 hα1 hs0 hs1 hq hζ
  let Cw : ℕ → ℝ := fun n => C * pulseFastDerivativeConstant n
  refine ⟨Cw, fun n => mul_nonneg (zero_le_one.trans hC)
    (pulseFastDerivativeConstant_nonneg n), Λ₀, hΛ₀, ?_⟩
  intro ι h _ _ Dm D hDα hDq hΛ hDζ hband m hm hmM slot hslot A ρ edge a b n
  apply iSup_le
  intro t
  apply iSup_le
  intro _ht
  apply iSup_le
  intro z
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  change ‖iteratedFDeriv ℝ n (fun w => Real.sqrt (D.kap m / D.kap (m - 1)) •
    ocPulseCellDrift D.α D.q D.Λ D.ζ m (D.kap m) slot t w) z‖ ≤ Cw n
  simp only [OCData.kap, Nat.min_eq_left (show m ≤ D.term by omega),
    Nat.min_eq_left (show m - 1 ≤ D.term by omega), hDα, hDq, hDζ]
  have hΛ1 : 1 ≤ D.Λ := by have hh := hΛ₀.trans hΛ; omega
  exact balancedPulseDrift_vector_fast_bound hΛ1
    (CycleReference.bandChain_pos hΛ1 hζ hband (by omega)) hζ hslot n n le_rfl
    (hbound D.Λ hΛ D.term (by omega) D.κ hband m hm hmM) t z
end

/-! The literal native lift drift satisfies its balanced uniform jet supremum. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}

/-- The raw balanced-pulse jet certificate gives the native drift supremum at any
level, including the terminal level and the plateau. No interior-scale estimate is assumed. -/
theorem native_lift_balanced_drift_sup_of_bound (D : OCData) (m : ℕ) (slot : ℤ)
    (A : RealChain) (ρ : ℝ) (edge : ConstituentEdges Dm h) (a b : ℝ)
    (K : ℕ) (Cw : ℕ → ℝ)
    (hbound : ∀ n ≤ K, ∀ t ∈ Set.Icc a b, ∀ z : Vec 2,
      ‖iteratedFDeriv ℝ n (fun w => Real.sqrt (D.kap m / D.kap (m - 1)) •
        ocPulseCellDrift D.α D.q D.Λ D.ζ m (D.kap m) slot t w) z‖ ≤ Cw n) :
    ∀ n ≤ K,
      (⨆ t ∈ Set.Icc a b, ⨆ z : Vec 2,
        ‖iteratedFDeriv ℝ n (fun w => Real.sqrt (familyLiftData D m slot A ρ edge).η •
          (familyLiftData D m slot A ρ edge).v t w) z‖ₑ) ≤ ENNReal.ofReal (Cw n) := by
  intro n hn
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  apply iSup_le
  intro z
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hbound n hn t ht z)
end

end AVRegularity.Construction.Preservation.FullLift
end
end

section
section
/-! A retained trace supported on the incoming component set has exactly the incoming weighted
norm, since its masses and markers depend only on the unchanged component history. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem weightedNorm_own_components {S T : Finset Comp} (hST : S ⊆ T)
    (q ρ : ℝ) (Λ : ℕ) (law : BirthLaw) (w : Comp → ℝ) {K : ℕ}
    (X : ∀ c : CompIn T, TorusHk K (hr c.1.root))
    (hzero : ∀ c, c.1 ∉ S → X c = 0) :
    weightedNorm ρ (fun c : CompIn T => compMass q Λ law c.1) (fun c => w c.1) X =
      weightedNorm ρ (fun v : CompIn S => compMass q Λ law v.1) (fun v => w v.1)
        (fun v => X ⟨v.1, hST v.2⟩) := by
  unfold weightedNorm massNormSq
  congr 1
  apply finite_own_component_sum hST
  intro c hc
  dsimp only
  rw [hzero c hc]
  change (compMass q Λ law c.1 / w c.1 ^ 2)⁻¹ *
    factorialNormSq ρ (0 : JetL2 (volume.restrict AVenhance.unitCube) K (hr c.1.root)) = 0
  rw [← CycleComparison.Coarse.norm_fjet_sq, CycleComparison.Coarse.fjet_zero,
    norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The literal readout is bounded component by component before taking time suprema. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem readout_component_factorial_square_le {S S' : Finset Comp} {K : ℕ}
    (m : ℕ) (E η ρ C w : ℝ) (hE : 0 ≤ E) (hw : 0 ≤ w)
    (z : CompIn S' → ℝ) (hz : ∀ c, 0 < z c) (v : CompIn S)
    (hentry : ∀ c : CompIn S', compParent m c.1 = v.1 →
      w / z c * E ^ (η * (compWord m c.1).length) ≤ 1)
    (hfiber : ((Finset.univ : Finset (CompIn S')).filter fun c => compParent m c.1 = v.1).card ≤ C)
    (X : ∀ c : CompIn S', TorusHk K (hr c.1.root)) :
    w ^ 2 * factorialNormSq ρ (succReadout m E η K X v).val ≤
      C * ∑ c : CompIn S', if compParent m c.1 = v.1 then
        z c ^ 2 * factorialNormSq ρ (X c).val else 0 := by
  have hs := weighted_parent_component_square_le (fun c : CompIn S' => compParent m c.1)
    v.1 (fun c => E ^ (η * (compWord m c.1).length))
    (fun c => Real.sqrt (factorialNormSq ρ (X c).val))
    (Real.sqrt (factorialNormSq ρ (succReadout m E η K X v).val)) w C z
    (Real.sqrt_nonneg _) hw hz (fun _ => Real.sqrt_nonneg _)
    (readout_factorial_amplitude m E η ρ hE X v) hentry hfiber
  have he : (∑ c : CompIn S', if compParent m c.1 = v.1 then
      (z c * Real.sqrt (factorialNormSq ρ (X c).val)) ^ 2 else 0) =
      ∑ c : CompIn S', if compParent m c.1 = v.1 then
        z c ^ 2 * factorialNormSq ρ (X c).val else 0 := by
    apply Finset.sum_congr rfl
    intro c _
    split_ifs
    · rw [mul_pow, Real.sq_sqrt (factorialNormSq_nonneg ρ _)]
    · rfl
  rw [he, mul_pow, Real.sq_sqrt (factorialNormSq_nonneg ρ _)] at hs
  exact hs

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The actual band recurrence supplies the lift contrast bound, including terminal levels. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.CycleReference
namespace AVRegularity.Construction.Preservation.FullLift

theorem native_kap_step_le (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (m : ℕ) (hm : 1 ≤ m) : D.kap m ≤ D.kap (m - 1) := by
  by_cases hM : m ≤ D.term
  · change D.κ (min m D.term) ≤ D.κ (min (m - 1) D.term)
    rw [Nat.min_eq_left hM, Nat.min_eq_left (by omega)]
    exact bandChain_step_ge hΛ hζ hκ hm hM
  · rw [EntryWeakProofs.weakData_kap_terminal D m (by omega),
      EntryWeakProofs.weakData_kap_terminal D (m - 1) (by omega)]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The compiled finite-chain chart estimate supplies uniform native Eulerian transport jets. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift
open EntryWeakProofs

/-- Convert the normalized chart estimate to the existing physical transport interface. -/
theorem jetBound_of_rescaled_chart {ρ C : ℝ} (hρ : 0 < ρ) {K : ℕ}
    (F : Vec 2 → Vec 2) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x,
      ‖iteratedFDeriv ℝ j (rescaledChart ρ F) x‖ ≤ C) :
    ChartTransport.JetBound F K C ρ := by
  intro j hj hjK y
  have hh := hb j hj hjK (ρ⁻¹ • y)
  rw [rescaledChart_positive_derivative_norm ρ hρ F hF j hj] at hh
  simp only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul] at hh
  have hd : ‖iteratedFDeriv ℝ j F y‖ ≤ C / ρ ^ (j - 1) :=
    (le_div_iff₀ (pow_pos hρ _)).mpr (by simpa only [mul_comm] using hh)
  simpa only [div_eq_mul_inv, inv_pow] using hd

theorem uniform_native_flow_jets (α s q : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (K : ℕ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      ∀ m, M + 1 ≤ m → ∀ slot : ℤ, Odd slot →
      ∀ ρ, 0 < ρ → ρ ≤ D.eps (m - 1) → ∀ u r,
      |u - D.slotAnchor m slot| ≤ ocTauPP D.α D.q D.Λ m →
      |r - D.slotAnchor m slot| ≤ ocTauPP D.α D.q D.Λ m →
      ∀ j, 1 ≤ j → j ≤ K → ∀ x,
        ‖iteratedFDeriv ℝ j
          (rescaledChart ρ (fun y => D.flowOf (m - 1) u y r)) x‖ ≤
          weakChartJetBudget K 0 := by
  obtain ⟨M, hM, hb⟩ := uniform_finite_weak_chart_eventually_bounded_jets
    α s q hα0 hα1 hs0 hs1 hq Λ hΛ ζ hζ 0 K
  refine ⟨M, hM, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq m hm slot hslot ρ hρ hρE u r hu hr j hj hjK x
  have hm1 : 1 ≤ m := by omega
  have hlevel : m - 1 + 1 = m := Nat.sub_add_cancel hm1
  have hu' : |u - D.slotAnchor (m - 1 + 1 + 0) slot| ≤
      finiteChainWindowRadius 0 0 * ocTauPP D.α D.q D.Λ (m - 1 + 1 + 0) := by
    simpa only [Nat.add_zero, hlevel, finiteChainWindowRadius, Nat.sub_self,
      Nat.cast_zero, mul_zero, zero_add, one_mul] using hu
  have hr' : |r - D.slotAnchor (m - 1 + 1 + 0) slot| ≤
      finiteChainWindowRadius 0 0 * ocTauPP D.α D.q D.Λ (m - 1 + 1 + 0) := by
    simpa only [Nat.add_zero, hlevel, finiteChainWindowRadius, Nat.sub_self,
      Nat.cast_zero, mul_zero, zero_add, one_mul] using hr
  exact hb D hDα hDq hDΛ hDζ hseq (m - 1) (by omega) 0 (fun _ => slot)
    (fun _ => ⟨0, 0⟩) (fun _ _ => hslot) (fun n hn => by omega)
    ρ hρ (by simpa only [Nat.add_zero] using hρE) 0 le_rfl u r hu' hr' j hj hjK x

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The actual reference-flux covariance primitive is symmetric entry by entry. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem ocPi_entry_symm (k : {k : ℤ // Odd k}) (i j : Fin 2) : ocPi k i j = ocPi k j i := by
  unfold ocPi
  split <;> fin_cases i <;> fin_cases j <;> norm_num

theorem refFlux_entry_symm {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (i j : Fin 2) :
    ocRefFlux α q Λ ζ m ν t i j = ocRefFlux α q Λ ζ m ν t j i := by
  have hI : (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = (1 : Matrix (Fin 2) (Fin 2) ℝ) j i := by
    simp only [Matrix.one_apply, eq_comm]
  rcases CycleReference.pulseMatrixSum_single (α := α) (q := q) (m := m) hΛ hζ ν t with
    ⟨k, _hk, hmatrix⟩ | ⟨_hquiet, hmatrix⟩
  · unfold ocRefFlux
    rw [hmatrix]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [ocPi_entry_symm k i j, hI]
  · unfold ocRefFlux
    rw [hmatrix]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul, mul_zero, add_zero]
    rw [hI]

theorem native_covPrimitive_entry_symm (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) (t : ℝ) (i j : Fin 2) :
    covPrimitive D m t i j = covPrimitive D m t j i := by
  change (∫ r in (0 : ℝ)..t, ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) r i j -
      D.κ (m - 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) =
    ∫ r in (0 : ℝ)..t, ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) r j i -
      D.κ (m - 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ) j i
  apply intervalIntegral.integral_congr
  intro r _
  change ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) r i j -
      D.κ (m - 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j =
    ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) r j i -
      D.κ (m - 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ) j i
  rw [refFlux_entry_symm hΛ hζ]
  simp only [Matrix.one_apply, eq_comm]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! One uniform normalized flow budget controls both physical charts on every active native pulse. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift
open EntryWeakProofs

theorem uniform_native_physical_flow_jets (α s q : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (K : ℕ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      ∀ m, M + 1 ≤ m → ∀ slot : ℤ, Odd slot →
      ∀ ρ, 0 < ρ → ρ ≤ D.eps (m - 1) → ∀ t ∈ ocPulseWindow D.α D.q D.Λ m slot,
        ChartTransport.JetBound
          (fun y => D.flowOf (m - 1) t y (D.slotAnchor m slot)) K (weakChartJetBudget K 0) ρ ∧
        ChartTransport.JetBound
          (fun y => D.flowOf (m - 1) (D.slotAnchor m slot) y t) K (weakChartJetBudget K 0) ρ := by
  obtain ⟨M, hM, hb⟩ := uniform_native_flow_jets α s q hα0 hα1 hs0 hs1 hq Λ hΛ ζ hζ K
  refine ⟨M, hM, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq m hm slot hslot ρ hρ hρE t ht
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hdist : |t - D.slotAnchor m slot| ≤ ocTauPP D.α D.q D.Λ m :=
    weak_lift_anchor_distance D.α D.q hΛD m slot t ht
  have hzero : |D.slotAnchor m slot - D.slotAnchor m slot| ≤ ocTauPP D.α D.q D.Λ m := by
    have hz : 0 ≤ ocTauPP D.α D.q D.Λ m := (Construction.Stream.ocTauPP_pos hΛD).le
    simpa only [sub_self, abs_zero] using hz
  constructor
  · apply jetBound_of_rescaled_chart hρ _
      (CycleReference.streamFlow_spatial_smooth (D.hΦ (m - 1)) t (D.slotAnchor m slot))
    exact hb D hDα hDq hDΛ hDζ hseq m hm slot hslot ρ hρ hρE t
      (D.slotAnchor m slot) hdist hzero
  · apply jetBound_of_rescaled_chart hρ _
      (CycleReference.streamFlow_spatial_smooth (D.hΦ (m - 1)) (D.slotAnchor m slot) t)
    exact hb D hDα hDq hDΛ hDζ hseq m hm slot hslot ρ hρ hρE
      (D.slotAnchor m slot) t hzero hdist

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The literal birth readout sends the selected component representatives to a classical field. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem readout_classicalRep {S S' : Finset Comp} {K r : ℕ} (hrK : r ≤ K)
    (m : ℕ) (E η : ℝ) (X : ∀ c : CompIn S', TorusHk K (hr c.1.root))
    (a : ∀ c : CompIn S', Vec 2 → hr c.1.root)
    (hrep : ∀ c, IsClassicalRep (X c) (a c) r) (v : CompIn S) :
    IsClassicalRep (succReadout m E η K X v)
      (fun x => ∑ c : CompIn S', if h : compParent m c.1 = v.1 then
        E ^ (η * (compWord m c.1).length) •
          cast (congrArg hr ((compParent_root m c.1).symm.trans (congrArg Comp.root h))) (a c x)
        else 0) r := by
  classical
  unfold succReadout
  apply classicalRep_sum hrK
  intro c
  by_cases h : compParent m c.1 = v.1
  · simp only [h, ↓reduceDIte]
    exact classicalRep_smul _ _
      (classicalRep_rootCast ((compParent_root m c.1).symm.trans (congrArg Comp.root h))
        (X c) (a c) (hrep c)) _
  · simp only [h, ↓reduceDIte]
    exact classicalRep_zero hrK

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Actual inflated identity prices and one marked ledger control both production kernel matrices. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_kernel_schur_of_marked_ledger
    (G : GenStage D hr Dm bw j₀) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (ν ρ a b A Sbound : ℝ) (π marker : CompIn G.comps → ℝ) (n : ℕ) (c : ℕ → ℝ)
    (hν : 0 < ν) (hA : 0 ≤ A) (hπ : ∀ v, 0 < π v) (hmarker : ∀ v, 0 < marker v)
    (hwidth : ∀ v u γ, 0 < (G.kernelOf P seedK freshK v u γ).width)
    (hc : ∀ j, j + 2 ≤ Dm → 0 ≤ c j)
    (hprice : ∀ v u γ,
      (∑ d : ↥(Finset.Icc 2 Dm),
        ((coefficientSeminorm ρ n a b (G.physCoeff v u γ d.1)).toReal * c (d.1 - 2)) /
          (ν * (G.kernelOf P seedK freshK v u γ).width ^ (d.1 - 2))) ≤
        A * (‖(G.fam.identity v u γ).map‖ * (G.fam.identity v u γ).record.size *
          constituentPrice (G.fam.identity v u γ).record))
    (hledger : markedLedger π marker G.fam ≤ Sbound) :
    ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = marker →
      SchurBound (A * Sbound)
        (kernelSchurMatrix ν ρ (fun v => π v / w v ^ 2) n Dm a b c
          (fun v u γ => (G.kernelOf P seedK freshK v u γ).width)
          (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
          (fun v u γ d => G.physCoeff v u γ d.1)) := by
  have hpriced := priced_record_ledger_schur G.fam π marker hπ hmarker Sbound hledger
  intro w hw
  apply native_kernel_schur_bound_of_priced_identity_prices G P seedK freshK ν ρ a b A Sbound
    (fun v => π v / w v ^ 2) n c hν hwidth hc hprice hA
  rcases hw with rfl | rfl
  · simpa only [one_pow, div_one] using hpriced.1
  · exact hpriced.2

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The marked incoming data bound also controls the ordinary preparation datum. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem ordinary_input_from_marked (G : GenStage D hr Dm b j₀)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (law : BirthLaw) (hiota : 0 ≤ law.iota)
    {K : ℕ} (ρ : ℝ) (f : ∀ v : CompIn G.comps, TorusHk K (hr v.1.root))
    {A : ℝ} (hf : weightedNorm ρ (G.mass law) (G.marker law) f ≤ A) :
    weightedNorm ρ (G.mass law) (fun _ => 1) f ≤ A := by
  apply le_trans _ hf
  apply weightedNorm_mono ρ (G.mass law) (fun _ => 1) (G.marker law)
  · intro v
    exact Buffer.birth_compMass_pos hq hΛ law v.1
  · intro _
    exact zero_le_one
  · intro v
    exact compMarker_one_le hq hΛ law hiota v.1

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The native covariance retains its original anchor and is continuous at every time. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem native_covPrimitive_entry_continuous (D : OCData) (m : ℕ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hν : 0 < D.κ m) (i j : Fin 2) :
    Continuous (fun t => covPrimitive D m t i j) := by
  have hc := (FreshAxes.refFlux_entry_continuous (α := D.α) (q := D.q) (m := m)
    hΛ hζ hν i j).sub (continuous_const (y :=
      D.κ (m - 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
  change Continuous (fun t => ∫ r in (0 : ℝ)..t,
    ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) r i j -
      D.κ (m - 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
  exact intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable (μ := volume) a b) 0

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Actual fresh kernels inherit regularizer certificates from their spanning bound. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

theorem exists_fresh_kernel_regularizer_constants_of_span_bound (φ₀ : Vec 2 → ℝ)
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (n : ℕ+) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] [CompleteSpace E],
    ∀ (D : OCData) (b : ℕ), 1 ≤ D.Λ → IsFastProfile D.ζ →
      0 < D.κ b → 0 < D.κ (b + 1) →
    ∀ (S : KernelSpec), S.order = n → 0 < S.width →
      IsFreshAxes D b S.H₁ S.H₂ →
    (∀ t, IsUnit (S.span t).det ∧
      ‖(Matrix.toLin' (S.span t)⁻¹).toContinuousLinearMap‖ ≤ 2) →
    ∀ (ρ a b' : ℝ) (k Dm : ℕ),
      IsSpatialRegularizerTorus (G := E) ρ k Dm a b' c S.width
        (S.op φ₀ (hd.continuous.integrable_of_hasCompactSupport hc)) := by
  classical
  obtain ⟨c, hcn, hreg⟩ := exists_kernelSpec_vector_regularizer_constants φ₀ hc hd n
  refine ⟨c, hcn, ?_⟩
  intro E _ _ _ _ _ _ D b hΛ hζ hκb hκnext S hn hr haxes hspan ρ a b' k Dm
  have hreal (t : ℝ) := fresh_axes_exists_equivalences D b hΛ hζ hκb hκnext
    S.H₁ S.H₂ haxes t
  choose R T hR hT using hreal
  let hu (t : ℝ) : IsUnit (S.span t).det := (hspan t).1
  let V (t : ℝ) := matrixContinuousLinearEquiv (S.span t) (hu t)
  refine hreg E S hn hr (fresh_axes_measurable D b hΛ S.H₁ S.H₂ haxes).1
    (fresh_axes_measurable D b hΛ S.H₁ S.H₂ haxes).2 R T V
    (fun t => (hR t).symm) (fun t => (hT t).symm) ?_ ?_ ?_ ρ a b' k Dm
  · intro t
    exact (kernelSpan_first_column S t (hu t)).trans
      (congrArg (fun f : Vec 2 →L[ℝ] Vec 2 => f (basisVec 0)) (hR t)).symm
  · intro t
    exact (kernelSpan_second_column S t (hu t)).trans
      (congrArg (fun f : Vec 2 →L[ℝ] Vec 2 => f (basisVec 1)) (hT t)).symm
  · intro t
    change ‖(matrixContinuousLinearEquiv (S.span t) (hu t)).symm.toContinuousLinearMap‖ ≤ 2
    rw [matrixContinuousLinearEquiv_symm_map]
    exact (hspan t).2

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The constructed classical covariance field satisfies the literal native duality definition. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem classicalRep_value_ae {K r : ℕ} (W : TorusHk K E) (a : Vec 2 → E)
    (hrep : IsClassicalRep W a r) :
    W.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube] a := by
  have h := hrep.2.2.2 0 (Nat.zero_le r) Fin.elim0
  unfold torusJetOrder at h
  simp only [Nat.zero_le, ↓reduceDIte, orderedDerivative_zero] at h
  exact h

theorem covariancePolynomial_isCovImage {K L : ℕ}
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, Hc i j = Hc j i)
    (p : ℕ) (a : ℕ → ℝ) (Z : TorusHk K E) (W : TorusHk L E) (u : Vec 2 → E)
    (hZ : IsClassicalRep Z u (2 * p))
    (hW : IsClassicalRep W (covariancePolynomial Hc p a u) 0) :
    IsCovImage (covariancePolynomial Hc p a) Z W := by
  intro φ hφ hpφ
  have hz := classicalRep_value_ae Z u hZ
  have hw := classicalRep_value_ae W (covariancePolynomial Hc p a u) hW
  calc
    _ = cellInner (covariancePolynomial Hc p a u) φ := by
      apply integral_congr_ae
      filter_upwards [hw] with x hx
      rw [hx]
    _ = cellInner u (covariancePolynomial Hc p a φ) :=
      covariancePolynomial_cellInner_adjoint Hc hH p a u φ hZ.2.1
        (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hZ.2.2.1 hpφ
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hz] with x hx
      rw [hx]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The weak gradient commutes with the literal parent readout, including its root casts. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]

theorem gradient_rootCast {r r' K : ℕ} (h : r = r') (X : TorusHk (K + 1) (hr r)) :
    torusGradientTensor (cast (congrArg (fun s => TorusHk (K + 1) (hr s)) h) X) =
      cast (congrArg (fun s => TorusHk K (PiLp 2 (fun _ : Fin 2 => hr s))) h)
        (torusGradientTensor X) := by
  subst r'
  rfl

theorem readout_gradient_tensor {S S' : Finset Comp} {K : ℕ} (m : ℕ) (E η : ℝ)
    (X : ∀ c : CompIn S', TorusHk (K + 1) (hr c.1.root)) (v : CompIn S) :
    torusGradientTensor (succReadout m E η (K + 1) X v) =
      succReadout (hr := fun r => PiLp 2 (fun _ : Fin 2 => hr r)) m E η K
        (fun c => torusGradientTensor (X c)) v := by
  classical
  rw [← torusGradientTensorCLM_apply]
  unfold succReadout
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs with h
  · rw [map_smul, torusGradientTensorCLM_apply,
      gradient_rootCast ((compParent_root m c.1).symm.trans (congrArg Comp.root h))]
  · exact map_zero _

end AVRegularity.Construction.Preservation.FullLift
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Construct the actual native covariance image from a reserved classical representative. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem covariancePolynomial_carrier_exists {K : ℕ}
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, Hc i j = Hc j i)
    (p n : ℕ) (a : ℕ → ℝ) (Z : TorusHk K E) (u : Vec 2 → E)
    (hZ : IsClassicalRep Z u (n + 2 * p)) :
    ∃ W : TorusHk n E,
      IsCovImage (covariancePolynomial Hc p a) Z W ∧
      IsClassicalRep W (covariancePolynomial Hc p a u) n := by
  have hc := covariancePolynomial_contDiff Hc p n a u hZ.2.1
  have huLow : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u := hZ.2.1.of_le
    (show ((2 * p : ℕ) : WithTop ℕ∞) ≤ ((n + 2 * p : ℕ) : WithTop ℕ∞) from
      by exact_mod_cast (Nat.le_add_left (2 * p) n))
  have hp := covariancePolynomial_periodic Hc p a u huLow hZ.2.2.1
  let W := classicalHilbertHk n (covariancePolynomial Hc p a u) hc hp
  have hW := classicalHilbertHk_rep n (covariancePolynomial Hc p a u) hc hp
  refine ⟨W, ?_, hW⟩
  exact covariancePolynomial_isCovImage Hc hH p a Z W u
    (classicalRep_order_mono Z u hZ (Nat.le_add_left (2 * p) n))
    (classicalRep_order_mono W _ hW (Nat.zero_le n))

theorem covPolyP_carrier_exists {K : ℕ}
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, Hc i j = Hc j i)
    (p n : ℕ) (Z : TorusHk K E) (u : Vec 2 → E)
    (hZ : IsClassicalRep Z u (n + 2 * p)) :
    ∃ W : TorusHk n E, IsCovImage (covPolyP Hc p) Z W ∧ IsClassicalRep W (covPolyP Hc p u) n := by
  obtain ⟨W, hI, hrep⟩ := covariancePolynomial_carrier_exists Hc hH p n
    (fun l => (l.factorial : ℝ)⁻¹) Z u hZ
  have hfun : covariancePolynomial (E := E) Hc p (fun l => (l.factorial : ℝ)⁻¹) = covPolyP Hc p := by
    funext f
    exact covariancePolynomial_eq_P Hc p f
  rw [hfun] at hI hrep
  exact ⟨W, hI, hrep⟩

theorem covPolyQ_carrier_exists {K : ℕ}
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, Hc i j = Hc j i)
    (p n : ℕ) (Z : TorusHk K E) (u : Vec 2 → E)
    (hZ : IsClassicalRep Z u (n + 2 * p)) :
    ∃ W : TorusHk n E, IsCovImage (covPolyQ Hc p) Z W ∧ IsClassicalRep W (covPolyQ Hc p u) n := by
  obtain ⟨W, hI, hrep⟩ := covariancePolynomial_carrier_exists Hc hH p n
    (fun l => (-1 : ℝ) ^ l / (l.factorial : ℝ)) Z u hZ
  have hfun : covariancePolynomial (E := E) Hc p (fun l => (-1 : ℝ) ^ l / (l.factorial : ℝ)) =
      covPolyQ Hc p := by
    funext f
    exact covariancePolynomial_eq_Q Hc p f
  rw [hfun] at hI hrep
  exact ⟨W, hI, hrep⟩
end

/-! The preparation's literal Q_p bound controls every retained trace, by exact reindexing of
its incoming support. No covariance estimate or chosen trace is added as a premise. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]

theorem common_preparation_retained_trace_norm {D : OCData} {Dm j₀ : ℕ} {b : ℝ}
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G Gr : GenStage D hr Dm b j₀)
    {cr Q CQ C : ℝ} {p Nout Naux m : ℕ} {s tf tp : ℝ}
    (hlevel : G.level = m) (hST : G.comps ⊆ Gr.comps)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hprep : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ C p Nout Naux s tf tp Preg)
    (w : Comp → ℝ) (hw : ((fun v : CompIn G.comps => w v.1) = fun _ => 1) ∨
      (fun v : CompIn G.comps => w v.1) = G.marker law)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ)
    (hf : weightedNorm 1 (G.mass law) (fun v => w v.1) f ≤ Ain)
    (Y0 : ∀ c : CompIn Gr.comps, TorusHk Naux (hr c.1.root))
    (htrace : IsRetainedTrace G Gr m p tp (Preg f) Y0) :
    weightedNorm (rhoEnh D cr G.level) (Gr.mass law) (fun c => w c.1) Y0 ≤ C * Ain := by
  let Qh : ∀ v : CompIn G.comps, TorusHk Naux (hr v.1.root) :=
    fun v => Y0 ⟨v.1, hST v.2⟩
  have hQ : ∀ v, IsCovImage (covPolyQ (covPrimitive D G.level tp) p) (Preg f v) (Qh v) := by
    intro v
    simpa only [hlevel, Qh] using htrace.1 ⟨v.1, hST v.2⟩ v.2
  have hb := (hprep.2.2.2.2 (fun v => w v.1) hw f).2.2.2 Ain hf Qh hQ
  have he := weightedNorm_own_components hST D.q (rhoEnh D cr G.level) D.Λ law w Y0 htrace.2
  exact he.trans_le hb
end

/-! Allocate the qualitative higher trace at any order supported by the existing preparation reserve. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem higher_covariance_Q_trace_at_order {Naux Nout R : ℕ} (p : ℕ)
    (hNR : Naux ≤ R) (hreserve : R + 2 * p + 2 ≤ Nout)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, Hc i j = Hc j i)
    (f : TorusHk Nout E) (Y0 : TorusHk Naux E)
    (htrace : IsCovImage (covPolyQ Hc p) f Y0) :
    ∃ Yhi : TorusHk R E, IsCovImage (covPolyQ Hc p) f Yhi ∧
      truncateTorusHk hNR Yhi = Y0 := by
  obtain ⟨a, ha⟩ := hilbert_classicalRep_exists Nout (R + 2 * p) hreserve f
  obtain ⟨Yhi, hI, _⟩ := covPolyQ_carrier_exists Hc hH p R f a ha
  exact ⟨Yhi, hI, covImage_unique (covPolyQ Hc p) f _ Y0
    (covImage_truncate hNR (covPolyQ Hc p) f Yhi hI) htrace⟩
end

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Construct the prepared covariance input with extra qualitative derivatives from higher retained values. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]

theorem higher_readout_covariance_input_exists {S S' : Finset Comp}
    (D : OCData) (m p Naux R s : ℕ) (hNR : Naux ≤ R)
    (hreserve : max (Naux - 2 * p) s + 2 * p + 2 ≤ R)
    (η tp tf : ℝ) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (Y : ∀ c : CompIn S', ℝ → TorusHk Naux (hr c.1.root))
    (Yhi : ∀ c : CompIn S', ℝ → TorusHk R (hr c.1.root))
    (heq : ∀ c, ∀ t ∈ Set.Icc tp tf, Y c t = truncateTorusHk hNR (Yhi c t)) :
    ∃ (PZ : ∀ v : CompIn S, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (a : ℝ → Vec 2 → ∀ v : CompIn S, hr v.1.root),
      (∀ v, ∀ t ∈ Set.Icc tp tf,
        IsCovImage (covPolyP (covPrimitive D m t) p)
          (succReadout m (D.eps (m - 1)) η Naux (fun c => Y c t) v) (PZ v t) ∧
        IsClassicalRep (PZ v t) (fun x => a t x v) (Naux - 2 * p)) ∧
      ∀ t, ContDiff ℝ (s : ℕ∞) (a t) := by
  classical
  let q := max (Naux - 2 * p) s
  have hex (v : CompIn S) (t : ℝ) :
      ∃ (W : TorusHk q (hr v.1.root)) (a : Vec 2 → hr v.1.root),
        IsCovImage (covPolyP (covPrimitive D m t) p)
          (succReadout m (D.eps (m - 1)) η R (fun c => Yhi c t) v) W ∧
        IsClassicalRep W a q := by
    obtain ⟨u, hu⟩ := hilbert_classicalRep_exists R (q + 2 * p) hreserve
      (succReadout m (D.eps (m - 1)) η R (fun c => Yhi c t) v)
    obtain ⟨W, hW, hw⟩ := covPolyP_carrier_exists (covPrimitive D m t)
      (native_covPrimitive_entry_symm D hΛ hζ m t) p q _ u hu
    exact ⟨W, _, hW, hw⟩
  choose W a ha using hex
  have hL : Naux - 2 * p ≤ q := Nat.le_max_left _ _
  refine ⟨fun v t => truncateTorusHk hL (W v t), fun t x v => a v t x, ?_, ?_⟩
  · intro v t ht
    refine ⟨?_, classicalRep_truncate hL le_rfl (W v t) (a v t)
      (classicalRep_order_mono (W v t) (a v t) (ha v t).2 hL)⟩
    have hc := covImage_truncate_input hNR _ _ _
      (covImage_truncate hL _ _ _ (ha v t).1)
    rw [truncate_succReadout] at hc
    have he : (fun c => truncateTorusHk hNR (Yhi c t)) = fun c => Y c t := by
      funext c
      exact (heq c t ht).symm
    rw [he] at hc
    exact hc
  · intro t
    apply contDiff_pi.mpr
    intro v
    exact (ha v t).2.2.1.of_le (by exact_mod_cast Nat.le_max_right (Naux - 2 * p) s)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Uniform regularization of actual fresh kernels, with constants chosen before data. -/

theorem uniform_fresh_kernel_regularizer
    (φ₀ : Vec 2 → ℝ) (hc : HasCompactSupport φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (n : ℕ+)
    (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧ ∃ m₀ : ℕ, 2 ≤ m₀ ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] [CompleteSpace E],
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ b : ℕ, m₀ ≤ b + 1 → b + 1 ≤ D.term →
    ∀ S : KernelSpec, S.order = n → 0 < S.width → IsFreshAxes D b S.H₁ S.H₂ →
    ∀ (ρ a b' : ℝ) (k Dm : ℕ),
      IsSpatialRegularizerTorus (G := E) ρ k Dm a b' c S.width
        (S.op φ₀ (hd.continuous.integrable_of_hasCompactSupport hc)) := by
  obtain ⟨c, hcn, hreg⟩ := exists_fresh_kernel_regularizer_constants_of_span_bound φ₀ hc hd n
  obtain ⟨m₀, hm₀, hspan⟩ := uniform_fresh_spanning_inverse_bound α s q hα₀ hα₁ hs₀ hs₁
    hq ζ hζ Λ hΛ
  refine ⟨c, hcn, m₀, hm₀, ?_⟩
  intro E _ _ _ _ _ _ D hDα hDq hDΛ hDζ hΦ hband b hb hterm S hn hr haxes
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hκnext := CycleReference.bandChain_pos hΛD hζD hband hterm
  have hκb := CycleReference.bandChain_pos hΛD hζD hband (show b ≤ D.term by omega)
  exact hreg E D b hΛD hζD hκb hκnext S hn hr haxes
    (hspan D hDα hDq hDΛ hDζ hΦ hband b hb hterm S haxes)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Upgrade the actual complete retained trace, including zero data on every new component. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem retained_trace_higher_exists_at_order (G Gr : GenStage D hr Dm b j₀) (m p : ℕ) (tp : ℝ)
    {Naux Nout R : ℕ} (hNR : Naux ≤ R) (hreserve : R + 2 * p + 2 ≤ Nout)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (h : ∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))
    (Y0 : ∀ c : CompIn Gr.comps, TorusHk Naux (hr c.1.root))
    (htrace : IsRetainedTrace G Gr m p tp h Y0) :
    ∃ Yhi : ∀ c : CompIn Gr.comps, TorusHk R (hr c.1.root),
      IsRetainedTrace G Gr m p tp h Yhi ∧
      ∀ c, truncateTorusHk hNR (Yhi c) = Y0 c := by
  classical
  let A (c : CompIn Gr.comps) (hc : c.1 ∈ G.comps) :=
    higher_covariance_Q_trace_at_order p hNR hreserve (covPrimitive D m tp)
      (native_covPrimitive_entry_symm D hΛ hζ m tp) (h ⟨c.1, hc⟩) (Y0 c) (htrace.1 c hc)
  let Yhi (c : CompIn Gr.comps) : TorusHk R (hr c.1.root) :=
    if hc : c.1 ∈ G.comps then Classical.choose (A c hc) else 0
  refine ⟨Yhi, ⟨?_, ?_⟩, ?_⟩
  · intro c hc
    dsimp only [Yhi]
    simp only [hc, ↓reduceDIte]
    exact (Classical.choose_spec (A c hc)).1
  · intro c hc
    dsimp only [Yhi]
    simp only [hc, ↓reduceDIte]
  · intro c
    by_cases hc : c.1 ∈ G.comps
    · dsimp only [Yhi]
      simp only [hc, ↓reduceDIte]
      exact (Classical.choose_spec (A c hc)).2
    · dsimp only [Yhi]
      simp only [hc, ↓reduceDIte, map_zero]
      exact (htrace.2 c hc).symm

end AVRegularity.Construction.Preservation.FullLift
end
end
