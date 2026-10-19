-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.QuietScalarEvolution
public import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets
public import AVRegularity.CycleComparison.Coarse.Adj.Coarse
import AVRegularity.CycleComparison.Coarse.Fact.GradFluxIdent
import AVRegularity.EntryWeakAssembly.CoordinateWordRawHilbertCurves
import AVRegularity.EntryWeak.IndependentTransportedCoefficientJetBound
public import AVRegularity.CycleComparison.Coarse.Fact.FBoundOps
import AVRegularity.CycleComparison.Error.WeakSolution

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.WeakEntryProofs

/-! Moving-adjoint identity for a native scalar row with an actual flux source.
This is the weak Duhamel identity used by the finite triangular quiet margin expansion.
The forcing and the adjoint gradient are genuine L² time trajectories. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The native forced moving-test identity. The flux is the supplied forcing,
not an assumed bound or a separately chosen representative of the source. -/
def WeakScalarForcedAdjointPairStatement : Prop :=
  ∀ {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2} (P : ℕ), a ≤ b →
    WeakScalarTorusDrift ν ρ a b v P →
    ∀ {D : ℕ} {f : TorusHk 0 E}
      {F : ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => E))}
      {u : ℝ → TorusHk 0 E} {w : ℝ → TorusHk 1 E},
    MemLp F 2 (volume.restrict (Icc a b)) →
    IsTorusForcedRow ν a b v D 0 f F (fun _ => 0) u w →
    ∀ {g : TorusHk P E} {z : ℝ → TorusHk P E} {zw : ℝ → TorusHk (P + 1) E},
    WeakScalarTorusSolution ν (-b) (-a) (fun t x => -v (-t) x) P g z zw →
    inner ℝ (u b) (truncateTorusHk (Nat.zero_le P) (z (-b))) -
      inner ℝ (u a) (truncateTorusHk (Nat.zero_le P) (z (-a))) =
      -(∫ t in a..b, inner ℝ (torusHkValueCLM (F t))
        (torusH1GradientL2CLM (E := E)
          (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le P)) (zw (-t)))))

/-- Flux divergence represented in H¹ by the adjoint of its gradient readout. -/
def weakScalarFluxDualPath
    (F : ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => E))) (t : ℝ) : TorusHk 1 E :=
  (torusH1GradientL2CLM (E := E)).adjoint (torusHkValueCLM (F t))

/-- The actual forced Riesz time derivative. -/
def weakScalarForcedDualPath {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {P : ℕ}
    (hd : WeakScalarTorusDrift ν ρ a b v P) (w : ℝ → TorusHk 1 E)
    (F : ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => E))) (t : ℝ) : TorusHk 1 E :=
  weakScalarDualPath hd w t - weakScalarFluxDualPath F t

/-- Square-integrable flux gives a square-integrable H¹ Riesz derivative. -/
theorem weak_scalar_flux_dual_memLp
    {a b : ℝ} {F : ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => E))}
    (hF : MemLp F 2 (volume.restrict (Icc a b))) :
    MemLp (weakScalarFluxDualPath F) 2 (volume.restrict (Icc a b)) :=
  ((torusH1GradientL2CLM (E := E)).adjoint.comp
    (torusHkValueCLM (E := PiLp 2 (fun _ : Fin 2 => E)) (K := 0))).comp_memLp' hF

/-- The native flux density is exactly its Hilbert readout pairing. -/
theorem weak_scalar_flux_spatial_pairing
    (F : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => E))) (φ : TorusHk 1 E) :
    Integrable (fun x => ∑ k : Fin 2, inner ℝ
      (F.toFunction.jet (valueIndex2 0) x k)
      (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x))
      (volume.restrict AVenhance.unitCube) ∧
    (∫ x in AVenhance.unitCube, ∑ k : Fin 2, inner ℝ
      (F.toFunction.jet (valueIndex2 0) x k)
      (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) =
      inner ℝ (torusHkValueCLM F) (torusH1GradientL2CLM (E := E) φ) := by
  have he : (fun x => ∑ k : Fin 2, inner ℝ
      (F.toFunction.jet (valueIndex2 0) x k)
      (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) =ᵐ[
        volume.restrict AVenhance.unitCube] fun x =>
      inner ℝ (torusHkValueCLM F x) (torusH1GradientL2CLM (E := E) φ x) := by
    filter_upwards [torusRawValue_ae F, torusRawTestGradient_ae φ] with x hFx hφx
    rw [hFx, ← hφx, PiLp.inner_apply]
  refine ⟨(L2.integrable_inner (𝕜 := ℝ) _ _).congr he.symm, ?_⟩
  rw [integral_congr_ae he, ← L2.inner_def]

/-- The literal transport, diffusion and forcing integrand represents the
forced H¹ Riesz derivative at every time in the window. -/
theorem weak_scalar_forced_spatial_pairing {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {P : ℕ} (hd : WeakScalarTorusDrift ν ρ a b v P)
    (w : ℝ → TorusHk 1 E) (F : ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => E)))
    (t : ℝ) (ht : t ∈ Icc a b) (φ : TorusHk 1 E) :
    (∫ x in AVenhance.unitCube,
      -(∑ k : Fin 2, v t x k * inner ℝ
        ((w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
        (φ.toFunction.jet (valueIndex2 1) x)) -
      ν * ∑ k : Fin 2, inner ℝ
        ((w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
        (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x) -
      ∑ k : Fin 2, inner ℝ ((F t).toFunction.jet (valueIndex2 0) x k)
        (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) =
      inner ℝ (weakScalarForcedDualPath hd w F t) φ := by
  have hbase := weak_scalar_native_spatial_pairing_integrable hd w t ht φ
  have hflux := weak_scalar_flux_spatial_pairing (F t) φ
  rw [integral_sub hbase.1 hflux.1, hbase.2, hflux.2]
  simp only [weakScalarForcedDualPath, weakScalarFluxDualPath, inner_sub_left,
    ContinuousLinearMap.adjoint_inner_left]

/-- A native forced row supplies the genuine weak Hilbert time curve.
Only L² flux and its order-zero weak equation are required. -/
theorem weak_scalar_forced_hilbert_curve {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {P D : ℕ} (hd : WeakScalarTorusDrift ν ρ a b v P)
    (hab : a ≤ b) {f : TorusHk 0 E}
    {F : ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => E))}
    {u : ℝ → TorusHk 0 E} {w : ℝ → TorusHk 1 E}
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hs : IsTorusForcedRow ν a b v D 0 f F (fun _ => 0) u w) :
    WeakScalarHilbertCurve a b (fun t => torusHkValueCLM (u t))
      w (weakScalarForcedDualPath hd w F) := by
  have hdual : MemLp (weakScalarForcedDualPath hd w F) 2
      (volume.restrict (Icc a b)) := by
    simpa only [weakScalarForcedDualPath, Pi.sub_apply] using!
      (weak_scalar_dual_path_memLp hd hab w (hs.2.1 0)).sub
        (weak_scalar_flux_dual_memLp hF)
  refine ⟨torusHkValueCLM.continuous.comp_continuousOn (hs.1 0),
    hs.2.1 0, hdual, ?_, ?_⟩
  · filter_upwards [hs.2.2.1 0] with t ht
    rw [← ht]
    rfl
  · intro s hsa t hta hst φ
    have hleft := CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_left hta.2 hs
    have hright := CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_right hsa.1 hst hleft
    have hh := hright.2.2.2.2 0 t ⟨hst, le_rfl⟩ φ
    simp only [CoupledWeakIdentity, zero_apply, Finset.sum_const_zero] at hh
    have he := hh.2.2.2.2
    rw [(torusRawValue_pairing_integrable_and_integral (u t) φ).2,
      (torusRawValue_pairing_integrable_and_integral (u s) φ).2] at he
    rw [intervalIntegral.integral_of_le hst]
    refine he.trans (integral_congr_ae ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hz : (0 : TorusHk 0 E).toFunction.jet (valueIndex2 0) =ᵐ[
        volume.restrict AVenhance.unitCube] fun _ => 0 := by
      exact (torusRawValue_ae (0 : TorusHk 0 E)).trans (by
        simpa only [map_zero, Pi.zero_apply] using! (Lp.coeFn_zero (E := E) (p := 2)
          (μ := volume.restrict AVenhance.unitCube)))
    rw [← weak_scalar_forced_spatial_pairing hd w F r
      ⟨hsa.1.trans hr.1.le, hr.2.trans hta.2⟩ φ]
    apply integral_congr_ae
    filter_upwards [hz] with x hx
    simp only [hx, inner_zero_left, add_zero, PiLp.zero_apply, zero_add]

/-- The native forced moving-adjoint formula, with the literal flux pairing
and actual values at both closed endpoints. -/
theorem weak_scalar_forced_adjoint_pair : WeakScalarForcedAdjointPairStatement (E := E) := by
  intro ν ρ a b v P hab hd D f F u w hF hu g z zw hz
  let z0 := fun t => truncateTorusHk (Nat.zero_le P) (z t)
  let z1 := fun t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le P)) (zw t)
  have hz0 := weak_scalar_torus_solution_truncate (Nat.zero_le P) hz
  have hf := weak_scalar_forced_hilbert_curve hd hab hF hu
  have ha := weak_scalar_solution_hilbert_curve hd.reflected (neg_le_neg hab) hz0
  have hb : WeakScalarHilbertCurve a b (fun t => torusHkValueCLM (z0 (-t)))
      (fun t => z1 (-t)) (fun t => -weakScalarDualPath hd.reflected z1 (-t)) := by
    simpa only [neg_neg] using! ha.timeReverse
  have he := hf.pairing_increment hab hb
  have hi : (∫ t in a..b,
      inner ℝ (weakScalarForcedDualPath hd w F t) (z1 (-t)) +
        inner ℝ (-weakScalarDualPath hd.reflected z1 (-t)) (w t)) =
      -(∫ t in a..b, inner ℝ (torusHkValueCLM (F t))
        (torusH1GradientL2CLM (E := E) (z1 (-t)))) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have hzero := weak_scalar_dual_adjoint_cancel hd hd.reflected t ht (-t)
      ⟨by linarith only [ht.2], by linarith only [ht.1]⟩
      (by funext x; simp only [neg_neg]) w z1
    simp only [weakScalarForcedDualPath, inner_sub_left, weakScalarFluxDualPath,
      ContinuousLinearMap.adjoint_inner_left]
    linarith only [hzero]
  rw [hi] at he
  change inner ℝ (torusHkValueCLM (u b)) (torusHkValueCLM (z0 (-b))) -
    inner ℝ (torusHkValueCLM (u a)) (torusHkValueCLM (z0 (-a))) = _ at he
  rw [← weak_scalar_zero_inner, ← weak_scalar_zero_inner] at he
  exact he

/-- The genuine moving flux-gradient pairing is integrable on the closed window. -/
theorem weak_scalar_forced_test_integrable {a b : ℝ} (hab : a ≤ b) {P : ℕ}
    {F : ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => E))}
    {zw : ℝ → TorusHk (P + 1) E}
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hzw : MemLp zw 2 (volume.restrict (Icc (-b) (-a)))) :
    IntervalIntegrable (fun t => inner ℝ (torusHkValueCLM (F t))
      (torusH1GradientL2CLM (E := E)
        (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le P)) (zw (-t))))) volume a b := by
  have hFm := (torusHkValueCLM (E := PiLp 2 (fun _ : Fin 2 => E)) (K := 0)).comp_memLp' hF
  have hzm : MemLp (fun t => zw (-t)) 2 (volume.restrict (Icc a b)) := by
    simpa only [neg_neg] using CycleEvolution.cellTimeReverse_memLp hzw
  have hgm := (torusH1GradientL2CLM (E := E)).comp_memLp'
    ((truncateTorusHk (E := E) (Nat.succ_le_succ (Nat.zero_le P))).comp_memLp' hzm)
  have hprod : Integrable (fun t => ‖torusHkValueCLM (F t)‖ *
      ‖torusH1GradientL2CLM (E := E)
        (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le P)) (zw (-t)))‖)
      (volume.restrict (Icc a b)) :=
    memLp_one_iff_integrable.mp (hFm.norm.mul hgm.norm : MemLp _ 1 _)
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  exact hprod.mono' (hFm.aestronglyMeasurable.inner hgm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs] using abs_real_inner_le_norm
        (torusHkValueCLM (F t))
        (torusH1GradientL2CLM (E := E)
          (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le P)) (zw (-t)))))

end AVRegularity.WeakEntryProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.WeakEntryProofs

/-! Source-flux costs on the parent quiet margin scale. The coefficient budget is at
length ε, while the Sobolev radius is c ε. The exact derivative reserve removes
ε^(r-1), leaving the physical flux scale ν/ε and a dimensionless scalar price.
Neither the derivative reserve nor any constant uses the construction cap Dm. -/

section Flux
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- The literal flux A ∇^r U at a finite reserve, using the parent-scale
coefficient budget. Only the coefficient order is lowered. -/
def weakQuietSourceFlux {K J r : ℕ} (hKJ : K ≤ J) (ε : ℝ) (hε : 0 < ε)
    (a b : ℝ) (A : ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 r => E) →L[ℝ] PiLp 2 (fun _ : Fin 2 => F))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤) (t : ℝ) (ht : t ∈ Icc a b)
    (hC : ContDiff ℝ (K : ℕ) (A t)) (hp : AVenhance.IsZ2Periodic (A t))
    (u : TorusHk (K + r) E) : TorusHk K (PiLp 2 (fun _ : Fin 2 => F)) :=
  torusMultiplyIntervalCoefficient ε hε K a b A
    (ne_top_of_le_ne_top hA (coefficientSeminorm_order_mono ε hKJ a b A))
    t ht hC hp (torusDerivativeTensor u)

/-- Positive-order source cost, with the actual parent-scale coefficient
seminorm and the exact finite derivative reserve. -/
def WeakQuietPositiveFluxStatement : Prop :=
  ∀ {K J r : ℕ} (hKJ : K ≤ J) {ε ρ a b : ℝ} (hε : 0 < ε) (_hρ : 0 < ρ), ρ ≤ ε →
  ∀ (A : ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 r => E) →L[ℝ] PiLp 2 (fun _ : Fin 2 => F))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤) (t : ℝ) (ht : t ∈ Icc a b)
    (hC : ContDiff ℝ (K : ℕ) (A t)) (hp : AVenhance.IsZ2Periodic (A t))
    (u : TorusHk (K + r) E),
    Real.sqrt (factorialNormSq ρ (weakQuietSourceFlux hKJ ε hε a b A hA t ht hC hp u).val) ≤
      ((coefficientSeminorm ε J a b A).toReal * derivativeReserveFactor ρ K r) *
        Real.sqrt (factorialNormSq ρ u.val)

/-- The native multiplier and derivative tensor prove the positive source
bound; the parent-scale coefficient budget is used only once. -/
theorem weak_quiet_positive_flux : WeakQuietPositiveFluxStatement (E := E) (F := F) := by
  intro K J r hKJ ε ρ a b hε hρ hρε A hA t ht hC hp u
  have hAK : coefficientSeminorm ε K a b A ≠ ⊤ :=
    ne_top_of_le_ne_top hA (coefficientSeminorm_order_mono ε hKJ a b A)
  let B := fun l : Fin (K + 1) => (coefficientOrderSup a b A l.val).toReal
  have hB (l : Fin (K + 1)) (x : Vec 2) :
      ‖coefficientDerivativeArray (A t) l.val x‖ ≤ B l :=
    coefficientOrderSup_derivative_bound ε hε K a b A hAK l.val
      (Nat.le_of_lt_succ l.isLt) t ht x
  have hmul := (torusDerivativeTensor (K := K) (r := r) u).mulCoefficient_factorialNorm_le
    hC hp hB hρ.le
  have hsum : (∑ l : Fin (K + 1), factorialRootWeight ρ l.val * B l) ≤
      (coefficientSeminorm ε J a b A).toReal := by
    calc
      _ ≤ ∑ l : Fin (K + 1), factorialRootWeight ε l.val * B l := by
        apply Finset.sum_le_sum
        intro l _
        apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
        exact div_le_div_of_nonneg_right
          (pow_le_pow_left₀ hρ.le hρε _) (Nat.cast_nonneg _)
      _ = (coefficientSeminorm ε K a b A).toReal :=
        coefficientSeminorm_eq_sum_real_budget ε hε K a b A hAK
      _ ≤ (coefficientSeminorm ε J a b A).toReal :=
        ENNReal.toReal_mono hA (coefficientSeminorm_order_mono ε hKJ a b A)
  have hder := torusDerivativeTensor_factorialNorm_le ρ hρ u
  calc
    _ ≤ (∑ l : Fin (K + 1), factorialRootWeight ρ l.val * B l) *
        Real.sqrt (factorialNormSq ρ (torusDerivativeTensor u).val) := hmul
    _ ≤ (coefficientSeminorm ε J a b A).toReal *
        Real.sqrt (factorialNormSq ρ (torusDerivativeTensor u).val) :=
      mul_le_mul_of_nonneg_right hsum (Real.sqrt_nonneg _)
    _ ≤ (coefficientSeminorm ε J a b A).toReal *
        (derivativeReserveFactor ρ K r * Real.sqrt (factorialNormSq ρ u.val)) :=
      mul_le_mul_of_nonneg_left hder ENNReal.toReal_nonneg
    _ = _ := (mul_assoc _ _ _).symm

end Flux

section AdjointCoefficient
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Taking a pointwise adjoint costs at most the number of derivative words,
not the dimension of either Hilbert fibre. -/
theorem weak_quiet_adjoint_array_bound (A : Vec 2 → E →L[ℝ] F) (j : ℕ)
    (hA : ContDiff ℝ (j : ℕ) A) (x : Vec 2) :
    ‖coefficientDerivativeArray (fun y => (A y).adjoint) j x‖ ≤
      2 ^ j * ‖coefficientDerivativeArray A j x‖ := by
  have hn : ‖CycleComparison.Coarse.adjointCLM E F‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => by
      change ‖T.adjoint‖ ≤ 1 * ‖T‖
      rw [LinearIsometryEquiv.norm_map, one_mul]
  have he := CycleComparison.Coarse.norm_array_clm_comp_le
    (CycleComparison.Coarse.adjointCLM E F) A j hA x
  exact he.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hn
        (ContinuousLinearMap.opNorm_nonneg (coefficientDerivativeArray A j x)))
      (by positivity : (0 : ℝ) ≤ 2 ^ j))

/-- Half the parent radius absorbs the entire adjoint word-array cost. -/
theorem weak_quiet_adjoint_weighted_array (A : Vec 2 → E →L[ℝ] F)
    {ρ ε : ℝ} (hρ : 0 ≤ ρ) (hρε : 2 * ρ ≤ ε) (j : ℕ)
    (hA : ContDiff ℝ (j : ℕ) A) (x : Vec 2) :
    factorialRootWeight ρ j * ‖coefficientDerivativeArray (fun y => (A y).adjoint) j x‖ ≤
      factorialRootWeight ε j * ‖coefficientDerivativeArray A j x‖ := by
  have hw : 0 ≤ factorialRootWeight ρ j := by unfold factorialRootWeight; positivity
  have hscale : factorialRootWeight ρ j * 2 ^ j ≤ factorialRootWeight ε j := by
    unfold factorialRootWeight
    have hp := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hρ) hρε j
    rw [mul_pow] at hp
    exact (le_of_eq (by ring : ρ ^ j / (j.factorial : ℝ) * 2 ^ j =
      (2 ^ j * ρ ^ j) / (j.factorial : ℝ))).trans
      (div_le_div_of_nonneg_right hp (Nat.cast_nonneg _))
  calc
    _ ≤ factorialRootWeight ρ j * (2 ^ j * ‖coefficientDerivativeArray A j x‖) :=
      mul_le_mul_of_nonneg_left (weak_quiet_adjoint_array_bound A j hA x) hw
    _ = (factorialRootWeight ρ j * 2 ^ j) * ‖coefficientDerivativeArray A j x‖ :=
      (mul_assoc _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale
      (ContinuousLinearMap.opNorm_nonneg (coefficientDerivativeArray A j x))

/-- A finite parent-scale coefficient budget controls the pointwise adjoint
budget at half radius, at every lower jet order, including infinite suprema. -/
theorem weak_quiet_adjoint_seminorm {ρ ε a b : ℝ} (hρ : 0 ≤ ρ) (hρε : 2 * ρ ≤ ε)
    {K J : ℕ} (hKJ : K ≤ J) (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hA : ∀ t ∈ Icc a b, ContDiff ℝ (J : ℕ) (A t)) :
    coefficientSeminorm ρ K a b (fun t x => (A t x).adjoint) ≤
      coefficientSeminorm ε J a b A := by
  refine le_trans ?_ (coefficientSeminorm_order_mono ε hKJ a b A)
  unfold coefficientSeminorm
  apply Finset.sum_le_sum
  intro j hj
  simp_rw [ENNReal.mul_iSup]
  refine iSup_mono fun t => iSup_mono fun ht => iSup_mono fun x => ?_
  have hjet : j ≤ J := (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hKJ
  have he := weak_quiet_adjoint_weighted_array (A t) hρ hρε j
    ((hA t ht).of_le (by exact_mod_cast hjet)) x
  have hweights : 0 ≤ factorialRootWeight ρ j := by unfold factorialRootWeight; positivity
  have hε : 0 ≤ ε := (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hρ).trans hρε
  have hwe : 0 ≤ factorialRootWeight ε j := by unfold factorialRootWeight; positivity
  unfold factorialRootWeight at he hweights hwe
  simpa only [← ENNReal.ofReal_coe_nnreal, coe_nnnorm,
    ← ENNReal.ofReal_mul hweights, ← ENNReal.ofReal_mul hwe] using
      ENNReal.ofReal_le_ofReal he

end AdjointCoefficient

end AVRegularity.WeakEntryProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleComparison.Coarse
namespace AVRegularity.WeakEntryProofs

/-! Formal adjoints of the actual ordered differential source. The spatial
integration by parts and the weighted closure rules reuse the coarse calculus.
Only a fixed finite reserve Kc enters the price, never the ambient stage cap. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- The complete ordered derivative tensor on classical fields. -/
def weakQuietDerivativeField (r : ℕ) (ψ : Vec 2 → E) :
    Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => E) :=
  fun x => WithLp.toLp 2 (fun α => AVRegularity.orderedDerivativeRev α ψ x)

/-- The formal adjoint of a constant coordinate injection. -/
def weakQuietInjectionAdj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι) (R Kc : ℕ) :
    TorusAdj (fun (ψ : Vec 2 → E) x => piSingleCLM E α (ψ x)) 0 R Kc
      ((Kc.factorial : ℝ) * 1) :=
  TorusAdj.constOp (piSingleCLM E α) (PiLp.proj 2 (fun _ : ι => E) α)
    (fun v w => by
      change inner ℝ (v α) w = inner ℝ v (piSingleCLM E α w)
      exact (real_inner_comm w (v α)).trans
        ((inner_piSingleCLM α w v).symm.trans (real_inner_comm v _)))
    (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      change ‖v α‖ ≤ 1 * ‖v‖
      rw [one_mul]
      exact PiLp.norm_apply_le v α) R Kc

/-- The formal adjoint of the full ordered derivative tensor, constructed
from existing coordinate derivatives and the orthogonal fibre injections. -/
def weakQuietDerivativeAdj (r R Kc : ℕ) :
    TorusAdj (weakQuietDerivativeField (E := E) r) r R Kc
      (∑ _α : DerivativeWord2 r, ((Kc.factorial : ℝ) * 1) * 1) :=
  (TorusAdj.sum Finset.univ fun α : DerivativeWord2 r =>
    ((weakQuietInjectionAdj (E := E) α R Kc).comp
      (TorusAdj.orderedDerivativeRev (E := E) α R Kc) le_rfl (by omega)).ofOrder
        (Nat.zero_add r)).ofOp (by
    funext ψ x
    apply PiLp.ext
    intro β
    simp only [piSingleCLM_apply, weakQuietDerivativeField, WithLp.ofLp_sum,
      Finset.sum_apply, PiLp.ofLp_single, Pi.single_apply, WithLp.ofLp_toLp,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true])

/-- Weighted adjoint cost of the complete tensor. Its word count depends
only on r, including when the Hilbert fibre has dimension zero. -/
theorem weak_quiet_derivative_adjoint_bound {ρ : ℝ} (hρ : 0 < ρ) (r R Kc : ℕ) :
    (weakQuietDerivativeAdj (E := E) r R Kc).FBound ρ
      (2 ^ r * ((Kc : ℝ) / ρ) ^ r) := by
  have hinj (α : DerivativeWord2 r) :
      (weakQuietInjectionAdj (E := E) α R Kc).FBound ρ 1 := by
    unfold weakQuietInjectionAdj
    exact TorusAdj.FBound.constOp hρ.le
  have h := TorusAdj.FBound.sum Finset.univ fun α : DerivativeWord2 r =>
    TorusAdj.FBound.ofOrder (Nat.zero_add r)
      (TorusAdj.FBound.comp (A₁ := weakQuietInjectionAdj (E := E) α R Kc)
        (hinj α)
        (TorusAdj.FBound.orderedDerivativeRev (E := E) hρ α R Kc)
        (by positivity) le_rfl (by omega))
  unfold weakQuietDerivativeAdj
  exact TorusAdj.FBound.ofOp _ (h.mono_const (le_of_eq (by
    simp [DerivativeWord2, DerivativeWord])))

/-- The divergence on a classical flux field. -/
def weakQuietDivergence (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => F)) : Vec 2 → F :=
  fun x => ∑ k : Fin 2, partialOp k (fun y => ψ y k) x

/-- Divergence, built from the existing component and derivative adjoints. -/
def weakQuietDivergenceAdj (R Kc : ℕ) :
    TorusAdj (weakQuietDivergence (F := F)) 1 R Kc
      (∑ _k : Fin 2, 1 * ((Kc.factorial : ℝ) * 1)) :=
  TorusAdj.sum Finset.univ fun k : Fin 2 =>
    ((TorusAdj.coordDeriv (E := F) k R Kc).comp
      (TorusAdj.componentOp (E := F) k (R + 1) Kc) le_rfl le_rfl).ofOrder (Nat.add_zero 1)

/-- The divergence adjoint is the genuine negative gradient. -/
theorem weak_quiet_divergence_adjoint_bound {ρ : ℝ} (hρ : 0 < ρ) (R Kc : ℕ) :
    (weakQuietDivergenceAdj (F := F) R Kc).FBound ρ (2 * ((Kc : ℝ) / ρ)) := by
  have h := TorusAdj.FBound.sum Finset.univ fun k : Fin 2 =>
    TorusAdj.FBound.ofOrder (Nat.add_zero 1)
      (TorusAdj.FBound.comp (TorusAdj.FBound.coordDeriv (E := F) hρ k R Kc)
        (TorusAdj.FBound.componentOp (E := F) hρ.le k (R + 1) Kc)
        zero_le_one le_rfl le_rfl)
  exact h.mono_const (le_of_eq (by simp))

omit [FiniteDimensional ℝ E] in
/-- Coefficient multiplication has its genuine formal adjoint at every finite
reserve. Half-radius control absorbs all adjoint coefficient-array costs. -/
theorem weak_quiet_coefficient_primal_adjoint {ρ ε a b : ℝ}
    (hρ : 0 < ρ) (hρε : 2 * ρ ≤ ε) {R Kc J : ℕ}
    (hRJ : R ≤ J) (hKJ : Kc ≤ J) (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hA : ∀ t ∈ Set.Icc a b, ContDiff ℝ (J : ℕ) (A t))
    (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (A t))
    (hbudget : coefficientSeminorm ε J a b A ≠ ⊤) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∃ C : ℝ, ∃ Adj : TorusAdj (fun (ψ : Vec 2 → E) x => A t x (ψ x)) 0 R Kc C,
      Adj.FBound ρ (coefficientSeminorm ε J a b A).toReal := by
  let N := fun t x => (A t x).adjoint
  have hn : coefficientSeminorm ρ Kc a b N ≤ coefficientSeminorm ε J a b A :=
    weak_quiet_adjoint_seminorm hρ.le hρε hKJ A hA
  have hfin : coefficientSeminorm ρ Kc a b N ≠ ⊤ := ne_top_of_le_ne_top hbudget hn
  let B := fun l => (coefficientOrderSup a b N l).toReal
  have hB (l : ℕ) (hl : l ≤ Kc) (x : Vec 2) :
      ‖coefficientDerivativeArray (N t) l x‖ ≤ B l :=
    coefficientOrderSup_derivative_bound ρ hρ Kc a b N hfin l hl t ht x
  have hN : ContDiff ℝ (Kc : ℕ) (N t) :=
    contDiff_clm_comp (adjointCLM E F) ((hA t ht).of_le (by exact_mod_cast hKJ))
  have hNp : AVenhance.IsZ2Periodic (N t) := fun k x => congrArg
    ContinuousLinearMap.adjoint (hp t ht k x)
  let Adj := TorusAdj.mulOp R Kc ((hA t ht).of_le (by exact_mod_cast hRJ))
    (hp t ht) hN hNp (fun x v w => ContinuousLinearMap.adjoint_inner_left (A t x) w v) B hB
  refine ⟨mulConst B Kc, Adj, ?_⟩
  have hsum : fbMulConst ρ B Kc = (coefficientSeminorm ρ Kc a b N).toReal := by
    unfold fbMulConst
    rw [← Fin.sum_univ_eq_sum_range]
    exact coefficientSeminorm_eq_sum_real_budget ρ hρ Kc a b N hfin
  exact TorusAdj.FBound.mono_const (A := Adj) (TorusAdj.FBound.mulOp hρ.le)
    (hsum.le.trans (ENNReal.toReal_mono hbudget hn))

/-- The actual ordered source in divergence form. -/
def weakQuietPrimalSource (r : ℕ)
    (A : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => E) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => F)) (ψ : Vec 2 → E) : Vec 2 → F :=
  weakQuietDivergence (fun x => A x (weakQuietDerivativeField r ψ x))

/-- A native formal adjoint of the full source, bounded in factorial norms.
The parent budget appears exactly once; only the fixed reserve Kc is charged. -/
def WeakQuietSourceAdjointStatement : Prop :=
  ∀ {ρ ε a b : ℝ}, 0 < ρ → 2 * ρ ≤ ε → ∀ (r R Kc J : ℕ),
  R + 1 ≤ J → Kc ≤ J →
  ∀ (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => E) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => F)),
  (∀ t ∈ Set.Icc a b, ContDiff ℝ (J : ℕ) (A t)) →
  (∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (A t)) →
  coefficientSeminorm ε J a b A ≠ ⊤ →
  ∀ t ∈ Set.Icc a b, ∃ C : ℝ,
    ∃ Adj : TorusAdj (weakQuietPrimalSource r (A t)) (r + 1) R Kc C,
      Adj.FBound ρ ((coefficientSeminorm ε J a b A).toReal *
        (2 ^ (r + 1) * ((Kc : ℝ) / ρ) ^ (r + 1)))

/-- The source adjoint is composition of the already proved coefficient,
complete derivative-tensor and divergence adjoints. -/
theorem weak_quiet_source_adjoint : WeakQuietSourceAdjointStatement (E := E) (F := F) := by
  intro ρ ε a b hρ hρε r R Kc J hRJ hKJ A hA hp hbudget t ht
  obtain ⟨C, Adj, hAdj⟩ := weak_quiet_coefficient_primal_adjoint hρ hρε hRJ hKJ A
    hA hp hbudget t ht
  let B := (Adj.comp (weakQuietDerivativeAdj (E := E) r (R + 1) Kc) le_rfl (by omega))
  let D := ((weakQuietDivergenceAdj (F := F) R Kc).comp B le_rfl le_rfl).ofOrder
    (by omega : 1 + (0 + r) = r + 1)
  refine ⟨_, D, ?_⟩
  have hB := TorusAdj.FBound.comp hAdj
    (weak_quiet_derivative_adjoint_bound (E := E) hρ r (R + 1) Kc) (by positivity)
    le_rfl (by omega : R + 1 + 0 ≤ R + 1)
  have hD := TorusAdj.FBound.ofOrder (by omega : 1 + (0 + r) = r + 1)
    (TorusAdj.FBound.comp (weak_quiet_divergence_adjoint_bound (F := F) hρ R Kc)
      hB (by positivity) le_rfl le_rfl)
  exact hD.mono_const (le_of_eq (by rw [pow_succ, pow_succ]; ring))

/-- The differential source spends r+1 derivatives and its coefficient has
scale ε^(r-1), leaving exactly the inverse heat-time scale ε^(-2). -/
theorem weak_quiet_source_scale_identity {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (L : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    ε ^ (r - 1) * (L / (c * ε)) ^ (r + 1) = (L / c) ^ (r + 1) / ε ^ 2 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  simp only [Nat.succ_sub_one, div_pow, mul_pow, pow_succ]
  field_simp

/-- The complete source adjoint has heat-time cost ν/ε² times a dimensionless
finite price, uniform in the construction depth and in the Hilbert fibres. -/
theorem weak_quiet_source_adjoint_normalized {ν ε c a b β : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hc1 : 2 * c ≤ 1) (r R Kc J : ℕ)
    (hr : 1 ≤ r) (hRJ : R + 1 ≤ J) (hKJ : Kc ≤ J)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => E) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => F))
    (hA : ∀ t ∈ Set.Icc a b, ContDiff ℝ (J : ℕ) (A t))
    (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (A t))
    (hfin : coefficientSeminorm ε J a b A ≠ ⊤)
    (hbudget : (coefficientSeminorm ε J a b A).toReal ≤ ν * ε ^ (r - 1) * β)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∃ C : ℝ, ∃ Adj : TorusAdj (weakQuietPrimalSource r (A t)) (r + 1) R Kc C,
      Adj.FBound (c * ε) (ν / ε ^ 2 *
        (β * (2 ^ (r + 1) * ((Kc : ℝ) / c) ^ (r + 1)))) := by
  have hρ := mul_pos hc hε
  have hρε : 2 * (c * ε) ≤ ε := by
    simpa only [mul_assoc, one_mul] using mul_le_mul_of_nonneg_right hc1 hε.le
  obtain ⟨C, Adj, hAdj⟩ := weak_quiet_source_adjoint hρ hρε r R Kc J hRJ hKJ
    A hA hp hfin t ht
  refine ⟨C, Adj, hAdj.mono_const ?_⟩
  have hs := mul_le_mul_of_nonneg_right hbudget
    (by positivity : 0 ≤ 2 ^ (r + 1) * ((Kc : ℝ) / (c * ε)) ^ (r + 1))
  have hid : (ν * ε ^ (r - 1) * β) *
      (2 ^ (r + 1) * ((Kc : ℝ) / (c * ε)) ^ (r + 1)) =
      ν / ε ^ 2 * (β * (2 ^ (r + 1) * ((Kc : ℝ) / c) ^ (r + 1))) := by
    calc
      _ = (ν * β * 2 ^ (r + 1)) *
          (ε ^ (r - 1) * ((Kc : ℝ) / (c * ε)) ^ (r + 1)) := by ring
      _ = _ := by rw [weak_quiet_source_scale_identity hε hc (Kc : ℝ) r hr]; ring
  exact hs.trans hid.le

end AVRegularity.WeakEntryProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleComparison.Coarse
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.WeakEntryProofs

/-! Identification of the classical formal source with its native weak flux.
Finite Fourier approximation is strong in the actual graph Sobolev space. -/

private theorem weakQuietSmooth_rev_eq_ordered {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℕ}
    (α : DerivativeWord2 r) (ψ : Vec 2 → E) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    orderedDerivativeRev α ψ = orderedDerivative α ψ := by
  unfold orderedDerivativeRev
  rw [List.foldr_eq_foldl_reverse]
  change CycleComparison.Lift.orderedListDerivative (List.ofFn α).reverse ψ =
    CycleComparison.Lift.orderedListDerivative (List.ofFn α) ψ
  exact CycleComparison.Lift.orderedListDerivative_perm (List.reverse_perm _) ψ hψ

/-- The Fourier approximation's stored jets are its actual classical ordered
partial derivatives, including the reversed convention of the source adjoint. -/
theorem weak_quiet_smooth_jet_ordered {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K L : ℕ} (N : ℕ) (u : TorusHk K E) :
    ∀ {r : ℕ} (hr : r ≤ L) (α : DerivativeWord2 r),
      smoothFourierJet (L := L) N u ⟨⟨r, Nat.lt_succ_of_le hr⟩, α⟩ =
        orderedDerivative α (smoothFourierJet (L := L) N u (valueIndex2 L)) := by
  intro r
  induction r with
  | zero =>
    intro _ α
    have he : (⟨⟨0, by omega⟩, α⟩ : JetIndex2 L) = valueIndex2 L := by
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (Subsingleton.elim _ _)
    rw [he]
    rfl
  | succ r ih =>
    intro hr α
    have hj : r < L := by omega
    have he : (⟨⟨r + 1, Nat.lt_succ_of_le hr⟩, α⟩ : JetIndex2 L) =
        nextIndex2 (⟨r, hj⟩ : Fin L) (Fin.init α) (α (Fin.last r)) := by
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (Fin.snoc_init_self α).symm
    rw [he]
    funext x
    rw [← smoothFourierJet_fderiv N u ⟨r, hj⟩ (Fin.init α) (α (Fin.last r)) x]
    change fderiv ℝ (smoothFourierJet (L := L) N u ⟨⟨r, by omega⟩, Fin.init α⟩)
      x (basisVec (α (Fin.last r))) = _
    rw [ih (by omega) (Fin.init α)]
    have hα := Fin.snoc_init_self α
    conv_rhs => rw [← hα]
    simp only [orderedDerivative, List.ofFn_succ', List.concat_eq_append,
      List.foldl_append, List.foldl_cons, List.foldl_nil, Fin.snoc_castSucc, Fin.snoc_last]

/-- Reversed classical words and the actual native Fourier jets agree. -/
theorem weak_quiet_smooth_jet_reversed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K L r : ℕ} (N : ℕ) (u : TorusHk K E) (hr : r ≤ L) (α : DerivativeWord2 r) :
    smoothFourierJet (L := L) N u ⟨⟨r, Nat.lt_succ_of_le hr⟩, α⟩ =
      orderedDerivativeRev α (smoothFourierJet (L := L) N u (valueIndex2 L)) := by
  rw [weakQuietSmooth_rev_eq_ordered α _ (smoothFourierJet_contDiff N u _)]
  exact weak_quiet_smooth_jet_ordered N u hr α

/-- The native multiplier/derivative flux of a finite Fourier approximation
has the exact classical source-flux representative. -/
theorem weak_quiet_source_flux_projection_ae {J r : ℕ} {ε a b : ℝ}
    (hε : 0 < ε)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (0 : ℕ) (A t)) (hp : AVenhance.IsZ2Periodic (A t))
    (N : ℕ) (u : TorusHk (0 + r) ℝ) :
    torusHkValueCLM
      (weakQuietSourceFlux (Nat.zero_le J) ε hε a b A hA t ht hC hp (galerkinProj N u)) =ᵐ[
        volume.restrict AVenhance.unitCube]
      fun y => A t y (weakQuietDerivativeField r
        (smoothFourierJet (L := 0 + r) N u (valueIndex2 (0 + r))) y) := by
  have hm := torusMulCoefficient_value_ae (torusDerivativeTensor (K := 0) (r := r) (galerkinProj N u))
    (A t) hC hp
    (fun l y => coefficientOrderSup_derivative_bound ε hε 0 a b A
      (ne_top_of_le_ne_top hA (coefficientSeminorm_order_mono ε (Nat.zero_le J) a b A))
      l.val (Nat.le_of_lt_succ l.isLt) t ht y)
  have hten := torusDerivativeTensor_value_ae (K := 0) (r := r) (galerkinProj N u)
  have hj : ∀ᵐ y ∂volume.restrict AVenhance.unitCube, ∀ α : DerivativeWord2 r,
      (galerkinProj N u).val ⟨⟨r, by omega⟩, α⟩ y =
        smoothFourierJet (L := 0 + r) N u ⟨⟨r, by omega⟩, α⟩ y :=
    ae_all_iff.mpr fun α => galerkinProj_jet_ae_smooth N u _
  filter_upwards [hm, hten, hj] with y hmy hty hjy
  change ((torusDerivativeTensor (K := 0) (r := r) (galerkinProj N u)).mulCoefficient
    (A t) hC hp _).val (valueIndex2 0) y = A t y _
  rw [hmy, hty]
  congr 1
  apply PiLp.ext
  intro α
  change (galerkinProj N u).val ⟨⟨r, by omega⟩, α⟩ y = orderedDerivativeRev α _ y
  rw [hjy α, weak_quiet_smooth_jet_reversed N u (by omega) α]

private theorem weakQuiet_divergence_test {K : ℕ} (U : TorusHk (K + 1) ℝ)
    (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℝ))
    (hF : ContDiff ℝ 1 F) (hp : AVenhance.IsZ2Periodic F) :
    cellInner (tval U) (weakQuietDivergence F) =
      -(∫ y in AVenhance.unitCube, ∑ k : Fin 2,
        inner ℝ (F y k) (U.toFunction.jet
          (nextIndex2 (⟨0, Nat.succ_pos K⟩ : Fin (K + 1)) Fin.elim0 k) y)) := by
  have hcomp (k : Fin 2) : ContDiff ℝ 1 (fun y => F y k) :=
    (contDiff_piLp 2).mp hF k
  have hcompP (k : Fin 2) : AVenhance.IsZ2Periodic (fun y => F y k) :=
    fun n y => congrArg (fun z => z k) (hp n y)
  have hder (k : Fin 2) : Continuous (partialOp k (fun y => F y k)) :=
    ((hcomp k).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hparts (k : Fin 2) : cellInner (tval U) (partialOp k (fun y => F y k)) =
      -cellInner (U.toFunction.jet
        (nextIndex2 (⟨0, Nat.succ_pos K⟩ : Fin (K + 1)) Fin.elim0 k)) (fun y => F y k) := by
    have hh := cellInner_firstDerivative_eq_neg U k (hcomp k) (hcompP k)
    change _ = -cellInner (tval U) (partialOp k (fun y => F y k)) at hh
    linarith only [hh]
  unfold cellInner weakQuietDivergence
  simp_rw [inner_sum]
  rw [integral_finsetSum _ (fun k _ => integrable_tval_inner U (hder k))]
  change (∑ k : Fin 2, cellInner (tval U) (partialOp k (fun y => F y k))) = _
  simp_rw [hparts]
  rw [Finset.sum_neg_distrib]
  congr 1
  unfold cellInner
  rw [integral_finsetSum _ (fun k _ =>
    (integrable_inner_continuous
      (U.toFunction.hasPeriodicWeakJet.2.1 _) (hcomp k).continuous).congr
        (Filter.Eventually.of_forall fun y => real_inner_comm _ _))]
  apply Finset.sum_congr rfl
  intro k _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => real_inner_comm _ _

private theorem weakQuiet_firstIndex (K : ℕ) (k : Fin 2) :
    nextIndex2 (⟨0, Nat.succ_pos K⟩ : Fin (K + 1)) Fin.elim0 k =
      (⟨⟨1, by omega⟩, fun _ => k⟩ : JetIndex2 (K + 1)) := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    funext j
    fin_cases j
    rfl

/-- A native H1 gradient pairs with the divergence of a C1 periodic flux.
The test is a genuine weak Sobolev field; it need not be classically smooth. -/
theorem weak_quiet_divergence_native_pair {K : ℕ} (φ : TorusHk (K + 1) ℝ)
    (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℝ))
    (hF : ContDiff ℝ 1 F) (hp : AVenhance.IsZ2Periodic F)
    (F0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ)))
    (hF0 : torusHkValueCLM F0 =ᵐ[volume.restrict AVenhance.unitCube] F) :
    cellInner (tval φ) (weakQuietDivergence F) =
      -inner ℝ (torusHkValueCLM F0)
        (torusH1GradientL2CLM (E := ℝ) (truncateTorusHk (by omega : 1 ≤ K + 1) φ)) := by
  have hgrad : ∀ᵐ y ∂volume.restrict AVenhance.unitCube, ∀ k : Fin 2,
      torusH1GradientL2CLM (E := ℝ) (truncateTorusHk (by omega : 1 ≤ K + 1) φ) y k =
        φ.toFunction.jet
          (nextIndex2 (⟨0, Nat.succ_pos K⟩ : Fin (K + 1)) Fin.elim0 k) y := by
    have hraw : ∀ᵐ y ∂volume.restrict AVenhance.unitCube, ∀ k : Fin 2,
        φ.toFunction.jet (⟨⟨1, by omega⟩, fun _ => k⟩ : JetIndex2 (K + 1)) y =
          φ.val (⟨⟨1, by omega⟩, fun _ => k⟩ : JetIndex2 (K + 1)) y :=
      ae_all_iff.mpr fun k => periodicJetRepresentative_ae φ.val _
    filter_upwards [torusH1GradientL2CLM_ae
      (truncateTorusHk (by omega : 1 ≤ K + 1) φ), hraw] with y hy hry
    intro k
    rw [hy, weakQuiet_firstIndex K k, hry k]
    rfl
  have he : inner ℝ (torusHkValueCLM F0)
      (torusH1GradientL2CLM (E := ℝ) (truncateTorusHk (by omega : 1 ≤ K + 1) φ)) =
      ∫ y in AVenhance.unitCube, ∑ k : Fin 2, inner ℝ (F y k)
        (φ.toFunction.jet (nextIndex2 (⟨0, Nat.succ_pos K⟩ : Fin (K + 1)) Fin.elim0 k) y) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hF0, hgrad] with y hy hgy
    rw [hy, PiLp.inner_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hgy k]
  rw [he]
  exact weakQuiet_divergence_test φ F hF hp

/-- The formal source adjoint agrees with the actual native flux on each
finite Fourier approximation. Only the coefficient needs C1 regularity here. -/
theorem weak_quiet_source_native_pair_projection {J r P R Kc : ℕ} {ε a b C : ℝ}
    (hε : 0 < ε)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (1 : ℕ) (A t)) (hp : AVenhance.IsZ2Periodic (A t))
    (Adj : TorusAdj (weakQuietPrimalSource r (A t)) (r + 1) R Kc C)
    (hP : P + (r + 1) ≤ Kc) (u : TorusHk (0 + r) ℝ)
    (φ : TorusHk (P + (r + 1)) ℝ) (N : ℕ) :
    inner ℝ (truncateTorusHk (Nat.zero_le (0 + r)) (galerkinProj N u))
      (truncateTorusHk (Nat.zero_le P) (Adj.adj P hP φ)) =
    -inner ℝ (torusHkValueCLM (weakQuietSourceFlux (Nat.zero_le J) ε hε a b A hA t ht
      (hC.of_le (by simp)) hp (galerkinProj N u)))
      (torusH1GradientL2CLM (E := ℝ) (truncateTorusHk (by omega) φ)) := by
  let ψ := smoothFourierJet (L := 0 + r) N u (valueIndex2 (0 + r))
  let F := fun y => A t y (weakQuietDerivativeField r ψ y)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := smoothFourierJet_contDiff N u _
  have hψp : AVenhance.IsZ2Periodic ψ := smoothFourierJet_periodic N u _
  have hfield : weakQuietDerivativeField r ψ = fun y =>
      WithLp.toLp 2 (fun α : DerivativeWord2 r =>
        smoothFourierJet (L := 0 + r) N u ⟨⟨r, by omega⟩, α⟩ y) := by
    funext y
    apply PiLp.ext
    intro α
    exact (congrFun (weak_quiet_smooth_jet_reversed N u (by omega) α) y).symm
  have hF : ContDiff ℝ 1 F := by
    apply hC.clm_apply
    rw [hfield]
    exact (contDiff_piLp 2).mpr fun α => (smoothFourierJet_contDiff N u _).of_le (by simp)
  have hFp : AVenhance.IsZ2Periodic F := by
    intro k y
    dsimp [F]
    rw [hp k y, hfield]
    congr 1
    apply PiLp.ext
    intro α
    exact smoothFourierJet_periodic N u _ k y
  have hl : inner ℝ (truncateTorusHk (Nat.zero_le (0 + r)) (galerkinProj N u))
      (truncateTorusHk (Nat.zero_le P) (Adj.adj P hP φ)) =
      cellInner (tval (Adj.adj P hP φ)) ψ := by
    rw [weak_scalar_zero_inner, L2.inner_def]
    unfold cellInner
    apply integral_congr_ae
    filter_upwards [galerkinProj_jet_ae_smooth N u (valueIndex2 (0 + r)),
      tval_ae (Adj.adj P hP φ)] with y hy hAy
    change inner ℝ ((galerkinProj N u).val (valueIndex2 (0 + r)) y)
      ((Adj.adj P hP φ).val (valueIndex2 P) y) = _
    rw [hy, hAy]
    exact real_inner_comm _ _
  rw [hl, Adj.ident P hP φ ψ (hψ.of_le (by simp)) hψp]
  have hh := weak_quiet_divergence_native_pair (K := P + r) φ F hF hFp
    (weakQuietSourceFlux (Nat.zero_le J) ε hε a b A hA t ht
      (hC.of_le (by simp)) hp (galerkinProj N u))
    (weak_quiet_source_flux_projection_ae hε A hA t ht (hC.of_le (by simp)) hp N u)
  exact hh

/-- The actual zero-order source flux as a bounded linear map on the native
order-r graph carrier. This is the existing multiplier composed with the
existing derivative tensor map, with no new norm estimate. -/
def weakQuietSourceFluxCLM {J r : ℕ} {ε a b : ℝ} (hε : 0 < ε)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (0 : ℕ) (A t)) (hp : AVenhance.IsZ2Periodic (A t)) :
    TorusHk (0 + r) ℝ →L[ℝ] TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ)) :=
  (KernelEnergy.torusMultiplierCLM (A t) hC hp
    (fun l : Fin (0 + 1) => (coefficientOrderSup a b A l.val).toReal)
    (fun l y => coefficientOrderSup_derivative_bound ε hε 0 a b A
      (ne_top_of_le_ne_top hA (coefficientSeminorm_order_mono ε (Nat.zero_le J) a b A))
      l.val (Nat.le_of_lt_succ l.isLt) t ht y) 1 zero_lt_one).comp
        (KernelEnergy.torusKernelDerivativeTensorCLM 0 r)

theorem weakQuietSourceFluxCLM_apply {J r : ℕ} {ε a b : ℝ} (hε : 0 < ε)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (0 : ℕ) (A t)) (hp : AVenhance.IsZ2Periodic (A t))
    (u : TorusHk (0 + r) ℝ) :
    weakQuietSourceFluxCLM hε A hA t ht hC hp u =
      weakQuietSourceFlux (Nat.zero_le J) ε hε a b A hA t ht hC hp u := by
  simp only [weakQuietSourceFluxCLM, ContinuousLinearMap.comp_apply,
    KernelEnergy.torusKernelDerivativeTensorCLM_apply]
  rfl

/-- Native source-pairing identification, including arbitrary weak Sobolev
inputs. The formal adjoint's smooth-test identity is extended by the actual
strong Fourier graph approximation and the bounded physical flux map. -/
theorem weak_quiet_source_native_pair {J r P R Kc : ℕ} {ε a b C : ℝ}
    (hε : 0 < ε)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (1 : ℕ) (A t)) (hp : AVenhance.IsZ2Periodic (A t))
    (Adj : TorusAdj (weakQuietPrimalSource r (A t)) (r + 1) R Kc C)
    (hP : P + (r + 1) ≤ Kc) (u : TorusHk (0 + r) ℝ)
    (φ : TorusHk (P + (r + 1)) ℝ) :
    inner ℝ (truncateTorusHk (Nat.zero_le (0 + r)) u)
      (truncateTorusHk (Nat.zero_le P) (Adj.adj P hP φ)) =
    -inner ℝ (torusHkValueCLM (weakQuietSourceFlux (Nat.zero_le J) ε hε a b A hA t ht
      (hC.of_le (by simp)) hp u))
      (torusH1GradientL2CLM (E := ℝ) (truncateTorusHk (by omega) φ)) := by
  let T := weakQuietSourceFluxCLM hε A hA t ht (hC.of_le (by simp)) hp
  have hl : Continuous (fun z : TorusHk (0 + r) ℝ =>
      inner ℝ (truncateTorusHk (Nat.zero_le (0 + r)) z)
        (truncateTorusHk (Nat.zero_le P) (Adj.adj P hP φ))) :=
    (truncateTorusHk (Nat.zero_le (0 + r))).continuous.inner continuous_const
  have hr : Continuous (fun z : TorusHk (0 + r) ℝ =>
      -inner ℝ (torusHkValueCLM (T z))
        (torusH1GradientL2CLM (E := ℝ) (truncateTorusHk (by omega) φ))) :=
    ((torusHkValueCLM.continuous.comp T.continuous).inner continuous_const).neg
  have hlN := hl.continuousAt.tendsto.comp (galerkinProj_tendsto u)
  have hrN := hr.continuousAt.tendsto.comp (galerkinProj_tendsto u)
  have hTN (z : TorusHk (0 + r) ℝ) : T z =
      weakQuietSourceFlux (Nat.zero_le J) ε hε a b A hA t ht (hC.of_le (by simp)) hp z :=
    weakQuietSourceFluxCLM_apply hε A hA t ht (hC.of_le (by simp)) hp z
  simp only [Function.comp_def, hTN] at hrN
  exact tendsto_nhds_unique hlN (hrN.congr (fun N =>
    (weak_quiet_source_native_pair_projection hε A hA t ht hC hp Adj hP u φ N).symm))

end AVRegularity.WeakEntryProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.CycleComparison.Coarse
namespace AVRegularity.WeakEntryProofs

/-! Native positive source operators. The divergence and multiplier use the
existing periodic Sobolev maps; the factorial estimates spend only the fixed
source reserve. No time regularity of coefficient derivatives is assumed. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- The genuine divergence, as a finite sum of existing coordinate derivatives. -/
def weakQuietNativeDivergence (K : ℕ) :
    TorusHk (K + 1) (PiLp 2 (fun _ : Fin 2 => F)) →L[ℝ] TorusHk K F :=
  ∑ k : Fin 2, (-(TorusAdj.coordDeriv (E := F) k K (K + 1)).adj K le_rfl).comp
    ((weakQuietInjectionAdj (E := F) k (K + 1) (K + 1)).adj (K + 1) le_rfl)

/-- Divergence spends one derivative, with the two spatial directions charged
explicitly and independently of the Hilbert fibre dimension. -/
theorem weak_quiet_native_divergence_bound {ρ : ℝ} (hρ : 0 < ρ) (K : ℕ)
    (u : TorusHk (K + 1) (PiLp 2 (fun _ : Fin 2 => F))) :
    Real.sqrt (factorialNormSq ρ (weakQuietNativeDivergence K u).val) ≤
      (2 * ((K + 1 : ℕ) : ℝ) / ρ) * Real.sqrt (factorialNormSq ρ u.val) := by
  have hc (k : Fin 2) :
      (weakQuietInjectionAdj (E := F) k (K + 1) (K + 1)).FBound ρ 1 := by
    unfold weakQuietInjectionAdj
    exact TorusAdj.FBound.constOp hρ.le
  have hb (k : Fin 2) := TorusAdj.FBound.coordDeriv (E := F) hρ k K (K + 1)
  unfold weakQuietNativeDivergence
  simp only [sum_apply]
  apply (sqrt_fNSq_torus_sum_le ρ Finset.univ _).trans
  calc
    _ ≤ ∑ k : Fin 2, (((K + 1 : ℕ) : ℝ) / ρ) * Real.sqrt (factorialNormSq ρ u.val) := by
      apply Finset.sum_le_sum
      intro k _
      rw [ContinuousLinearMap.comp_apply, neg_apply, sqrt_fNSq_torus_neg]
      exact (hb k K le_rfl _).trans
        (mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hc k (K + 1) le_rfl u)
          (by positivity))
    _ = _ := by simp only [Fin.sum_univ_two]; ring

/-- The native divergence is the formal transpose of the negative gradient. -/
def weakQuietNativeGradientAdj (R Kc : ℕ) :
    TorusAdj (fun (ψ : Vec 2 → F) y =>
      ∑ k : Fin 2, piSingleCLM F k (-partialOp k ψ y)) 1 R Kc
      (∑ _k : Fin 2, ((Kc.factorial : ℝ) * 1) * 1) :=
  TorusAdj.sum Finset.univ fun k : Fin 2 =>
    ((weakQuietInjectionAdj (E := F) k R Kc).comp
      (TorusAdj.coordDeriv (E := F) k R Kc).neg le_rfl (Nat.le_refl R)).ofOrder
        (Nat.zero_add 1)

/-- The formal-transpose realization is exactly the native divergence map. -/
theorem weak_quiet_native_gradient_adjoint_apply (K : ℕ)
    (u : TorusHk (K + 1) (PiLp 2 (fun _ : Fin 2 => F))) :
    (weakQuietNativeGradientAdj (F := F) K (K + 1)).adj K le_rfl u =
      weakQuietNativeDivergence K u := by
  rfl

/-- The actual coefficient-times-derivative flux as one continuous linear map. -/
def weakQuietNativeFlux {K J r : ℕ} (hKJ : K ≤ J) {ε a b : ℝ} (hε : 0 < ε)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => E) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => F))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (K : ℕ) (A t)) (hp : AVenhance.IsZ2Periodic (A t)) :
    TorusHk (K + r) E →L[ℝ] TorusHk K (PiLp 2 (fun _ : Fin 2 => F)) :=
  (torusMulCLM (A t) hC hp (fun l x =>
    coefficientOrderSup_derivative_bound ε hε K a b A
      (ne_top_of_le_ne_top hA (coefficientSeminorm_order_mono ε hKJ a b A))
      l.val (Nat.le_of_lt_succ l.isLt) t ht x)).comp
    (KernelEnergy.torusKernelDerivativeTensorCLM K r)

/-- The bundled native flux is the already estimated literal source flux. -/
theorem weak_quiet_native_flux_apply {K J r : ℕ} (hKJ : K ≤ J) {ε a b : ℝ} (hε : 0 < ε)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => E) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => F))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (K : ℕ) (A t)) (hp : AVenhance.IsZ2Periodic (A t))
    (u : TorusHk (K + r) E) :
    weakQuietNativeFlux hKJ hε A hA t ht hC hp u =
      weakQuietSourceFlux hKJ ε hε a b A hA t ht hC hp u := by
  unfold weakQuietNativeFlux
  simp only [ContinuousLinearMap.comp_apply, KernelEnergy.torusKernelDerivativeTensorCLM_apply]
  rfl

/-- The positive source is divergence of the actual flux. -/
def weakQuietNativeSource {K J r : ℕ} (hKJ : K + 1 ≤ J) {ε a b : ℝ} (hε : 0 < ε)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => E) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => F))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (K + 1 : ℕ) (A t)) (hp : AVenhance.IsZ2Periodic (A t)) :
    TorusHk ((K + 1) + r) E →L[ℝ] TorusHk K F :=
  (weakQuietNativeDivergence (F := F) K).comp
    (weakQuietNativeFlux (E := E) (F := F) hKJ hε A hA t ht hC hp)

/-- The positive divergence source uses exactly the parent coefficient budget. -/
theorem weak_quiet_native_source_bound {K J r : ℕ} (hKJ : K + 1 ≤ J)
    {ε ρ a b : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hρε : ρ ≤ ε)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => E) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => F))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (K + 1 : ℕ) (A t)) (hp : AVenhance.IsZ2Periodic (A t))
    (u : TorusHk ((K + 1) + r) E) :
    Real.sqrt (factorialNormSq ρ (weakQuietNativeSource (E := E) (F := F) hKJ hε A hA t ht hC hp u).val) ≤
      ((coefficientSeminorm ε J a b A).toReal *
        (2 * ((K + 1 : ℕ) : ℝ) / ρ * derivativeReserveFactor ρ (K + 1) r)) *
          Real.sqrt (factorialNormSq ρ u.val) := by
  dsimp only [weakQuietNativeSource, ContinuousLinearMap.comp_apply]
  have hh := weak_quiet_native_divergence_bound (F := F) hρ K
    (weakQuietNativeFlux (E := E) (F := F) hKJ hε A hA t ht hC hp u)
  have hf := weak_quiet_positive_flux (E := E) (F := F) hKJ hε hρ hρε A hA t ht hC hp u
  rw [← weak_quiet_native_flux_apply] at hf
  calc
    _ ≤ _ := hh
    _ ≤ (2 * ((K + 1 : ℕ) : ℝ) / ρ) *
        (((coefficientSeminorm ε J a b A).toReal * derivativeReserveFactor ρ (K + 1) r) *
          Real.sqrt (factorialNormSq ρ u.val)) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ = _ := by ring

end AVRegularity.WeakEntryProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleComparison.Coarse
namespace AVRegularity.WeakEntryProofs

/-! Abstract finite-order prices for both signs of one divergence source.
All scale cancellation is real algebra; the cap here is the fixed weak
reserve, never the ambient construction order. -/

/-- A factorial derivative reserve is bounded by one fixed top order per
spent derivative. -/
theorem weak_quiet_derivative_reserve_le {ρ : ℝ} (hρ : 0 < ρ)
    (K r L : ℕ) (hL : K + r ≤ L) : derivativeReserveFactor ρ K r ≤ (L / ρ) ^ r := by
  have he : derivativeReserveFactor ρ K r = ((K + 1).ascFactorial r : ℝ) / ρ ^ r := by
    unfold derivativeReserveFactor
    rw [← Nat.factorial_mul_ascFactorial]
    push_cast
    field_simp
  rw [he, div_pow]
  apply div_le_div_of_nonneg_right _ (pow_nonneg hρ.le r)
  exact_mod_cast (Nat.ascFactorial_le_pow_add K r).trans (Nat.pow_le_pow_left hL r)

/-- The positive divergence costs no more than the same finite base that
bounds the formal adjoint. -/
theorem weak_quiet_positive_derivative_price {ρ : ℝ} (hρ : 0 < ρ)
    (K r L : ℕ) (hL : K + 1 + r ≤ L) :
    2 * ((K + 1 : ℕ) : ℝ) / ρ * derivativeReserveFactor ρ (K + 1) r ≤
      2 * (L / ρ) ^ (r + 1) := by
  have hK : ((K + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast (show K + 1 ≤ L by omega)
  calc
    _ ≤ (2 * (L / ρ)) * (L / ρ) ^ r :=
      mul_le_mul (by simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hK hρ.le) (by norm_num : (0 : ℝ) ≤ 2))
        (weak_quiet_derivative_reserve_le hρ (K + 1) r L hL)
        (by unfold derivativeReserveFactor; positivity) (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- The common insertion price dominates the adjoint's word count, at all
orders no larger than the fixed weak differential order. -/
theorem weak_quiet_adjoint_order_price {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (L d m : ℕ) (hd : d ≤ m) :
    2 ^ d * ((L : ℝ) / c) ^ d ≤ (2 * (L + 1 : ℕ) / c) ^ m := by
  have hb : 1 ≤ 2 * (L + 1 : ℕ) / c := by
    apply (le_div_iff₀ hc).mpr
    have hL : (1 : ℝ) ≤ (L + 1 : ℕ) := by exact_mod_cast Nat.succ_pos L
    linarith only [hc1, hL]
  calc
    _ = (2 * ((L : ℝ) / c)) ^ d := (mul_pow _ _ _).symm
    _ ≤ (2 * (L + 1 : ℕ) / c) ^ d := by
      apply pow_le_pow_left₀ (by positivity)
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ L) hc.le
    _ ≤ _ := pow_le_pow_right₀ hb hd

/-- A positive source with differential order r+1 uses the same common price. -/
theorem weak_quiet_positive_order_price {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (L r m : ℕ) (hd : r + 1 ≤ m) :
    2 * ((L : ℝ) / c) ^ (r + 1) ≤ (2 * (L + 1 : ℕ) / c) ^ m := by
  have htwo : (2 : ℝ) ≤ 2 ^ (r + 1) := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_add_left 1 r))
  exact (mul_le_mul_of_nonneg_right htwo (by positivity)).trans
    (weak_quiet_adjoint_order_price hc hc1 L (r + 1) m hd)

/-- One positive source has the common inverse-heat-time cost after exact
parent-scale normalization. This bound is uniform in the ambient order cap. -/
theorem weak_quiet_native_source_normalized {K J r m L : ℕ}
    (hKJ : K + 1 ≤ J) (hL : K + 1 + r ≤ L) (hr : 1 ≤ r) (hm : r + 1 ≤ m)
    {ν ε c a b β : ℝ} (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hc1 : c ≤ 1)
    (hβ : 0 ≤ β)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤)
    (hbudget : (coefficientSeminorm ε J a b A).toReal ≤ ν * ε ^ (r - 1) * β)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K + 1 : ℕ) (A t))
    (hp : AVenhance.IsZ2Periodic (A t)) (u : TorusHk ((K + 1) + r) ℝ) :
    Real.sqrt (factorialNormSq (c * ε)
      (weakQuietNativeSource hKJ hε A hA t ht hC hp u).val) ≤
      (ν / ε ^ 2 * (2 * (L + 1 : ℕ) / c) ^ m * β) *
        Real.sqrt (factorialNormSq (c * ε) u.val) := by
  have hρ := mul_pos hc hε
  have hρε : c * ε ≤ ε := by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hc1 hε.le
  have hbase := weak_quiet_native_source_bound hKJ hε hρ hρε A hA t ht hC hp u
  have hder := weak_quiet_positive_derivative_price hρ K r L hL
  have hnum :
      (coefficientSeminorm ε J a b A).toReal *
        (2 * ((K + 1 : ℕ) : ℝ) / (c * ε) * derivativeReserveFactor (c * ε) (K + 1) r) ≤
      (ν * ε ^ (r - 1) * β) * (2 * ((L : ℝ) / (c * ε)) ^ (r + 1)) :=
    mul_le_mul hbudget hder (by unfold derivativeReserveFactor; positivity)
      (by positivity)
  have hs : (ν * ε ^ (r - 1) * β) * (2 * ((L : ℝ) / (c * ε)) ^ (r + 1)) =
      ν / ε ^ 2 * (2 * ((L : ℝ) / c) ^ (r + 1)) * β := by
    calc
      _ = (ν * β * 2) * (ε ^ (r - 1) * ((L : ℝ) / (c * ε)) ^ (r + 1)) := by ring
      _ = _ := by rw [weak_quiet_source_scale_identity hε hc (L : ℝ) r hr]; ring
  rw [hs] at hnum
  have hprice := weak_quiet_positive_order_price hc hc1 L r m hm
  have htot := hnum.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hprice (by positivity : 0 ≤ ν / ε ^ 2)) hβ)
  exact hbase.trans (mul_le_mul_of_nonneg_right htot (Real.sqrt_nonneg _))

end AVRegularity.WeakEntryProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.WeakEntryProofs

/-! Genuine mixed primitive reserves and source support uniformly produce the fast carriers of every inverse word. -/

open AVRegularity.EntryWeakProofs
open scoped ContDiff
variable {d H : ℕ}

theorem coordinate_word_finite_window_higher_carrier_exists {a b : ℝ} (hab : a < b)
    (N : ℕ) (hN : N ≤ H)
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : ℝ → Vec 2 → Vec d → ℂ} {F : ℝ → Vec 2 → Vec d → ComplexCellVector}
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (hm : ∀ Y i j, Measurable (fun t => G t Y i j))
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hbG : ∀ n, n ≤ H → ∀ t Y i j,
      ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ B n)
    (Qf : IndependentParameterSourceReserve H f) (QF : IndependentParameterSourceReserve H F)
    (P : Vec d → MolecularData)
    (Cv : ℕ → ℝ) (hCv : ∀ K, 0 ≤ Cv K)
    (hv : ∀ Y K, K ≤ H → ∀ t, ContDiff ℝ (K : ℕ∞) ((P Y).v t))
    (hp : ∀ Y t, AVenhance.IsZ2Periodic ((P Y).v t))
    (hb : ∀ Y K, K ≤ H → ∀ t j, j ≤ K → ∀ k x,
      ‖iteratedFDeriv ℝ j (fun z => (P Y).v t z k) x‖ ≤ Cv K)
    (c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
    (hsol : ∀ Y w, w.length ≤ N → IsCellSolution (Icc a b) (dataCoefficients (P Y))
      (fun t => cellQ0 (coordinateSourceWord f w Y t))
      (coordinateSourceWord F w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y))
    (hi : ∀ Y w, w.length ≤ N →
      cellValue (c w Y) a =ᵐ[volume.restrict AVenhance.unitCube] 0)
    (w : List (Fin d)) (hw : w.length ≤ N) (K : ℕ) (hK : K + w.length ≤ H) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ Y, ∃ u : ℝ → TorusHk K ℂ,
      StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧
      ∀ t ∈ Icc a b, torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube]
        cellValue (c w Y) t := by
  let Ns := fun (u : List (Fin d)) (K : ℕ) => ∑ j : JetIndex2 K, 2 * Qf.budget (u.length + j.1.val)
  let Nf := fun (u : List (Fin d)) (K : ℕ) => ∑ j : JetIndex2 K, QF.budget (u.length + j.1.val)
  apply uniform_word_finite_window_carrier hab N H P
    (fun Y u t => independentMetricWordJet G u.length (coordinateWordDirections u) Y t)
    (fun Y u t => cellQ0 (coordinateSourceWord f u Y t))
    (fun Y u => coordinateSourceWord F u Y) (fun Y u => c u Y) Cv hCv hv hp hb
    (fun Y u _ K hK => coordinateWordHigherSourceData Qf QF u K hK a b Y) Ns Nf
    (fun Y u _ K hK => by rw [coordinateWordHigherSourceData_scalar_budget])
    (fun Y u _ K hK => by rw [coordinateWordHigherSourceData_flux_budget])
    (fun u => B u.length) (fun u _ => hB _)
    (fun Y u hu t i j => general_metric_word_entry_bound hr B hbG u.length (hu.trans hN) _ (coordinateWordDirections_norm u) Y t i j)
    (fun Y u _ i j => general_metric_word_entry_measurable hr hm u.length _ Y i j)
    hsol hi w hw K hK

end AVRegularity.WeakEntryProofs
end
