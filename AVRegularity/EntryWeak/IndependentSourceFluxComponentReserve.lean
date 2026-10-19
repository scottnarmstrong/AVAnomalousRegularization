-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeak.IndependentExplicitNaturalCoefficientCalibration
public import AVRegularity.EntryWeak.IndependentTransportedCoefficientJetBound
import AVRegularity.CycleComparison.Lift.SecondCrossMean
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Every finite fresh-child parameter family has genuine full joint spatial smoothness. -/

def independentFreshChildrenList {r : ℕ} (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) :
    List (ℤ × (Vec (4 * r) → ChainChild)) :=
  List.ofFn (fun j => (slots j, fun Y => independentFreshChild birthLength j Y))

theorem independentFreshChildrenList_smooth {r : ℕ} (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) :
    ∀ e ∈ independentFreshChildrenList slots birthLength,
      ContDiff ℝ (⊤ : ℕ∞) (fun Y => (e.2 Y).center) ∧
      ContDiff ℝ (⊤ : ℕ∞) (fun Y => (e.2 Y).phase) := by
  intro e he
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
  exact ⟨(independentFreshChildProjection j false).contDiff.const_smul _,
    (independentFreshChildProjection j true).contDiff⟩

theorem independentFreshChainExtension_joint_smooth {r : ℕ} (D : OCData) (A : RealChain)
    (hA : A.WellSlotted) (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) :
    (∀ u s, ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec (4 * r) × Vec 2 =>
      (independentChainExtension (fun _ => A) (independentFreshChildrenList slots birthLength) Y.1).geom D |>.1 u Y.2 s)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun Y =>
      ((independentChainExtension (fun _ => A) (independentFreshChildrenList slots birthLength) Y).geom D).2.1) := by
  have hgeo : (fun Y => (independentChainExtension (fun _ : Vec (4 * r) => A)
      (independentFreshChildrenList slots birthLength) Y).geom D) =
      independentChainExtensionGeom D A.ctxLevel A.slot (fun _ => A.geom D)
        (independentFreshChildrenList slots birthLength) := by
    funext Y
    exact independentChainExtension_geom D _ (fun _ => A) (fun _ => hA) _ _ (fun _ => rfl) (fun _ => rfl) Y
  have hh := independentChainExtensionGeom_joint_smooth D
    (independentFreshChildrenList slots birthLength)
    (independentFreshChildrenList_smooth slots birthLength) A.ctxLevel A.slot
    (fun _ => A.geom D) (A.geom D).2.2 (fun _ => rfl)
    (fun u s => (geomSpatialSmooth_geom D A u s).comp contDiff_snd) contDiff_const
  simpa only [← hgeo] using hh

/-! Raw flow closeness supplies a spatial Lipschitz constant independent of mixed family jets. -/

theorem planar_linear_norm_le_two_of_close (L : Vec 2 →L[ℝ] Vec 2)
    (hL : ‖L - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1) : ‖L‖ ≤ 2 := by
  calc
    ‖L‖ = ‖(L - ContinuousLinearMap.id ℝ (Vec 2)) + ContinuousLinearMap.id ℝ (Vec 2)‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖L - ContinuousLinearMap.id ℝ (Vec 2)‖ + ‖ContinuousLinearMap.id ℝ (Vec 2)‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add hL ContinuousLinearMap.norm_id_le
    _ = 2 := by norm_num

theorem centeredGeometryChart_spatial_derivative_le_two (g : ChainGeom) (hg : GeomSpatialSmooth g)
    (ρ : ℝ) (hρ : 0 < ρ) (u : ℝ)
    (hc : ∀ x, ‖fderiv ℝ (fun y => g.1 u y g.2.2) x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1)
    (X : Vec 2) : ‖fderiv ℝ (centeredGeometryChart g ρ u) X‖ ≤ 2 := by
  rw [centeredGeometryChart_fderiv_norm g hg ρ hρ u]
  exact planar_linear_norm_le_two_of_close _ (hc _)

theorem centeredGeometryChartInv_spatial_derivative_le_two (g : ChainGeom) (hg : GeomSpatialSmooth g)
    (ρ : ℝ) (hρ : 0 < ρ) (u : ℝ)
    (hc : ∀ x, ‖fderiv ℝ (fun y => g.1 g.2.2 y u) x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1)
    (X : Vec 2) : ‖fderiv ℝ (centeredGeometryChartInv g ρ u) X‖ ≤ 2 := by
  rw [centeredGeometryChartInv_fderiv_norm g hg ρ hρ u]
  exact planar_linear_norm_le_two_of_close _ (hc _)

theorem centeredGeometryChart_value_le_two (g : ChainGeom) (hg : GeomSpatialSmooth g)
    (ρ : ℝ) (hρ : 0 < ρ) (u : ℝ)
    (hc : ∀ x, ‖fderiv ℝ (fun y => g.1 u y g.2.2) x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1)
    (X : Vec 2) : ‖centeredGeometryChart g ρ u X‖ ≤ 2 * ‖X‖ := by
  have hF : ContDiff ℝ 1 (centeredGeometryChart g ρ u) :=
    ((((hg u g.2.2).of_le (by simp)).comp
      (contDiff_const.add (contDiff_id.const_smul ρ))).sub contDiff_const).const_smul _
  have hh := independent_parameter_lipschitz (centeredGeometryChart g ρ u) hF 2
    (centeredGeometryChart_spatial_derivative_le_two g hg ρ hρ u hc) 0 X
  simpa only [centeredGeometryChart_zero, sub_zero] using hh

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! A finite price for the first response tests, chosen before the primitive family. -/

def independentFirstSourcePrice (d H : ℕ) (C : ℝ) (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  (1 + ((d : ℝ) + 1) ^ H * (H + 1 : ℕ)) * (C * ∑ i : Fin 2, |A (basisVec i)|)

theorem independentFirstSourcePrice_nonneg (d H : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (A : Vec 2 →L[ℝ] ℝ) : 0 ≤ independentFirstSourcePrice d H C A := by
  unfold independentFirstSourcePrice
  exact mul_nonneg (by positivity) (mul_nonneg hC (Finset.sum_nonneg fun _ _ => abs_nonneg _))

def independentFirstCalibrationPrice (d H m : ℕ) (C : ℝ) : ℝ :=
  ∑ p : Fin (m + 1) × Fin 2, independentFirstSourcePrice d H C
    ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))

theorem independentFirstCalibrationPrice_nonneg (d H m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ independentFirstCalibrationPrice d H m C :=
  Finset.sum_nonneg fun _ _ => independentFirstSourcePrice_nonneg d H C hC _

theorem independentFirstSourcePrice_le_calibrated (d H m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (p : Fin (m + 1) × Fin 2) :
    independentFirstSourcePrice d H C ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) ≤
      independentFirstCalibrationPrice d H m C := by
  unfold independentFirstCalibrationPrice
  exact Finset.single_le_sum
    (fun q (_ : q ∈ Finset.univ) => independentFirstSourcePrice_nonneg d H C hC
      ((q.2 : ℝ) • coordinateSymbolDirection (q.1 : ℝ))) (Finset.mem_univ p)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Native family charts are jointly smooth in their slow point and all fresh child parameters. -/

theorem independentFreshFamilyChart_joint_smooth {r : ℕ} (D : OCData) (A : RealChain)
    (hA : A.WellSlotted) (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) (ρ u : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec (4 * r) × Vec 2 => ρ⁻¹ •
      (independentChainExtension (fun _ => A) (independentFreshChildrenList slots birthLength) Y.1).famMap D u (ρ • Y.2)) := by
  let es := independentFreshChildrenList slots birthLength
  let B := independentChainExtension (fun _ : Vec (4 * r) => A) es
  let anchor := independentChainExtensionAnchor D A.ctxLevel (A.geom D).2.2 es
  have ha Y : ((B Y).geom D).2.2 = anchor := by
    rw [independentChainExtension_geom D es (fun _ => A) (fun _ => hA)
      A.ctxLevel A.slot (fun _ => rfl) (fun _ => rfl)]
    exact independentChainExtensionGeom_anchor D es A.ctxLevel A.slot (fun _ => A.geom D)
      (A.geom D).2.2 (fun _ => rfl) Y
  obtain ⟨hf, hc⟩ := independentFreshChainExtension_joint_smooth D A hA slots birthLength
  have hshift : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec (4 * r) × Vec 2 =>
      ((B Y.1).geom D).2.1 + ρ • Y.2) :=
    (hc.comp contDiff_fst).add (contDiff_snd.const_smul _)
  have hleft := (hf u anchor).comp (contDiff_fst.prodMk hshift)
  have hright : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec (4 * r) × Vec 2 =>
      ((B Y.1).geom D).1 u ((B Y.1).geom D).2.1 anchor) :=
    (hf u anchor).comp (contDiff_fst.prodMk (hc.comp contDiff_fst))
  have he : (fun Y : Vec (4 * r) × Vec 2 => ρ⁻¹ • (B Y.1).famMap D u (ρ • Y.2)) =
      (fun Y => ρ⁻¹ • (((B Y.1).geom D).1 u (((B Y.1).geom D).2.1 + ρ • Y.2) anchor -
        ((B Y.1).geom D).1 u ((B Y.1).geom D).2.1 anchor)) := by
    funext Y
    simp only [RealChain.famMap, ha]
  rw [he]
  exact (hleft.sub hright).const_smul _

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! The normalized test polynomial has a direction cost fixed before its actual coefficient family. -/

section
variable {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [Fintype ι] [DecidableEq ι]

theorem independentNormalizedLiftTestReserve_uniform_budget (H n : ℕ)
    (c : P → LiftCoeff ι (fun _ => ℝ)) (x : P → Vec 2)
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val,
      IndependentParameterSourceReserve H (fun t z Y => c Y m.val α t (x Y) z v u 1))
    (θ B : ℝ) (hQc : ∀ m α r, r ≤ H → (Qc m α).budget r ≤ θ * B)
    (r : ℕ) (hr : r ≤ H) :
    (independentNormalizedLiftTestReserve H n c x A v u Qc).budget r ≤
      θ * (finiteLiftSymbolBudget n A * B) := by
  rw [independentNormalizedLiftTestReserve_budget]
  apply (Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (fun α _ =>
    mul_le_mul_of_nonneg_left (hQc m α r hr) (norm_nonneg _)))).trans_eq
  simp only [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs]
  unfold finiteLiftSymbolBudget
  rw [← Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  ring
end

/-! Genuine produced scalar coefficient fields produce the finite tests for the next inverse recurrence. -/

section
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def independentScalarCoefficientLift
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (Y : P) : LiftCoeff ι (fun _ => ℝ) :=
  fun m α t _ z v u => c m α t z Y v u • ContinuousLinearMap.id ℝ ℝ

def independentScalarLiftTestSource (n : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι) (t : ℝ) (z : Vec 2) (Y : P) : ℝ :=
  normalizedLiftTestField (independentScalarCoefficientLift c Y) n A u v 1 t 0 z

def independentScalarLiftTestSourceReserve (H n : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val,
      IndependentParameterSourceReserve H (fun t z Y => c m.val α t z Y v u)) :
    IndependentParameterSourceReserve H (independentScalarLiftTestSource n c A v u) :=
  independentNormalizedLiftTestReserve H n (independentScalarCoefficientLift c) (fun _ => 0) A v u
    (fun m α => (Qc m α).congrSource (by
      funext t z Y
      simp only [independentScalarCoefficientLift, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, mul_one]))

theorem independentScalarLiftTestSourceReserve_uniform_budget (H n : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val,
      IndependentParameterSourceReserve H (fun t z Y => c m.val α t z Y v u))
    (θ B : ℝ) (hQ : ∀ m α r, r ≤ H → (Qc m α).budget r ≤ θ * B) (r : ℕ) (hr : r ≤ H) :
    (independentScalarLiftTestSourceReserve H n c A v u Qc).budget r ≤
      θ * (finiteLiftSymbolBudget n A * B) := by
  unfold independentScalarLiftTestSourceReserve
  apply independentNormalizedLiftTestReserve_uniform_budget H n _ _ A v u _ θ B
  · intro m α s hs
    rw [IndependentParameterSourceReserve.congrSource_budget]
    exact hQ m α s hs
  · exact hr
end

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! A native spatial Jacobian is a genuine derivative of the full independent parameter chart. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independent_parameter_jacobian_entry_eq (F : P × Vec 2 → Vec 2)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (i j : Fin 2) (Y : P × Vec 2) :
    jacMatrix (fun x => F (Y.1, x)) Y.2 i j = fderiv ℝ F Y (0, basisVec j) i := by
  let L := ContinuousLinearMap.inr ℝ P (Vec 2)
  have hmap : HasFDerivAt (fun x : Vec 2 => (Y.1, x)) L Y.2 := by
    have hh := L.hasFDerivAt (x := Y.2)
    simpa only [L, ContinuousLinearMap.inr_apply, Prod.add_def, zero_add, add_zero] using
      hh.const_add (Y.1, (0 : Vec 2))
  have hcomp := (hF.differentiable (by simp) Y).hasFDerivAt.comp Y.2 hmap
  change fderiv ℝ (fun x => F (Y.1, x)) Y.2 (basisVec j) i = _
  change fderiv ℝ (F ∘ fun x => (Y.1, x)) Y.2 (basisVec j) i = _
  rw [hcomp.fderiv]
  rfl

theorem independent_parameter_jacobian_entry_contDiff (F : P × Vec 2 → Vec 2)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Y : P × Vec 2 => jacMatrix (fun x => F (Y.1, x)) Y.2 i j) := by
  have he : (fun Y : P × Vec 2 => jacMatrix (fun x => F (Y.1, x)) Y.2 i j) =
      (fun Y : P × Vec 2 => fderiv ℝ F Y (0, basisVec j) i) :=
    funext (independent_parameter_jacobian_entry_eq F hF i j)
  rw [he]
  exact contDiff_pi.1 ((hF.fderiv_right (by simp)).clm_apply contDiff_const) i

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! The produced independent finite test is exactly the actual normalized exponential readout. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem normalized_scalar_lift_test_polynomial (n : ℕ) (C : LiftCoeff ι (fun _ => ℝ))
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι) (t : ℝ) (X z : Vec 2) :
    normalizedLiftTestField C n A u v 1 t X z =
      ∑ m : Fin (n + 1), ∑ α : DerivativeWord2 m.val,
        ((List.ofFn α).map (fun j => A (basisVec j))).prod • C m.val α t X z v u 1 := by
  have hp := normalized_exponential_lift_polynomial n C A t X z v u (1 : ℝ) 1
  simp only [one_smul, one_pow] at hp
  rw [← Fin.sum_univ_eq_sum_range] at hp
  exact hp

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem independent_scalar_lift_test_eq_actual (n : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (C : LiftCoeff ι (fun _ => ℝ)) (A : Vec 2 →L[ℝ] ℝ) (v u : ι)
    (t : ℝ) (z X : Vec 2) (Y : P)
    (hcopy : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val,
      C m.val α t X z v u 1 = c m.val α t z Y v u) :
    independentScalarLiftTestSource n c A v u t z Y = normalizedLiftTestField C n A u v 1 t X z := by
  change normalizedLiftTestField (independentScalarCoefficientLift c Y) n A u v 1 t (0 : Vec 2) z = _
  rw [normalized_scalar_lift_test_polynomial, normalized_scalar_lift_test_polynomial]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro α _
  rw [hcopy]
  simp only [independentScalarCoefficientLift, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, mul_one]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The base coarse flow has genuine mixed jets when unused family parameters are retained. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independent_scaled_coarse_flow_derivative_norm (D : OCData) (s : ℝ)
    (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - D.α) / 2)
    (hq : IsAdmissibleQ D.α s D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (m : ℕ) (hm : 1 ≤ m) (r t : ℝ)
    (ht : |t - r| ≤ 2 ^ (-25 : ℤ) * (ocA D.α D.q D.Λ m)⁻¹)
    (ρ : ℝ) (hρ : 0 < ρ) (hρe : ρ ≤ D.eps m) (y y' : Vec 2)
    (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (X : P × Vec 2) :
    ‖iteratedFDeriv ℝ n (fun Z : P × Vec 2 =>
      ρ⁻¹ • (D.flowOf m t (y' + ρ • Z.2) r - y)) X‖ ≤ weakBaseChartJetBudget K := by
  let f := fun z : Vec 2 => ρ⁻¹ • (D.flowOf m t (y' + ρ • z) r - y)
  let L : (P × Vec 2) →L[ℝ] Vec 2 := ContinuousLinearMap.snd ℝ P (Vec 2)
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun Z => by
    rw [one_mul]; exact norm_snd_le Z)
  have hraw : ContDiff ℝ (⊤ : ℕ∞) (fun z => D.flowOf m t z r) :=
    CycleReference.streamFlow_spatial_smooth (D.hΦ m) t r
  have hf : ContDiff ℝ (n : ℕ∞) f :=
    (((hraw.of_le (by simp)).comp (contDiff_const.add (contDiff_id.const_smul ρ))).sub
      contDiff_const).const_smul _
  have hh := finite_affine_derivative_norm_le f n hf L hL 0 X
  simp only [add_zero] at hh
  have hb := scaled_coarse_flow_derivative_norm D s hα₀ hα₁ hs₀ hs₁ hq hΛ hζ hseq
    m hm r t ht ρ hρ hρe y y' n hn X.2
  exact (hh.trans hb).trans (weakBaseChartJetBudget_bounds_order K n hnK)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! The native planar coefficient slice keeps the full independent parameter fields in its slow slot. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def independentScalarCoefficientSlice
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (L : Vec 2 →L[ℝ] P) (offset : P) : LiftCoeff ι (fun _ => ℝ) :=
  fun m α t X z v u => c m α t z (L X + offset) v u • ContinuousLinearMap.id ℝ ℝ

theorem independent_scalar_coefficient_slice_test (n : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (L : Vec 2 →L[ℝ] P) (offset : P) (A : Vec 2 →L[ℝ] ℝ) (v u : ι)
    (t : ℝ) (z X : Vec 2) :
    normalizedLiftTestField (independentScalarCoefficientSlice c L offset) n A u v 1 t X z =
      independentScalarLiftTestSource n c A v u t z (L X + offset) := by
  symm
  apply independent_scalar_lift_test_eq_actual
  intro m α
  simp only [independentScalarCoefficientSlice, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, mul_one]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Joint independent Jacobian jets spend exactly one genuine chart derivative. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independent_parameter_jacobian_entry_jet_bound (F : P × Vec 2 → Vec 2)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (i j : Fin 2) (n : ℕ) (X : P × Vec 2) :
    ‖iteratedFDeriv ℝ n (fun Z : P × Vec 2 => jacMatrix (fun y => F (Z.1, y)) Z.2 i j) X‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) F X‖ := by
  have he : (fun Z : P × Vec 2 => jacMatrix (fun y => F (Z.1, y)) Z.2 i j) =
      fun Z : P × Vec 2 => fderiv ℝ F Z (0, basisVec j) i :=
    funext (independent_parameter_jacobian_entry_eq F hF i j)
  rw [he]
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hb := norm_iteratedFDeriv_clm_apply_const (c := ((0 : P), basisVec j))
    (hd.contDiffAt (x := X)) (n := n) (by simp)
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun Z : P × Vec 2 => fderiv ℝ F Z (0, basisVec j)) :=
    hd.clm_apply contDiff_const
  let L : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun z => by
    simpa only [L, ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm z i)
  have hp := L.norm_iteratedFDeriv_comp_left (hv.contDiffAt (x := X)) (n := n) (by simp)
  have hp' : ‖iteratedFDeriv ℝ n (fun Z : P × Vec 2 => fderiv ℝ F Z (0, basisVec j) i) X‖ ≤
      ‖iteratedFDeriv ℝ n (fun Z : P × Vec 2 => fderiv ℝ F Z (0, basisVec j)) X‖ := by
    change ‖iteratedFDeriv ℝ n (L ∘ fun Z : P × Vec 2 => fderiv ℝ F Z (0, basisVec j)) X‖ ≤ _
    exact hp.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have hj : ‖((0 : P), basisVec j)‖ = 1 := by
    simp only [Prod.norm_def, norm_zero,
      show ‖(basisVec j : Vec 2)‖ = 1 by simp [basisVec, Pi.norm_single], max_eq_right zero_le_one]
  rw [hj, one_mul, norm_iteratedFDeriv_fderiv] at hb
  exact hp'.trans hb

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Literal native exponential applications of coefficient slices give the independent test fields. -/

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independent_coefficient_slice_apply (n : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (L : Vec 2 →L[ℝ] Vec d) (offset : Vec d) (A : Vec 2 →L[ℝ] ℝ) (u : ι)
    (t : ℝ) (X z : Vec 2) :
    liftApply n (independentScalarCoefficientSlice c L offset)
      (fun _ X => Real.exp (A X) • (Pi.single u (1 : ℝ) : ι → ℝ)) t X z =
      Real.exp (A X) • (fun v => independentScalarLiftTestSource n c A v u t z (L X + offset)) := by
  funext v
  have he := independent_scalar_coefficient_slice_test n c L offset A v u t z X
  change (Real.exp (A X))⁻¹ • liftApply n (independentScalarCoefficientSlice c L offset)
    (fun _ X => Real.exp (A X) • (Pi.single u (1 : ℝ) : ι → ℝ)) t X z v = _ at he
  change _ = Real.exp (A X) • independentScalarLiftTestSource n c A v u t z (L X + offset)
  rw [← he, smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory Set AVenhance
namespace AVRegularity.EntryWeakProofs

/-! Full independent Piola sources have a genuine window reserve with their recorded weight retained. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentPiolaSourcePrice (N Dγ n r : ℕ) (E C : ℝ)
    (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
    ((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C * MB d I *
      (E⁻¹ ^ (d - 1 - r) * (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ (d - 1))

theorem independentPiolaSourcePrice_nonneg (N Dγ n r : ℕ) (E C : ℝ)
    (hE : 0 ≤ E) (hC : 0 ≤ C)
    (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) (hMB : ∀ d J, 0 ≤ MB d J) :
    0 ≤ independentPiolaSourcePrice N Dγ n r E C MB := by
  unfold independentPiolaSourcePrice
  apply Finset.sum_nonneg
  intro d _
  apply Finset.sum_nonneg
  intro J _
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hC) (hMB d J))
    (mul_nonneg (pow_nonneg (inv_nonneg.mpr hE) _)
      (pow_nonneg (by positivity) _))

theorem independentPiolaSource_periodic
    (K : Vec 2 → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ h a b, IsZ2Periodic (fun z => K z h a b))
    (Dγ r : ℕ) (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 → Vec 2)
    (hB : ∀ d J a, IsZ2Periodic (fun z => B d J z a))
    (A : DerivativeWord2 r) (a : Fin 2) :
    IsZ2Periodic (fun z => transportedCoeff (K z) Dγ (fun d J => B d J z) r A 0 a) := by
  intro k z
  have heK : K (z + latticeShift k) = K z := by
    funext h i j
    exact hK h i j k z
  have heB : (fun d J => B d J (z + latticeShift k)) = fun d J => B d J z := by
    funext d J i
    exact hB d J i k z
  dsimp only
  rw [heK, heB]

theorem independentPiolaSource_measurable
    (K : (ℝ × Vec 2) → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hKm : ∀ h a b, Measurable (fun X => K X h a b))
    (hK : ∀ X a b, ContDiff ℝ (⊤ : ℕ∞) (fun h => K X h a b))
    (Dγ r : ℕ) (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → (ℝ × Vec 2) → Vec 2)
    (hB : ∀ d J a, Measurable (fun X => B d J X a))
    (A : DerivativeWord2 r) (a : Fin 2) :
    Measurable (fun X => transportedCoeff (K X) Dγ (fun d J => B d J X) r A 0 a) :=
  transportedCoeff_parameter_measurable K hKm hK Dγ B hB r A 0 a

theorem independentPiolaSource_slow_contDiff
    (K : ℝ → Vec 2 → P → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ t a b, ContDiff ℝ (⊤ : ℕ∞)
      (fun Z : (Vec 2 × P) × Vec 2 => K t Z.1.1 Z.1.2 Z.2 a b))
    (H Dγ r : ℕ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ → Vec 2 → P → Vec 2)
    (Q : ∀ d J a, IndependentParameterSourceReserve H (fun t z Y => B d J t z Y a))
    (A : DerivativeWord2 r) (a : Fin 2) (t : ℝ) :
    ContDiff ℝ (H : ℕ∞) (fun X : Vec 2 × P =>
      transportedCoeff (K t X.1 X.2) Dγ (fun d J => B d J t X.1 X.2) r A 0 a) :=
  independent_transported_coefficient_zero_contDiff (P := Vec 2 × P) (fun X h => K t X.1 X.2 h) (hK t)
    Dγ H (fun d J X => B d J t X.1 X.2) (fun d J a => (Q d J a).regular t) r A a

theorem independentPiolaSource_jet_bound
    (H N Dγ r : ℕ) (hHN : H + Dγ ≤ N) (E : ℝ) (hE : 0 < E)
    (C : ℝ) (hC : 0 ≤ C) (I : Set ℝ) (_hI : MeasurableSet I)
    (K : ℝ → Vec 2 → P → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ t a b, ContDiff ℝ (⊤ : ℕ∞)
      (fun Z : (Vec 2 × P) × Vec 2 => K t Z.1.1 Z.1.2 Z.2 a b))
    (_hKm : ∀ Y h a b, Measurable (fun Z : ℝ × Vec 2 => K Z.1 Z.2 Y h a b))
    (_hKp : ∀ t Y h a b, IsZ2Periodic (fun z => K t z Y h a b))
    (hKC : ∀ t ∈ I, ∀ X : Vec 2 × P, ∀ a b j, j ≤ N →
      ‖iteratedFDeriv ℝ j (fun Z : (Vec 2 × P) × Vec 2 =>
        K t Z.1.1 Z.1.2 (E • Z.2) a b) (X, 0)‖ ≤ C)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ → Vec 2 → P → Vec 2)
    (Q : ∀ d J a, IndependentParameterSourceReserve H (fun t z Y => B d J t z Y a))
    (θ : ℝ) (_hθ : 0 ≤ θ) (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ)
    (_hMB : ∀ d J, 0 ≤ MB d J) (hQ : ∀ d J a n, n ≤ H → (Q d J a).budget n ≤ θ * MB d J)
    (A : DerivativeWord2 r) (a : Fin 2) (n : ℕ) (hn : n ≤ H)
    (t : ℝ) (ht : t ∈ I) (X : Vec 2 × P) :
    ‖iteratedFDeriv ℝ n (fun Z : Vec 2 × P =>
      transportedCoeff (K t Z.1 Z.2) Dγ (fun d J => B d J t Z.1 Z.2) r A 0 a) X‖ ≤
      θ * independentPiolaSourcePrice N Dγ n r E C MB := by
  exact independent_transported_coefficient_zero_jet_bound (P := Vec 2 × P) (fun Z h => K t Z.1 Z.2 h)
      (hK t) E hE N Dγ n r C hC (by omega) X (hKC t ht X)
      (fun d J Z => B d J t Z.1 Z.2)
      (fun d J i => ((Q d J i).regular t).of_le (by exact_mod_cast hn)) θ MB
      (fun d _ J i j hj => ((Q d J i).derivative_bound j (by omega) t X).trans (hQ d J i j (by omega))) A a

theorem independentPiolaWindowSourceReserve
    (H N Dγ r : ℕ) (hHN : H + Dγ ≤ N) (E : ℝ) (hE : 0 < E)
    (C : ℝ) (hC : 0 ≤ C) (I : Set ℝ) (hI : MeasurableSet I)
    (K : ℝ → Vec 2 → P → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ t a b, ContDiff ℝ (⊤ : ℕ∞)
      (fun Z : (Vec 2 × P) × Vec 2 => K t Z.1.1 Z.1.2 Z.2 a b))
    (hKm : ∀ Y h a b, Measurable (fun Z : ℝ × Vec 2 => K Z.1 Z.2 Y h a b))
    (hKp : ∀ t Y h a b, IsZ2Periodic (fun z => K t z Y h a b))
    (hKC : ∀ t ∈ I, ∀ X : Vec 2 × P, ∀ a b j, j ≤ N →
      ‖iteratedFDeriv ℝ j (fun Z : (Vec 2 × P) × Vec 2 =>
        K t Z.1.1 Z.1.2 (E • Z.2) a b) (X, 0)‖ ≤ C)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ → Vec 2 → P → Vec 2)
    (Q : ∀ d J a, IndependentParameterSourceReserve H (fun t z Y => B d J t z Y a))
    (θ : ℝ) (hθ : 0 ≤ θ) (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ)
    (hMB : ∀ d J, 0 ≤ MB d J) (hQ : ∀ d J a n, n ≤ H → (Q d J a).budget n ≤ θ * MB d J)
    (A : DerivativeWord2 r) :
    ∃ R : IndependentParameterSourceReserve H
      (fun t z Y a => independentTimeWindowSource I
        (fun t z Y => transportedCoeff (K t z Y) Dγ (fun d J => B d J t z Y) r A 0 a) t z Y),
      ∀ n ≤ H, R.budget n ≤ θ *
        (2 * ∑ j : Fin (H + 1), independentPiolaSourcePrice N Dγ j.val r E C MB) := by
  let price := fun n => independentPiolaSourcePrice N Dγ n r E C MB
  have hprice n : 0 ≤ price n :=
    independentPiolaSourcePrice_nonneg N Dγ n r E C hE.le hC MB hMB
  let f := fun a t z Y => transportedCoeff (K t z Y) Dγ (fun d J => B d J t z Y) r A 0 a
  have hf a t : ContDiff ℝ (H : ℕ∞) (fun X : Vec 2 × P => f a t X.1 X.2) :=
    independentPiolaSource_slow_contDiff K hK H Dγ r B Q A a t
  have hp a t Y : IsZ2Periodic (fun z => f a t z Y) :=
    independentPiolaSource_periodic (fun z h => K t z Y h) (hKp t Y) Dγ r
      (fun d J z => B d J t z Y) (fun d J a => (Q d J a).periodic t Y) A a
  have hm a Y : Measurable (fun X : ℝ × Vec 2 => f a X.1 X.2 Y) :=
    independentPiolaSource_measurable (fun X h => K X.1 X.2 Y h)
      (fun h i j => hKm Y h i j)
      (fun X i j => (hK X.1 i j).comp
        ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec 2 => (X.2, Y))).prodMk contDiff_id))
      Dγ r (fun d J X => B d J X.1 X.2 Y) (fun d J i => (Q d J i).measurable Y) A a
  have hb a n (hn : n ≤ H) t (ht : t ∈ I) (X : Vec 2 × P) :
      ‖iteratedFDeriv ℝ n (fun Z : Vec 2 × P => f a t Z.1 Z.2) X‖ ≤ θ * price n := by
    exact independentPiolaSource_jet_bound H N Dγ r hHN E hE C hC I hI K hK hKm hKp hKC
      B Q θ hθ MB hMB hQ A a n hn t ht X
  exact windowIndependentVectorReserve H I hI
    (fun t z Y a => f a t z Y) hf hp hm θ hθ price hprice hb

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! A single finite symbol price covers every earlier independent lift test. -/

theorem finiteLiftSymbolBudget_mono (q n : ℕ) (hqn : q ≤ n) (A : Vec 2 →L[ℝ] ℝ) :
    finiteLiftSymbolBudget q A ≤ finiteLiftSymbolBudget n A := by
  unfold finiteLiftSymbolBudget
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun _ _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentScalarLiftTestSourceReserve_menu_budget (H q n : ℕ) (hqn : q ≤ n)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι)
    (Qc : ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val,
      IndependentParameterSourceReserve H (fun t z Y => c m.val α t z Y v u))
    (θ B : ℝ) (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (hQc : ∀ m α r, r ≤ H → (Qc m α).budget r ≤ θ * B) (r : ℕ) (hr : r ≤ H) :
    (independentScalarLiftTestSourceReserve H q c A v u Qc).budget r ≤
      θ * (finiteLiftSymbolBudget n A * B) := by
  exact (independentScalarLiftTestSourceReserve_uniform_budget H q c A v u Qc θ B hQc r hr).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (finiteLiftSymbolBudget_mono q n hqn A) hB) hθ)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Two genuinely weighted factors produce a full-family averaged drift response at their product weight. -/

section
variable {d H : ℕ}

theorem independentDriftMean_squared_response_production
    (v f : ℝ → Vec 2 → Vec d → ℝ)
    (Qv : IndependentParameterSourceReserve H v) (Qf : IndependentParameterSourceReserve H f)
    (θ w BV BF : ℝ) (hθ : 0 ≤ θ) (hw : 0 ≤ w) (hBV : 0 ≤ BV) (hBF : 0 ≤ BF)
    (hvB : ∀ r ≤ H, Qv.budget r ≤ θ * BV) (hfB : ∀ r ≤ H, Qf.budget r ≤ (θ * w) * BF) :
    ∃ Qm : IndependentParameterSourceReserve H
      (fun t (_ : Vec 2) Y => fieldCellMean (fun z => v t z Y • f t z Y)),
      ∀ r ≤ H, Qm.budget r ≤ (θ ^ 2 * w) *
        (((d : ℝ) + 1) ^ H * ((H + 1 : ℕ) *
          (‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ * 2 ^ H * BV * BF))) := by
  let R := Qv.scalarProduct Qf
  let B := ‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ * 2 ^ H * BV * BF
  have hR r (hr : r ≤ H) : R.budget r ≤ (θ ^ 2 * w) * B := by
    have hh := Qv.bilinear_uniform_budget Qf (ContinuousLinearMap.lsmul ℝ ℝ)
      θ (θ * w) BV BF hθ (mul_nonneg hθ hw) hBV hBF hvB hfB r hr
    exact hh.trans_eq (by dsimp only [B]; ring)
  exact ⟨R.mean, fun r hr => R.mean_uniform_budget (θ ^ 2 * w) B hR r hr⟩
end

/-! Full independent Piola source prices retain the exact common physical dimension. -/

theorem independentPiolaSourcePrice_dimensional (N Dγ k r n : ℕ) (E κ e C B₀ : ℝ)
    (hE : 0 < E) : independentPiolaSourcePrice N Dγ k r E C
      (fun d _ => κ * e ^ (n - 2) * E ^ ((d : ℝ) - (n : ℝ)) * B₀) =
      (κ * e ^ (n - 2) * E ^ (((r + 1 : ℕ) : ℝ) - (n : ℝ))) *
        ∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ _I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
          ((k + 1 : ℕ) * (2 : ℝ) ^ k) ^ 2 * C * B₀ *
            (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ (d - 1) := by
    unfold independentPiolaSourcePrice
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hmem
    have hrd : r + 1 ≤ d := (Finset.mem_Icc.mp hmem).1
    apply Finset.sum_congr rfl
    intro I _
    apply Finset.sum_congr rfl
    intro i _
    have hcount := weak_piola_lowering_dimensional_count E hE n d r hrd
    calc
      _ = (κ * e ^ (n - 2)) *
          (E ^ ((d : ℝ) - (n : ℝ)) * E⁻¹ ^ (d - 1 - r)) *
          (((k + 1 : ℕ) * (2 : ℝ) ^ k) ^ 2 * C * B₀ *
            (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ (d - 1)) := by ring
      _ = _ := by rw [hcount]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory Set AVenhance
namespace AVRegularity.EntryWeakProofs

/-! Windowed independent Piola production has a source-linear dimensionless price. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentPiolaDimensionlessPrice (N Dγ k : ℕ) (C B₀ : ℝ) (r : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ _I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
    ((k + 1 : ℕ) * (2 : ℝ) ^ k) ^ 2 * C * B₀ *
      (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ (d - 1)

theorem independentPiolaWindowDimensionalSourceReserve
    (H N Dγ r : ℕ) (hHN : H + Dγ ≤ N) (E : ℝ) (hE : 0 < E)
    (C : ℝ) (hC : 0 ≤ C) (I : Set ℝ) (hI : MeasurableSet I)
    (K : ℝ → Vec 2 → P → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ t a b, ContDiff ℝ (⊤ : ℕ∞)
      (fun Z : (Vec 2 × P) × Vec 2 => K t Z.1.1 Z.1.2 Z.2 a b))
    (hKm : ∀ Y h a b, Measurable (fun Z : ℝ × Vec 2 => K Z.1 Z.2 Y h a b))
    (hKp : ∀ t Y h a b, IsZ2Periodic (fun z => K t z Y h a b))
    (hKC : ∀ t ∈ I, ∀ X : Vec 2 × P, ∀ a b j, j ≤ N →
      ‖iteratedFDeriv ℝ j (fun Z : (Vec 2 × P) × Vec 2 =>
        K t Z.1.1 Z.1.2 (E • Z.2) a b) (X, 0)‖ ≤ C)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ → Vec 2 → P → Vec 2)
    (Q : ∀ d J a, IndependentParameterSourceReserve H (fun t z Y => B d J t z Y a))
    (θ κ e B₀ : ℝ) (nγ : ℕ) (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) (he : 0 ≤ e) (hB₀ : 0 ≤ B₀)
    (hQ : ∀ d J a n, n ≤ H → (Q d J a).budget n ≤
      θ * (κ * e ^ (nγ - 2) * E ^ ((d : ℝ) - (nγ : ℝ)) * B₀))
    (A : DerivativeWord2 r) :
    ∃ R : IndependentParameterSourceReserve H
      (fun t z Y a => independentTimeWindowSource I
        (fun t z Y => transportedCoeff (K t z Y) Dγ (fun d J => B d J t z Y) r A 0 a) t z Y),
      ∀ n ≤ H, R.budget n ≤ θ * (κ * e ^ (nγ - 2) * E ^ (((r + 1 : ℕ) : ℝ) - (nγ : ℝ))) *
        (2 * ∑ j : Fin (H + 1), independentPiolaDimensionlessPrice N Dγ j.val C B₀ r) := by
  let MB := fun (d : ℕ) (_J : DerivativeWord2 (d - 1)) =>
    κ * e ^ (nγ - 2) * E ^ ((d : ℝ) - (nγ : ℝ)) * B₀
  have hMB : ∀ d J, 0 ≤ MB d J := by
    intro d J
    exact mul_nonneg (mul_nonneg (mul_nonneg hκ (pow_nonneg he _))
      (Real.rpow_nonneg hE.le _)) hB₀
  obtain ⟨R, hR⟩ := independentPiolaWindowSourceReserve H N Dγ r hHN E hE C hC I hI K hK hKm hKp hKC
    B Q θ hθ MB hMB hQ A
  refine ⟨R, ?_⟩
  intro n hn
  apply (hR n hn).trans_eq
  have hprice j : independentPiolaSourcePrice N Dγ j r E C MB =
      (κ * e ^ (nγ - 2) * E ^ (((r + 1 : ℕ) : ℝ) - (nγ : ℝ))) *
        independentPiolaDimensionlessPrice N Dγ j C B₀ r :=
    independentPiolaSourcePrice_dimensional N Dγ j r nγ E κ e C B₀ hE
  simp only [hprice, ← Finset.mul_sum]
  ring

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory AVenhance
namespace AVRegularity.EntryWeakProofs

/-! Concrete smooth transition matrices and produced arrays supply windowed Piola inputs. -/

variable (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]

structure IndependentPiolaWindowDatum (H N Dγ nγ : ℕ) (E C θ κ e B₀ : ℝ) where
  window : Set ℝ
  measurable_window : MeasurableSet window
  matrix : ℝ → Vec 2 → P → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ
  smooth : ∀ t a b, ContDiff ℝ (⊤ : ℕ∞)
    (fun Z : (Vec 2 × P) × Vec 2 => matrix t Z.1.1 Z.1.2 Z.2 a b)
  measurable : ∀ Y h a b, Measurable (fun Z : ℝ × Vec 2 => matrix Z.1 Z.2 Y h a b)
  periodic : ∀ t Y h a b, IsZ2Periodic (fun z => matrix t z Y h a b)
  jets : ∀ t ∈ window, ∀ X : Vec 2 × P, ∀ a b j, j ≤ N →
    ‖iteratedFDeriv ℝ j (fun Z : (Vec 2 × P) × Vec 2 =>
      matrix t Z.1.1 Z.1.2 (E • Z.2) a b) (X, 0)‖ ≤ C
  array : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ → Vec 2 → P → Vec 2
  reserve : ∀ d J a, IndependentParameterSourceReserve H (fun t z Y => array d J t z Y a)
  budget : ∀ d J a n, n ≤ H → (reserve d J a).budget n ≤
    θ * (κ * e ^ (nγ - 2) * E ^ ((d : ℝ) - (nγ : ℝ)) * B₀)

variable {P}

def IndependentPiolaWindowDatum.source {H N Dγ nγ : ℕ} {E C θ κ e B₀ : ℝ}
    (S : IndependentPiolaWindowDatum P H N Dγ nγ E C θ κ e B₀)
    (r : ℕ) (A : DerivativeWord2 r) (t : ℝ) (z : Vec 2) (Y : P) : Vec 2 :=
  fun a => independentTimeWindowSource S.window
    (fun t z Y => transportedCoeff (S.matrix t z Y) Dγ (fun d J => S.array d J t z Y) r A 0 a) t z Y

theorem IndependentPiolaWindowDatum.production {H N Dγ nγ : ℕ} {E C θ κ e B₀ : ℝ}
    (S : IndependentPiolaWindowDatum P H N Dγ nγ E C θ κ e B₀)
    (hHN : H + Dγ ≤ N) (hE : 0 < E) (hC : 0 ≤ C)
    (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) (he : 0 ≤ e) (hB₀ : 0 ≤ B₀)
    (r : ℕ) (A : DerivativeWord2 r) :
    ∃ R : IndependentParameterSourceReserve H (S.source r A),
      ∀ n ≤ H, R.budget n ≤ θ * (κ * e ^ (nγ - 2) * E ^ (((r + 1 : ℕ) : ℝ) - (nγ : ℝ))) *
        (2 * ∑ j : Fin (H + 1), independentPiolaDimensionlessPrice N Dγ j.val C B₀ r) :=
  independentPiolaWindowDimensionalSourceReserve H N Dγ r hHN E hE C hC S.window S.measurable_window
    S.matrix S.smooth S.measurable S.periodic S.jets S.array S.reserve
    θ κ e B₀ nγ hθ hκ he hB₀ S.budget A

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Uniform genuine primitive budgets produce higher carriers for every finite ordered inverse word. -/

section
variable {I Y : Type*}

theorem uniform_word_higher_carrier_of_initial_zero {a b : ℝ} (hab : a < b)
    (N H : ℕ) (P : Y → MolecularData)
    (G : Y → List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (src : Y → List I → ℝ → Vec 2 → ℂ)
    (F : Y → List I → ℝ → Vec 2 → ComplexCellVector)
    (c : Y → List I → ℝ → RawJet2 1 ℂ)
    (V : ∀ y K, K ≤ H → MolecularFiniteDriftBudget (P y) K)
    (Q : ∀ y w, w.length ≤ N → ∀ K, K + w.length ≤ H →
      HigherSourceCarrierData (Icc a b) K (src y w) (F y w))
    (Ns Nf : List I → ℕ → ℝ)
    (hNs : ∀ w K, 0 ≤ Ns w K) (hNf : ∀ w K, 0 ≤ Nf w K)
    (hQs : ∀ y w hw K hK, (Q y w hw K hK).Ns ≤ Ns w K)
    (hQf : ∀ y w hw K hK, (Q y w hw K hK).Nf ≤ Nf w K)
    (B : List I → ℝ) (hB : ∀ w, w.length ≤ N → 0 ≤ B w)
    (hGb : ∀ y w, w.length ≤ N → ∀ t i j, |G y w t i j| ≤ B w)
    (hGm : ∀ y w, w.length ≤ N → ∀ i j, Measurable (fun t => G y w t i j))
    (hsol : ∀ y w, w.length ≤ N → IsCellInverseValue (dataCoefficients (P y)) (src y w)
      (F y w + independentWordMetricFlux (fun p t _ => G y p t) (c y) w) (c y w))
    (hi : ∀ y w, w.length ≤ N → cellValue (c y w) a =ᵐ[volume.restrict AVenhance.unitCube] 0)
    (w : List I) (hw : w.length ≤ N) (K : ℕ) (hK : K + w.length ≤ H) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ u : ℝ → TorusHk K ℂ,
      StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧
      ∀ t ∈ Icc a b, torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube]
        cellValue (c y w) t := by
  classical
  have main (n : ℕ) : ∀ w : List I, w.length = n → w.length ≤ N → ∀ K,
      K + w.length ≤ H → ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ u : ℝ → TorusHk K ℂ,
        StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧
        ∀ t ∈ Icc a b, torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube]
          cellValue (c y w) t := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn hw K hK
      have hall (p : List I) : ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ u : ℝ → TorusHk (K + 1) ℂ,
          StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧
          (p.length < w.length → ∀ t ∈ Icc a b,
            torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (c y p) t) := by
        by_cases hp : p.length < w.length
        · obtain ⟨R, hR, hh⟩ := ih p.length (by omega) p rfl (by omega) (K + 1) (by omega)
          refine ⟨R, hR, fun y => ?_⟩
          obtain ⟨u, hum, hub, hue⟩ := hh y
          exact ⟨u, hum, hub, fun _ => hue⟩
        · exact ⟨0, le_rfl, fun _ => ⟨0, stronglyMeasurable_const,
            (fun _ => by simp), fun h => (hp h).elim⟩⟩
      choose R hR u hum hub hue using hall
      let r := ((independentWordForcing w).map
        (fun p => B p.1 * metricGradientCarrierConstant K * R p.2)).sum
      have hr : 0 ≤ r := by
        apply List.sum_nonneg
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        have hl := independentWordForcing_lengths w p hp
        exact mul_nonneg (mul_nonneg (hB p.1 (by omega)) (metricGradientCarrierConstant_nonneg K)) (hR p.2)
      refine ⟨fluxProductionConstant K * (Ns w K + Nf w K + r),
        mul_nonneg (fluxProductionConstant_nonneg K) (add_nonneg (add_nonneg (hNs w K) (hNf w K)) hr), ?_⟩
      intro y
      let Qbase := Q y w hw K hK
      have hG (p : List I) (hp : p.length ≤ N) :
          cellMetricSupNorm (fun t (_ : Vec 2) => G y p t) < ⊤ ∧
          Measurable (Function.uncurry (fun t (_ : Vec 2) => G y p t)) := by
        have hb : cellMetricSupNorm (fun t (_ : Vec 2) => G y p t) ≤ ENNReal.ofReal (B p) := by
          apply iSup_le
          intro t
          apply iSup_le
          intro z
          apply iSup_le
          intro i
          apply iSup_le
          intro j
          rw [← ofReal_norm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal (hGb y p hp t i j)
        refine ⟨hb.trans_lt ENNReal.ofReal_lt_top, ?_⟩
        apply Measurable.of_eval
        intro i
        apply Measurable.of_eval
        intro j
        exact (hGm y p hp i j).comp measurable_fst
      have hl p (hp : p ∈ independentWordForcing w) := independentWordForcing_lengths w p hp
      obtain ⟨Qnext, hs, hf⟩ := Qbase.metricFluxList_exists (independentWordForcing w)
        (fun p => G y p.1) (fun p => c y p.2) (fun p => u p.2 y)
        (fun p => B p.1) (fun p => R p.2)
        (fun p hp => hB p.1 (by have hh := hl p hp; omega))
        (fun p _ => hR p.2)
        (fun p hp => hGm y p.1 (by have hh := hl p hp; omega))
        (fun p hp => hGb y p.1 (by have hh := hl p hp; omega))
        (fun p _ => hum p.2 y) (fun p _ => hub p.2 y)
        (fun p hp => (cellSolution_restrict (subset_univ _) ordConnected_Icc
          (hsol y p.2 (by have hh := hl p hp; omega)).1).2.1)
        (fun p hp => ae_restrict_of_forall_mem measurableSet_Icc
          (hue p.2 y (hl p hp).2.2))
        (fun p hp => by
          have hm := cellMetricFlux_aestronglyMeasurable univ _ _
            (hG p.1 (by have hh := hl p hp; omega)).2
            (hsol y p.2 (by have hh := hl p hp; omega)).1.2.2.2.1
          have hb := (cellMetricFlux_ul_bound univ _ (hG p.1 (by have hh := hl p hp; omega)).1
            (hG p.1 (by have hh := hl p hp; omega)).2 _
            (hsol y p.2 (by have hh := hl p hp; omega)).1.2.2.2.1).trans_lt
            (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num)
              (hG p.1 (by have hh := hl p hp; omega)).1)
              (hsol y p.2 (by have hh := hl p hp; omega)).2.2)
          exact cellUl_memLp_product_interval_ae univ _ hm hb a b (subset_univ _))
      obtain ⟨v, hvm, hvb, hve⟩ := source_window_carrier_exists hab Qnext (V y K (by omega))
        (c y w) (cellSolution_restrict (subset_univ _) ordConnected_Icc (hsol y w hw).1) (hi y w hw)
      refine ⟨v, hvm, fun t => (hvb t).trans ?_, hve⟩
      apply mul_le_mul_of_nonneg_left _ (fluxProductionConstant_nonneg K)
      rw [hs, hf]
      simpa only [add_assoc] using
        add_le_add (hQs y w hw K hK) (add_le_add (hQf y w hw K hK) (le_refl r))
  exact main w.length w rfl hw K hK
end

/-! Uniform genuine primitive budgets produce higher carriers for every finite ordered inverse word. -/

section
variable {I Y : Type*}

theorem uniform_word_higher_carrier_variable_window_of_initial_zero (a b : Y → ℝ) (hab : ∀ y, a y < b y)
    (N H : ℕ) (P : Y → MolecularData)
    (G : Y → List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (src : Y → List I → ℝ → Vec 2 → ℂ)
    (F : Y → List I → ℝ → Vec 2 → ComplexCellVector)
    (c : Y → List I → ℝ → RawJet2 1 ℂ)
    (V : ∀ y K, K ≤ H → MolecularFiniteDriftBudget (P y) K)
    (Q : ∀ y w, w.length ≤ N → ∀ K, K + w.length ≤ H →
      HigherSourceCarrierData (Icc (a y) (b y)) K (src y w) (F y w))
    (Ns Nf : List I → ℕ → ℝ)
    (hNs : ∀ w K, 0 ≤ Ns w K) (hNf : ∀ w K, 0 ≤ Nf w K)
    (hQs : ∀ y w hw K hK, (Q y w hw K hK).Ns ≤ Ns w K)
    (hQf : ∀ y w hw K hK, (Q y w hw K hK).Nf ≤ Nf w K)
    (B : List I → ℝ) (hB : ∀ w, w.length ≤ N → 0 ≤ B w)
    (hGb : ∀ y w, w.length ≤ N → ∀ t i j, |G y w t i j| ≤ B w)
    (hGm : ∀ y w, w.length ≤ N → ∀ i j, Measurable (fun t => G y w t i j))
    (hsol : ∀ y w, w.length ≤ N → IsCellInverseValue (dataCoefficients (P y)) (src y w)
      (F y w + independentWordMetricFlux (fun p t _ => G y p t) (c y) w) (c y w))
    (hi : ∀ y w, w.length ≤ N → cellValue (c y w) (a y) =ᵐ[volume.restrict AVenhance.unitCube] 0)
    (w : List I) (hw : w.length ≤ N) (K : ℕ) (hK : K + w.length ≤ H) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ u : ℝ → TorusHk K ℂ,
      StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧
      ∀ t ∈ Icc (a y) (b y), torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube]
        cellValue (c y w) t := by
  classical
  have main (n : ℕ) : ∀ w : List I, w.length = n → w.length ≤ N → ∀ K,
      K + w.length ≤ H → ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ u : ℝ → TorusHk K ℂ,
        StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧
        ∀ t ∈ Icc (a y) (b y), torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube]
          cellValue (c y w) t := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn hw K hK
      have hall (p : List I) : ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ u : ℝ → TorusHk (K + 1) ℂ,
          StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧
          (p.length < w.length → ∀ t ∈ Icc (a y) (b y),
            torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (c y p) t) := by
        by_cases hp : p.length < w.length
        · obtain ⟨R, hR, hh⟩ := ih p.length (by omega) p rfl (by omega) (K + 1) (by omega)
          refine ⟨R, hR, fun y => ?_⟩
          obtain ⟨u, hum, hub, hue⟩ := hh y
          exact ⟨u, hum, hub, fun _ => hue⟩
        · exact ⟨0, le_rfl, fun _ => ⟨0, stronglyMeasurable_const,
            (fun _ => by simp), fun h => (hp h).elim⟩⟩
      choose R hR u hum hub hue using hall
      let r := ((independentWordForcing w).map
        (fun p => B p.1 * metricGradientCarrierConstant K * R p.2)).sum
      have hr : 0 ≤ r := by
        apply List.sum_nonneg
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        have hl := independentWordForcing_lengths w p hp
        exact mul_nonneg (mul_nonneg (hB p.1 (by omega)) (metricGradientCarrierConstant_nonneg K)) (hR p.2)
      refine ⟨fluxProductionConstant K * (Ns w K + Nf w K + r),
        mul_nonneg (fluxProductionConstant_nonneg K) (add_nonneg (add_nonneg (hNs w K) (hNf w K)) hr), ?_⟩
      intro y
      let Qbase := Q y w hw K hK
      have hG (p : List I) (hp : p.length ≤ N) :
          cellMetricSupNorm (fun t (_ : Vec 2) => G y p t) < ⊤ ∧
          Measurable (Function.uncurry (fun t (_ : Vec 2) => G y p t)) := by
        have hb : cellMetricSupNorm (fun t (_ : Vec 2) => G y p t) ≤ ENNReal.ofReal (B p) := by
          apply iSup_le
          intro t
          apply iSup_le
          intro z
          apply iSup_le
          intro i
          apply iSup_le
          intro j
          rw [← ofReal_norm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal (hGb y p hp t i j)
        refine ⟨hb.trans_lt ENNReal.ofReal_lt_top, ?_⟩
        apply Measurable.of_eval
        intro i
        apply Measurable.of_eval
        intro j
        exact (hGm y p hp i j).comp measurable_fst
      have hl p (hp : p ∈ independentWordForcing w) := independentWordForcing_lengths w p hp
      obtain ⟨Qnext, hs, hf⟩ := Qbase.metricFluxList_exists (independentWordForcing w)
        (fun p => G y p.1) (fun p => c y p.2) (fun p => u p.2 y)
        (fun p => B p.1) (fun p => R p.2)
        (fun p hp => hB p.1 (by have hh := hl p hp; omega))
        (fun p _ => hR p.2)
        (fun p hp => hGm y p.1 (by have hh := hl p hp; omega))
        (fun p hp => hGb y p.1 (by have hh := hl p hp; omega))
        (fun p _ => hum p.2 y) (fun p _ => hub p.2 y)
        (fun p hp => (cellSolution_restrict (subset_univ _) ordConnected_Icc
          (hsol y p.2 (by have hh := hl p hp; omega)).1).2.1)
        (fun p hp => ae_restrict_of_forall_mem measurableSet_Icc
          (hue p.2 y (hl p hp).2.2))
        (fun p hp => by
          have hm := cellMetricFlux_aestronglyMeasurable univ _ _
            (hG p.1 (by have hh := hl p hp; omega)).2
            (hsol y p.2 (by have hh := hl p hp; omega)).1.2.2.2.1
          have hb := (cellMetricFlux_ul_bound univ _ (hG p.1 (by have hh := hl p hp; omega)).1
            (hG p.1 (by have hh := hl p hp; omega)).2 _
            (hsol y p.2 (by have hh := hl p hp; omega)).1.2.2.2.1).trans_lt
            (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num)
              (hG p.1 (by have hh := hl p hp; omega)).1)
              (hsol y p.2 (by have hh := hl p hp; omega)).2.2)
          exact cellUl_memLp_product_interval_ae univ _ hm hb (a y) (b y) (subset_univ _))
      obtain ⟨v, hvm, hvb, hve⟩ := source_window_carrier_exists (hab y) Qnext (V y K (by omega))
        (c y w) (cellSolution_restrict (subset_univ _) ordConnected_Icc (hsol y w hw).1) (hi y w hw)
      refine ⟨v, hvm, fun t => (hvb t).trans ?_, hve⟩
      apply mul_le_mul_of_nonneg_left _ (fluxProductionConstant_nonneg K)
      rw [hs, hf]
      simpa only [add_assoc] using
        add_le_add (hQs y w hw K hK) (add_le_add (hQf y w hw K hK) (le_refl r))
  exact main w.length w rfl hw K hK
end

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Genuine independent forcing copies and earlier coefficient germs transfer the actual native inverse. -/

variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem independent_native_inverse_transfer
    (Q : LiftOperatorData ι (fun _ => ℝ) D) (Cc Dc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (f : ℝ → Vec 2 → ι → ℝ) (hh n sZ : ℕ) (hn : 1 ≤ n)
    (a b : ℝ) (A : Vec 2 →L[ℝ] ℝ) (U : Set (Vec 2)) (hU : IsOpen U)
    (X : Vec 2) (hX : X ∈ U) (Y : Vec d)
    (g : ℝ → Vec 2 → Vec d → ι → ℝ)
    (hcopy : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m ≤ q,
      ∀ α, ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z v u,
      Cc p q m α t Z z v u = Dc p q m α t Z z v u)
    (hforce : ∀ t ∈ Icc a b, ∀ z,
      g t z Y = normalizedLiftCellSource Q Dc f hh n A t z X)
    (hc : IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => liftCellSource Q Cc f hh n t X z)
      (fun t z => liftApply n (Cc hh n) f t X z)) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => independentTimeWindowSource (Ioc a b) g t z Y)
      (fun t z => (Real.exp (A X))⁻¹ • liftApply n (Cc hh n) f t X z) := by
  have hi := cellFieldInverse_const_smul _ _ sZ a b 0 _ _ hc ((Real.exp (A X))⁻¹)
  have hz : (fun z : Vec 2 => (Real.exp (A X))⁻¹ • (0 : Vec 2 → ι → ℝ) z) = 0 := by
    funext z
    simp only [Pi.zero_apply, smul_zero]
  rw [hz] at hi
  have hi' : IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => g t z Y)
      (fun t z => (Real.exp (A X))⁻¹ • liftApply n (Cc hh n) f t X z) := by
    apply cellFieldInverse_source_congr_on _ _ sZ a b 0 _ _ _ _ hi
    intro t ht
    funext z
    rw [hforce t ht z]
    exact congrArg (fun w : ι → ℝ => (Real.exp (A X))⁻¹ • w)
      (liftCellSource_slow_open_congr_predecessors hU Q Cc Dc f hh n hn t
        (fun p q hpq m hm α Z hZ z v u => hcopy p q hpq m hm α t ht Z hZ z v u) X hX z)
  apply cellFieldInverse_source_ae_congr hi'
  filter_upwards [independent_time_window_Ioc_ae_eq g a b] with t ht
  exact (congrArg (fun f => fun z => f z Y) ht).symm

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Inherited constituent fluxes preserve genuine coefficient reserves over independent family parameters. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def independentSourceFluxComponentCoefficient
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (f : ℝ → Vec 2 → P → ι → ℝ) (k : Fin 2) (j : ℕ) (v : ι)
    (t : ℝ) (z : Vec 2) (Y : P) : ℝ :=
  ∑ u : ι, ∑ d : Finset.Icc 2 D,
    ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.val - 1),
      a v u d γ α t z Y k • γ.map
        (independentCovariantListCoefficients L A η (List.ofFn α)
          (fun t z Y => f t z Y u) j t z Y)).sum

def independentSourceFluxComponentReserve (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (f : ℝ → Vec 2 → P → ι → ℝ)
    (Qf : ∀ u, IndependentParameterSourceReserve (H + D) (fun t z Y => f t z Y u))
    (Qa : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IndependentParameterSourceReserve H (a v u d γ α))
    (k : Fin 2) (j : ℕ) (v : ι) :
    IndependentParameterSourceReserve H
      (independentSourceFluxComponentCoefficient edge a L A η f k j v) := by
  let F := fun (u : ι) (d : Finset.Icc 2 D)
      (γ : Constituent d.val ℝ ℝ) (α : DerivativeWord2 (d.val - 1)) t z Y =>
    a v u d γ α t z Y k • γ.map
      (independentCovariantListCoefficients L A η (List.ofFn α)
        (fun t z Y => f t z Y u) j t z Y)
  let Qword := fun (u : ι) (d : Finset.Icc 2 D) (α : DerivativeWord2 (d.val - 1)) =>
    (Qf u).covariantList H L hL A η (List.ofFn α)
      (by simp only [List.length_ofFn]; have hd := (Finset.mem_Icc.mp d.property).2; omega) j
  let Q := fun (u : ι) (d : Finset.Icc 2 D)
      (γ : Constituent d.val ℝ ℝ) (hγ : γ ∈ edge v u d)
      (α : DerivativeWord2 (d.val - 1)) =>
    ((Qa v u d γ hγ α).map
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k)).scalarProduct
        ((Qword u d α).map γ.map)
  exact IndependentParameterSourceReserve.fintypeSum H
    (fun u t z Y => ∑ d : Finset.Icc 2 D,
      ((edge v u d).map (fun γ => ∑ α, F u d γ α t z Y)).sum)
    (fun u => IndependentParameterSourceReserve.fintypeSum H
      (fun d t z Y => ((edge v u d).map (fun γ => ∑ α, F u d γ α t z Y)).sum)
      (fun d => IndependentParameterSourceReserve.listSum (edge v u d) H
        (fun γ t z Y => ∑ α, F u d γ α t z Y)
        (fun γ hγ => IndependentParameterSourceReserve.fintypeSum H (F u d γ) (Q u d γ hγ))))

end AVRegularity.EntryWeakProofs
end
