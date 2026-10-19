-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PeriodizedCompactCoefficientPairingIntegrable
import AVRegularity.CycleReference.TorusChartEquation
import AVRegularity.CycleJoint.PlaneImageJetMomentNorm
import AVRegularity.CycleJoint.PeriodicOperatorLocalization
import AVRegularity.CycleJoint.PlaneJetMultiplierSuperposition
import AVRegularity.CycleWords.CellTransitionGeometry
import AVRegularity.Weighted.ParameterCoefficientJetMeasurable
import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
public import AVRegularity.Weighted.PlaneH1SpectralCutoff
import AVRegularity.CycleComparison.Coarse.SecondOrderResponse
import AVRegularity.CycleReference.TransitionTaylorBounds
import AVRegularity.CycleReference.MeanEnhancementScale
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Uniform moments preserve the actual torus Sobolev time trace after periodization. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem periodizeRadialPlaneCarrier_continuousOn {X : Type*} [TopologicalSpace X]
    (f : X → PlaneHk Set.univ K E) (s : Set X) (hf : ContinuousOn f s) (z : Vec 2)
    (hm : ∀ t a, MemLp (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet a y) 2 volume)
    (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ t ∈ s, ∀ a, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet a y) 2 volume ≤ ENNReal.ofReal M) :
    ContinuousOn (fun t => periodizeRadialPlaneCarrier (f t) z (hm t)) s := by
  have ha (a : JetIndex2 K) : ContinuousOn
      (fun t => (periodizeRadialPlaneCarrier (f t) z (hm t)).val a) s := by
    have hc := periodized_image_jet_continuousOn AVenhance.unitCube 2 (by norm_num)
      unitCube_subset_ball_two z a f s hf M hM
      (fun t _ => (hm t a).aestronglyMeasurable) (fun t ht => hb t ht a)
    exact hc.congr (fun t _ => periodizeRadialPlaneCarrier_component_eq_series (f t) z (hm t) a)
  have hp : ContinuousOn
      (fun t => fun a : JetIndex2 K => (periodizeRadialPlaneCarrier (f t) z (hm t)).val a) s :=
    continuousOn_pi.mpr ha
  let e := PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : JetIndex2 K => ComponentL2 (volume.restrict AVenhance.unitCube) E)
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  have hj := e.symm.continuous.comp_continuousOn hp
  convert hj using 1
  funext t
  exact (e.symm_apply_apply (periodizeRadialPlaneCarrier (f t) z (hm t)).val).symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Full Piola coefficient sums retain the original molecular derivative reserve
at every lowered native order, without paying the number of original edges. -/

theorem transportedPolynomialJetPrice_reserve_cancellation
    (N D r K : ℕ) (hr : 1 ≤ r) (C ρ R : ℝ)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hR : 0 < R) (hρR : ρ ≤ R)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) (hB : ∀ d I, 0 ≤ B d I) :
    transportedPolynomialJetPrice N D r K C R
        (fun d I => B d I / derivativeReserveFactor ρ K (d - 2)) *
      derivativeReserveFactor ρ K (r - 1) ≤
    ∑ d ∈ Finset.Icc (r + 1) D, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
      ((K + 1 : ℕ) * (2 : ℝ) ^ K) ^ 2 * C * B d I *
        (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ (d - 1) := by
  unfold transportedPolynomialJetPrice
  simp only [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro I _
  apply Finset.sum_le_sum
  intro i _
  have horder : r - 1 + (d - 1 - r) = d - 2 := by
    simp only [Finset.mem_Icc] at hd
    omega
  have hb := derivativeReserveFactor_order_lowering_budget ρ R hρ hR hρR K (r - 1)
    (d - 1 - r) (B d I) (hB d I)
  rw [horder] at hb
  let L := ((K + 1 : ℕ) * (2 : ℝ) ^ K) ^ 2 * C *
    (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ (d - 1)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  calc
    _ = L * ((B d I / derivativeReserveFactor ρ K (d - 2)) * R⁻¹ ^ (d - 1 - r) *
        derivativeReserveFactor ρ K (r - 1)) := by dsimp only [L]; ring
    _ ≤ L * B d I := mul_le_mul_of_nonneg_left hb hL
    _ = _ := by dsimp only [L]; ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization AVenhance Set AVRegularity.CycleReference
open scoped Matrix.Norms.Elementwise
namespace AVRegularity.CycleJointProofs

/-! Qualitative native chart coefficient budgets are confined to the prescribed compact time set. -/

theorem chartMetric_joint_smooth {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => chartMetric hφ s p.1 p.2) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact chartMetric_entry_smooth hφ s i j

theorem chartMetric_periodic {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) : IsZ2Periodic (chartMetric hφ s t) := by
  intro k x
  unfold chartMetric chartJac
  rw [streamFlow_jacMatrix_spatial_periodic]

theorem streamVel_bounded_on_compact_time {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (T : Set ℝ) (hT : IsCompact T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ T, ∀ x, ‖streamVel φ t x‖ ≤ C :=
  spatial_periodic_bound_on_compact_time _
    (Infra.Construction.smoothPeriodic_streamVel hφ).smooth.continuous
    (fun t x k => admissible_streamVel_periodic hφ t k x) T hT

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A bounded radius times mesh gives a uniform weighted energy bound at each order. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem spatialPatchLocalization_factorial_order_sum {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) {K : ℕ} (f : TorusHk K E) (j : Fin (K + 1))
    (ρ L B : ℝ) (hρ : 0 ≤ ρ) (hL : 1 ≤ L) (hmesh : ρ * (N : ℝ) ≤ L)
    (hB : 0 ≤ B)
    (hb : ∀ l, l ≤ j.val → ∀ k x, ‖coefficientDerivativeArray
      (spatialPatchCoefficient (E := E) ζ N k) l x‖ ≤ B * (N : ℝ) ^ l) :
    (∑ p : Fin 2 → Fin N, factorialWeight ρ j.val * derivativeNormSq
      (spatialPatchLocalization hζ N hN (fun i => (p i : ℤ)) K f).val j) ≤
      (Fintype.card (PositionMask j.val) : ℝ) ^ 2 *
        (9 * B ^ 2 * L ^ (2 * K)) * factorialNormSq ρ f.val := by
  let c : ℝ := Fintype.card (PositionMask j.val)
  let P : ℝ := 9 * B ^ 2 * L ^ (2 * K)
  have hP : 0 ≤ P := by positivity
  have ht := mul_le_mul_of_nonneg_left
    (spatialPatchLocalization_derivativeNormSq_sum hζ N hN f j
      (fun l => B * (N : ℝ) ^ l) (fun l => mul_nonneg hB (pow_nonneg (Nat.cast_nonneg N) l)) hb)
    (factorialWeight_nonneg ρ j.val)
  rw [← Finset.mul_sum]
  apply ht.trans
  rw [← mul_assoc, mul_comm (factorialWeight ρ j.val) c, mul_assoc, Finset.mul_sum]
  have hs : (∑ m : PositionMask j.val, factorialWeight ρ j.val *
      ((9 * (B * (N : ℝ) ^ maskLeftLength j.val m) ^ 2) *
        derivativeNormSq f.val ⟨maskRightLength j.val m,
          Nat.lt_succ_of_le ((maskRightLength_le j.val m).trans (Nat.le_of_lt_succ j.isLt))⟩)) ≤
      c * (P * factorialNormSq ρ f.val) := by
    calc
      _ ≤ ∑ _m : PositionMask j.val, P * factorialNormSq ρ f.val := by
        apply Finset.sum_le_sum
        intro m _
        rw [← mul_assoc]
        apply le_trans (mul_le_mul_of_nonneg_right
          (factorialWeight_coefficient_mesh_price ρ (N : ℝ) L B hρ (Nat.cast_nonneg N)
            hL hmesh (Nat.le_of_lt_succ j.isLt) m) (derivativeNormSq_nonneg f.val _))
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (factorial_component_energy_le ρ f.val
          ⟨maskRightLength j.val m,
            Nat.lt_succ_of_le ((maskRightLength_le j.val m).trans
              (Nat.le_of_lt_succ j.isLt))⟩) hP
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, c]
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ c from Nat.cast_nonneg _)
  convert hm using 1
  dsimp only [c, P]
  ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Uniform finite-order Piola prices remove physical inverse-length powers
using the original reserve; the remaining chart constant is fixed in advance. -/

def transportedPolynomialUniformReservePrice (N Dmax K : ℕ) (C : ℝ) : ℝ :=
  ((K + 1 : ℕ) * (2 : ℝ) ^ K) ^ 2 * C *
    ∑ j ∈ Finset.range (Dmax + 1), (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ j

theorem transportedPolynomialUniformReservePrice_nonneg (N Dmax K : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ transportedPolynomialUniformReservePrice N Dmax K C := by
  unfold transportedPolynomialUniformReservePrice
  positivity

theorem transportedPolynomialJetPrice_uniform_reserve_bound
    (N D Dmax r K : ℕ) (hD : D ≤ Dmax) (hr : 1 ≤ r) (C ρ R : ℝ)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hR : 0 < R) (hρR : ρ ≤ R)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) (hB : ∀ d I, 0 ≤ B d I) :
    transportedPolynomialJetPrice N D r K C R
        (fun d I => B d I / derivativeReserveFactor ρ K (d - 2)) *
      derivativeReserveFactor ρ K (r - 1) ≤
    transportedPolynomialUniformReservePrice N Dmax K C *
      (∑ d ∈ Finset.Icc (r + 1) D, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2, B d I) := by
  apply (transportedPolynomialJetPrice_reserve_cancellation N D r K hr C ρ R hC hρ hR hρR B hB).trans
  unfold transportedPolynomialUniformReservePrice
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro I _
  apply Finset.sum_le_sum
  intro i _
  let Q := 3 * (N + 1 : ℕ) * (2 : ℝ) ^ N * C
  let P := ((K + 1 : ℕ) * (2 : ℝ) ^ K) ^ 2 * C
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hpow : Q ^ (d - 1) ≤ ∑ j ∈ Finset.range (Dmax + 1), Q ^ j :=
    Finset.single_le_sum (fun j _ => pow_nonneg hQ j)
      (Finset.mem_range.mpr (by have hh := (Finset.mem_Icc.mp hd).2; omega))
  have hh := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (show 0 ≤ P by dsimp only [P]; positivity) (hB d I))
  change P * B d I * Q ^ (d - 1) ≤ _
  simp only [← Finset.mul_sum]
  convert hh using 1
  dsimp only [P, Q]
  ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Spatial smoothness of the weighted actual piece array through its exact natural formula. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem weighted_piece_array_spatial_smooth
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) E n)
    (p : P') (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (r : ℕ) (A : DerivativeWord2 r) (a : Fin 2) (t : Set.Icc tS tZ) :
    ContDiff ℝ (n v : ℕ) (fun x : Vec 2 => F.weight p t *
      transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e E p c v u γ d I t
          (((F.piece p).material t).symm x)
          (e⁻¹ • ((F.piece p).material t).symm x)) r A x a) := by
  let K := naturalPreparationJacobian hφ (F.piece p).anchor t
  let B := fun d (I : DerivativeWord2 (d - 1)) (x : Vec 2) =>
    F.weight p t • F.dimFlux ν e E p c v u γ d I t
      (streamFlow φ hφ (F.piece p).anchor x t)
      (e⁻¹ • streamFlow φ hφ (F.piece p).anchor x t)
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => ((t : ℝ), x)) :=
    contDiff_const.prodMk contDiff_id
  have hK : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j) := by
    intro i j
    exact (naturalPreparationJacobian_entry_smooth hφ (F.piece p).anchor i j).comp he
  have hy : ContDiff ℝ (n v : ℕ) (fun x : Vec 2 =>
      streamFlow φ hφ (F.piece p).anchor x t) := by
    have hh : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 =>
        ((F.piece p).anchor, (x, (t : ℝ)))) :=
      contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)
    exact ((streamFlow_joint_smooth hφ).comp hh).of_le (by simp)
  have hB : ∀ d I i, ContDiff ℝ (n v : ℕ) (fun x => B d I x i) := by
    intro d I i
    have hb := (weighted_dimFlux_spatial_smooth F ν e E tS tZ n hs p c v u γ d I t).comp
      (hy.prodMk (hy.const_smul (e⁻¹)))
    exact contDiff_pi.mp hb i
  have hm := transportedCoeff_spatial_smooth K hK (F.identity v u γ).maxOrder (n v) B hB r A a
  convert hm using 1
  funext x
  exact congrFun (weighted_piece_array_eq_natural F hc ν e E p c v u γ r A t x) a

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open AVRegularity.CycleWords Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Actual sampled original flux coefficients retain their positive molecular price. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem familyPointwiseMolecular_sample_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p) :
    ∀ t : ℝ, (∀ Y : Vec 2, (t, Y) ∈ dom p c) →
      ∀ X0 φ j, j ≤ K v → ∀ z,
      (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (fun y =>
        F.flux p c v u γ d I t (X0 + (e / E) • y) (y + φ)) z‖ ≤
        (4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2 *
          molecularRealPrice ν ρ (K v) (d - 2)
            (pointwiseMolecularJet ρ e (K v) 0 (fun x : F.Index => dom x.1 x.2)
              (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) /
                derivativeReserveFactor (ρ / e) (K v) (d - 2) := by
  intro t hdom X0 φ j hj z
  have ht := familyPointwiseMolecular_uniform_reserve F π hπ K Kmax hK dom ν e E ρ
    hν he hE hρ C J b₀ henv v u γ hγ d hd I 0 (Nat.zero_le J) p c t
  let M := molecularRealPrice ν ρ (K v) (d - 2)
    (pointwiseMolecularJet ρ e (K v) 0 (fun x : F.Index => dom x.1 x.2)
      (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
  let R := derivativeReserveFactor (ρ / e) (K v) (d - 2)
  have hR : 0 < R := by dsimp [R, derivativeReserveFactor]; positivity
  have hM : 0 ≤ M := molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _
  have hf : ContDiff ℝ (K v : ℕ) (Function.uncurry (F.flux p c v u γ d I t)) :=
    (molecular_joint_contDiff F dom E hE.ne' (fun v => K v + J)
      henv.1 p c t hdom v u γ d I).of_le (by exact_mod_cast Nat.le_add_right (K v) J)
  have hb (a b : ℕ) (hab : a + b ≤ K v) (X z : Vec 2) :
      (ρ / e) ^ (a + b) * |e / E| ^ a *
        ‖iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b
          (F.flux p c v u γ d I t X') z) X‖ ≤ (Kmax.factorial : ℝ) ^ 2 * M / R := by
    apply (le_div_iff₀ hR).mpr
    have hh := ht hdom a b hab X z
    rw [Nat.zero_add] at hh
    simpa only [pow_zero, mul_one, abs_of_pos (div_pos he hE), M, R] using hh
  have hh := jointSample_normalized_jet_le hf (ρ / e) (e / E)
    ((Kmax.factorial : ℝ) ^ 2 * M / R) (div_pos hρ he).le (by positivity) hb X0 φ j hj z
  apply hh.trans
  have hs := mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (hK v))
    (show 0 ≤ (Kmax.factorial : ℝ) ^ 2 * M / R by positivity)
  simpa only [mul_div_assoc, mul_assoc, M, R] using hs

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory Set AVRegularity.CycleReference
open scoped Matrix.Norms.Elementwise
namespace AVRegularity.CycleJointProofs

/-! Smooth periodic physical drifts supply qualitative windowed native material coefficients. -/

theorem materialChartDrift_smooth {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
      chartVector hφ s (fun r x => v r x - streamVel φ r x) p.1 p.2) :=
  chartVector_joint_smooth hφ s (hv.sub (Infra.Construction.smoothPeriodic_streamVel hφ).smooth)

theorem materialChartDrift_periodic {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s : ℝ) (v : ℝ → Vec 2 → Vec 2) (hp : ∀ t, IsZ2Periodic (v t)) (t : ℝ) :
    IsZ2Periodic (chartVector hφ s (fun r x => v r x - streamVel φ r x) t) := by
  apply chartVector_periodic hφ s
  intro r k x
  dsimp only
  rw [hp r k x, admissible_streamVel_periodic hφ r k x]

theorem materialChartDrift_bound {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ t, IsZ2Periodic (v t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x,
      ‖chartVector hφ s (fun r y => v r y - streamVel φ r y) t x‖ ≤ C :=
  spatial_periodic_bound_on_compact_time _ (materialChartDrift_smooth hφ s v hv).continuous
    (fun t x k => materialChartDrift_periodic hφ s v hp t k x) (Icc a b) isCompact_Icc

theorem viscousChartMetric_smooth {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s ν : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ν • chartMetric hφ s p.1 p.2) :=
  ContDiff.const_smul ν (chartMetric_joint_smooth hφ s)

theorem viscousChartMetric_bound {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s ν a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ i j x,
      |(ν • chartMetric hφ s t x) i j| ≤ C := by
  obtain ⟨C, hC, hb⟩ := spatial_periodic_bound_on_compact_time _
    (viscousChartMetric_smooth hφ s ν).continuous
    (fun t x k => congrArg (fun M => ν • M) (chartMetric_periodic hφ s t k x))
    (Icc a b) isCompact_Icc
  refine ⟨C, hC, ?_⟩
  intro t ht i j x
  have he : |(ν • chartMetric hφ s t x) i j| ≤ ‖ν • chartMetric hφ s t x‖ := by
    simpa only [Real.norm_eq_abs] using
      (Matrix.norm_entry_le_entrywise_sup_norm (ν • chartMetric hφ s t x) (i := i) (j := j))
  exact he.trans (hb t ht x)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The actual spatially varying metric has finite native order coefficients
and finite regularity on its actual time window. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

theorem metric_order_coefficients_finite
    (K : ι → ℕ) (D : ℕ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (ρ a b : ℝ) (v u : ι) (d : admissibleOrders K D v u)
    (hG : ∀ t ∈ Set.Icc a b, ∀ k j, ContDiff ℝ (K v : ℕ) (fun x => G t x k j))
    (M : Fin (K v + 1) → ℝ)
    (hb : ∀ (l : Fin (K v + 1)) t, t ∈ Set.Icc a b → ∀ x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M l) :
    coefficientSeminorm ρ (K v) a b
      (planeDiagonalGradientCoefficient (h := h) K D (fun _ t z => G t z - 1) v u d) ≠ ⊤ := by
  by_cases huv : u = v
  · subst u
    by_cases hd : d.1 = 2
    · have heq : planeDiagonalGradientCoefficient (h := h) K D (fun _ t z => G t z - 1) v v d =
          fun t z => metricFlux (h := h) (G t z - 1) (d.1 - 1) (a := v) rfl (by omega) := by
        funext t x
        exact planeDiagonalGradientCoefficient_self_eq_metricFlux K D (fun _ t z => G t z - 1) v d hd t x
      rw [heq]
      exact metricFlux_deviation_coefficientSeminorm_ne_top ρ (K v) a b G hG M hb
        (d.1 - 1) rfl (by omega)
    · have hz : planeDiagonalGradientCoefficient (h := h) K D (fun _ t z => G t z - 1) v v d = 0 := by
        funext t x
        exact planeDiagonalGradientCoefficient_of_order_ne K D _ v v d t x hd
      rw [hz, CycleComparison.Coarse.coefficientSeminorm_zero_coefficient]
      exact ENNReal.zero_ne_top
  · have hz : planeDiagonalGradientCoefficient (h := h) K D (fun _ t z => G t z - 1) v u d = 0 := by
      funext t x
      exact planeDiagonalGradientCoefficient_of_component_ne K D _ v u d t x huv
    rw [hz, CycleComparison.Coarse.coefficientSeminorm_zero_coefficient]
    exact ENNReal.zero_ne_top

theorem metric_order_coefficient_contDiff
    (K : ι → ℕ) (D : ℕ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v u : ι) (d : admissibleOrders K D v u) (t : ℝ)
    (hG : ∀ k j, ContDiff ℝ (K v : ℕ) (fun x => G t x k j)) :
    ContDiff ℝ (K v : ℕ)
      (planeDiagonalGradientCoefficient (h := h) K D (fun _ t z => G t z - 1) v u d t) := by
  by_cases huv : u = v
  · subst u
    by_cases hd : d.1 = 2
    · have heq : planeDiagonalGradientCoefficient (h := h) K D
          (fun _ t z => G t z - 1) v v d t =
          fun z => metricFlux (h := h) (G t z - 1) (d.1 - 1) (a := v) rfl (by omega) := by
        funext x
        exact planeDiagonalGradientCoefficient_self_eq_metricFlux K D
          (fun _ t z => G t z - 1) v d hd t x
      rw [heq]
      apply metricFlux_contDiff
      intro k j
      exact (hG k j).sub contDiff_const
    · have hz : planeDiagonalGradientCoefficient (h := h) K D
          (fun _ t z => G t z - 1) v v d t = 0 := by
        funext x
        exact planeDiagonalGradientCoefficient_of_order_ne K D _ v v d t x hd
      rw [hz]
      exact contDiff_const
  · have hz : planeDiagonalGradientCoefficient (h := h) K D
        (fun _ t z => G t z - 1) v u d t = 0 := by
      funext x
      exact planeDiagonalGradientCoefficient_of_component_ne K D _ v u d t x huv
    rw [hz]
    exact contDiff_const

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Positive native Piola transport bounds pass to the literal assembled operator coefficient. -/

theorem native_transport_assembly_jet_bound
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (N Dγ n r : ℕ) (C E ρ : ℝ) (hC : 0 ≤ C) (hE : 0 < E)
    (hρ : 0 ≤ ρ) (hρE : ρ ≤ E) (hn : n + Dγ ≤ N)
    (hKC : ∀ a b j, j ≤ N → ∀ x,
      E ^ j * ‖iteratedFDeriv ℝ j (fun y => K y a b) x‖ ≤ C)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 → Vec 2)
    (hB : ∀ d I i, ContDiff ℝ (n : ℕ) (fun x => B d I x i))
    (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ)
    (hBj : ∀ d ∈ Finset.Icc (r + 1) Dγ, ∀ I i j, j ≤ n → ∀ y,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => B d I x i) y‖ ≤ MB d I)
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Cmap : U →L[ℝ] V) (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => nativeArrayAssembly r Cmap
      (fun a A => transportedCoeff K Dγ (fun d I => B d I y) r A y a)) x‖ ≤
      ∑ _a : Fin 2, ∑ _A : DerivativeWord2 r, ‖Cmap‖ *
        (∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
          ((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C * MB d I *
            ((3 * (N + 1 : ℕ) * 2 ^ N * C) ^ (d - 1) * E⁻¹ ^ (d - 1 - r))) := by
  have hh := nativeArrayAssembly_jet_norm_le r n Cmap
    (fun y a A => transportedCoeff K Dγ (fun d I => B d I y) r A y a)
    (fun a A => transportedCoeff_spatial_smooth K hK Dγ n B hB r A a) x
  apply (mul_le_mul_of_nonneg_left hh (pow_nonneg hρ n)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left
    (transportedCoeff_molecular_jet_bound K hK N Dγ n r C E ρ hC hE hρ hρE hn
      hKC B hB MB hBj A a x) (norm_nonneg _)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Integrable moment bounds periodize the genuine full Sobolev carrier in L2 time. -/

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [MeasurableSpace X] {K : ℕ}

theorem periodizeRadialPlaneCarrier_time_memLp (μ : Measure X)
    (f : X → PlaneHk Set.univ K E) (hf : MemLp f 2 μ) (z : Vec 2)
    (hm : ∀ t a, MemLp (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet a y) 2 volume)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hb : ∀ᵐ t ∂μ, ∀ a, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet a y) 2 volume ≤ ENNReal.ofReal ‖M t‖) :
    MemLp (fun t => periodizeRadialPlaneCarrier (f t) z (hm t)) 2 μ := by
  apply torusHk_time_memLp_of_jets
  intro a
  have ht := periodized_image_jet_time_memLp μ AVenhance.unitCube 2 (by norm_num)
    unitCube_subset_ball_two z a f hf M hM
    (Filter.Eventually.of_forall (fun t => (hm t a).aestronglyMeasurable))
    (hb.mono (fun _ ht => ht a))
  have he : (fun t => (periodizeRadialPlaneCarrier (f t) z (hm t)).val a) =
      (fun t => ∑' n : Fin 2 → ℤ, planeImageJetCLM AVenhance.unitCube (AVenhance.latticeShift n) a (f t)) :=
    funext (fun t => periodizeRadialPlaneCarrier_component_eq_series (f t) z (hm t) a)
  rwa [he]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The full factorial-energy localization budget is independent of fiber dimension. -/

def patchLeibnizEnergyCount (K : ℕ) : ℝ :=
  ∑ j : Fin (K + 1), (Fintype.card (PositionMask j.val) : ℝ) ^ 2

theorem patchLeibnizEnergyCount_nonneg (K : ℕ) : 0 ≤ patchLeibnizEnergyCount K :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem spatialPatchLocalization_factorialNormSq_sum {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) {K : ℕ} (f : TorusHk K E)
    (ρ L B : ℝ) (hρ : 0 ≤ ρ) (hL : 1 ≤ L) (hmesh : ρ * (N : ℝ) ≤ L)
    (hB : 0 ≤ B)
    (hb : ∀ l, l ≤ K → ∀ k x, ‖coefficientDerivativeArray
      (spatialPatchCoefficient (E := E) ζ N k) l x‖ ≤ B * (N : ℝ) ^ l) :
    (∑ p : Fin 2 → Fin N, factorialNormSq ρ
      (spatialPatchLocalization hζ N hN (fun i => (p i : ℤ)) K f).val) ≤
      (patchLeibnizEnergyCount K * (9 * B ^ 2 * L ^ (2 * K))) * factorialNormSq ρ f.val := by
  unfold factorialNormSq
  rw [Finset.sum_comm]
  have ht := Finset.sum_le_sum (s := Finset.univ)
    (fun (j : Fin (K + 1)) _ => spatialPatchLocalization_factorial_order_sum hζ N hN f j
      ρ L B hρ hL hmesh hB (fun l hl => hb l (hl.trans (Nat.le_of_lt_succ j.isLt))))
  apply ht.trans_eq
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The literal transition array reconstructs every positive native ordered derivative after an
inverse chart change. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inverseChart_ordered_native_jet_expansion (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) ⇑X) (hY : ContDiff ℝ (⊤ : ℕ∞) ⇑X.symm)
    {n : ℕ} (hn : 0 < n) (I : DerivativeWord2 n)
    (g : Vec 2 → E) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Vec 2) :
    (∑ r ∈ Finset.Icc 1 n, ∑ A : DerivativeWord2 r,
      transitionT (chartInvJacobian ⇑X.symm) (List.ofFn I) (List.ofFn A) y •
        orderedDerivative A (g ∘ X.symm) y) = orderedDerivative I g (X.symm y) := by
  have he := congrFun (inverseChart_native_jet_expansion X hX hY (List.ofFn I) g hg) y
  rw [listCoordinateDerivative_eq_ordered I g hg] at he
  have hp : transitionJetExpansion (chartInvJacobian ⇑X.symm) (List.ofFn I)
      (g ∘ X.symm) y = ∑ r ∈ Finset.Icc 1 n,
        transitionJetTerm (chartInvJacobian ⇑X.symm) (List.ofFn I) r (g ∘ X.symm) y := by
    have hne : List.ofFn I ≠ [] := by
      intro h
      have hh := congrArg List.length h
      simp only [List.length_ofFn, List.length_nil] at hh
      omega
    cases hlist : List.ofFn I with
    | nil => exact (hne hlist).elim
    | cons i J =>
      have hl : (i :: J).length = n := by rw [← hlist, List.length_ofFn]
      simpa only [hlist, hl] using
        transitionJetExpansion_positive (chartInvJacobian ⇑X.symm) i J (g ∘ X.symm) y
  rw [hp] at he
  unfold transitionJetTerm at he
  simp_rw [listCoordinateDerivative_eq_ordered _ (g ∘ X.symm) (hg.comp hY)] at he
  exact he

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory Set AVRegularity.CycleReference
open scoped Matrix.Norms.Elementwise
namespace AVRegularity.CycleJointProofs

/-! Native material coefficient slices and their joint window measurability. -/

theorem materialChartDrift_continuous_slice {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2)) (t : ℝ) :
    Continuous (chartVector hφ s (fun r x => v r x - streamVel φ r x) t) := by
  have hg : Continuous (fun x : Vec 2 => (t, x)) := continuous_const.prodMk continuous_id
  have hc := (materialChartDrift_smooth hφ s v hv).continuous.comp hg
  exact hc

theorem viscousChartMetric_continuous_entry_slice {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s ν t : ℝ) (i j : Fin 2) :
    Continuous (fun x => (ν • chartMetric hφ s t x) i j) := by
  have hg : Continuous (fun x : Vec 2 => (t, x)) := continuous_const.prodMk continuous_id
  have hc := ((continuous_apply j).comp ((continuous_apply i).comp
    (viscousChartMetric_smooth hφ s ν).continuous)).comp hg
  exact hc

theorem materialChartDrift_measurable_window {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2)) :
    Measurable (fun p : Icc a b × Vec 2 =>
      chartVector hφ s (fun r x => v r x - streamVel φ r x) p.1 p.2) := by
  have hm : Measurable (fun p : Icc a b × Vec 2 => ((p.1 : ℝ), p.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hg := (materialChartDrift_smooth hφ s v hv).continuous.measurable
  have hp := hg.comp hm
  exact hp

theorem viscousChartMetric_measurable_window {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s ν a b : ℝ) :
    Measurable (fun p : Icc a b × Vec 2 => ν • chartMetric hφ s p.1 p.2) := by
  have hm : Measurable (fun p : Icc a b × Vec 2 => ((p.1 : ℝ), p.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  apply Measurable.of_eval_matrix
  intro i j
  have he : (fun p : ℝ × Vec 2 => (ν • chartMetric hφ s p.1 p.2) i j) =
      (fun p => ν * chartMetric hφ s p.1 p.2 i j) := by
    funext p
    rfl
  have hg : Measurable (fun p : ℝ × Vec 2 => (ν • chartMetric hφ s p.1 p.2) i j) := by
    rw [he]
    have hc : Measurable (fun _ : ℝ × Vec 2 => ν) := measurable_const
    exact hc.mul (chartMetric_entry_smooth hφ s i j).continuous.measurable
  have hp := hg.comp hm
  exact hp

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Membership in the true moment domain supplies absolute image-series convergence. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem radialCarrier_image_enorm_tsum_lt_top (f : PlaneHk Set.univ K E) (z : Vec 2)
    (hf : HasRadialPlaneMoments f z) (a : JetIndex2 K) :
    (∑' n : Fin 2 → ℤ,
      ‖planeImageJetCLM AVenhance.unitCube (AVenhance.latticeShift n) a f‖ₑ) < ⊤ := by
  let M := (eLpNorm (fun y => (1 + ‖y - z‖) ^ 4 • f.toFunction.jet a y) 2 volume).toReal
  have he : eLpNorm (fun y => (1 + ‖y - z‖) ^ 4 • f.toFunction.jet a y) 2 volume =
      ENNReal.ofReal M := (ENNReal.ofReal_toReal (hf a).eLpNorm_lt_top.ne).symm
  exact planeImageJetCLM_radial_enorm_tsum_lt_top AVenhance.unitCube 2 (by norm_num)
    unitCube_subset_ball_two z a f M ENNReal.toReal_nonneg (hf a).aestronglyMeasurable he.le

theorem radialCarrier_images_summable (f : PlaneHk Set.univ K E) (z : Vec 2)
    (hf : HasRadialPlaneMoments f z) (a : JetIndex2 K) :
    Summable (fun n : Fin 2 → ℤ =>
      planeImageJetCLM AVenhance.unitCube (AVenhance.latticeShift n) a f) :=
  Summable.of_enorm (radialCarrier_image_enorm_tsum_lt_top f z hf a).ne

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Every reserved Sobolev order of a compact smooth Hilbert spacetime field has strong native time regularity. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def compactSpacetimeHilbertHk (K : ℕ) (f : ℝ × Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (t : ℝ) : PlaneHk univ K E :=
  smoothCompactPlaneHk K (fun x => f (t, x))
    (hf.comp (contDiff_const.prodMk contDiff_id)) (compactSpacetime_slice_compact f hs t)

omit [FiniteDimensional ℝ E] in
theorem compactSpacetimeHilbertHk_jet_ae (K : ℕ) (f : ℝ × Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f)
    (t : ℝ) (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n) :
    (compactSpacetimeHilbertHk K f hf hs t).val ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩
      =ᵐ[volume.restrict univ] (fun x => spacetimeOrderedDerivative f w (t, x)) := by
  have ha := smoothCompactPlaneHk_jet_ae K (fun x => f (t, x))
    (hf.comp (contDiff_const.prodMk contDiff_id)) (compactSpacetime_slice_compact f hs t) n hn w
  rw [planeJetOrder_eq_stored hn] at ha
  change (compactSpacetimeHilbertHk K f hf hs t).val ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩
    =ᵐ[volume] orderedDerivative w (fun x => f (t, x)) at ha
  apply (ha.filter_mono (ae_mono Measure.restrict_le_self)).trans
  exact Filter.Eventually.of_forall (fun x => (spacetimeOrderedDerivative_slice f hf w t x).symm)

theorem compactSpacetimeHilbertHk_strong_time (K : ℕ) (f : ℝ × Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (a b : ℝ) :
    CycleEvolution.StrongTimeRegularity a b (compactSpacetimeHilbertHk K f hf hs)
      (compactSpacetimeHilbertHk K (fun p => fderiv ℝ f p (1, 0))
        ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const)
        (hs.fderiv_apply ℝ (1, 0))) := by
  let D := fun p => fderiv ℝ f p (1, 0)
  have hD : ContDiff ℝ (⊤ : ℕ∞) D :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hsD : HasCompactSupport D := hs.fderiv_apply ℝ (1, 0)
  apply planeHk_strong_time_of_jets
  rintro ⟨⟨n, hn⟩, w⟩
  let G := spacetimeOrderedDerivative f w
  have hG := spacetimeOrderedDerivative_smooth f hf w
  have hsG := spacetimeOrderedDerivative_compact f hs w
  apply compactHilbert_native_strong_time G (hG.of_le (by simp)) hsG a b
  · exact fun t => compactSpacetimeHilbertHk_jet_ae K f hf hs t n (Nat.le_of_lt_succ hn) w
  · intro t
    apply (compactSpacetimeHilbertHk_jet_ae K D hD hsD t n (Nat.le_of_lt_succ hn) w).trans
    exact Filter.Eventually.of_forall (fun x => congrFun
      (spacetimeOrderedDerivative_time_commute f hf w) (t, x))

theorem compactSpacetimeHilbertHk_continuous (K : ℕ) (f : ℝ × Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) :
    Continuous (compactSpacetimeHilbertHk K f hf hs) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc := (compactSpacetimeHilbertHk_strong_time K f hf hs (t - 1) (t + 1)).ac.continuousOn
  have hab : t - 1 ≤ t + 1 := by linarith
  rw [uIcc_of_le hab] at hc
  exact hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The molecular envelope bounds the actual dimensional diagonal sample before chart transport. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem pointwise_molecular_physical_sample_jet_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p) :
    ∀ t : ℝ, (∀ Y : Vec 2, (t, Y) ∈ dom p c) → ∀ j, j ≤ K v → ∀ x,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun y => F.dimFlux ν e E p c v u γ d I t y (e⁻¹ • y)) x‖ ≤
        |ν * e ^ (d - 2)| * ((4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2 *
          molecularRealPrice ν ρ (K v) (d - 2)
            (pointwiseMolecularJet ρ e (K v) 0 (fun z : F.Index => dom z.1 z.2)
              (fun z => F.dimFlux ν e E z.1 z.2 v u γ d I)) /
                derivativeReserveFactor (ρ / e) (K v) (d - 2)) := by
  intro t hdom j hj x
  have ht := familyPointwiseMolecular_sample_budget F π hπ K Kmax hK dom ν e E ρ
    hν he hE hρ C J b henv v u γ hγ d hd I p c t
  let f := fun y : Vec 2 => F.flux p c v u γ d I t ((e / E) • y) y
  have hf : ContDiff ℝ (K v : ℕ) f := by
    have hh : ContDiff ℝ (K v : ℕ) (Function.uncurry (F.flux p c v u γ d I t)) :=
      (molecular_joint_contDiff F dom E hE.ne' (fun v => K v + J)
      henv.1 p c t hdom v u γ d I).of_le
        (by exact_mod_cast Nat.le_add_right (K v) J)
    exact hh.comp ((contDiff_id.const_smul (e / E)).prodMk contDiff_id)
  have hb (z : Vec 2) := ht hdom (0 : Vec 2) (0 : Vec 2) j hj z
  simp only [zero_add, add_zero] at hb
  have hm := normalized_physical_sample_jet_le f j
    (hf.of_le (by exact_mod_cast hj)) (ν * e ^ (d - 2)) e ρ _ he hb x
  have hee : (e / E) * e⁻¹ = E⁻¹ := by field_simp
  have heq : (fun y => F.dimFlux ν e E p c v u γ d I t y (e⁻¹ • y)) =
      (fun y => (ν * e ^ (d - 2)) • f (e⁻¹ • y)) := by
    funext y
    simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux, f, smul_smul, hee]
  rw [heq]
  exact hm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A profile-only constant controls factorial localization for every Hilbert fiber. -/

def patchFactorialEnergyBudget {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (K : ℕ) (L : ℝ) : ℝ :=
  patchLeibnizEnergyCount K *
    (9 * (patchProfileDerivativeBudget hζ K * (2 : ℝ) ^ K) ^ 2 * L ^ (2 * K))

theorem patchFactorialEnergyBudget_nonneg {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (K : ℕ) (L : ℝ) : 0 ≤ patchFactorialEnergyBudget hζ K L := by
  unfold patchFactorialEnergyBudget
  have hp : 0 ≤ L ^ (2 * K) := by rw [Nat.mul_comm, pow_mul]; positivity
  exact mul_nonneg (patchLeibnizEnergyCount_nonneg K)
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hp)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem spatialPatchLocalization_uniform_factorial_energy {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) {K : ℕ} (f : TorusHk K E)
    (ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : 1 ≤ L) (hmesh : ρ * (N : ℝ) ≤ L) :
    (∑ p : Fin 2 → Fin N, factorialNormSq ρ
      (spatialPatchLocalization hζ N hN (fun i => (p i : ℤ)) K f).val) ≤
      patchFactorialEnergyBudget hζ K L * factorialNormSq ρ f.val := by
  exact spatialPatchLocalization_factorialNormSq_sum hζ N hN f ρ L
    (patchProfileDerivativeBudget hζ K * (2 : ℝ) ^ K) hρ hL hmesh
    (mul_nonneg (patchProfileDerivativeBudget_nonneg hζ K) (by positivity))
    (fun l hl k x => spatialPatchCoefficient_profile_budget hζ K N l hl k x)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Uniform finite-reserve constants preserve every positive native-order and word summand. -/

theorem uniform_native_transport_assembly_jet_bound
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (N Dγ Dmax Kmax n r : ℕ)
    (hD : Dγ ≤ Dmax) (hkn : n ≤ Kmax) (C E ρ : ℝ) (hC : 1 ≤ C) (hE : 0 < E)
    (hρ : 0 ≤ ρ) (hρE : ρ ≤ E) (hn : n + Dγ ≤ N)
    (hKC : ∀ a b j, j ≤ N → ∀ x,
      E ^ j * ‖iteratedFDeriv ℝ j (fun y => K y a b) x‖ ≤ C)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 → Vec 2)
    (hB : ∀ d I i, ContDiff ℝ (n : ℕ) (fun x => B d I x i))
    (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ)
    (hMB : ∀ d I, 0 ≤ MB d I)
    (hBj : ∀ d ∈ Finset.Icc (r + 1) Dγ, ∀ I i j, j ≤ n → ∀ y,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => B d I x i) y‖ ≤ MB d I)
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Cmap : U →L[ℝ] V) (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => nativeArrayAssembly r Cmap
      (fun a A => transportedCoeff K Dγ (fun d I => B d I y) r A y a)) x‖ ≤
      ∑ _a : Fin 2, ∑ _A : DerivativeWord2 r, ‖Cmap‖ *
        (∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
          (((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) ^ 2 * C *
            (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ Dmax) *
              (MB d I * E⁻¹ ^ (d - 1 - r))) := by
  have hh := native_transport_assembly_jet_bound K hK N Dγ n r C E ρ
    (zero_le_one.trans hC) hE hρ hρE hn hKC B hB MB hBj Cmap x
  apply hh.trans
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro A _
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro I _
  apply Finset.sum_le_sum
  intro i _
  have hc := finite_native_transport_constant N Kmax Dmax n d hkn
    ((Finset.mem_Icc.mp hd).2.trans hD) C hC
  have hterm := mul_le_mul_of_nonneg_right hc
    (mul_nonneg (hMB d I) (pow_nonneg (inv_nonneg.mpr hE.le) (d - 1 - r)))
  convert hterm using 1; ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVenhance.Infra.Section5 AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Measurability and the preparation certificate imply joint measurability of the physical coefficients. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem constituentPhysical_joint_measurable
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) E n)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u) (d : ℕ) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 =>
      constituentPhysical F ν e E actual v u γ d z.1 z.2) := by
  let b := fun p (z : Set.Icc tS tZ × Vec 2) k (A : DerivativeWord2 (d - 1)) =>
    transportedCoeff (chartInvJacobian ⇑((F.piece p).material z.1).symm)
      (F.identity v u γ).maxOrder
      (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I z.1
        (((F.piece p).material z.1).symm z.2)
        (e⁻¹ • ((F.piece p).material z.1).symm z.2)) (d - 1) A z.2 k
  change Measurable (fun z : Set.Icc tS tZ × Vec 2 => ∑ᶠ p,
    F.weight p z.1 • (nativeArrayAssembly (d - 1) (F.identity v u γ).map (b p z)))
  apply measurable_piece_finsum_onWindow F tS tZ
  · intro p
    have hm := nativeArrayAssembly_measurable (d - 1) (F.identity v u γ).map
      (fun z k A => F.weight p z.1 * b p z k A)
      (fun k A => weighted_piece_array_joint_measurable F hc ν e E n hs hmeas hwmeas
        p (actual p) v u γ (d - 1) A k)
    convert hm using 1
    funext z
    exact ((nativeArrayAssembly (d - 1) (F.identity v u γ).map).map_smul
      (F.weight p z.1) (b p z)).symm
  · intro p z hout
    rw [F.weight_zero p z.1 hout]
    exact zero_smul ℝ (nativeArrayAssembly (d - 1) (F.identity v u γ).map (b p z))

theorem physicalCoefficient_joint_measurable
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) E n)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (actual : ∀ p, Ctx p) (v u : ι) (d : ℕ) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 =>
      physicalCoefficient F ν e E actual v u d z.1 z.2) := by
  unfold physicalCoefficient
  exact Finset.measurable_sum _ (fun γ _ =>
    constituentPhysical_joint_measurable F hc ν e E n hs hmeas hwmeas actual v u γ d)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Exact window traces and almost everywhere energy representatives determine the same native weak curve. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakCurve_congr {a b : ℝ}
    {u v : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice state dual rhs : ℝ → PlaneHk univ 1 E}
    (h : PlaneWeakHilbertCurve a b u slice dual)
    (hu : EqOn v u (Icc a b))
    (hs : state =ᵐ[volume.restrict (Icc a b)] slice)
    (hd : rhs =ᵐ[volume.restrict (Icc a b)] dual) :
    PlaneWeakHilbertCurve a b v state rhs := by
  refine ⟨h.trace.congr hu, (memLp_congr_ae hs).mpr h.state, (memLp_congr_ae hd).mpr h.dual_mem, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Icc, h.agrees, hs] with t ht ha he
    rw [hu ht, he, ha]
  · intro s hs' t ht hst z
    rw [hu ht, hu hs', h.increment s hs' t ht hst z]
    apply intervalIntegral.integral_congr_ae_restrict
    have he := ae_restrict_of_ae_restrict_of_subset
      (show uIoc s t ⊆ Icc a b by
        rw [uIoc_of_le hst]
        intro r hr
        exact ⟨hs'.1.trans hr.1.le, hr.2.trans ht.2⟩) hd
    filter_upwards [he] with r hr
    rw [hr]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Weak Hilbert curves depend only on the derivative on their physical time window. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- A weak Hilbert curve depends only on its three curves on the solution window. -/
theorem planeWeakHilbertCurve_congr_on {a b : ℝ}
    {u u' : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice slice' dual dual' : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve a b u slice dual)
    (hu : ∀ t ∈ Icc a b, u t = u' t)
    (hs : ∀ t ∈ Icc a b, slice t = slice' t)
    (hd : ∀ t ∈ Icc a b, dual t = dual' t) :
    PlaneWeakHilbertCurve a b u' slice' dual' := by
  have hsae : slice =ᵐ[volume.restrict (Icc a b)] slice' := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hs t ht
  have hdae : dual =ᵐ[volume.restrict (Icc a b)] dual' := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hd t ht
  refine ⟨h.trace.congr (fun t ht => (hu t ht).symm), MemLp.ae_eq hsae h.state, MemLp.ae_eq hdae h.dual_mem, ?_, ?_⟩
  · filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hmem
    rw [← hu t hmem, ← hs t hmem]
    exact ht
  · intro s hs' t ht hst z
    rw [← hu t ht, ← hu s hs']
    refine (h.increment s hs' t ht hst z).trans ?_
    apply intervalIntegral.integral_congr
    intro r hr
    have hrab : r ∈ Icc a b :=
      Icc_subset_Icc hs'.1 ht.2 (by simpa only [uIcc_of_le hst] using hr)
    change inner ℝ (dual r) z = inner ℝ (dual' r) z
    rw [hd r hrab]

end AVRegularity.CycleJointProofs
end
end
