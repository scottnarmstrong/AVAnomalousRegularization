-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVenhance.Infra.Section5.AnalyticBridge.Sobolev
import AVRegularity.Statements.Definitions.EuclidBall
public import AVRegularity.Sobolev.FactorialShift
public import AVenhance.Infra.Heat.WeakBridge
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.UniformSpace.Ascoli

section
@[expose] public section
noncomputable section
open Set Filter Topology UniformSpace
open scoped Uniformity
namespace AVRegularity.External

/-! Local uniform compactness from the compact-open Arzelà--Ascoli theorem. -/

/-- Arzelà--Ascoli on a weakly locally compact σ-compact metric domain. The input maps are
continuous and uniformly bounded and equicontinuous on each compact set. Mathlib's compact-open
Ascoli theorem gives a compact closure; σ-compactness makes the compact-open function space
sequential, and compact-open convergence is locally uniform convergence. -/
theorem arzelaAscoliDiagonal
    {X : Type*} [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] (F : ℕ → C(X, ℝ))
    (hbounded : ∀ K : Set X, IsCompact K →
      ∃ M : ℝ, ∀ n : ℕ, ∀ x, x ∈ K → ‖F n x‖ ≤ M)
    (hequicontinuous : ∀ K : Set X, IsCompact K →
      EquicontinuousOn (fun n x => F n x) K) :
    ∃ (φ : ℕ → ℕ) (f : C(X, ℝ)), StrictMono φ ∧
      TendstoLocallyUniformly (fun n x => F (φ n) x) f atTop := by
  classical
  let eval (f : C(X, ℝ)) : X → ℝ := fun x => f x
  have hclosed : IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set X | IsCompact K} ∘ eval) := by
    have hclosed' : IsClosedEmbedding
        (ContinuousMap.toUniformOnFunIsCompact (α := X) (β := ℝ)) := by
      refine ⟨(ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
        (α := X) (β := ℝ)).isEmbedding, ?_⟩
      rw [ContinuousMap.range_toUniformOnFunIsCompact]
      exact UniformOnFun.isClosed_setOfPred_continuous
        (CompactlyCoherentSpace.isCoherentWith (X := X))
    have heq : UniformOnFun.ofFun {K : Set X | IsCompact K} ∘ eval =
        ContinuousMap.toUniformOnFunIsCompact := by
      funext f
      rfl
    rw [heq]
    exact hclosed'
  have hfamily : IsCompact (closure (Set.range F)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖 := {K : Set X | IsCompact K})
      (𝔖_compact := by
        intro K hK
        exact hK)
      (F_clemb := hclosed)
    · intro K hK
      let chooseIndex : Set.range F → ℕ := fun f => Classical.choose f.property
      have hcomp := (hequicontinuous K hK).comp chooseIndex
      have hEq : (fun f : Set.range F => fun x => F (chooseIndex f) x) =
          fun f => eval f.1 := by
        funext f x
        exact congrArg (fun g : C(X, ℝ) => g x) (Classical.choose_spec f.property)
      change EquicontinuousOn (fun f : Set.range F => fun x => eval f.1 x) K
      rw [← hEq]
      exact hcomp
    · intro K hK x hx
      obtain ⟨M, hM⟩ := hbounded {x} isCompact_singleton
      refine ⟨Metric.closedBall (0 : ℝ) (max M 0), isCompact_closedBall _ _, ?_⟩
      rintro f ⟨n, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hM n x (by simp)).trans (le_max_left M 0)
  obtain ⟨f, hfmem, φ, hφ, hlim⟩ := hfamily.tendsto_subseq fun n =>
    subset_closure ⟨n, rfl⟩
  refine ⟨φ, f, hφ, ?_⟩
  exact (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim)

end AVRegularity.External
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.External

/-! Fourier spectral gaps for smooth and weak torus functions in a centered Bloch zone. -/

private theorem smoothFourierCoeff_add
    {f g : Vec 2 → ℂ} (hf : Continuous f) (hg : Continuous g)
    (k : Fin 2 → ℤ) :
    AVenhance.Infra.Torus.smoothFourierCoeff (fun x => f x + g x) k =
      AVenhance.Infra.Torus.smoothFourierCoeff f k +
        AVenhance.Infra.Torus.smoothFourierCoeff g k := by
  unfold AVenhance.Infra.Torus.smoothFourierCoeff
  change (∫ x, AVenhance.Infra.Torus.torusCharacter k x * (f x + g x)
      ∂(volume.restrict (AVenhance.Infra.Torus.unitCell 2))) = _
  rw [show (fun x => AVenhance.Infra.Torus.torusCharacter k x * (f x + g x)) =
      (fun x => AVenhance.Infra.Torus.torusCharacter k x * f x) +
        (fun x => AVenhance.Infra.Torus.torusCharacter k x * g x) by
    funext x
    change AVenhance.Infra.Torus.torusCharacter k x * (f x + g x) =
      AVenhance.Infra.Torus.torusCharacter k x * f x +
        AVenhance.Infra.Torus.torusCharacter k x * g x
    ring]
  exact integral_add
    (AVenhance.Infra.Torus.Calculus.continuous_integrableOn_unitCell
      ((AVenhance.Infra.Torus.torusCharacter_contDiff k).continuous.mul hf))
    (AVenhance.Infra.Torus.Calculus.continuous_integrableOn_unitCell
      ((AVenhance.Infra.Torus.torusCharacter_contDiff k).continuous.mul hg))

private theorem smoothFourierCoeff_const_mul
    {f : Vec 2 → ℂ} (c : ℂ) (k : Fin 2 → ℤ) :
    AVenhance.Infra.Torus.smoothFourierCoeff (fun x => c * f x) k =
      c * AVenhance.Infra.Torus.smoothFourierCoeff f k := by
  unfold AVenhance.Infra.Torus.smoothFourierCoeff
  change (∫ x, AVenhance.Infra.Torus.torusCharacter k x * (c * f x)
      ∂(volume.restrict (AVenhance.Infra.Torus.unitCell 2))) = _
  rw [show (fun x => AVenhance.Infra.Torus.torusCharacter k x * (c * f x)) =
      (fun x => c * (AVenhance.Infra.Torus.torusCharacter k x * f x)) by
    funext x
    ring]
  exact integral_const_mul c _

end AVRegularity.External
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open Homogenization
namespace AVRegularity.External

/-! Weighted interpolation on the unit torus Fourier coefficient carrier. -/

/-- The squared frequency of an integer mode on the two dimensional torus. -/
def torusFrequencySq (k : Fin 2 → ℤ) : ℝ :=
  ∑ i : Fin 2, (k i : ℝ) ^ 2

/-- General weighted Fourier Cauchy--Schwarz readout. Any positive frequency weight with
summable reciprocal converts its weighted coefficient `L²` energy into a uniform bound. This
form isolates the analytic step used by scaled Sobolev readouts from the choice of jet norm. -/
theorem torusFourierWeightedSupReadout
    {f : Vec 2 → ℂ} (hf : Continuous f)
    (hper : AVenhance.Infra.Torus.IsZdPeriodic f)
    (w : (Fin 2 → ℤ) → ℝ) (hw : ∀ k, 0 < w k)
    (hwinv : Summable (fun k => (w k)⁻¹)) {S : ℝ}
    (hsum : HasSum
      (fun k : Fin 2 → ℤ => w k *
        ‖AVenhance.Infra.Torus.smoothFourierCoeff f k‖ ^ 2) S)
    (x : Vec 2) :
    ‖f x‖ ≤ Real.sqrt (∑' k, (w k)⁻¹) * Real.sqrt S := by
  have hfinite (s : Finset (Fin 2 → ℤ)) :
      ∑ k ∈ s, ‖AVenhance.Infra.Torus.smoothFourierCoeff f k‖ ≤
        Real.sqrt (∑' k, (w k)⁻¹) * Real.sqrt S := by
    have hCS := Real.sum_mul_le_sqrt_mul_sqrt s
      (fun k => ‖AVenhance.Infra.Torus.smoothFourierCoeff f k‖ * Real.sqrt (w k))
      (fun k => (Real.sqrt (w k))⁻¹)
    have hterm : ∀ k,
        (‖AVenhance.Infra.Torus.smoothFourierCoeff f k‖ * Real.sqrt (w k)) *
            (Real.sqrt (w k))⁻¹ =
          ‖AVenhance.Infra.Torus.smoothFourierCoeff f k‖ := by
      intro k
      have hne : Real.sqrt (w k) ≠ 0 := (Real.sqrt_pos.mpr (hw k)).ne'
      field_simp
    have hsq1 : ∀ k,
        (‖AVenhance.Infra.Torus.smoothFourierCoeff f k‖ * Real.sqrt (w k)) ^ 2 =
          w k * ‖AVenhance.Infra.Torus.smoothFourierCoeff f k‖ ^ 2 := by
      intro k
      rw [mul_pow, Real.sq_sqrt (hw k).le]
      ring
    have hsq2 : ∀ k, ((Real.sqrt (w k))⁻¹) ^ 2 = (w k)⁻¹ := by
      intro k
      rw [inv_pow, Real.sq_sqrt (hw k).le]
    simp only [hterm, hsq1, hsq2] at hCS
    have h1 : ∑ k ∈ s, w k *
        ‖AVenhance.Infra.Torus.smoothFourierCoeff f k‖ ^ 2 ≤ S :=
      sum_le_hasSum s (fun k _ => mul_nonneg (hw k).le (sq_nonneg _)) hsum
    have h2 : ∑ k ∈ s, (w k)⁻¹ ≤ ∑' k, (w k)⁻¹ :=
      hwinv.sum_le_tsum s (fun k _ => (inv_pos.mpr (hw k)).le)
    calc
      ∑ k ∈ s, ‖AVenhance.Infra.Torus.smoothFourierCoeff f k‖ ≤
          Real.sqrt (∑ k ∈ s, (w k)⁻¹) *
            Real.sqrt (∑ k ∈ s, w k *
              ‖AVenhance.Infra.Torus.smoothFourierCoeff f k‖ ^ 2) := by
        simpa only [mul_comm] using hCS
      _ ≤ Real.sqrt (∑' k, (w k)⁻¹) * Real.sqrt S := by
        exact mul_le_mul (Real.sqrt_le_sqrt h2) (Real.sqrt_le_sqrt h1)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsumm : Summable (fun k : Fin 2 → ℤ =>
      ‖AVenhance.Infra.Torus.smoothFourierCoeff f k‖) :=
    summable_of_sum_le (fun k => norm_nonneg _) hfinite
  let g : C(UnitAddTorus (Fin 2), ℂ) :=
    ⟨AVenhance.Infra.Torus.periodicToTorus f,
      AVenhance.Infra.Section5.AnalyticBridge.Sobolev.continuous_periodicToTorus hf hper⟩
  have hcoeff (k : Fin 2 → ℤ) : UnitAddTorus.mFourierCoeff g k =
      AVenhance.Infra.Torus.smoothFourierCoeff f k :=
    AVenhance.Infra.Section5.AnalyticBridge.Sobolev.mFourierCoeff_periodicToTorus f k
  have hgsumm : Summable (UnitAddTorus.mFourierCoeff g) := by
    have hEq : UnitAddTorus.mFourierCoeff g =
        AVenhance.Infra.Torus.smoothFourierCoeff f := funext hcoeff
    rw [hEq]
    exact hsumm.of_norm
  have hseries := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hgsumm
    (AVenhance.Infra.Torus.toUnitTorus 2 x)
  have hgx : g (AVenhance.Infra.Torus.toUnitTorus 2 x) = f x := by
    exact congrFun (AVenhance.Infra.Torus.fromUnitTorus_periodicToTorus hper) x
  rw [hgx] at hseries
  have hpoint : ‖f x‖ ≤ ∑' k,
      ‖AVenhance.Infra.Torus.smoothFourierCoeff f k‖ := by
    refine hseries.norm_le_of_bounded hsumm.hasSum (fun k => ?_)
    rw [hcoeff, norm_smul]
    have hm : ‖UnitAddTorus.mFourier k (AVenhance.Infra.Torus.toUnitTorus 2 x)‖ ≤ 1 := by
      calc
        ‖UnitAddTorus.mFourier k (AVenhance.Infra.Torus.toUnitTorus 2 x)‖ ≤
            ‖UnitAddTorus.mFourier k‖ := ContinuousMap.norm_coe_le_norm _ _
        _ = 1 := UnitAddTorus.mFourier_norm
    calc
      ‖AVenhance.Infra.Torus.smoothFourierCoeff f k‖ *
          ‖UnitAddTorus.mFourier k (AVenhance.Infra.Torus.toUnitTorus 2 x)‖ ≤
          ‖AVenhance.Infra.Torus.smoothFourierCoeff f k‖ * 1 :=
        mul_le_mul_of_nonneg_left hm (norm_nonneg _)
      _ = ‖AVenhance.Infra.Torus.smoothFourierCoeff f k‖ := mul_one _
  exact hpoint.trans (hasSum_le_of_sum_le hsumm.hasSum hfinite)

end AVRegularity.External
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped FourierTransform
namespace AVRegularity.External

/-! Fourier and Poincare wrappers for the unit two dimensional torus and the Euclidean plane. -/

/-- Parseval for the upstream torus `L²` carrier, with the coefficients and cell integral exposed.
This is `AVenhance.Infra.Torus.hasSum_sq_periodicL2FourierCoeff`. -/
theorem torusL2Parseval {d : ℕ} (f : AVenhance.Infra.Torus.TorusL2 d) :
    HasSum
      (fun k : Fin d → ℤ =>
        ‖AVenhance.Infra.Torus.periodicL2FourierCoeff f k‖ ^ 2)
      (∫ x in AVenhance.Infra.Torus.unitCell d,
        ‖AVenhance.Infra.Torus.periodicL2Representative f x‖ ^ 2) :=
  AVenhance.Infra.Torus.hasSum_sq_periodicL2FourierCoeff f

/-- Bounded pointwise multiplication acts on the two-sided `ℓ²` Fourier coefficient carrier. -/
theorem exists_lp_boundedFourierMultiplier
    {ι : Type*} (m : ι → ℂ) (a : lp (fun _ : ι => ℂ) 2) (M : ℝ)
    (hM : 0 ≤ M) (hm : ∀ i, ‖m i‖ ≤ M) :
    ∃ b : lp (fun _ : ι => ℂ) 2,
      (∀ i, b i = m i * a i) ∧ ‖b‖ ≤ M * ‖a‖ := by
  let c : lp (fun _ : ι => ℂ) 2 := ⟨fun i => (M : ℂ) * a i,
    (lp.memℓp a).const_mul (M : ℂ)⟩
  have hbmem : Memℓp (fun i => ‖c i‖) 2 := lp.memℓp c |>.norm
  have houtmem : Memℓp (fun i => m i * a i) 2 := hbmem.mono fun i => by
    dsimp [c]
    rw [norm_mul]
    have hci : ‖(M : ℂ) * a i‖ = M * ‖a i‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]
    rw [hci]
    exact mul_le_mul_of_nonneg_right (hm i) (norm_nonneg _)
  let b : lp (fun _ : ι => ℂ) 2 := ⟨fun i => m i * a i, houtmem⟩
  have hc : c = (M : ℂ) • a := by
    apply Subtype.ext
    funext i
    rfl
  have hpoint : ∀ i, ‖b i‖ ≤ ‖c i‖ := by
    intro i
    change ‖m i * a i‖ ≤ ‖(M : ℂ) * a i‖
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]
    exact mul_le_mul_of_nonneg_right (hm i) (norm_nonneg _)
  refine ⟨b, fun _ => rfl, ?_⟩
  have hne : (2 : ENNReal) ≠ 0 := by norm_num
  calc
    ‖b‖ ≤ ‖c‖ := lp.norm_mono hne hpoint
    _ = M * ‖a‖ := by
      rw [hc, norm_smul]
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]

/-- Every bounded multiplier on the unit two dimensional torus acts boundedly on `L²`.
The operator is defined by conjugating coefficientwise multiplication with the torus Fourier
Hilbert basis. -/
theorem exists_torusL2FourierMultiplier (m : (Fin 2 → ℤ) → ℂ)
    (f : AVenhance.Infra.Torus.TorusL2 2) (M : ℝ)
    (hM : 0 ≤ M) (hm : ∀ k, ‖m k‖ ≤ M) :
    ∃ g : AVenhance.Infra.Torus.TorusL2 2,
      (∀ k, UnitAddTorus.mFourierCoeff g k =
        m k * UnitAddTorus.mFourierCoeff f k) ∧ ‖g‖ ≤ M * ‖f‖ := by
  let B := UnitAddTorus.mFourierBasis (d := Fin 2)
  obtain ⟨a, ha, hnorm⟩ := exists_lp_boundedFourierMultiplier m (B.repr f) M hM hm
  refine ⟨B.repr.symm a, ?_, ?_⟩
  · intro k
    rw [← UnitAddTorus.mFourierBasis_repr (B.repr.symm a) k]
    calc
      B.repr (B.repr.symm a) k = a k :=
        congrArg (fun x : lp (fun _ : Fin 2 → ℤ => ℂ) 2 => x k)
          (B.repr.apply_symm_apply a)
      _ = m k * B.repr f k := ha k
      _ = m k * UnitAddTorus.mFourierCoeff f k := by
        rw [UnitAddTorus.mFourierBasis_repr]
  · calc
      ‖B.repr.symm a‖ = ‖a‖ := B.repr.symm.norm_map a
      _ ≤ M * ‖B.repr f‖ := hnorm
      _ = M * ‖f‖ := by rw [B.repr.norm_map]

end AVRegularity.External
end
end

section
@[expose] public section
noncomputable section
open Homogenization Filter Set Topology Metric
open scoped ENNReal Topology
namespace AVRegularity.External

/-! Lebesgue differentiation on project discs and continuity of translations in `L¹`. -/

private theorem euclidBall_subset_closedBall (x : Vec 2) {r : ℝ} (hr : 0 < r) :
    euclidBall x r ⊆ Metric.closedBall x r := by
  intro y hy
  have hcoord (i : Fin 2) : |y i - x i| ≤ r := by
    have hsq := Homogenization.sq_apply_le_vecNormSq (y - x) i
    have hsq' : |y i - x i| ^ 2 ≤ r ^ 2 := by
      rw [sq_abs]
      exact (le_of_lt (lt_of_le_of_lt hsq hy))
    exact le_of_sq_le_sq hsq' hr.le
  have hdist : dist y x ≤ r := (dist_pi_le_iff hr.le).2 fun i => by
    simpa [dist_eq_norm, Real.norm_eq_abs] using hcoord i
  exact Metric.mem_closedBall.mpr hdist

end AVRegularity.External
end
end
end

section
@[expose] public section
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open AVenhance.Infra.Heat
namespace AVRegularity.External

/-! Fourier coefficient identities for ordered weak torus jets. -/

/-- The torus `L²` class of one component of a real ordered weak jet. -/
def torusJetComponentL2 {K : ℕ} (f : AVRegularity.Sobolev.TorusHk K ℝ)
    (a : AVRegularity.Sobolev.JetIndex2 K) : AVenhance.Infra.Torus.TorusL2 2 :=
  frozenCellToTorusL2 (f.toFunction.hasPeriodicWeakJet.2.1 a)

end AVRegularity.External
end
end

section
/-! Parseval identities for the value and ordered weak jets of the torus carrier. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization

local instance carrierParsevalMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance carrierParsevalIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance carrierParsevalProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVRegularity.External

/-- Parseval for an individual real weak-jet component, with its cell integral identified with
the squared norm of the corresponding `TorusHk` component. -/
theorem torusJetComponentParseval
    {K : ℕ} (f : AVRegularity.Sobolev.TorusHk K ℝ)
    (a : AVRegularity.Sobolev.JetIndex2 K) :
    HasSum
      (fun k : Fin 2 → ℤ =>
        ‖UnitAddTorus.mFourierCoeff (torusJetComponentL2 f a) k‖ ^ 2)
      (‖f.val a‖ ^ 2) := by
  let hmem := f.toFunction.hasPeriodicWeakJet.2.1 a
  let g := torusJetComponentL2 f a
  have hparse := torusL2Parseval g
  have htorus :
      (∫ y : UnitAddTorus (Fin 2), ‖g y‖ ^ 2) = ‖g‖ ^ 2 := by
    have h := AVenhance.Infra.Heat.WeakBridge.normSq_memLpToLp_eq_integral
      (fun y : UnitAddTorus (Fin 2) => g y) (Lp.memLp g)
    simpa using h.symm
  have hmeasure :
      (∫ x in AVenhance.Infra.Torus.unitCell 2,
        ‖AVenhance.Infra.Torus.periodicL2Representative g x‖ ^ 2) =
        ‖g‖ ^ 2 := by
    have hcell := AVenhance.Infra.Torus.integral_fromUnitTorus_eq_unitCellAt
      (fun y : UnitAddTorus (Fin 2) => ‖g y‖ ^ 2) (fun _ => 0)
    have hcell' :
        (∫ y : UnitAddTorus (Fin 2), ‖g y‖ ^ 2) =
          ∫ x in AVenhance.Infra.Torus.unitCell 2,
            AVenhance.Infra.Torus.fromUnitTorus (fun y => ‖g y‖ ^ 2) x := by
      simpa [AVenhance.Infra.Torus.unitCell, AVenhance.Infra.Torus.unitCellAt] using hcell
    have hpoint :
        (∫ x in AVenhance.Infra.Torus.unitCell 2,
          ‖AVenhance.Infra.Torus.periodicL2Representative g x‖ ^ 2) =
        ∫ x in AVenhance.Infra.Torus.unitCell 2,
          AVenhance.Infra.Torus.fromUnitTorus (fun y => ‖g y‖ ^ 2) x := by
      apply integral_congr_ae
      filter_upwards with x
      rfl
    rw [← htorus]
    calc
      ∫ x in AVenhance.Infra.Torus.unitCell 2,
          ‖AVenhance.Infra.Torus.periodicL2Representative g x‖ ^ 2 =
        ∫ y : UnitAddTorus (Fin 2), ‖g y‖ ^ 2 := hpoint.trans hcell'.symm
      _ = _ := rfl
  have hnorm : ‖g‖ ^ 2 = ‖f.val a‖ ^ 2 := by
    calc
      ‖g‖ ^ 2 = AVenhance.l2NormSq
          (AVRegularity.Sobolev.periodicJetRepresentative f.val a) := by
        change ‖AVenhance.Infra.Heat.frozenCellToTorusL2 hmem‖ ^ 2 = _
        simpa [AVRegularity.Sobolev.TorusHk.toFunction] using
          (AVenhance.Infra.Heat.normSq_frozenCellToTorusL2_eq hmem)
      _ = ‖f.val a‖ ^ 2 := by
        have hae := AVRegularity.Sobolev.periodicJetRepresentative_ae f.val a
        have hLp : ‖f.val a‖ ^ 2 =
            ∫ x, ‖(f.val a : Vec 2 → ℝ) x‖ ^ 2
              ∂(volume.restrict AVenhance.unitCube) := by
          calc
            ‖f.val a‖ ^ 2 = inner ℝ (f.val a) (f.val a) :=
              (real_inner_self_eq_norm_sq _).symm
            _ = ∫ x, inner ℝ ((f.val a : Vec 2 → ℝ) x)
                ((f.val a : Vec 2 → ℝ) x)
                  ∂(volume.restrict AVenhance.unitCube) := MeasureTheory.L2.inner_def _ _
            _ = _ := by
              apply integral_congr_ae
              filter_upwards with x
              exact real_inner_self_eq_norm_sq _
        calc
          AVenhance.l2NormSq
              (AVRegularity.Sobolev.periodicJetRepresentative f.val a) =
              ∫ x, ‖(f.val a : Vec 2 → ℝ) x‖ ^ 2
                  ∂(volume.restrict AVenhance.unitCube) := by
            rw [AVenhance.l2NormSq]
            apply integral_congr_ae
            filter_upwards [hae] with x hx
            rw [hx, Real.norm_eq_abs, sq_abs]
          _ = ‖f.val a‖ ^ 2 := hLp.symm
  have hcell := hmeasure.trans hnorm
  rw [hcell] at hparse
  simpa only [AVenhance.Infra.Torus.periodicL2FourierCoeff] using hparse

/-- Parseval summed over every ordered weak-jet component, with the factorial weights of the
project carrier. This is the all-orders finite-carrier energy identity used by interpolation and
Fourier readout. -/
theorem torusJetFactorialParseval
    {K : ℕ} (f : AVRegularity.Sobolev.TorusHk K ℝ) (ρ : ℝ) :
    HasSum
      (fun k : Fin 2 → ℤ =>
        ∑ a : AVRegularity.Sobolev.JetIndex2 K,
          AVRegularity.Sobolev.factorialWeight ρ a.1.val *
            ‖UnitAddTorus.mFourierCoeff (torusJetComponentL2 f a) k‖ ^ 2)
      (AVRegularity.Sobolev.factorialNormSq ρ f.val) := by
  let F : AVRegularity.Sobolev.JetIndex2 K → (Fin 2 → ℤ) → ℝ := fun a k =>
    AVRegularity.Sobolev.factorialWeight ρ a.1.val *
      ‖UnitAddTorus.mFourierCoeff (torusJetComponentL2 f a) k‖ ^ 2
  let A : AVRegularity.Sobolev.JetIndex2 K → ℝ := fun a =>
    AVRegularity.Sobolev.factorialWeight ρ a.1.val * ‖f.val a‖ ^ 2
  have hsum :=
    AVenhance.Infra.Torus.FourierCalculus.hasSum_finset_sum Finset.univ
      F A (fun a _ => (torusJetComponentParseval f a).mul_left
        (AVRegularity.Sobolev.factorialWeight ρ a.1.val))
  have henergy :
      (∑ a : AVRegularity.Sobolev.JetIndex2 K,
        AVRegularity.Sobolev.factorialWeight ρ a.1.val * ‖f.val a‖ ^ 2) =
      AVRegularity.Sobolev.factorialNormSq ρ f.val := by
    simp only [AVRegularity.Sobolev.factorialNormSq,
      AVRegularity.Sobolev.derivativeNormSq,
      AVRegularity.Sobolev.factorialWeight]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j hj
    change Finset.univ.sum (fun y : AVRegularity.Sobolev.DerivativeWord2 j =>
        (ρ ^ (2 * j.val) / (j.val.factorial : ℝ) ^ 2) *
          ‖f.val ⟨j, y⟩‖ ^ 2) =
      (ρ ^ (2 * j.val) / (j.val.factorial : ℝ) ^ 2) *
        Finset.univ.sum (fun y : AVRegularity.Sobolev.DerivativeWord2 j =>
          ‖f.val ⟨j, y⟩‖ ^ 2)
    exact (Finset.mul_sum Finset.univ
      (fun y : AVRegularity.Sobolev.DerivativeWord2 j => ‖f.val ⟨j, y⟩‖ ^ 2)
      (ρ ^ (2 * j.val) / (j.val.factorial : ℝ) ^ 2)).symm
  rw [henergy] at hsum
  exact hsum

end AVRegularity.External
end
end
