-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVenhance.Infra.Section4.Amnr.StreamProfileJets
import AVRegularity.CycleWords.CellAffineHomeomorph
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
public import AVRegularity.Construction.ChainGeometry.Offset
public import AVRegularity.CycleJoint.ConstituentPhysicalOrderSupport
import AVRegularity.Construction.ChildInert.Center
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Fast derivative operator norms for the literal normalized cosine pulse. -/

theorem cosine_coordinate_derivative_norm_le (c ω : ℝ) (hω : 0 ≤ ω)
    (i : Fin 2) (n : ℕ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun y : Vec 2 => c * Real.cos (ω * y i)) x‖ ≤
      |c| * ω ^ n := by
  let P : Vec 2 →L[ℝ] ℝ := ω • ContinuousLinearMap.proj i
  let g := fun u : ℝ => c * Real.cos u
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by dsimp [g]; fun_prop
  have hP : ‖P‖ ≤ ω := by
    apply ContinuousLinearMap.opNorm_le_bound _ hω
    intro y
    change ‖ω * y i‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hω]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm y i) hω
  have hcos : ‖iteratedFDeriv ℝ n Real.cos (P x)‖ ≤ 1 := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
      Real.abs_iteratedDeriv_cos_le_one n (P x)
  have hgj : ‖iteratedFDeriv ℝ n g (P x)‖ ≤ |c| := by
    change ‖iteratedFDeriv ℝ n (fun u => c • Real.cos u) (P x)‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (by fun_prop), norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hcos (abs_nonneg c)).trans_eq (mul_one _)
  have hh := AVenhance.Infra.Section4.amnr_iteratedFDeriv_comp_linear_norm_le hg P n x
  change ‖iteratedFDeriv ℝ n (g ∘ P) x‖ ≤ _
  exact hh.trans (mul_le_mul hgj (pow_le_pow_left₀ (norm_nonneg P) hP n)
    (pow_nonneg (norm_nonneg P) n) (abs_nonneg c))

/-! The cosine operator bound. -/

theorem cosine_vector_derivative_norm_le (c ω : ℝ) (hω : 0 ≤ ω) (i j : Fin 2) (b : ℕ) (y : Vec 2) :
    ‖iteratedFDeriv ℝ b (fun x : Vec 2 => (c * Real.cos (ω * x i)) • basisVec j) y‖ ≤
      |c| * ω ^ b := by
  let P : Vec 2 →L[ℝ] ℝ := ω • ContinuousLinearMap.proj i
  let g := fun u : ℝ => (c * Real.cos u) • basisVec j
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by dsimp [g]; fun_prop
  have hP : ‖P‖ ≤ ω := by
    apply ContinuousLinearMap.opNorm_le_bound _ hω
    intro x
    change ‖ω * x i‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hω]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) hω
  have hcos : ‖iteratedFDeriv ℝ b Real.cos (P y)‖ ≤ 1 := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
      Real.abs_iteratedDeriv_cos_le_one b (P y)
  have hgj : ‖iteratedFDeriv ℝ b g (P y)‖ ≤ |c| := by
    have he : g = fun u : ℝ => c • (Real.cos u • basisVec j) := by
      funext u
      simp only [g, smul_smul]
    rw [he, iteratedFDeriv_const_smul_apply' (by fun_prop), norm_smul, Real.norm_eq_abs]
    rw [iteratedFDeriv_smul_const_apply (i := b) (x := P y) (v := basisVec j)
      ((Real.contDiff_cos : ContDiff ℝ (⊤ : ℕ∞) Real.cos).contDiffAt.of_le (by simp))]
    have hl := ContinuousLinearMap.norm_compContinuousMultilinearMap_le
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec j)) (iteratedFDeriv ℝ b Real.cos (P y))
    simp only [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_id,
      show ‖basisVec j‖ = 1 by simp [basisVec, Pi.norm_single], mul_one, one_mul] at hl
    exact (mul_le_mul_of_nonneg_left (hl.trans hcos) (abs_nonneg c)).trans_eq (mul_one _)
  have hc := AVenhance.Infra.Section4.amnr_iteratedFDeriv_comp_linear_norm_le hg P b y
  have hbound : ‖iteratedFDeriv ℝ b (g ∘ P) y‖ ≤ |c| * ω ^ b :=
    hc.trans (mul_le_mul hgj (pow_le_pow_left₀ (norm_nonneg P) hP b)
      (pow_nonneg (norm_nonneg P) b) (abs_nonneg c))
  exact hbound

/-! The weak-entry derivative budget includes the actual uniform drift bound. -/

theorem drift_value_bound (l : ℕ) (v : ℝ → Vec 2 → Vec 2) (Cv : ℝ)
    (hb : ∀ t (j : ℕ), j ≤ l + 1 → ∀ z, ‖iteratedFDeriv ℝ j (v t) z‖ ≤ Cv)
    (t : ℝ) (z : Vec 2) : ‖v t z‖ ≤ Cv := by
  simpa only [norm_iteratedFDeriv_zero] using hb t 0 (by omega) z

theorem drift_budget_nonneg (l : ℕ) (v : ℝ → Vec 2 → Vec 2) (Cv : ℝ)
    (hb : ∀ t (j : ℕ), j ≤ l + 1 → ∀ z, ‖iteratedFDeriv ℝ j (v t) z‖ ≤ Cv) :
    0 ≤ Cv := (norm_nonneg (v 0 0)).trans (drift_value_bound l v Cv hb 0 0)

theorem scaled_drift_square_bound (l : ℕ) (v : ℝ → Vec 2 → Vec 2) (Cv Pe : ℝ)
    (hb : ∀ t (j : ℕ), j ≤ l + 1 → ∀ z, ‖iteratedFDeriv ℝ j (v t) z‖ ≤ Cv)
    (t : ℝ) (z : Vec 2) : ∑ i, (Pe • v t z) i ^ 2 ≤ (2 * Pe * Cv) ^ 2 := by
  have hCv := drift_budget_nonneg l v Cv hb
  have h (i : Fin 2) : |v t z i| ≤ Cv := by
    exact (le_trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (v t z) i)
      (drift_value_bound l v Cv hb t z))
  have h0 := (sq_le_sq₀ (abs_nonneg _) hCv).mpr (h 0)
  have h1 := (sq_le_sq₀ (abs_nonneg _) hCv).mpr (h 1)
  simp only [sq_abs] at h0 h1
  have he := mul_le_mul_of_nonneg_left (add_le_add h0 h1) (sq_nonneg Pe)
  simp only [Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
  nlinarith only [he, mul_nonneg (sq_nonneg Pe) (sq_nonneg Cv)]

/-! Smoothness of the two flow compositions used to recenter a child. -/

theorem jointFlowRecenterCenter_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (flow : E → ℝ → Vec 2 → ℝ → Vec 2) (center child offset : E → Vec 2)
    (a s : ℝ)
    (hf : ∀ u v, ContDiff ℝ (⊤ : ℕ∞)
      (fun Y : E × Vec 2 => flow Y.1 u Y.2 v))
    (hc : ContDiff ℝ (⊤ : ℕ∞) center)
    (hd : ContDiff ℝ (⊤ : ℕ∞) child)
    (hh : ContDiff ℝ (⊤ : ℕ∞) offset) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Y =>
      flow Y s (flow Y a (center Y + child Y) s + offset Y) a - center Y) := by
  have hi : ContDiff ℝ (⊤ : ℕ∞)
      (fun Y => flow Y a (center Y + child Y) s) :=
    (hf a s).comp (contDiff_id.prodMk (hc.add hd))
  exact ((hf s a).comp (contDiff_id.prodMk (hi.add hh))).sub hc

end AVRegularity.EntryWeakProofs
end
end

section
/-! Absolutely summable torus Fourier series represent their original L² class. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVenhance.Infra.Torus AVenhance.Infra.Heat

local instance sobolevContinuousFourierMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance sobolevContinuousFourierAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance sobolevContinuousFourierProbTorus : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVRegularity.EntryWeakProofs

def torusFourierContinuous (u : TorusL2 2) : C(UnitAddTorus (Fin 2), ℂ) :=
  ∑' k : Frequency, UnitAddTorus.mFourierCoeff u k • UnitAddTorus.mFourier k

theorem torusFourierContinuous_toLp (u : TorusL2 2)
    (hu : Summable (fun k : Frequency => ‖UnitAddTorus.mFourierCoeff u k‖)) :
    ContinuousMap.toLp 2 volume ℂ (torusFourierContinuous u) = u := by
  let g : Frequency → C(UnitAddTorus (Fin 2), ℂ) :=
    fun k => UnitAddTorus.mFourierCoeff u k • UnitAddTorus.mFourier k
  have hg : Summable g := by
    apply Summable.of_norm_bounded hu
    intro k
    simp only [g, norm_smul, UnitAddTorus.mFourier_norm, mul_one, le_refl]
  have hL2 : HasSum (fun k : Frequency => ContinuousMap.toLp 2 volume ℂ (g k)) u := by
    simpa only [g, map_smul, UnitAddTorus.mFourierLp] using UnitAddTorus.hasSum_mFourier_series_L2 u
  change ContinuousMap.toLp 2 volume ℂ (∑' k, g k) = u
  rw [ContinuousLinearMap.map_tsum (ContinuousMap.toLp 2 volume ℂ) hg]
  exact hL2.tsum_eq

theorem torusFourierContinuous_eval (u : TorusL2 2)
    (hu : Summable (fun k : Frequency => ‖UnitAddTorus.mFourierCoeff u k‖)) (x : Vec 2) :
    torusFourierContinuous u (toUnitTorus 2 x) =
      ∑' k : Frequency, UnitAddTorus.mFourierCoeff u k • torusCharacter (-k) x := by
  have hg : Summable (fun k : Frequency => UnitAddTorus.mFourierCoeff u k • UnitAddTorus.mFourier k) := by
    apply Summable.of_norm_bounded hu
    intro k
    simp only [norm_smul, UnitAddTorus.mFourier_norm, mul_one, le_refl]
  rw [torusFourierContinuous, ← ContinuousMap.tsum_apply hg (toUnitTorus 2 x)]
  apply tsum_congr
  intro k
  simp only [torusCharacter, neg_neg]
  rfl

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance.Infra.Heat
namespace AVRegularity.EntryWeakProofs

/-! The two reserved derivatives supply a square-summable two-dimensional reciprocal weight. -/

def latticeWeight (k : Frequency) : ℝ := (1 + |(k 0 : ℝ)|) * (1 + |(k 1 : ℝ)|)

theorem latticeWeight_pos (k : Frequency) : 0 < latticeWeight k := by
  unfold latticeWeight
  positivity

theorem integerReciprocal_square_summable :
    Summable (fun n : ℤ => (1 / (1 + |(n : ℝ)|)) ^ 2) := by
  have h : Summable (fun n : ℕ => (1 / (1 + (n : ℝ))) ^ 2) := by
    have hh := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
    exact hh.congr (fun n => by
      rw [Real.rpow_two, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1),
        one_div_pow, add_comm])
  apply Summable.of_nat_of_neg
  · exact h.congr (fun n => by rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)])
  · exact h.congr (fun n => by rw [Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg n)])

theorem latticeReciprocal_square_summable : Summable (fun k : Frequency => (1 / latticeWeight k) ^ 2) := by
  have h := integerReciprocal_square_summable
  have hnorm : Summable (fun n : ℤ => ‖(1 / (1 + |(n : ℝ)|)) ^ 2‖) :=
    h.congr (fun n => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (1 / (1 + |(n : ℝ)|)))])
  have hh := summable_mul_of_summable_norm hnorm hnorm
  have ht := hh.comp_injective (finTwoArrowEquiv ℤ).injective
  exact ht.congr (fun k => by
    change (1 / (1 + |(k 0 : ℝ)|)) ^ 2 * (1 / (1 + |(k 1 : ℝ)|)) ^ 2 = _
    rw [← mul_pow, one_div_mul_one_div]
    rfl)

theorem latticeReciprocal_memLp : Memℓp (fun k : Frequency => (1 / latticeWeight k : ℂ)) 2 := by
  apply memℓp_gen
  refine ⟨∑' k : Frequency, (1 / latticeWeight k) ^ 2, ?_⟩
  have hh := latticeReciprocal_square_summable.hasSum
  convert hh using 1
  funext k
  rw [ENNReal.toReal_ofNat, norm_div, norm_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (latticeWeight_pos k), Real.rpow_two]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Spatial normalization commutes exactly with chart composition. -/

def rescaledChart (ρ : ℝ) (F : Vec 2 → Vec 2) (x : Vec 2) : Vec 2 :=
  ρ⁻¹ • F (ρ • x)

theorem rescaledChart_comp (ρ : ℝ) (hρ : 0 < ρ) (F G : Vec 2 → Vec 2) :
    rescaledChart ρ (F ∘ G) = rescaledChart ρ F ∘ rescaledChart ρ G := by
  funext x
  simp [rescaledChart, smul_smul, mul_inv_cancel₀ hρ.ne']

theorem rescaledChart_smooth (ρ : ℝ) (F : Vec 2 → Vec 2)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (rescaledChart ρ F) :=
  (hF.comp (contDiff_id.const_smul ρ)).const_smul _

theorem rescaledChart_positive_derivative_norm (ρ : ℝ) (hρ : 0 < ρ)
    (F : Vec 2 → Vec 2) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (n : ℕ) (hn : 1 ≤ n) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (rescaledChart ρ F) x‖ =
      ρ ^ (n - 1) * ‖iteratedFDeriv ℝ n F (ρ • x)‖ := by
  change ‖iteratedFDeriv ℝ n (fun z => ρ⁻¹ • F (ρ • z)) x‖ = _
  simpa only [zero_add, sub_zero] using
    CycleWords.cell_rescaled_iteratedFDeriv_norm F hF ρ hρ 0 0 n hn x

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
open AVenhance.Infra.Torus AVenhance.Infra.Heat
namespace AVRegularity.EntryWeakProofs

/-! Square-summable Fourier coefficients of every real ordered weak jet. -/

def realJetFourier (K : ℕ) (f : TorusHk K ℝ) (a : JetIndex2 K) :
    lp (fun _ : Frequency => ℂ) 2 :=
  UnitAddTorus.mFourierBasis.repr
    (frozenCellToTorusL2 (f.toFunction.hasPeriodicWeakJet.2.1 a))

theorem realJetFourier_apply (K : ℕ) (f : TorusHk K ℝ) (a : JetIndex2 K) (k : Frequency) :
    realJetFourier K f a k = UnitAddTorus.mFourierCoeff
      (periodicToTorus (fun x => (f.toFunction.jet a x : ℂ))) k := by
  rw [realJetFourier, UnitAddTorus.mFourierBasis_repr]
  exact (AVenhance.Infra.Parabolic.WeakUniqueness.WeakProjection.weakProjection_frozenCellToTorus_coeff
    (f.toFunction.hasPeriodicWeakJet.2.1 a) k).symm

theorem realJetFourier_next (K : ℕ) (f : TorusHk K ℝ) (j : Fin K)
    (w : DerivativeWord2 j.val) (i : Fin 2) (k : Frequency) :
    realJetFourier K f (nextIndex2 j w i) k =
      (2 * Real.pi * Complex.I * (k i : ℂ)) * realJetFourier K f (lowerIndex2 j w) k := by
  rw [realJetFourier_apply, realJetFourier_apply]
  have hh := AVenhance.Infra.Parabolic.WeakUniqueness.WeakProjection.weakProjection_realFourierMultiplier
    (torusJetCoordinate_isPeriodicH1With f j w (1 : ℝ)) i k
  simpa only [torusJetCoordinateValue, torusJetCoordinateGradient, RCLike.inner_apply,
    map_one, mul_one] using hh

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Heat
namespace AVRegularity.EntryWeakProofs

/-! The Fourier multiplier of a weak ordered derivative, with arbitrary finite indices. -/

def appendJetIndex (K : ℕ) (a : JetIndex2 K) (i : Fin 2) (ha : a.1.val < K) : JetIndex2 K :=
  ⟨⟨a.1.val + 1, by omega⟩, Fin.snoc a.2 i⟩

theorem realJetFourier_append (K : ℕ) (f : TorusHk K ℝ) (a : JetIndex2 K)
    (i : Fin 2) (ha : a.1.val < K) (k : Frequency) :
    realJetFourier K f (appendJetIndex K a i ha) k =
      (2 * Real.pi * Complex.I * (k i : ℂ)) * realJetFourier K f a k :=
  realJetFourier_next K f ⟨a.1.val, ha⟩ a.2 i k

theorem complexFrequencyMultiplier_norm (m : ℤ) :
    ‖(2 * Real.pi * Complex.I * (m : ℂ))‖ = 2 * Real.pi * |(m : ℝ)| := by
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_I, mul_one, Complex.norm_intCast]

theorem realJetFourier_append_norm (K : ℕ) (f : TorusHk K ℝ) (a : JetIndex2 K)
    (i : Fin 2) (ha : a.1.val < K) (k : Frequency) :
    |(k i : ℝ)| * ‖realJetFourier K f a k‖ ≤
      ‖realJetFourier K f (appendJetIndex K a i ha) k‖ := by
  rw [realJetFourier_append, norm_mul, complexFrequencyMultiplier_norm]
  have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  calc
    _ = 1 * (|(k i : ℝ)| * ‖realJetFourier K f a k‖) := (one_mul _).symm
    _ ≤ (2 * Real.pi) * (|(k i : ℝ)| * ‖realJetFourier K f a k‖) :=
      mul_le_mul_of_nonneg_right hp (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    _ = _ := (mul_assoc _ _ _).symm

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
open Filter Topology
namespace AVRegularity.EntryWeakProofs

/-! Every fixed finite-chain budget is absorbed by the renewal-window smallness. -/

theorem weak_anchor_product_tendsto_zero (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) :
    Tendsto (fun m => ocA α q Λ (m - 1) * ocTauPP α q Λ m) atTop (𝓝 0) := by
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hp : 0 < 2 * ocDelta α q := by linarith
  have hpow := (Real.continuousAt_rpow_const 0 (2 * ocDelta α q) (Or.inr hp.le)).tendsto.comp
    (CycleReference.epsilon_parent_tendsto_zero hq.1 hΛ)
  have ht : Tendsto (fun m => (2 : ℝ) ^ (-25 : ℤ) *
      ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q)) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow hp.ne', mul_zero, Function.comp_def] using
      hpow.const_mul ((2 : ℝ) ^ (-25 : ℤ))
  have hn : ∀ m : ℕ, 0 ≤ ocA α q Λ (m - 1) * ocTauPP α q Λ m := by
    intro m
    have he := (Scales.epsilon_basic (m := m - 1) hq.1 hΛ).1
    exact mul_nonneg (Real.rpow_nonneg he.le _)
      (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ Λ)).le
  apply squeeze_zero' (Eventually.of_forall hn) ?_ ht
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact (Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq hΛ hm).2.2.2.2.1

theorem weak_anchor_product_eventually_small (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (C c : ℝ) (hc : 0 < c) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M,
      C * (ocA α q Λ (m - 1) * ocTauPP α q Λ m) ≤ c := by
  have ht := (weak_anchor_product_tendsto_zero α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ).const_mul C
  simp only [mul_zero] at ht
  have he : ∀ᶠ m : ℕ in atTop,
      C * (ocA α q Λ (m - 1) * ocTauPP α q Λ m) < c := by
    exact ht.eventually (gt_mem_nhds hc)
  obtain ⟨M, hM⟩ := eventually_atTop.1 he
  exact ⟨max 2 M, le_max_left _ _, fun m hm => (hM m (by omega)).le⟩

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! Uniform primitive Jacobian errors on every finite enlarged renewal window. -/

theorem weak_finite_chart_eventually_small (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M,
      2 * R * ocTauPP α q Λ m ≤ (2 : ℝ) ^ (-25 : ℤ) * (ocA α q Λ (m - 1))⁻¹ ∧
      2 ^ 23 * (2 * R * ocTauPP α q Λ m) * ocA α q Λ (m - 1) ≤ δ ∧
      (4 * Real.pi ^ 2) * (2 * R * ocTauPP α q Λ m) * ocA α q Λ (m - 1) ≤ δ := by
  let C := 2 * R * (1 + (2 : ℝ) ^ 23 + 4 * Real.pi ^ 2)
  have hc : 0 < min δ ((2 : ℝ) ^ (-25 : ℤ)) := lt_min hδ (by positivity)
  obtain ⟨M, hM, hb⟩ := weak_anchor_product_eventually_small α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ C
    (min δ ((2 : ℝ) ^ (-25 : ℤ))) hc
  refine ⟨M, hM, ?_⟩
  intro m hm
  have hA : 0 < ocA α q Λ (m - 1) := by
    unfold ocA
    exact Real.rpow_pos_of_pos (Scales.epsilon_basic hq.1 hΛ).1 _
  have hτ : 0 ≤ ocTauPP α q Λ m := (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ Λ)).le
  have hP : 0 ≤ ocA α q Λ (m - 1) * ocTauPP α q Λ m := mul_nonneg hA.le hτ
  have hC0 : 2 * R ≤ C := by dsimp [C]; nlinarith [sq_nonneg Real.pi]
  have hC1 : 2 ^ 23 * (2 * R) ≤ C := by dsimp [C]; nlinarith [sq_nonneg Real.pi]
  have hC2 : (4 * Real.pi ^ 2) * (2 * R) ≤ C := by dsimp [C]; nlinarith
  have hzero := (mul_le_mul_of_nonneg_right hC0 hP).trans (hb m hm)
  have hone := (mul_le_mul_of_nonneg_right hC1 hP).trans (hb m hm)
  have htwo := (mul_le_mul_of_nonneg_right hC2 hP).trans (hb m hm)
  refine ⟨?_, ?_, ?_⟩
  · rw [← div_eq_mul_inv, le_div_iff₀ hA]
    calc
      _ = (2 * R) * (ocA α q Λ (m - 1) * ocTauPP α q Λ m) := by ring
      _ ≤ min δ ((2 : ℝ) ^ (-25 : ℤ)) := hzero
      _ ≤ _ := min_le_right _ _
  · have h := hone.trans (min_le_left _ _)
    nlinarith [h]
  · have h := htwo.trans (min_le_left _ _)
    nlinarith [h]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Native centered geometry charts expose the exact normalization used in child differences. -/

def centeredGeometryChart (g : ChainGeom) (ρ u : ℝ) (X : Vec 2) : Vec 2 :=
  ρ⁻¹ • (g.1 u (g.2.1 + ρ • X) g.2.2 - g.1 u g.2.1 g.2.2)

def centeredGeometryChartInv (g : ChainGeom) (ρ u : ℝ) (X : Vec 2) : Vec 2 :=
  ρ⁻¹ • (g.1 g.2.2 (g.1 u g.2.1 g.2.2 + ρ • X) u - g.2.1)

theorem centeredGeometryChart_smul (g : ChainGeom) (ρ : ℝ) (hρ : ρ ≠ 0) (u : ℝ) (X : Vec 2) :
    ρ • centeredGeometryChart g ρ u X =
      g.1 u (g.2.1 + ρ • X) g.2.2 - g.1 u g.2.1 g.2.2 := by
  rw [centeredGeometryChart, smul_smul, mul_inv_cancel₀ hρ, one_smul]

theorem centeredGeometryChartInv_forward (g : ChainGeom) (hg : ChainGeometry.InvLaw g)
    (ρ : ℝ) (hρ : ρ ≠ 0) (u : ℝ) (X : Vec 2) :
    centeredGeometryChartInv g ρ u (centeredGeometryChart g ρ u X) = X := by
  unfold centeredGeometryChartInv
  rw [centeredGeometryChart_smul g ρ hρ]
  rw [add_sub_cancel, hg, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hρ, one_smul]

theorem centeredGeometryChart_difference (g : ChainGeom) (ρ u : ℝ) (X V : Vec 2) :
    centeredGeometryChart g ρ u (X + V) - centeredGeometryChart g ρ u X =
      ρ⁻¹ • (g.1 u (g.2.1 + ρ • (X + V)) g.2.2 - g.1 u (g.2.1 + ρ • X) g.2.2) := by
  unfold centeredGeometryChart
  rw [← smul_sub]
  congr 1
  abel

/-! Recentring a child keeps its offset flow and translates its center by the requested real offset. -/

def recenteredChild (D : OCData) (k : ℕ) (s' : ℝ) (g : ChainGeom)
    (c : ChainChild) (h : Vec 2) : ChainChild :=
  let x' := g.1 s' (g.2.1 + c.center) g.2.2
  let R := g.1 g.2.2 (x' + h) s' - g.2.1 - c.center
  ⟨c.center + R, c.phase + (D.eps k)⁻¹ • R⟩

theorem childGeom_recenter (D : OCData) (k : ℕ) (pk : ℤ) (s' : ℝ)
    (g : ChainGeom) (hg : ChainGeometry.InvLaw g) (c : ChainChild) (h : Vec 2) :
    D.childGeom k pk s' (recenteredChild D k s' g c h) g =
      ((D.childGeom k pk s' c g).1, (D.childGeom k pk s' c g).2.1 + h, s') := by
  let x' := g.1 s' (g.2.1 + c.center) g.2.2
  let R := g.1 g.2.2 (x' + h) s' - g.2.1 - c.center
  have hp : (c.phase + (D.eps k)⁻¹ • R) -
      (D.eps k)⁻¹ • (g.2.1 + (c.center + R)) =
      c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center) := by
    rw [show g.2.1 + (c.center + R) = (g.2.1 + c.center) + R by abel, smul_add]
    abel
  have hc : g.2.1 + (c.center + R) = g.1 g.2.2 (x' + h) s' := by
    dsimp only [R]
    abel
  apply Prod.ext
  · funext u x r
    change g.1 u (g.1 g.2.2 x r + D.eps k • D.relDisp k pk u r
      ((D.eps k)⁻¹ • g.1 g.2.2 x r +
        ((c.phase + (D.eps k)⁻¹ • R) - (D.eps k)⁻¹ • (g.2.1 + (c.center + R))))) g.2.2 = _
    rw [hp]
    rfl
  · apply Prod.ext
    · change g.1 s' (g.2.1 + (c.center + R)) g.2.2 = x' + h
      rw [hc]
      exact hg s' g.2.2 (x' + h)
    · rfl

/-! Centered child charts expose the cancellations before estimating independent parameter jets. -/

def childCenterReturn (g : ChainGeom) (anchor : ℝ) (c : ChainChild) (h : Vec 2) : Vec 2 :=
  g.1 g.2.2 (g.1 anchor (g.2.1 + c.center) g.2.2 + h) anchor - g.2.1 - c.center

theorem childGeom_centered_flow_formula (D : OCData) (k : ℕ) (slot : ℤ) (anchor : ℝ)
    (g : ChainGeom) (hg : ChainGeometry.InvLaw g) (c : ChainChild) (u : ℝ) (h : Vec 2) :
    let child := D.childGeom k slot anchor c g
    child.1 u (child.2.1 + h) anchor - child.1 u child.2.1 anchor =
      g.1 u (g.2.1 + c.center + childCenterReturn g anchor c h +
        D.eps k • D.relDisp k slot u anchor
          (c.phase + (D.eps k)⁻¹ • childCenterReturn g anchor c h)) g.2.2 -
      g.1 u (g.2.1 + c.center + D.eps k • D.relDisp k slot u anchor c.phase) g.2.2 := by
  let R := childCenterReturn g anchor c h
  have hpoint : g.1 g.2.2 (g.1 anchor (g.2.1 + c.center) g.2.2 + h) anchor =
      g.2.1 + c.center + R := by
    dsimp only [R, childCenterReturn]
    abel
  have hphase : (D.eps k)⁻¹ • (g.2.1 + c.center + R) +
      (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)) =
      c.phase + (D.eps k)⁻¹ • R := by
    rw [smul_add]
    abel
  have hphase0 : (D.eps k)⁻¹ • (g.2.1 + c.center) +
      (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)) = c.phase := by abel
  dsimp only [OCData.childGeom]
  rw [hpoint, hg, hphase, hphase0]

/-! Re-anchoring turns the centered inverse chart into a centered forward chart. -/

def reanchoredGeometry (g : ChainGeom) (u : ℝ) : ChainGeom :=
  (g.1, g.1 u g.2.1 g.2.2, u)

theorem centeredGeometryChartInv_reanchor (g : ChainGeom) (hg : ChainGeometry.InvLaw g)
    (ρ u : ℝ) (X : Vec 2) :
    centeredGeometryChartInv g ρ u X =
      centeredGeometryChart (reanchoredGeometry g u) ρ g.2.2 X := by
  unfold centeredGeometryChartInv centeredGeometryChart reanchoredGeometry
  rw [hg]

def reanchoredChild (D : OCData) (k : ℕ) (slot : ℤ) (anchor u : ℝ)
    (c : ChainChild) : ChainChild :=
  ⟨c.center + D.eps k • D.relDisp k slot u anchor c.phase,
    c.phase + D.relDisp k slot u anchor c.phase⟩

theorem childGeom_reanchor (D : OCData) (k : ℕ) (slot : ℤ) (anchor u : ℝ)
    (g : ChainGeom) (hg : ChainGeometry.InvLaw g) (c : ChainChild) (he : D.eps k ≠ 0) :
    D.childGeom k slot u (reanchoredChild D k slot anchor u c) g =
      reanchoredGeometry (D.childGeom k slot anchor c g) u := by
  let δ := D.relDisp k slot u anchor c.phase
  have hp : (c.phase + δ) - (D.eps k)⁻¹ • (g.2.1 + (c.center + D.eps k • δ)) =
      c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center) := by
    rw [show g.2.1 + (c.center + D.eps k • δ) = (g.2.1 + c.center) + D.eps k • δ by abel,
      smul_add, smul_smul, inv_mul_cancel₀ he, one_smul]
    abel
  apply Prod.ext
  · funext v x r
    change g.1 v (g.1 g.2.2 x r + D.eps k • D.relDisp k slot v r
      ((D.eps k)⁻¹ • g.1 g.2.2 x r +
        ((c.phase + δ) - (D.eps k)⁻¹ • (g.2.1 + (c.center + D.eps k • δ))))) g.2.2 = _
    rw [hp]
    rfl
  · apply Prod.ext
    · change g.1 u (g.2.1 + (c.center + D.eps k • δ)) g.2.2 =
        g.1 u (g.1 g.2.2 (g.1 anchor (g.2.1 + c.center) g.2.2) anchor +
          D.eps k • D.relDisp k slot u anchor
            ((D.eps k)⁻¹ • g.1 g.2.2 (g.1 anchor (g.2.1 + c.center) g.2.2) anchor +
              (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)))) g.2.2
      rw [hg]
      have hphase : (D.eps k)⁻¹ • (g.2.1 + c.center) +
          (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)) = c.phase := by abel
      rw [hphase]
      dsimp only [δ]
      rw [add_assoc]
    · rfl

/-! Re-express a child-scale difference in its parent native chart. -/

theorem centeredGeometryChart_scale_difference (g : ChainGeom) (ρ θ u : ℝ)
    (X V : Vec 2) :
    (ρ * θ)⁻¹ • (g.1 u (g.2.1 + ρ • (X + θ • V)) g.2.2 -
      g.1 u (g.2.1 + ρ • X) g.2.2) =
      θ⁻¹ • (centeredGeometryChart g ρ u (X + θ • V) -
        centeredGeometryChart g ρ u X) := by
  rw [centeredGeometryChart_difference, smul_smul, mul_inv_rev]

/-! A chain with a last child exposes exactly one geometric child step. -/

theorem geom_append_child (D : OCData) (base : ℕ) (slots : List ℤ)
    (Y : Vec 2) (children : List ChainChild) (hl : slots.length = children.length + 1)
    (slot : ℤ) (c : ChainChild) :
    (⟨base, slots ++ [slot], Y, children ++ [c]⟩ : RealChain).geom D =
      D.childGeom (base + 1 + children.length) (slots.getLastD 0)
        (D.slotAnchor (base + 1 + children.length + 1) slot) c
        ((⟨base, slots, Y, children⟩ : RealChain).geom D) := by
  have hh : (slots ++ [slot]).headD 0 = slots.headD 0 := by
    cases slots with
    | nil => simp only [List.length_nil] at hl; omega
    | cons a l => rfl
  unfold RealChain.geom
  simp only [hh]
  exact ChainGeometry.geomAux_append D slot c children (base + 1) slots
    (D.flowOf base, Y, D.slotAnchor (base + 1) (slots.headD 0)) hl

theorem recenter_append_child (D : OCData) (base : ℕ) (slots : List ℤ)
    (Y : Vec 2) (children : List ChainChild) (slot : ℤ) (c : ChainChild) (h : Vec 2) :
    (⟨base, slots ++ [slot], Y, children ++ [c]⟩ : RealChain).recenter D h =
      ⟨base, slots ++ [slot], Y, children ++
        [recenteredChild D (base + 1 + children.length)
          (D.slotAnchor (base + 1 + children.length + 1) slot)
          ((⟨base, slots, Y, children⟩ : RealChain).geom D) c h]⟩ := by
  simp [RealChain.recenter, RealChain.dropLastChild, RealChain.lastLevel, RealChain.slot,
    recenteredChild, Nat.add_comm, Nat.add_left_comm]

/-! Exact normalized child returns, before taking any independent derivatives. -/

theorem childCenterReturn_normalized (g : ChainGeom) (anchor ρ : ℝ) (hρ : ρ ≠ 0)
    (c : ChainChild) (C H : Vec 2) (hc : c.center = ρ • C) :
    ρ⁻¹ • childCenterReturn g anchor c (ρ • H) =
      centeredGeometryChartInv g ρ anchor (centeredGeometryChart g ρ anchor C + H) - C := by
  have harg : g.1 anchor g.2.1 g.2.2 +
      ρ • (centeredGeometryChart g ρ anchor C + H) =
      g.1 anchor (g.2.1 + ρ • C) g.2.2 + ρ • H := by
    rw [smul_add, centeredGeometryChart_smul g ρ hρ]
    abel
  unfold centeredGeometryChartInv childCenterReturn
  rw [harg, hc, smul_sub, smul_sub, smul_smul, inv_mul_cancel₀ hρ, one_smul]

theorem childCenterReturn_parent_scale (g : ChainGeom) (hg : ChainGeometry.InvLaw g)
    (anchor ρ θ : ℝ) (hρ : ρ ≠ 0) (c : ChainChild) (C H : Vec 2)
    (hc : c.center = ρ • C) :
    (ρ * θ)⁻¹ • childCenterReturn g anchor c ((ρ * θ) • H) =
      θ⁻¹ • (centeredGeometryChartInv g ρ anchor
          (centeredGeometryChart g ρ anchor C + θ • H) -
        centeredGeometryChartInv g ρ anchor (centeredGeometryChart g ρ anchor C)) := by
  have hreturn := childCenterReturn_normalized g anchor ρ hρ c C (θ • H) hc
  rw [centeredGeometryChartInv_forward g hg ρ hρ]
  rw [mul_inv_rev, ← smul_smul, ← hreturn, smul_smul]
  simp only [smul_smul]

/-! Actual chain recentering leaves the offset flow and anchor fixed and translates its center. -/

theorem geom_recenter_append_child (D : OCData) (base : ℕ) (slots : List ℤ)
    (Y : Vec 2) (children : List ChainChild) (hl : slots.length = children.length + 1)
    (slot : ℤ) (c : ChainChild) (h : Vec 2) :
    ((⟨base, slots ++ [slot], Y, children ++ [c]⟩ : RealChain).recenter D h).geom D =
      (((⟨base, slots ++ [slot], Y, children ++ [c]⟩ : RealChain).geom D).1,
        ((⟨base, slots ++ [slot], Y, children ++ [c]⟩ : RealChain).geom D).2.1 + h,
        ((⟨base, slots ++ [slot], Y, children ++ [c]⟩ : RealChain).geom D).2.2) := by
  let g := (⟨base, slots, Y, children⟩ : RealChain).geom D
  have hg : ChainGeometry.InvLaw g :=
    ChainGeometry.invLaw_geomAux D children (base + 1) slots
      (ChainGeometry.invLaw_base D base Y (D.slotAnchor (base + 1) (slots.headD 0)))
  rw [recenter_append_child]
  rw [geom_append_child D base slots Y children hl slot]
  rw [childGeom_recenter D (base + 1 + children.length) (slots.getLastD 0)
    (D.slotAnchor (base + 1 + children.length + 1) slot) g hg c h]
  rw [geom_append_child D base slots Y children hl slot c]
  rfl

theorem geom_recenter (D : OCData) (A : RealChain)
    (hl : A.slots.length = A.children.length + 1) (h : Vec 2) :
    (A.recenter D h).geom D = ((A.geom D).1, (A.geom D).2.1 + h, (A.geom D).2.2) := by
  rcases A with ⟨base, slots, Y, children⟩
  dsimp only at hl
  by_cases hc : children = []
  · subst children
    obtain ⟨slot, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hl)
    simp [RealChain.recenter, RealChain.geom, OCData.geomAux]
  · have hs : slots ≠ [] := by intro he; simp only [he, List.length_nil] at hl; omega
    let cs := children.dropLast
    let c := children.getLast hc
    let sl := slots.dropLast
    let slot := slots.getLast hs
    have hcs : cs ++ [c] = children := List.dropLast_append_getLast hc
    have hsl : sl ++ [slot] = slots := List.dropLast_append_getLast hs
    have hlen : sl.length = cs.length + 1 := by
      have h₁ := congrArg List.length hcs
      have h₂ := congrArg List.length hsl
      simp only [List.length_append, List.length_singleton] at h₁ h₂
      omega
    rw [← hcs, ← hsl]
    exact geom_recenter_append_child D base sl Y cs hlen slot c h

/-! Equal family geometries give identical molecular metrics on every recentered germ. -/

theorem weak_family_metric_geom_congr (D : OCData) (A B : RealChain)
    (hgeom : A.geom D = B.geom D) (t : ℝ) : A.famMetric D t = B.famMetric D t := by
  simp only [RealChain.famMetric, RealChain.famJac, hgeom]

theorem weak_family_metric_recenter_geom_congr (D : OCData) (A B : RealChain)
    (hA : A.slots.length = A.children.length + 1)
    (hB : B.slots.length = B.children.length + 1) (hgeom : A.geom D = B.geom D)
    (h : Vec 2) (t : ℝ) :
    (A.recenter D h).famMetric D t = (B.recenter D h).famMetric D t := by
  apply weak_family_metric_geom_congr
  rw [geom_recenter D A hA h, geom_recenter D B hB h, hgeom]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Literal weak physical coefficients inherit genuine active-piece jet bounds. -/

open CycleJointProofs
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

def weakPhysicalPieceCoefficient (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ)
    (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u) (d : ℕ) (t : ℝ) (p : P)
    (x : Vec 2) : (PiLp 2 (fun _ : DerivativeWord2 (d - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v)) :=
  nativeArrayAssembly (d - 1) (F.identity v u γ).map
    (fun k A => transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
      (F.identity v u γ).maxOrder
      (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I t
        (((F.piece p).material t).symm x) (e⁻¹ • ((F.piece p).material t).symm x))
      (d - 1) A x k)

theorem weak_constituentPhysical_piece_sum (F : ChartedFamily ι h D P Ctx)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u) (d : ℕ) (t : ℝ) :
    constituentPhysical F ν e E actual v u γ d t =
      fun x => ∑ᶠ p, F.weight p t • weakPhysicalPieceCoefficient F ν e E actual v u γ d t p x :=
  rfl

theorem weak_constituentPhysical_jet_assembly (F : ChartedFamily ι h D P Ctx)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u)
    (d n : ℕ) (ρ B : ℝ) (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (t : ℝ)
    (hgs : ∀ p, t ∈ (F.piece p).output →
      ContDiff ℝ (n : ℕ) (weakPhysicalPieceCoefficient F ν e E actual v u γ d t p))
    (hjet : ∀ p, t ∈ (F.piece p).output → ∀ x,
      ρ ^ n * ‖iteratedFDeriv ℝ n
        (weakPhysicalPieceCoefficient F ν e E actual v u γ d t p) x‖ ≤ B) (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (constituentPhysical F ν e E actual v u γ d t) x‖ ≤ B := by
  let g := weakPhysicalPieceCoefficient F ν e E actual v u γ d t
  let f := fun p y => F.weight p t • g p y
  rw [weak_constituentPhysical_piece_sum]
  have hz p (hout : t ∉ (F.piece p).output) : f p = fun _ => 0 := by
    funext y
    dsimp only [f]
    rw [F.weight_zero p t hout]
    exact zero_smul ℝ (g p y)
  apply positive_piece_jet_assembly_total F t t t ⟨le_refl _, le_refl _⟩ f n
    (fun p => by
      by_cases hout : t ∈ (F.piece p).output
      · exact (hgs p hout).const_smul _
      · rw [hz p hout]
        exact contDiff_const) _ ρ B hρ hB _ x
  · intro p y hout
    exact congrFun (hz p hout) y
  · intro p y
    by_cases hout : t ∈ (F.piece p).output
    · dsimp only [f]
      rw [iteratedFDeriv_const_smul_apply' (hgs p hout).contDiffAt, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (F.weight_nonneg p t)]
      have hh := mul_le_mul_of_nonneg_left (hjet p hout y) (F.weight_nonneg p t)
      convert hh using 1; ring
    · rw [hz p hout, iteratedFDeriv_fun_zero, F.weight_zero p t hout]
      simp only [Pi.zero_apply, norm_zero, mul_zero, zero_mul, le_refl]

theorem weak_constituentPhysical_spatial_contDiff (F : ChartedFamily ι h D P Ctx)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u) (d n : ℕ) (t : ℝ)
    (hgs : ∀ p, t ∈ (F.piece p).output →
      ContDiff ℝ (n : ℕ) (weakPhysicalPieceCoefficient F ν e E actual v u γ d t p)) :
    ContDiff ℝ (n : ℕ) (constituentPhysical F ν e E actual v u γ d t) := by
  classical
  let g := weakPhysicalPieceCoefficient F ν e E actual v u γ d t
  let f := fun p y => F.weight p t • g p y
  have hz p (hout : t ∉ (F.piece p).output) : f p = fun _ => 0 := by
    funext y
    dsimp only [f]
    rw [F.weight_zero p t hout]
    exact zero_smul ℝ (g p y)
  let s := (F.locally_finite t t).toFinset
  have he (x : Vec 2) : (∑ᶠ p, f p x) = ∑ p ∈ s, f p x := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    change p ∈ (F.locally_finite t t).toFinset
    rw [Set.Finite.mem_toFinset]
    have hout : t ∈ (F.piece p).output := by
      by_contra hh
      exact hp (congrFun (hz p hh) x)
    exact ⟨t, hout, le_refl _, le_refl _⟩
  rw [weak_constituentPhysical_piece_sum]
  change ContDiff ℝ (n : ℕ) (fun x => ∑ᶠ p, f p x)
  simp_rw [he]
  apply ContDiff.sum
  intro p _
  by_cases hout : t ∈ (F.piece p).output
  · exact (hgs p hout).const_smul _
  · rw [hz p hout]
    exact contDiff_const

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! The full lift-solving window remains inside the short renewal-anchor window. -/

theorem weak_lift_anchor_distance (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ)
    (m : ℕ) (k : ℤ) (t : ℝ)
    (ht : t ∈ Set.Icc (((k : ℝ) - 61 / 48) * ocTau α q Λ m)
      (((k : ℝ) + 61 / 48) * ocTau α q Λ m)) :
    |t - (ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m| ≤ ocTauPP α q Λ m := by
  set h := ocTauPP α q Λ m
  set τ := ocTau α q Λ m
  have hh : 0 < h := Construction.Stream.ocTauPP_pos hΛ
  have hτ : 0 < τ := Construction.Stream.ocTau_pos hΛ
  have hL := ChildInert.ocL_ge_five α q hΛ m
  have hτle : τ ≤ h / 25 := by
    have he : τ = h / (ocL α q Λ m : ℝ) ^ 2 := rfl
    rw [he]
    apply div_le_div_of_nonneg_left hh.le (by norm_num)
    nlinarith
  set l := ocLabel α q Λ m k
  have hf1 : (l : ℝ) ≤ ((k : ℝ) * τ + (h - τ) / 2) / h := Int.floor_le _
  have hf2 : ((k : ℝ) * τ + (h - τ) / 2) / h < l + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hh] at hf1
  rw [div_lt_iff₀ hh] at hf2
  rw [abs_le]
  constructor <;> nlinarith [ht.1, ht.2]

/-! Scheduled slots have renewal anchors separated by the sum of their window radii. -/

theorem scheduled_anchor_distance (D : OCData) (hΛ : 1 ≤ D.Λ)
    (i : ℕ) (p' p : ℤ) (hs : IsScheduledIn D i p' p) :
    |D.slotAnchor (i + 1) p' - D.slotAnchor i p| ≤
      ocTauPP D.α D.q D.Λ (i + 1) + ocTauPP D.α D.q D.Λ i := by
  obtain ⟨t, ht', ht⟩ := hs
  have hc : ocCutoff D.α D.q D.Λ (i + 1) p' t ≠ 0 := ht'
  have ha' := ChildInert.anchor_dist D.α D.q hΛ (i + 1) p' t hc
  have ha := weak_lift_anchor_distance D.α D.q hΛ i p t ht
  change |t - D.slotAnchor (i + 1) p'| ≤ _ at ha'
  change |t - D.slotAnchor i p| ≤ _ at ha
  exact (abs_sub_le _ t _).trans (add_le_add (by simpa only [abs_sub_comm] using ha') ha)

end AVRegularity.EntryWeakProofs
end
end
