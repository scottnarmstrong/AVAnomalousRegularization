-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Seam.NegTest
import AVRegularity.CycleWords.Seam.OldAdjointIdentification
import AVRegularity.CycleWords.Seam.B1PlainNeg
import AVRegularity.CycleWords.MixedWords.Discard.PlainPassStage
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import AVRegularity.CycleWords.MixedWords.B1WCrudeH4
import AVRegularity.CycleWords.MixedWords.Discard.JetFourier
import AVRegularity.CycleWords.MixedWords.StageExpansionLetter
import AVRegularity.CycleWords.Seam.CutoffComplementTaylor
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.SimpleGraph.Basic

section
/-! # The duality inequality for one moment

`∑_x π_x⁻¹ ∑_e (2π)⁻² ∫ m |ĝ_{x,e}|² ≤ (C ‖φ‖_{-n,k})²` for a smooth even multiplier `m ≥ 0` of
compact support with `|ξ|^{2l} m ≤ 1` for `l ≤ k`, where `g_{x,e}` is the `e`-th scaled component
of the moment `β`, `|β| ≤ n`, of `φ_x`.
-/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard
open scoped ENNReal

namespace AVRegularity.CycleWords.Seam.NegLowBand

open AVRegularity.CycleWords.Seam.YoungKernel AVRegularity.CycleWords.Seam

universe u v

theorem sq_le_of_le_mul_sqrt' {P A D : ℝ} (hP : 0 ≤ P) (h : P ≤ A * Real.sqrt P * D) :
    P ≤ (A * D) ^ 2 := by
  rcases hP.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have hs : 0 < Real.sqrt P := Real.sqrt_pos.2 hpos
    have hsq : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP
    have h1 : Real.sqrt P ≤ A * D := by
      have : Real.sqrt P * Real.sqrt P ≤ Real.sqrt P * (A * D) := by nlinarith
      exact le_of_mul_le_mul_left this hs
    calc P = Real.sqrt P ^ 2 := hsq.symm
      _ ≤ (A * D) ^ 2 := pow_le_pow_left₀ hs.le h1 2

theorem hasCompactSupport_qfun (ϖ : ℝ) (β : ℕ × ℕ) {R : ℝ} (hR : R ≠ 0) :
    HasCompactSupport (qfun ϖ β R) := by
  refine (chiR_compact hR).mono fun z hz => ?_
  rw [Function.mem_support] at hz ⊢
  intro h0
  apply hz
  rw [qfun_eq, h0, mul_zero]

theorem chiR_eq_one {R : ℝ} (hR : 0 < R) {z : Vec 2} (hz : ‖z‖ ≤ R) : chiR R z = 1 := by
  unfold chiR chi
  refine chiBump.one_of_mem_closedBall ?_
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
  have : (chiBump.rIn : ℝ) = 1 := rfl
  rw [this]
  calc R⁻¹ * ‖z‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hz (inv_nonneg.2 hR.le)
    _ = 1 := inv_mul_cancel₀ hR.ne'

theorem neg_dual (n k : ℕ) (β : ℕ × ℕ) (hβ : β.1 + β.2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      (π : ι → ℝ), (∀ x, 0 < π x) → ∀ ϖ : ℝ, 0 < ϖ → ϖ ≤ 1 →
      ∀ φ : ∀ x, Vec 2 → h x, (∀ x, StronglyMeasurable (φ x)) →
      (∀ x, HasCompactSupport (φ x)) → (∀ x, MemLp (φ x) 2 volume) →
      ∀ m : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) m → HasCompactSupport m → (∀ θ, m (-θ) = m θ) →
      (∀ ξ, 0 ≤ m ξ) → (∀ l ≤ k, ∀ ξ : Vec 2, (ξ 0 ^ 2 + ξ 1 ^ 2) ^ l * m ξ ≤ 1) →
      ∑ x, ENNReal.ofReal ((π x)⁻¹) * ∑ e : Fin (Module.finrank ℝ (h x)),
          (ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ∫⁻ ξ, ENNReal.ofReal (m ξ) *
            ‖planeTransform (gsc ϖ β (φ x) (stdOrthonormalBasis ℝ (h x) e)) ξ‖ₑ ^ 2) ≤
        (ENNReal.ofReal C * AVRegularity.CycleWords.Assembly.negJetNorm π (n : ℝ) k ϖ 1 φ) ^ 2 := by
  choose Cq hCq0 hCq using fun i : ℕ => qfun_weight_bound n β hβ i
  refine ⟨jetCoeff k Cq + 1, by have := jetCoeff_nonneg k Cq; linarith, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ ϖ hϖ0 hϖ1 φ hφm hφc hφ2 m hs hc hev hm0 hmk
  set b : ∀ x, OrthonormalBasis (Fin (Module.finrank ℝ (h x))) ℝ (h x) :=
    fun x => stdOrthonormalBasis ℝ (h x) with hb
  set Gv : ∀ x, Vec 2 → h x := fun x => gvec ϖ β (φ x) with hGv
  have hGv2 : ∀ x, MemLp (Gv x) 2 volume := fun x => gvec_memLp ϖ β (hφm x) (hφc x) (hφ2 x)
  have hGvc : ∀ x, HasCompactSupport (Gv x) := fun x => gvec_hasCompactSupport ϖ β (hφc x)
  have hGv1 : ∀ x, Integrable (Gv x) volume := fun x => integrable_of_memLp_compact (hGv2 x) (hGvc x)
  set U : ∀ x, Vec 2 → h x := fun x => fourierCutoff m (Gv x) with hU
  have hUs : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (U x) := fun x => fourierCutoff_contDiff m hs hc (hGv1 x)
  set gc : ∀ x, Fin (Module.finrank ℝ (h x)) → Vec 2 → ℝ :=
    fun x e => gsc ϖ β (φ x) (b x e) with hgc
  have hgc_eq : ∀ x e y, inner ℝ (b x e) (Gv x y) = gc x e y := fun x e y => inner_gvec ϖ β (φ x) _ y
  have hgc1 : ∀ x e, Integrable (gc x e) volume := by
    intro x e
    have := (innerSL ℝ (b x e)).integrable_comp (hGv1 x)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [innerSL_apply_apply]
    exact hgc_eq x e y
  have hgcm : ∀ x e, AEStronglyMeasurable (gc x e) volume := fun x e => (hgc1 x e).aestronglyMeasurable
  have hgc2 : ∀ x e, MemLp (gc x e) 2 volume := by
    intro x e
    refine (hGv2 x).of_le (hgcm x e) (Filter.Eventually.of_forall fun y => ?_)
    rw [← hgc_eq x e y, Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [(b x).norm_eq_one e, one_mul]
  obtain ⟨Rm, hRm⟩ := radius' m hc
  set Uc : ∀ x, Fin (Module.finrank ℝ (h x)) → Vec 2 → ℝ := fun x e => fourierCutoff m (gc x e)
    with hUc
  have hUcinner : ∀ x e z, inner ℝ (b x e) (U x z) = Uc x e z := by
    intro x e z
    rw [hU, ← fourierCutoff_inner m hs hc (hGv1 x) (b x e) z]
    simp only [hUc]
    congr 1
    funext y
    exact hgc_eq x e y
  have hUc2 : ∀ x e, MemLp (Uc x e) 2 volume := fun x e =>
    fourierCutoff_memLp m Rm hRm hs (hgc2 x e)
  have hUcs : ∀ x e, ContDiff ℝ (⊤ : ℕ∞) (Uc x e) := fun x e =>
    fourierCutoff_contDiff m hs hc (hgc1 x e)
  set Pxe : ∀ x, Fin (Module.finrank ℝ (h x)) → ℝ :=
    fun x e => ∫ z, gc x e z * Uc x e z with hPxe
  have hPxe0 : ∀ x e, 0 ≤ Pxe x e := fun x e =>
    pairing_nonneg m hs hc hev hm0 (hgc1 x e) (hgc2 x e)
  have hPxeE : ∀ x e, ENNReal.ofReal (Pxe x e) = ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) *
      ∫⁻ ξ, ENNReal.ofReal (m ξ) * ‖planeTransform (gsc ϖ β (φ x) (b x e)) ξ‖ₑ ^ 2 := fun x e =>
    pairing_eq m hs hc hev hm0 (hgc1 x e) (hgc2 x e)
  set P : ℝ := ∑ x, (π x)⁻¹ * ∑ e, Pxe x e with hP
  have hpi : ∀ x, 0 ≤ (π x)⁻¹ := fun x => (inv_pos.2 (hπ x)).le
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun x _ =>
    mul_nonneg (hpi x) (Finset.sum_nonneg fun e _ => hPxe0 x e)
  have hPE : ENNReal.ofReal P = ∑ x, ENNReal.ofReal ((π x)⁻¹) * ∑ e, ENNReal.ofReal (Pxe x e) := by
    rw [hP, ENNReal.ofReal_sum_of_nonneg fun x _ =>
      mul_nonneg (hpi x) (Finset.sum_nonneg fun e _ => hPxe0 x e)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.ofReal_mul (hpi x), ENNReal.ofReal_sum_of_nonneg fun e _ => hPxe0 x e]
  -- the left side is `ofReal P`
  have hL : ∑ x, ENNReal.ofReal ((π x)⁻¹) * ∑ e : Fin (Module.finrank ℝ (h x)),
      (ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ∫⁻ ξ, ENNReal.ofReal (m ξ) *
        ‖planeTransform (gsc ϖ β (φ x) (stdOrthonormalBasis ℝ (h x) e)) ξ‖ₑ ^ 2) = ENNReal.ofReal P := by
    rw [hPE]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    exact (hPxeE x e).symm
  rw [hL]
  -- the jets of `U`
  have hjetsq : ∀ x l z, jetS l (U x) z ^ 2 =
      ∑ e, ∑ w : DerivativeWord2 l, orderedDerivative w (Uc x e) z ^ 2 := by
    intro x l z
    unfold jetS
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    have h1 : ∀ w : DerivativeWord2 l, ‖orderedDerivative w (U x) z‖ ^ 2 =
        ∑ e, orderedDerivative w (Uc x e) z ^ 2 := by
      intro w
      rw [← sum_inner_sq (b x) (orderedDerivative w (U x) z)]
      refine Finset.sum_congr rfl fun e _ => ?_
      have key := congrFun (orderedDerivative_comp (innerSL ℝ (b x e)) w (hUs x)) z
      have hfun : (fun y => (innerSL ℝ (b x e)) (U x y)) = Uc x e := by
        funext y
        rw [innerSL_apply_apply]
        exact hUcinner x e y
      rw [hfun, innerSL_apply_apply] at key
      rw [← key]
    simp_rw [h1]
    exact Finset.sum_comm
  have hlint : ∀ x, ∀ l ≤ k, eLpNorm (jetS l (U x)) 2 volume ^ 2 ≤
      ∑ e, ENNReal.ofReal (Pxe x e) := by
    intro x l hl
    rw [eLpNorm_two_sq''' _ (jetS_continuous (hUs x)).aestronglyMeasurable]
    have e1 : ∀ z, ‖jetS l (U x) z‖ₑ ^ 2 =
        ∑ e, ∑ w : DerivativeWord2 l, ENNReal.ofReal (orderedDerivative w (Uc x e) z ^ 2) := by
      intro z
      rw [Real.enorm_of_nonneg (jetS_nonneg l (U x) z),
        ← ENNReal.ofReal_pow (jetS_nonneg l (U x) z), hjetsq,
        ENNReal.ofReal_sum_of_nonneg (fun e _ => Finset.sum_nonneg fun w _ => sq_nonneg _)]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun w _ => sq_nonneg _]
    simp_rw [e1]
    have hmeas : ∀ e (w : DerivativeWord2 l), Measurable fun z =>
        ENNReal.ofReal (orderedDerivative w (Uc x e) z ^ 2) := fun e w =>
      ENNReal.measurable_ofReal.comp
        ((AVRegularity.orderedDerivative_contDiff w (hUcs x e)).continuous.measurable.pow_const 2)
    rw [lintegral_finsetSum _ fun e _ => Finset.measurable_sum _ fun w _ => hmeas e w]
    refine Finset.sum_le_sum fun e _ => ?_
    rw [lintegral_finsetSum _ fun w _ => hmeas e w,
      jets_plancherel m hs hc hev (hgc1 x e) (hgc2 x e) l, hPxeE x e]
    refine mul_le_mul' le_rfl (lintegral_mono fun ξ => mul_le_mul' ?_ le_rfl)
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hmk l hl ξ
    have h2 := hm0 ξ
    calc (ξ 0 ^ 2 + ξ 1 ^ 2) ^ l * m ξ ^ 2 = ((ξ 0 ^ 2 + ξ 1 ^ 2) ^ l * m ξ) * m ξ := by ring
      _ ≤ 1 * m ξ := mul_le_mul_of_nonneg_right h1 h2
      _ = m ξ := one_mul _
  have hQ : ∀ l ≤ k, ∑ x, ENNReal.ofReal ((π x)⁻¹) * eLpNorm (jetS l (U x)) 2 volume ^ 2 ≤
      ENNReal.ofReal P := by
    intro l hl
    rw [hPE]
    exact Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl (hlint x l hl)
  -- the radius of the supports
  choose R0 hR0nn hR0 using fun x => exists_support_radius (hφc x)
  set R : ℝ := 1 + ∑ x, R0 x with hR
  have hsum0 : 0 ≤ ∑ x, R0 x := Finset.sum_nonneg fun x _ => hR0nn x
  have hRge : ∀ x, R0 x ≤ R := fun x => by
    have := Finset.single_le_sum (f := R0) (fun x _ => hR0nn x) (Finset.mem_univ x)
    linarith
  have hR1 : 1 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  have hRne : R ≠ 0 := hRpos.ne'
  set T : ∀ x, Vec 2 → h x := fun x z => qfun ϖ β R z • U x z with hT
  have hTt : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (T x) ∧ HasCompactSupport (T x) := fun x =>
    ⟨(qfun_contDiff ϖ β R).smul (hUs x), (hasCompactSupport_qfun ϖ β hRne).smul_right⟩
  have hjetT := weightedJet_smul_le π n k ϖ Cq hCq0 (qfun_contDiff ϖ β R)
    (fun i z => hCq i ϖ R hR1 hϖ0 hϖ1 z) hUs (ENNReal.ofReal P) hQ
  -- the pairing
  have hpairx : ∀ x, ∫ z, inner ℝ (φ x z) (T x z) = ∑ e, Pxe x e := by
    intro x
    have h1 : ∀ z, inner ℝ (φ x z) (T x z) = ∑ e, gc x e z * Uc x e z := by
      intro z
      by_cases hz : R0 x < ‖z‖
      · have h0 : φ x z = 0 := hR0 x z hz
        simp [h0, hgc, gsc]
      · rw [not_lt] at hz
        have hchi := chiR_eq_one hRpos (hz.trans (hRge x))
        have hq : qq ϖ β z * inner ℝ (φ x z) (U x z) = inner ℝ (Gv x z) (U x z) := by
          simp only [hGv, gvec]
          rw [inner_smul_left]
          simp
        change inner ℝ (φ x z) (qfun ϖ β R z • U x z) = _
        rw [inner_smul_right, qfun_eq, hchi, mul_one, hq, ← (b x).sum_inner_mul_inner (Gv x z) (U x z)]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [real_inner_comm (b x e) (Gv x z), hgc_eq x e z, hUcinner x e z]
    simp_rw [h1]
    rw [integral_finsetSum]
    intro e _
    exact (hgc2 x e).integrable_mul (hUc2 x e)
  have hpair : ∑ x, (π x)⁻¹ * ∫ z, inner ℝ (φ x z) (T x z) = P := by
    rw [hP]
    exact Finset.sum_congr rfl fun x _ => by rw [hpairx x]
  -- the conclusion
  by_cases hP00 : P = 0
  · rw [hP00]; simp
  have hPpos : 0 < P := lt_of_le_of_ne hP0 (Ne.symm hP00)
  have hCk := jetCoeff_nonneg k Cq
  set Bnd : ℝ := (jetCoeff k Cq + 1) * Real.sqrt P with hBnd
  have hBpos : 0 < Bnd := by positivity
  have hjet : weightedJetNorm π (-(n : ℝ)) k ϖ 1 (fun x _ wd z => orderedDerivative wd (T x) z) ≤
      ENNReal.ofReal Bnd := by
    refine hjetT.trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg hP0 (by norm_num), ← ENNReal.ofReal_mul hCk]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hBnd, ← Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have hcmp := cutoff_compact_test_pair_le π (n : ℝ) k ϖ 1 φ T hTt Bnd hBpos hjet
  rw [hpair, abs_of_nonneg hP0] at hcmp
  set D := AVRegularity.CycleWords.Assembly.negJetNorm π (n : ℝ) k ϖ 1 φ with hD
  by_cases hDtop : D = ⊤
  · rw [hDtop, ENNReal.mul_top (by simp; linarith)]
    simp
  have hDr : D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hDtop).symm
  rw [hDr, ← ENNReal.ofReal_mul hBpos.le, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hcmp
  have hfin := sq_le_of_le_mul_sqrt' hP0 (A := jetCoeff k Cq + 1) (D := D.toReal)
    (by simpa [hBnd, mul_assoc] using hcmp)
  rw [hDr, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_pow (by positivity)]
  exact ENNReal.ofReal_le_ofReal hfin

end AVRegularity.CycleWords.Seam.NegLowBand
end
end

section
/-! # The negative band of a moment is bounded by the negative jet norm

The multipliers `m_j = (1 + |ξ|²)^{-k} χ(ξ/(j+1))` converge to `(1 + |ξ|²)^{-k}`; Fatou's lemma
passes to the limit in the duality inequality of `neg_dual`.
-/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard AVRegularity.CycleWords.Seam
  Filter Topology
open scoped ENNReal

namespace AVRegularity.CycleWords.Seam.NegLowBand

open AVRegularity.CycleWords.Seam.YoungKernel

universe u v

/-- The multiplier of the duality. -/
def mneg (k : ℕ) (R : ℝ) (ξ : Vec 2) : ℝ := ((1 + vecDot ξ ξ) ^ k)⁻¹ * chiR R ξ

theorem vecDot_eq (ξ : Vec 2) : vecDot ξ ξ = ξ 0 ^ 2 + ξ 1 ^ 2 := by
  simp [vecDot, Fin.sum_univ_two, sq]

theorem one_add_vecDot_pos (ξ : Vec 2) : 0 < 1 + vecDot ξ ξ := by
  rw [vecDot_eq]; positivity

theorem mneg_contDiff (k : ℕ) (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (mneg k R) := by
  unfold mneg
  refine ContDiff.mul ?_ (chiR_contDiff R)
  refine ContDiff.inv ?_ fun ξ => (pow_pos (one_add_vecDot_pos ξ) k).ne'
  refine ContDiff.pow (contDiff_const.add ?_) k
  simp only [vecDot_eq]
  fun_prop

theorem mneg_compact (k : ℕ) {R : ℝ} (hR : R ≠ 0) : HasCompactSupport (mneg k R) :=
  (chiR_compact hR).mul_left

theorem chiR_even (R : ℝ) (ξ : Vec 2) : chiR R (-ξ) = chiR R ξ := by
  unfold chiR chi
  rw [smul_neg]
  exact chiBump.neg _

theorem chiR_nonneg (R : ℝ) (ξ : Vec 2) : 0 ≤ chiR R ξ := chiBump.nonneg

theorem chiR_le_one (R : ℝ) (ξ : Vec 2) : chiR R ξ ≤ 1 := chiBump.le_one

theorem mneg_even (k : ℕ) (R : ℝ) (ξ : Vec 2) : mneg k R (-ξ) = mneg k R ξ := by
  unfold mneg
  rw [chiR_even]
  congr 3
  simp [vecDot_eq]

theorem mneg_nonneg (k : ℕ) (R : ℝ) (ξ : Vec 2) : 0 ≤ mneg k R ξ := by
  unfold mneg
  have := one_add_vecDot_pos ξ
  have := chiR_nonneg R ξ
  positivity

theorem mneg_mk (k : ℕ) (R : ℝ) (l : ℕ) (hl : l ≤ k) (ξ : Vec 2) :
    (ξ 0 ^ 2 + ξ 1 ^ 2) ^ l * mneg k R ξ ≤ 1 := by
  have ha : 0 ≤ ξ 0 ^ 2 + ξ 1 ^ 2 := by positivity
  have hp := one_add_vecDot_pos ξ
  rw [vecDot_eq] at hp
  have h1 : (ξ 0 ^ 2 + ξ 1 ^ 2) ^ l ≤ (1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ k := by
    calc (ξ 0 ^ 2 + ξ 1 ^ 2) ^ l ≤ (1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ l :=
          pow_le_pow_left₀ ha (by linarith) l
      _ ≤ (1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ k := pow_le_pow_right₀ (by linarith) hl
  have hk : 0 < (1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ k := pow_pos hp k
  unfold mneg
  rw [vecDot_eq]
  have hc0 := chiR_nonneg R ξ
  have hc1 := chiR_le_one R ξ
  calc (ξ 0 ^ 2 + ξ 1 ^ 2) ^ l * (((1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ k)⁻¹ * chiR R ξ)
      ≤ (1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ k * (((1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ k)⁻¹ * 1) := by
        refine mul_le_mul h1 (mul_le_mul_of_nonneg_left hc1 (inv_nonneg.2 hk.le))
          (mul_nonneg (inv_nonneg.2 hk.le) hc0) hk.le
    _ = 1 := by rw [mul_one, mul_inv_cancel₀ hk.ne']

theorem mneg_tendsto (k : ℕ) (ξ : Vec 2) :
    Tendsto (fun j : ℕ => mneg k ((j : ℝ) + 1) ξ) atTop (𝓝 (((1 + vecDot ξ ξ) ^ k)⁻¹)) := by
  have h0 : Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹ • ξ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    simpa using h1.smul_const ξ
  have h2 := (chi_contDiff.continuous.tendsto 0).comp h0
  have h3 := h2.const_mul (((1 + vecDot ξ ξ) ^ k)⁻¹)
  rw [chi_zero, mul_one] at h3
  exact h3

/-- **The negative band of one moment.** -/
theorem neg_total (n k : ℕ) (β : ℕ × ℕ) (hβ : β.1 + β.2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      (π : ι → ℝ), (∀ x, 0 < π x) → ∀ ϖ : ℝ, 0 < ϖ → ϖ ≤ 1 →
      ∀ φ : ∀ x, Vec 2 → h x, (∀ x, StronglyMeasurable (φ x)) →
      (∀ x, HasCompactSupport (φ x)) → (∀ x, MemLp (φ x) 2 volume) →
      ∑ x, ENNReal.ofReal ((π x)⁻¹) * ∑ e : Fin (Module.finrank ℝ (h x)),
          ∫⁻ ξ, negBandIntegrand k (gsc ϖ β (φ x) (stdOrthonormalBasis ℝ (h x) e)) ξ ≤
        ENNReal.ofReal ((2 * Real.pi) ^ 2) *
          (ENNReal.ofReal C * AVRegularity.CycleWords.Assembly.negJetNorm π (n : ℝ) k ϖ 1 φ) ^ 2 := by
  obtain ⟨C, hC, hdual⟩ := neg_dual.{u, v} n k β hβ
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ ϖ hϖ0 hϖ1 φ hφm hφc hφ2
  set D := AVRegularity.CycleWords.Assembly.negJetNorm π (n : ℝ) k ϖ 1 φ with hD
  set b : ∀ x, OrthonormalBasis (Fin (Module.finrank ℝ (h x))) ℝ (h x) :=
    fun x => stdOrthonormalBasis ℝ (h x) with hb
  have hgi : ∀ x e, Integrable (gsc ϖ β (φ x) (b x e)) volume := fun x e =>
    gsc_integrable ϖ β (hφm x) (hφc x) (hφ2 x) _
  set a : ∀ x, Fin (Module.finrank ℝ (h x)) → Vec 2 → ℝ≥0∞ :=
    fun x e ξ => ‖planeTransform (gsc ϖ β (φ x) (b x e)) ξ‖ₑ ^ 2 with ha
  have ham : ∀ x e, Measurable (a x e) := fun x e =>
    (Ft_continuous (hgi x e)).measurable.enorm.pow_const 2
  set A : Vec 2 → ℝ≥0∞ := fun ξ => ∑ x, ENNReal.ofReal ((π x)⁻¹) * ∑ e,
    ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * a x e ξ with hA
  have hAm : Measurable A := by
    refine Finset.measurable_sum _ fun x _ => (Finset.measurable_sum _ fun e _ => ?_).const_mul _
    exact (ham x e).const_mul _
  -- the duality inequality for `m_j` is an integral against `A`
  have hdj : ∀ j : ℕ, ∫⁻ ξ, ENNReal.ofReal (mneg k ((j : ℝ) + 1) ξ) * A ξ ≤
      (ENNReal.ofReal C * D) ^ 2 := by
    intro j
    have hR : ((j : ℝ) + 1) ≠ 0 := by positivity
    have h1 := hdual π hπ ϖ hϖ0 hϖ1 φ hφm hφc hφ2 (mneg k ((j : ℝ) + 1)) (mneg_contDiff k _)
      (mneg_compact k hR) (mneg_even k _) (mneg_nonneg k _) (fun l hl => mneg_mk k _ l hl)
    refine le_trans (le_of_eq ?_) h1
    have hmeas : ∀ x e, Measurable fun ξ => ENNReal.ofReal (mneg k ((j : ℝ) + 1) ξ) * a x e ξ :=
      fun x e => (ENNReal.measurable_ofReal.comp (mneg_contDiff k _).continuous.measurable).mul
        (ham x e)
    have e1 : ∀ ξ, ENNReal.ofReal (mneg k ((j : ℝ) + 1) ξ) * A ξ =
        ∑ x, ∑ e, (ENNReal.ofReal ((π x)⁻¹) * ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹)) *
          (ENNReal.ofReal (mneg k ((j : ℝ) + 1) ξ) * a x e ξ) := by
      intro ξ
      simp only [hA]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      ring
    calc ∫⁻ ξ, ENNReal.ofReal (mneg k ((j : ℝ) + 1) ξ) * A ξ
        = ∫⁻ ξ, ∑ x, ∑ e, (ENNReal.ofReal ((π x)⁻¹) * ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹)) *
          (ENNReal.ofReal (mneg k ((j : ℝ) + 1) ξ) * a x e ξ) := lintegral_congr e1
      _ = ∑ x, ∑ e, (ENNReal.ofReal ((π x)⁻¹) * ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹)) *
          ∫⁻ ξ, ENNReal.ofReal (mneg k ((j : ℝ) + 1) ξ) * a x e ξ := by
          rw [lintegral_finsetSum _ (fun x _ => Finset.measurable_sum _ fun e _ =>
            (hmeas x e).const_mul _)]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [lintegral_finsetSum _ (fun e _ => (hmeas x e).const_mul _)]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [lintegral_const_mul _ (hmeas x e)]
      _ = _ := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [mul_assoc]
  -- Fatou
  have hlim : ∀ ξ, Tendsto (fun j : ℕ => ENNReal.ofReal (mneg k ((j : ℝ) + 1) ξ) * A ξ) atTop
      (𝓝 (ENNReal.ofReal (((1 + vecDot ξ ξ) ^ k)⁻¹) * A ξ)) := fun ξ =>
    ENNReal.Tendsto.mul_const ((ENNReal.continuous_ofReal.tendsto _).comp (mneg_tendsto k ξ))
      (Or.inl (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos (one_add_vecDot_pos ξ) k))).ne')
  have hfatou : ∫⁻ ξ, ENNReal.ofReal (((1 + vecDot ξ ξ) ^ k)⁻¹) * A ξ ≤ (ENNReal.ofReal C * D) ^ 2 := by
    calc ∫⁻ ξ, ENNReal.ofReal (((1 + vecDot ξ ξ) ^ k)⁻¹) * A ξ
        = ∫⁻ ξ, liminf (fun j : ℕ => ENNReal.ofReal (mneg k ((j : ℝ) + 1) ξ) * A ξ) atTop :=
          lintegral_congr fun ξ => (hlim ξ).liminf_eq.symm
      _ ≤ liminf (fun j : ℕ => ∫⁻ ξ, ENNReal.ofReal (mneg k ((j : ℝ) + 1) ξ) * A ξ) atTop :=
          lintegral_liminf_le fun j =>
            (ENNReal.measurable_ofReal.comp (mneg_contDiff k _).continuous.measurable).mul hAm
      _ ≤ _ := Filter.liminf_le_of_frequently_le' (Filter.Eventually.frequently
          (Filter.Eventually.of_forall hdj))
  -- the left side
  have hneg : ∀ x e ξ, negBandIntegrand k (gsc ϖ β (φ x) (b x e)) ξ =
      ENNReal.ofReal (((1 + vecDot ξ ξ) ^ k)⁻¹) * a x e ξ := by
    intro x e ξ
    simp only [negBandIntegrand, ha]
    rw [ENNReal.ofReal_mul (inv_nonneg.2 (pow_pos (one_add_vecDot_pos ξ) k).le),
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hnm : ∀ x e, Measurable fun ξ => ENNReal.ofReal (((1 + vecDot ξ ξ) ^ k)⁻¹) * a x e ξ :=
    fun x e => (ENNReal.measurable_ofReal.comp (((continuous_const.add vecDot_cont).pow k).inv₀
      fun ξ => (pow_pos (one_add_vecDot_pos ξ) k).ne').measurable).mul (ham x e)
  have hS : ∫⁻ ξ, ENNReal.ofReal (((1 + vecDot ξ ξ) ^ k)⁻¹) * A ξ =
      ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ∑ x, ENNReal.ofReal ((π x)⁻¹) * ∑ e : Fin (Module.finrank ℝ (h x)),
        ∫⁻ ξ, negBandIntegrand k (gsc ϖ β (φ x) (b x e)) ξ := by
    have e1 : ∀ ξ, ENNReal.ofReal (((1 + vecDot ξ ξ) ^ k)⁻¹) * A ξ =
        ∑ x, ∑ e, (ENNReal.ofReal ((π x)⁻¹) * ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹)) *
          (ENNReal.ofReal (((1 + vecDot ξ ξ) ^ k)⁻¹) * a x e ξ) := by
      intro ξ
      simp only [hA]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      ring
    calc ∫⁻ ξ, ENNReal.ofReal (((1 + vecDot ξ ξ) ^ k)⁻¹) * A ξ
        = ∫⁻ ξ, ∑ x, ∑ e, (ENNReal.ofReal ((π x)⁻¹) * ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹)) *
          (ENNReal.ofReal (((1 + vecDot ξ ξ) ^ k)⁻¹) * a x e ξ) := lintegral_congr e1
      _ = ∑ x, ∑ e, (ENNReal.ofReal ((π x)⁻¹) * ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹)) *
          ∫⁻ ξ, ENNReal.ofReal (((1 + vecDot ξ ξ) ^ k)⁻¹) * a x e ξ := by
          rw [lintegral_finsetSum _ (fun x _ => Finset.measurable_sum _ fun e _ =>
            (hnm x e).const_mul _)]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [lintegral_finsetSum _ (fun e _ => (hnm x e).const_mul _)]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [lintegral_const_mul _ (hnm x e)]
      _ = _ := by
          simp_rw [hneg]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          ring
  rw [hS] at hfatou
  have hX : ENNReal.ofReal ((2 * Real.pi) ^ 2) * ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
  calc ∑ x, ENNReal.ofReal ((π x)⁻¹) * ∑ e : Fin (Module.finrank ℝ (h x)),
        ∫⁻ ξ, negBandIntegrand k (gsc ϖ β (φ x) (stdOrthonormalBasis ℝ (h x) e)) ξ
      = ENNReal.ofReal ((2 * Real.pi) ^ 2) * (ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) *
        ∑ x, ENNReal.ofReal ((π x)⁻¹) * ∑ e : Fin (Module.finrank ℝ (h x)),
          ∫⁻ ξ, negBandIntegrand k (gsc ϖ β (φ x) (stdOrthonormalBasis ℝ (h x) e)) ξ) := by
        rw [← mul_assoc, hX, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hfatou

end AVRegularity.CycleWords.Seam.NegLowBand
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # The fast remainder on compact data, the core

`s3b_compact_core`: for a chain from compactly supported data, at slots whose last slot carries
`K_max` derivatives, the output norm of `Z(f) − R(μf)` is at most
`X₁ C₅ N + X₂ E_a (N + C₁ C₅ N)`, `N` the negative norm of the datum. The hypotheses at the fixed
block: the chain discard on compact data (`X₁`), the quiet margin on the plane (`X₂ (E_a ‖·‖_neg +
‖μ₂ ·‖_mom)`), the lossless low passes `μ` and `μ₂` (`C₅`, `C₅'`) and the negative norm
by the moment norm (`C₁`).

Route. Compact `g_j → μf` in the moment norm (`compactDensity`; `μf` has finite moment
norm by the lossless low pass). `Z(f) − Z(g_j)` is the chain of `f − g_j` (`isPlaneChain_trunc_sub`), so
`‖Z(f) − R(g_j)‖ ≤ ‖Z(g_j) − R(g_j)‖ + ‖Z(f − g_j)‖` (`discard_step_le`). The first term is the
discard; the second is the quiet margin, with `‖f − g_j‖_neg ≤ N + C₁‖g_j‖_mom` and
`μ₂(f − g_j) = μ₂(μf − g_j)` (`μ₂μ = μ₂`), which tends to `0`. Fatou in `j`: the jets of
`R(g_j)` converge to those of `R(μf)` (`retainedMap_orderedDerivative_tendsto`). -/

open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

universe u v

/-- The cutoff of a difference of square-integrable functions. -/
theorem s3b_fourierCutoff_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : Vec 2 → ℝ) (R : ℝ) (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m) {g₁ g₂ : Vec 2 → E} (h₁ : MemLp g₁ 2 volume)
    (h₂ : MemLp g₂ 2 volume) :
    fourierCutoff m (fun z => g₁ z - g₂ z) =
      fun y => fourierCutoff m g₁ y - fourierCutoff m g₂ y := by
  funext y
  unfold fourierCutoff
  rw [← integral_sub (s3b_cutoff_integrand_integrable m R hm hs h₁ y)
    (s3b_cutoff_integrand_integrable m R hm hs h₂ y)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_sub]

/-- **The core**: the fast remainder of a chain from compactly supported data. -/
theorem s3b_compact_core {K : ScalarConstants}
    {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D Nw Kmax pout k : ℕ} (hD : 2 ≤ D) {d Ks : Fin Nw → ℕ} {π : ι → ℝ} (hπ : ∀ x, 0 < π x)
    {letters : Fin Nw → CycleLetter ι h D} (hslow : ∀ i, (letters i).slow = Ks i)
    {η S ηg rstar t₀ ϖ : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {X₀ : Vec 2} {χlo μ μ₂ : Vec 2 → ℝ} (hμ : IsSeamLowPass μ)
    (hμ₂s : ContDiff ℝ (⊤ : ℕ∞) μ₂) (hμ₂c : HasCompactSupport μ₂) (hμ₂e : ∀ θ, μ₂ (-θ) = μ₂ θ)
    (hμ₂R : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ₂ ξ = 0)
    (hprod : ∀ θ, μ₂ θ * μ θ = μ₂ θ)
    {R : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x)}
    (hR : IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R) (hr : 0 < 2 * K.ξlo * Real.sqrt η)
    {κ : Fin (Nw + 1) → ι → ℕ} (hκf : ∀ x, Kmax ≤ κ (Fin.last Nw) x) (hκ : IsWordSlots letters κ)
    (hWc : IsWordSlots letters (cappedWordSlots κ Kmax d))
    {f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x)}
    {u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x)}
    {w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)}
    (hcd : IsCompactDatum f)
    (hch : IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f
      (fun _ _ _ => 0) u w)
    {X₁ X₂ Ea : ℝ≥0∞} (hX₁ : X₁ ≠ ⊤) (hX₂ : X₂ ≠ ⊤) (hEa : Ea ≠ ⊤) {C₁ C₅ C₅' : ℝ}
    (hEx : ∀ fk : ∀ x, PlaneHk Set.univ (cappedWordSlots κ Kmax d 0 x) (h x), IsCompactDatum fk →
      ∃ (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (cappedWordSlots κ Kmax d j x) (h x))
        (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (cappedWordSlots κ Kmax d j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κ Kmax d) t₀ (t₀ + S)
          v fk (fun _ _ _ => 0) uk wk)
    (hDis : ∀ (fk : ∀ x, PlaneHk Set.univ (cappedWordSlots κ Kmax d 0 x) (h x))
      (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κ Kmax d j x) (h x))
      (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κ Kmax d j x + 1) (h x)),
      IsCompactDatum fk →
      IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κ Kmax d) t₀ (t₀ + S) v
        fk (fun _ _ _ => 0) uk wk →
      jetOutputNorm π pout Kmax ϖ rstar
          (fun x a wd z => planeJetOrder (uk (Fin.last Nw) x (t₀ + S)) a wd z -
            orderedDerivative wd (R (fun x' => planeValue (fk x')) x) z) ≤
        X₁ * momentNorm π (wordReserveN pout Ks) ϖ (fun x => planeValue (fk x)))
    (hCol : ∀ (f' : ∀ x, PlaneHk Set.univ (cappedWordSlots κ Kmax d 0 x) (h x))
      (u' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κ Kmax d j x) (h x))
      (w' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κ Kmax d j x + 1) (h x)),
      IsCompactDatum f' →
      IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κ Kmax d) t₀ (t₀ + S) v
        f' (fun _ _ _ => 0) u' w' →
      jetOutputNorm π pout Kmax ϖ rstar
          (fun x a wd z => planeJetOrder (u' (Fin.last Nw) x (t₀ + S)) a wd z) ≤
        X₂ * (Ea * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1
            (fun x => planeValue (f' x)) +
          momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ₂ (planeValue (f' x)))))
    (hB5 : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, MemLp (Gf x) 2 volume) →
      momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ (Gf x)) ≤
        ENNReal.ofReal C₅ * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf)
    (hB5' : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, MemLp (Gf x) 2 volume) →
      momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ₂ (Gf x)) ≤
        ENNReal.ofReal C₅' * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf)
    (hP1 : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (Gf x) volume) →
      negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf ≤
        ENNReal.ofReal C₁ * momentNorm π (wordReserveN pout Ks) ϖ Gf) :
    jetOutputNorm π pout Kmax ϖ rstar
        (fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
          orderedDerivative wd (R (fun x' => fourierCutoff μ (planeValue (f x'))) x) z) ≤
      X₁ * (ENNReal.ofReal C₅ * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1
          (fun x => planeValue (f x))) +
        X₂ * (Ea * (negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1
          (fun x => planeValue (f x)) + ENNReal.ofReal C₁ * (ENNReal.ofReal C₅ *
            negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 (fun x => planeValue (f x))))) := by
  classical
  set n := wordReserveN pout Ks with hn
  set F : ∀ x, Vec 2 → h x := fun x => planeValue (f x) with hFdef
  set NN := negJetNorm π (n : ℝ) k ϖ 1 F with hNN
  have hle : ∀ j x, cappedWordSlots κ Kmax d j x ≤ κ j x := cappedWordSlots_le_original κ Kmax d
  have hlast : ∀ x, cappedWordSlots κ Kmax d (Fin.last Nw) x = Kmax :=
    fun x => cappedWordSlots_last κ Kmax d x (hκf x)
  -- the datum
  choose φ hφ1 hφ2 hfφ using hcd
  have hφ : IsCompactFamily φ := fun x => ⟨hφ1 x, hφ2 x⟩
  have hFm : ∀ x, AEStronglyMeasurable (F x) volume :=
    fun x => planeJetOrder_aestronglyMeasurable (f x) 0 _
  have hF2 : ∀ x, MemLp (F x) 2 volume := fun x => planeJetOrder_memLp (Nat.zero_le _) (f x) _
  have hF1 : ∀ x, Integrable (F x) volume := fun x =>
    ((hφ x).1.continuous.integrable_of_hasCompactSupport (hφ x).2).congr (hfφ x).symm
  have hmF : momentNorm π n ϖ F < ⊤ := by
    rw [momentNorm_congr_ae' π n ϖ hfφ]
    exact momentNorm_lt_top_of_compact π n ϖ hφ
  have hNNfin : NN < ⊤ := (hP1 F hFm).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmF)
  set μF : ∀ x, Vec 2 → h x := fun x => fourierCutoff μ (F x) with hμFdef
  have hμF2 : ∀ x, MemLp (μF x) 2 volume := fun x =>
    fourierCutoff_memLp_of_memLp μ (Real.pi / 2) hμ.supp hμ.smooth (hF2 x)
  have hμFm : momentNorm π n ϖ μF ≤ ENNReal.ofReal C₅ * NN := hB5 F hF2
  have hμFfin : momentNorm π n ϖ μF < ⊤ :=
    hμFm.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hNNfin)
  -- compact approximants of `μf` and their chains
  obtain ⟨φs, hφs, hconv⟩ := compactDensity.{u, v}.2 μF fun x => (hμF2 x).aestronglyMeasurable
  have hconvN := hconv π n ϖ hμFfin
  have hlift : ∀ j x, ∃ fk : PlaneHk Set.univ (cappedWordSlots κ Kmax d 0 x) (h x),
      planeValue fk =ᵐ[volume] φs j x :=
    fun j x => compactDensity.{u, v}.1 _ (φs j x) (hφs j x).1 (hφs j x).2
  choose fk hfk using hlift
  have hcdk : ∀ j, IsCompactDatum (fk j) :=
    fun j x => ⟨φs j x, (hφs j x).1, (hφs j x).2, hfk j x⟩
  choose uk wk huk using fun j => hEx (fk j) (hcdk j)
  have hφs2 : ∀ j x, MemLp (φs j x) 2 volume :=
    fun j x => (hφs j x).1.continuous.memLp_of_hasCompactSupport (hφs j x).2
  have hφsm : ∀ j x, AEStronglyMeasurable (φs j x) volume :=
    fun j x => (hφs j x).1.continuous.aestronglyMeasurable
  -- one approximant
  have hstep : ∀ j, jetOutputNorm π pout Kmax ϖ rstar
      (fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
        orderedDerivative wd (R (φs j) x) z) ≤
      X₁ * momentNorm π n ϖ (φs j) +
        X₂ * (Ea * (NN + ENNReal.ofReal C₁ * momentNorm π n ϖ (φs j)) +
          ENNReal.ofReal C₅' * (ENNReal.ofReal C₁ *
            momentNorm π n ϖ (fun x z => μF x z - φs j x z))) := by
    intro j
    -- the discard of the approximant
    have hA := hDis (fk j) (uk j) (wk j) (hcdk j) (huk j)
    have hRk : R (fun x' => planeValue (fk j x')) = R (φs j) := hR.congr _ _ (hfk j)
    have hmk : momentNorm π n ϖ (fun x => planeValue (fk j x)) = momentNorm π n ϖ (φs j) :=
      momentNorm_congr_ae' π n ϖ (hfk j)
    rw [hRk, hmk] at hA
    -- the difference chain
    have hdiff := isPlaneChain_trunc_sub hD G letters X₀ (ϖ * ηg) t₀ (t₀ + S) v κ
      (cappedWordSlots κ Kmax d) hle hκ hWc f u w (fk j) (uk j) (wk j) hch (huk j)
    have hval : ∀ x, planeValue ((1 : ℝ) • truncatePlaneHk (hle 0 x) (f x) + (-1 : ℝ) • fk j x)
        =ᵐ[volume] fun z => F x z - φs j x z := by
      intro x
      filter_upwards [planeJetOrder_trunc_sub_ae (hle 0 x) (f x) (fk j x) (Nat.zero_le _)
        (fun i => i.elim0), hfk j x] with z h1 h2
      rw [planeValue, h1]
      change planeValue (f x) z - planeValue (fk j x) z = _
      rw [h2]
    have hcdD : IsCompactDatum fun x =>
        (1 : ℝ) • truncatePlaneHk (hle 0 x) (f x) + (-1 : ℝ) • fk j x := fun x =>
      ⟨fun z => φ x z - φs j x z, (hφ x).1.sub (hφs j x).1, (hφ x).2.sub (hφs j x).2, by
        filter_upwards [hval x, hfφ x] with z h1 h2
        rw [h1]
        show planeValue (f x) z - φs j x z = _
        rw [h2]⟩
    have hDc := hCol _ _ _ hcdD hdiff
    have hneg : negJetNorm π (n : ℝ) k ϖ 1 (fun x => planeValue
        ((1 : ℝ) • truncatePlaneHk (hle 0 x) (f x) + (-1 : ℝ) • fk j x)) ≤
        NN + ENNReal.ofReal C₁ * momentNorm π n ϖ (φs j) := by
      rw [negJetNorm_congr_ae π _ k ϖ 1 hval]
      exact (s3b_negJetNorm_sub_le π _ k ϖ 1 F (φs j) hF2 (hφs2 j)).trans
        (add_le_add le_rfl (hP1 (φs j) (hφsm j)))
    have hlow : momentNorm π n ϖ (fun x => fourierCutoff μ₂ (planeValue
        ((1 : ℝ) • truncatePlaneHk (hle 0 x) (f x) + (-1 : ℝ) • fk j x))) ≤
        ENNReal.ofReal C₅' * (ENNReal.ofReal C₁ *
          momentNorm π n ϖ (fun x z => μF x z - φs j x z)) := by
      have heq : ∀ x, fourierCutoff μ₂ (planeValue
          ((1 : ℝ) • truncatePlaneHk (hle 0 x) (f x) + (-1 : ℝ) • fk j x)) =ᵐ[volume]
          fourierCutoff μ₂ (fun z => μF x z - φs j x z) := by
        intro x
        rw [fourierCutoff_congr_ae' μ₂ (hval x),
          s3b_fourierCutoff_sub μ₂ (Real.pi / 2) hμ₂R hμ₂s (hF2 x) (hφs2 j x),
          s3b_fourierCutoff_sub μ₂ (Real.pi / 2) hμ₂R hμ₂s (hμF2 x) (hφs2 j x)]
        filter_upwards [s3b_fourierCutoff_comp hμ.smooth hμ.compact hμ.even hμ₂s hμ₂c hμ₂e hprod
          (hF1 x) (hF2 x)] with z hz
        simp only [hμFdef, hz]
      rw [momentNorm_congr_ae' π n ϖ heq]
      refine (hB5' _ fun x => (hμF2 x).sub (hφs2 j x)).trans (mul_le_mul_right ?_ _)
      exact hP1 _ fun x => (hμF2 x).aestronglyMeasurable.sub (hφsm j x)
    have hDb := hDc.trans (mul_le_mul_right (add_le_add (mul_le_mul_right hneg _) hlow) _)
    exact discard_step_le π pout Kmax ϖ rstar (hle (Fin.last Nw)) hlast
      (fun x => u (Fin.last Nw) x (t₀ + S)) (fun x => uk j (Fin.last Nw) x (t₀ + S))
      (fun x => R (φs j) x) (fun x M => (hR.band _ x).1 M) hA hDb
  -- the retained map along the approximants
  have hslowF : (fun i => (letters i).slow) = Ks := funext hslow
  have hlim0 : Tendsto (fun j => momentNorm π (wordReserveN 0 fun i => (letters i).slow) ϖ
      (fun x z => μF x z - φs j x z)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconvN
      (fun j => zero_le) (fun j => ?_)
    rw [hslowF]
    exact momentNorm_mono (by rw [hn]; unfold wordReserveN; omega) _ _ _
  have hRlim : ∀ x a (wd : DerivativeWord2 a) z,
      Tendsto (fun j => orderedDerivative wd (R (φs j) x) z) atTop
        (𝓝 (orderedDerivative wd (R μF x) z)) :=
    fun x a wd z => retainedMap_orderedDerivative_tendsto amplitudePlancherel hR hr hπ μF φs
      (fun x => (hμF2 x).aestronglyMeasurable) hφsm hlim0 x a wd z
  -- Fatou
  have hfatou := jetOutputNorm_le_liminf π pout Kmax ϖ rstar
    (fun j x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
      orderedDerivative wd (R (φs j) x) z)
    (fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
      orderedDerivative wd (R μF x) z)
    (fun j x a wd => (planeJetOrder_aestronglyMeasurable _ a wd).sub
      (orderedDerivative_continuous wd ((hR.band _ x).1 a)).aestronglyMeasurable)
    (fun x a wd => (planeJetOrder_aestronglyMeasurable _ a wd).sub
      (orderedDerivative_continuous wd ((hR.band _ x).1 a)).aestronglyMeasurable)
    (fun x a wd z => tendsto_const_nhds.sub (hRlim x a wd z))
  -- the limit of the bounds
  have hmφ := momentNorm_tendsto π n ϖ μF φs hμFfin hconvN
  have hW : Tendsto (fun j => X₁ * momentNorm π n ϖ (φs j) +
      X₂ * (Ea * (NN + ENNReal.ofReal C₁ * momentNorm π n ϖ (φs j)) +
        ENNReal.ofReal C₅' * (ENNReal.ofReal C₁ *
          momentNorm π n ϖ (fun x z => μF x z - φs j x z)))) atTop
      (𝓝 (X₁ * momentNorm π n ϖ μF + X₂ * (Ea * (NN + ENNReal.ofReal C₁ * momentNorm π n ϖ μF) +
        ENNReal.ofReal C₅' * (ENNReal.ofReal C₁ * 0)))) := by
    refine (ENNReal.Tendsto.const_mul hmφ (Or.inr hX₁)).add
      (ENNReal.Tendsto.const_mul ?_ (Or.inr hX₂))
    refine (ENNReal.Tendsto.const_mul (tendsto_const_nhds.add
      (ENNReal.Tendsto.const_mul hmφ (Or.inr ENNReal.ofReal_ne_top))) (Or.inr hEa)).add ?_
    exact ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul hconvN
      (Or.inr ENNReal.ofReal_ne_top)) (Or.inr ENNReal.ofReal_ne_top)
  calc _ ≤ _ := hfatou
    _ ≤ liminf (fun j => X₁ * momentNorm π n ϖ (φs j) +
          X₂ * (Ea * (NN + ENNReal.ofReal C₁ * momentNorm π n ϖ (φs j)) +
            ENNReal.ofReal C₅' * (ENNReal.ofReal C₁ *
              momentNorm π n ϖ (fun x z => μF x z - φs j x z)))) atTop :=
        liminf_le_liminf (Filter.Eventually.of_forall hstep)
    _ = _ := hW.liminf_eq
    _ ≤ _ := by
        simp only [mul_zero, add_zero]
        exact add_le_add (mul_le_mul_right hμFm _) (mul_le_mul_right (mul_le_mul_right
          (add_le_add le_rfl (mul_le_mul_right hμFm _)) _) _)

end AVRegularity.CycleWords.Seam
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Seam

/-! # Quiet margin fibre bound: the plain pass on one frame, with negative input

`b1_plain_stage_frame_neg`: `plain_stage_frame` from a start `a₁ ∈ [a, b]`, with the
scaled stage values at `a₁` measured by their pairings with the tests of their order (`X_i`),
through `b1_plain_pass_neg` on `[a₁, b]` (the stage curves, the adjoint curves and the
representation of the sources restricted to `[a₁, b]`). -/

open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

universe u v

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The plain pass on one frame, with negative input.** -/
theorem b1_plain_stage_frame_neg {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (d : Fin Nw → ℕ) (s₀ : ℕ) (hs₀ : (Finset.univ.sup d) + 3 ≤ s₀)
    (hlet : ∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l)
    (hJ : Finset.univ.sup d ≤ F.J)
    (hM : ∀ (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ),
      ∃ (Dθ : ℝ → RawJet2 1 ℂ) (src : ℝ → Vec 2 → ℂ)
        (Fl : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)),
        MemLp (Function.uncurry src) 2
          ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube)) ∧
        (∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Fl p.1 p.2 k) 2
          ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube))) ∧
        (∀ᵐ r ∂volume.restrict (Icc F.a F.b),
          src r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralSource F θ j x e β r ∧
          Fl r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralFlux F θ j x e β r) ∧
        IsCellSolution (Icc F.a F.b)
          (fibreCoefficients F.η F.G F.v (planeFibreFrequency F.η θ) (fun _ => 0)) src Fl Dθ ∧
        ∀ t ∈ Icc F.a F.b, cellValue Dθ t =ᵐ[volume.restrict AVenhance.unitCube]
          planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x t) y)))
    (B : ℝ) (hB : 0 ≤ B)
    (hprov : ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (k k' : ℕ), k' < k →
      ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
        ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k') ℂ,
          (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
            =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
              ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
                star (b1wTestTransform F θ i i' r (fun y => star
                  (torusHigherClassicalValue (b1wLadderAt Nw s₀ d Ks k) (ψ i) y)) y)) ∧
          ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)
    (V : ℝ) (hb : ∀ t x, ∑ i, F.v t x i ^ 2 ≤ V ^ 2) (κ : ℝ → ℝ → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hκ : IsFibreKernel (b1wCoeff F θ) F.piece.hGm V F.piece.hv.1 hb F.a F.b A κ)
    (Ca : ℝ) (hCa : 0 ≤ Ca)
    (hadj : ∀ k < b1wM Nw m Ks, ∀ t ∈ Icc F.a F.b, ∀ ψ : TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
      ∃ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ)
        (U : ℝ → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ),
        CellWeakHilbertCurve F.a t Ψv Ψs (fun r =>
          -cellDualDerivative
            (cellAdjointCoefficients ⟨fun s _ => F.G s, F.v, fun k => ((θ k : ℝ) : ℂ), 0⟩)
            F.piece.hGm V (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) r (Ψs r) 0 0) ∧
        Ψv t = torusHkValueCLM ψ ∧
        ∀ r ∈ Icc F.a t, torusHkValueCLM (U r) = Ψv r ∧ ‖U r‖ ≤ Ca * κ r t * ‖ψ‖)
    (a₁ : ℝ) (ha₁ : a₁ ∈ Icc F.a F.b) (Xn : B1WIndex ι h Nw m Ks → ℝ)
    (hX : ∀ k < b1wM Nw m Ks, ∀ i, b1wSt i = k → ∀ w : ComplexCellL2,
      (w : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] stageScaled F θ i a₁ →
      ∀ φ : TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
        ‖cellComplexPair w (torusHkValueCLM φ)‖ ≤ Xn i * ‖φ‖) :
    ∃ Wc : B1WIndex ι h Nw m Ks → ℝ → ComplexCellL2,
      (∀ i, ∀ t ∈ Icc F.a F.b,
        (Wc i t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] stageScaled F θ i t) ∧
      ∀ k < b1wM Nw m Ks, ∀ t ∈ Icc a₁ F.b,
        ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
        ‖∑ i ∈ stageSet b1wSt k, cellComplexPair (Wc i t) (torusHkValueCLM (ψ i))‖ ≤
          plainConst Ca A B k * (1 + (t - a₁)) ^ k * κ a₁ t *
            Real.sqrt (∑ i, Xn i ^ 2) *
            Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) := by
  classical
  have hϖ : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
  obtain ⟨Dθ, src, Fl, hcur, hval, hlit, hmem, hsl⟩ := b1w_stage_curves F m Ks θ hM V hb
    (b1wScale F.π F.ϖ F.ηg F.letters)
  -- the stage expansion at almost every time
  have hord : ∀ l, (F.letters l).order ≤ F.J := fun l => by
    rw [(hlet l).1]
    exact (Finset.le_sup (f := d) (Finset.mem_univ l)).trans hJ
  have hsup : (Finset.univ.sup fun l => (F.letters l).order) = Finset.univ.sup d := by
    congr 1
    funext l
    exact (hlet l).1
  have hexp : ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
      ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ), ContDiff ℝ (Finset.univ.sup d + 1 : ℕ) φ →
        AVenhance.IsZ2Periodic φ →
        b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
          ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
            b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y := by
    filter_upwards [stageExpansion K g₁ F θ m Ks (fun l => (hlet l).2) hord letterBloch
      (amplitudeIdMoments K g₁ F)] with r hr i φ hφ hper
    refine hr i φ ?_ hper
    rw [hsup]
    exact_mod_cast hφ
  -- the inputs of the abstract pass
  have hW := fun i => cellWeakHilbertCurve_shift (b1wCoeff_eq_real F θ) (hcur i)
  have hrep : ∀ k < b1wM Nw m Ks, ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
      ∀ (z : B1WIndex ι h Nw m Ks → TorusHk 1 ℂ)
        (ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ),
        (∀ i, torusHkValueCLM (z i) = torusHkValueCLM (ψ i)) →
      ∃ Φ : ∀ k', B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k') ℂ,
        (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k', ‖Φ k' i'‖ ^ 2) ≤
          B * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)) ∧
        ∑ i ∈ stageSet b1wSt k, cellComplexSource (fun k => ((θ k : ℝ) : ℂ))
            (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) r))
            (fun j => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
              (cellSourceSlice (fun r z => Fl i r z j) r)) (z i) =
          ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k',
            cellComplexPair (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i')
              (cellRawTrace (Dθ i') r)) (torusHkValueCLM (Φ k' i')) := by
    intro k _
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_all_iff.2 hlit, ae_all_iff.2 hsl, hexp,
      hprov] with r hr hl hs he hp z ψ hzψ
    have hgood := b1w_good_stage_ae F θ Dθ src Fl r (fun i => hval i r hr) (fun i => hmem i r hr)
      (fun i => ⟨(hs i).1, (hl i).1, (hs i).2, (hl i).2⟩)
    have hN : Finset.univ.sup d + 1 + 2 ≤ b1wLadderAt Nw s₀ d Ks k :=
      (by omega : Finset.univ.sup d + 1 + 2 ≤ s₀).trans (le_b1wLadderAt Nw s₀ d Ks k)
    obtain ⟨UΦ, Φall, hUΦval, hUΦn, hsum⟩ := b1w_repr_crude_at F θ r k F.piece.hπ hϖ
      (b1wLadderAt Nw s₀ d Ks) (Finset.univ.sup d + 1) (b1wLadderAt Nw s₀ d Ks k) (by omega) hN
      (fun i => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellRawTrace (Dθ i) r))
      (fun i => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) r))
      (fun i j => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
        (cellSourceSlice (fun r z => Fl i r z j) r))
      (fun i _ => hgood.1 i) (fun i _ j => hgood.2.1 i j) (fun i _ φ hφ hper => he i φ hφ hper)
      (fun i hi i' hi' φ => stageTransformEarlier K g₁ F θ m Ks (fun l => (hlet l).2) i i'
        (by rw [(Finset.mem_filter.1 hi).2]; exact hi') r φ)
      (fun i' => hgood.2.2 i') B (fun ψ k' hk' => hp k k' hk' ψ) z ψ hzψ
    refine ⟨UΦ, fun k' hk' => ?_, ?_⟩
    · calc Real.sqrt (∑ i' ∈ stageSet b1wSt k', ‖UΦ k' i'‖ ^ 2)
          ≤ Real.sqrt (B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) :=
            Real.sqrt_le_sqrt (hUΦn k' hk')
        _ = B * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) := by
            rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB]
    · rw [hsum]
      refine Finset.sum_congr rfl fun k' hk' => Finset.sum_congr rfl fun i' hi' => ?_
      rw [hUΦval k' (Finset.mem_range.1 hk') i' hi']
  have hadj' : ∀ k < b1wM Nw m Ks, ∀ t ∈ Icc F.a F.b,
      ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
      ∃ (Ψv : B1WIndex ι h Nw m Ks → ℝ → ComplexCellL2)
        (Ψs : B1WIndex ι h Nw m Ks → ℝ → TorusHk 1 ℂ)
        (U : B1WIndex ι h Nw m Ks → ℝ → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ),
        (∀ i, CellWeakHilbertCurve F.a t (Ψv i) (Ψs i) (fun r =>
          -cellDualDerivative
            (cellAdjointCoefficients ⟨fun s _ => F.G s, F.v, fun k => ((θ k : ℝ) : ℂ), 0⟩)
            F.piece.hGm V (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) r
            (Ψs i r) 0 0)) ∧
        (∀ i, Ψv i t = torusHkValueCLM (ψ i)) ∧
        (∀ i, ∀ r ∈ Icc F.a t, torusHkValueCLM (U i r) = Ψv i r) ∧
        ∀ r ∈ Icc F.a t, Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖U i r‖ ^ 2) ≤
          Ca * κ r t * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) := by
    intro k hk t ht ψ
    choose Ψv Ψs U hΨ using fun i => hadj k hk t ht (ψ i)
    refine ⟨Ψv, Ψs, U, fun i => (hΨ i).1, fun i => (hΨ i).2.1,
      fun i r hr => ((hΨ i).2.2 r hr).1, fun r hr => ?_⟩
    exact sqrt_sum_sq_le_mul _ (fun i => ‖U i r‖) (fun i => ‖ψ i‖)
      (mul_nonneg hCa (hκ.pos r t).le) (fun i _ => norm_nonneg _)
      (fun i _ => ((hΨ i).2.2 r hr).2)
  refine ⟨fun i t => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellRawTrace (Dθ i) t),
    fun i t ht => ?_, ?_⟩
  · filter_upwards [cellScalarCLM_ae (b1wScale F.π F.ϖ F.ηg F.letters i)
      (cellRawTrace (Dθ i) t), cellRawTrace_ae (Dθ i) t (hmem i t ht), hval i t ht]
      with y h1 h2 h3
    rw [h1, h2, h3]
    rfl
  · have hsub : Icc a₁ F.b ⊆ Icc F.a F.b := Icc_subset_Icc ha₁.1 le_rfl
    have hWa : ∀ i, (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
        (cellRawTrace (Dθ i) a₁) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
          stageScaled F θ i a₁ := by
      intro i
      filter_upwards [cellScalarCLM_ae (b1wScale F.π F.ϖ F.ηg F.letters i)
        (cellRawTrace (Dθ i) a₁), cellRawTrace_ae (Dθ i) a₁ (hmem i a₁ ha₁), hval i a₁ ha₁]
        with y h1 h2 h3
      rw [h1, h2, h3]
      rfl
    have hadj₁ : ∀ k < b1wM Nw m Ks, ∀ t ∈ Icc a₁ F.b,
        ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
        ∃ (Ψv : B1WIndex ι h Nw m Ks → ℝ → ComplexCellL2)
          (Ψs : B1WIndex ι h Nw m Ks → ℝ → TorusHk 1 ℂ)
          (U : B1WIndex ι h Nw m Ks → ℝ → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ),
          (∀ i, CellWeakHilbertCurve a₁ t (Ψv i) (Ψs i) (fun r =>
            -cellDualDerivative
              (cellAdjointCoefficients ⟨fun s _ => F.G s, F.v, fun k => ((θ k : ℝ) : ℂ), 0⟩)
              F.piece.hGm V (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) r
              (Ψs i r) 0 0)) ∧
          (∀ i, Ψv i t = torusHkValueCLM (ψ i)) ∧
          (∀ i, ∀ r ∈ Icc a₁ t, torusHkValueCLM (U i r) = Ψv i r) ∧
          ∀ r ∈ Icc a₁ t, Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖U i r‖ ^ 2) ≤
            Ca * κ r t * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) := by
      intro k hk t ht ψ
      obtain ⟨Ψv, Ψs, U, h1, h2, h3, h4⟩ := hadj' k hk t (hsub ht) ψ
      have hs' : Icc a₁ t ⊆ Icc F.a t := Icc_subset_Icc ha₁.1 le_rfl
      exact ⟨Ψv, Ψs, U, fun i => (h1 i).mono hs', h2, fun i r hr => h3 i r (hs' hr),
        fun r hr => h4 r (hs' hr)⟩
    exact b1_plain_pass_neg b1wSt (b1wLadderAt Nw s₀ d Ks) (b1wM Nw m Ks)
      ⟨fun s _ => F.G s, F.v, fun k => ((θ k : ℝ) : ℂ), 0⟩ F.piece.hGm V F.piece.hv hb _ _ _ _
      (fun i => (hW i).mono hsub) κ A Ca B (fun r t => (hκ.pos r t).le)
      (fun r t h1 h2 h3 => hκ.mul_le a₁ r t ha₁.1 h1 h2 h3) hA hCa hB Xn
      (fun k hk i hi φ => hX k hk i hi _ (hWa i) φ) hadj₁
      (fun k hk => ae_restrict_of_ae_restrict_of_subset hsub (hrep k hk))

end Frame

end AVRegularity.CycleWords.Seam
end
end
