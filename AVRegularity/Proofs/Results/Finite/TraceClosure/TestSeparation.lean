-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Applications.Torus.JointContinuityMain
import AVRegularity.External.FourierCarrierParseval
public import AVRegularity.Statements.Definitions.CsNormLe
public import AVenhance.Statements.Roots.UnitCube
public import Mathlib.Analysis.Fourier.AddCircle
import AVRegularity.CoupledEnergy.Galerkin.TorusProjection
public import AVenhance.Statements.Roots.IsZ2Periodic
public import Homogenization.Sobolev.H1.Definitions
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public section
open Filter Topology Homogenization AVRegularity.Applications
namespace AVRegularity.Providers.TraceClosure

/-! Compactness of a family of periodic functions with a uniform `C^s` bound: a subsequence
converges pointwise (locally uniformly, by Arzelà–Ascoli) to a continuous periodic function with
the same `C^s` bound. -/

/-- A `C^s` bound bounds the values. -/
theorem abs_le_of_csNormLe {s B : ℝ} {g : Vec 2 → ℝ} (hg : CsNormLe s g B) (x : Vec 2) :
    |g x| ≤ B := by
  have hne : torusDist (0 : Vec 2) (fun _ => 1 / 4) ≠ 0 := by
    have hsmall : eNorm ((0 : Vec 2) - fun _ => 1 / 4) ≤ 1 / 2 := by
      unfold eNorm
      rw [Real.sqrt_le_left (by norm_num)]
      simp [vecNormSq, vecDot]
      norm_num
    have hne0 : (0 : Vec 2) ≠ fun _ => 1 / 4 := by
      intro h; have := congrFun h 0; norm_num at this
    exact (torusDist_pos_of_small hne0 hsmall).ne'
  have h := hg x 0 (fun _ => 1 / 4) hne
  have h1 : 0 ≤ |g 0 - g fun _ => 1 / 4| / torusDist 0 (fun _ => 1 / 4) ^ s :=
    div_nonneg (abs_nonneg _) (Real.rpow_nonneg (torusDist_nonneg _ _) _)
  linarith

/-- A uniform `C^s` bound gives a uniform modulus of continuity. -/
theorem exists_csNormLe_modulus {s B : ℝ} (hs : 0 < s) (hB : 0 ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : Vec 2 → ℝ, CsNormLe s g B → ∀ x y : Vec 2, dist y x < δ →
      |g y - g x| < ε := by
  obtain ⟨δ, hδ, hδ4, hδε⟩ : ∃ δ > 0, δ ≤ 1 / 4 ∧ B * (2 * δ) ^ s < ε := by
    have ht : Tendsto (fun δ : ℝ => B * (2 * δ) ^ s) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous fun δ : ℝ => B * (2 * |δ|) ^ s :=
        continuous_const.mul ((continuous_const.mul continuous_abs).rpow_const
          fun _ => Or.inr hs.le)
      have := hc.tendsto 0
      simp only [abs_zero, mul_zero, Real.zero_rpow hs.ne'] at this
      refine (this.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      rw [abs_of_pos hδ]
    have hev := (ht.eventually (gt_mem_nhds hε)).and
      (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))
    obtain ⟨δ, hδ1, hδ2⟩ := hev.exists
    exact ⟨δ, hδ2.1, hδ2.2.le, hδ1⟩
  refine ⟨δ, hδ, fun g hg x y hy => ?_⟩
  have he : eNorm (y - x) ≤ 2 * δ := by
    unfold eNorm
    rw [Real.sqrt_le_left (by positivity)]
    have h0 := (dist_pi_lt_iff hδ).1 hy 0
    have h1 := (dist_pi_lt_iff hδ).1 hy 1
    rw [Real.dist_eq] at h0 h1
    simp only [vecNormSq, vecDot, Fin.sum_univ_two, Pi.sub_apply]
    nlinarith [abs_lt.1 h0, abs_lt.1 h1]
  have he2 : eNorm (y - x) ≤ 1 / 2 := by linarith
  calc |g y - g x| ≤ B * eNorm (y - x) ^ s := csNormLe_increment_euclid hs hg he2
    _ ≤ B * (2 * δ) ^ s := by
        gcongr
        exact eNorm_nonneg _
    _ < ε := hδε

/-- **Compactness under a uniform `C^s` bound.** A sequence of periodic functions with
`‖Θₙ‖_{C^s} ≤ B` has a subsequence converging pointwise to a continuous periodic function with
`‖Θ‖_{C^s} ≤ B`. -/
theorem exists_csNormLe_limit {s B : ℝ} (hs : 0 < s) (Θ : ℕ → Vec 2 → ℝ)
    (hper : ∀ n, AVenhance.IsZ2Periodic (Θ n)) (hcs : ∀ n, CsNormLe s (Θ n) B) :
    ∃ (φ : ℕ → ℕ) (Θl : Vec 2 → ℝ), StrictMono φ ∧
      (∀ x, Tendsto (fun k => Θ (φ k) x) atTop (𝓝 (Θl x))) ∧
      AVenhance.IsZ2Periodic Θl ∧ CsNormLe s Θl B ∧ Continuous Θl := by
  have hB : 0 ≤ B := csNormLe_K_nonneg (hcs 0)
  let F : ℕ → C(Vec 2, ℝ) := fun n => ⟨Θ n, continuous_of_csNormLe hs (hcs n)⟩
  have hequi : Equicontinuous (fun n x => F n x) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := exists_csNormLe_modulus hs hB hε
    refine ⟨δ, hδ, fun x hx n => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    exact hmod (Θ n) (hcs n) x₀ x hx
  obtain ⟨φ, f, hφ, hlim⟩ := AVRegularity.External.arzelaAscoliDiagonal F
    (fun K _ => ⟨B, fun n x _ => by
      rw [Real.norm_eq_abs]; exact abs_le_of_csNormLe (hcs n) x⟩)
    (fun K _ => hequi.equicontinuousOn K)
  have hpt : ∀ x, Tendsto (fun k => Θ (φ k) x) atTop (𝓝 (f x)) := fun x =>
    (tendstoLocallyUniformlyOn_univ.2 hlim).tendsto_at (Set.mem_univ x)
  refine ⟨φ, f, hφ, hpt, fun n x => ?_, fun x y z hyz => ?_, f.continuous⟩
  · exact tendsto_nhds_unique (hpt (x + AVenhance.latticeShift n))
      ((hpt x).congr fun k => (hper (φ k) n x).symm)
  · have hl : Tendsto (fun k => |Θ (φ k) x| + |Θ (φ k) y - Θ (φ k) z| / torusDist y z ^ s)
        atTop (𝓝 (|f x| + |f y - f z| / torusDist y z ^ s)) :=
      (hpt x).abs.add ((((hpt y).sub (hpt z)).abs).div_const _)
    exact le_of_tendsto hl (Eventually.of_forall fun k => hcs (φ k) x y z hyz)

end AVRegularity.Providers.TraceClosure
end
end

section
open MeasureTheory Homogenization AVenhance.Infra.Heat AVenhance.Infra.Torus
  AVRegularity.CoupledEnergy.Galerkin AVRegularity.Analysis.Convolution

/-! Smooth periodic tests separate `L²` functions on the unit cell: a function of `L²(unitCube)`
orthogonal to every smooth `ℤ²`-periodic test vanishes a.e. on the cell (all its Fourier
coefficients vanish, and the Fourier basis is complete). -/

@[expose] public noncomputable section

local instance testSeparationMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance testSeparationAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance testSeparationProbTorus : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVRegularity.Providers.TraceClosure

private theorem unitCube_measurableSet : MeasurableSet AVenhance.unitCube := by
  simpa [AVenhance.unitCube, Set.pi] using
    (MeasurableSet.univ_pi' (fun _ : Fin 2 =>
      (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) 1))))

private theorem unitCube_finite : volume AVenhance.unitCube < ⊤ := by
  refine lt_of_le_of_lt (measure_mono (t := Set.Icc (0 : Vec 2) 1) ?_) isCompact_Icc.measure_lt_top
  intro x hx
  exact ⟨fun i => (hx i (Set.mem_univ i)).1.le, fun i => (hx i (Set.mem_univ i)).2.le⟩

private theorem integrable_char_part {g : Vec 2 → ℝ} (hgi : IntegrableOn g AVenhance.unitCube)
    {ψ : Vec 2 → ℝ} (hψ : Continuous ψ) (hb : ∀ x, ‖ψ x‖ ≤ 1) :
    IntegrableOn (fun x => g x * ψ x) AVenhance.unitCube := by
  refine Integrable.mul_bdd (c := 1) hgi hψ.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall hb

private theorem coeff_eq_zero {g : Vec 2 → ℝ}
    (hgi : IntegrableOn g AVenhance.unitCube)
    (h : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      ∫ x in AVenhance.unitCube, g x * ψ x = 0) (k : Frequency) :
    ∫ x in AVenhance.unitCube, torusCharacter k x * (g x : ℂ) = 0 := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (torusCharacter k) :=
    (torusCharacter_contDiff (d := 2) k).of_le le_top
  have hn : ∀ x, ‖torusCharacter k x‖ = 1 := fun x => by
    simp [torusCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      toUnitTorus, Complex.norm_exp, Complex.mul_re]
  have hre : ContDiff ℝ (⊤ : ℕ∞) (fun x => (torusCharacter k x).re) :=
    Complex.reCLM.contDiff.comp hc
  have him : ContDiff ℝ (⊤ : ℕ∞) (fun x => (torusCharacter k x).im) :=
    Complex.imCLM.contDiff.comp hc
  have hper := torusCharacter_periodic (d := 2) k
  have hpre : AVenhance.IsZ2Periodic (fun x => (torusCharacter k x).re) := by
    rw [← isZdPeriodic_iff_frozen]; intro n x; simp [hper n x]
  have hpim : AVenhance.IsZ2Periodic (fun x => (torusCharacter k x).im) := by
    rw [← isZdPeriodic_iff_frozen]; intro n x; simp [hper n x]
  have h1 := h _ hre hpre
  have h2 := h _ him hpim
  have i1 := integrable_char_part hgi hre.continuous
    (fun x => (Complex.abs_re_le_norm _).trans (hn x).le)
  have i2 := integrable_char_part hgi him.continuous
    (fun x => (Complex.abs_im_le_norm _).trans (hn x).le)
  have hfun : (fun x => torusCharacter k x * (g x : ℂ)) = fun x =>
      (((g x * (torusCharacter k x).re : ℝ)) : ℂ) +
        ((g x * (torusCharacter k x).im : ℝ) : ℂ) * Complex.I := by
    funext x
    apply Complex.ext <;> simp [mul_comm]
  rw [hfun, integral_add (f := fun x => ((g x * (torusCharacter k x).re : ℝ) : ℂ))
    (g := fun x => ((g x * (torusCharacter k x).im : ℝ) : ℂ) * Complex.I)
    i1.ofReal (i2.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal, h1, h2]
  simp

/-- **Smooth periodic tests separate `L²(unitCube)`.** -/
theorem ae_eq_zero_of_smooth_periodic_tests {g : Vec 2 → ℝ}
    (hg : MemL2On AVenhance.unitCube g)
    (h : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      ∫ x in AVenhance.unitCube, g x * ψ x = 0) :
    g =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
  have hgi : IntegrableOn g AVenhance.unitCube := by
    have : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
      ⟨by simpa [Measure.restrict_apply_univ] using unitCube_finite⟩
    exact hg.integrable (by norm_num)
  let u := frozenCellToTorusL2 hg
  have hu : u = 0 := by
    apply UnitAddTorus.mFourierBasis.repr.injective
    ext k
    have hur := (memLp_frozenCellTransfer hg).coeFn_toLp
    simp only [UnitAddTorus.mFourierBasis_repr, map_zero, lp.coeFn_zero, Pi.zero_apply]
    have : UnitAddTorus.mFourierCoeff u k =
        ∫ x in unitCell 2, torusCharacter k x * (g x : ℂ) := by
      rw [← integral_periodicToTorus_eq_unitCell
        (fun x => torusCharacter k x * (g x : ℂ))]
      unfold UnitAddTorus.mFourierCoeff
      apply integral_congr_ae
      filter_upwards [hur] with y hy
      have hchar : torusCharacter k (unitTorusRepresentative 2 y) =
          UnitAddTorus.mFourier (-k) y := by
        simp [torusCharacter, toUnitTorus_unitTorusRepresentative]
      change UnitAddTorus.mFourier (-k) y • u y = torusCharacter k (unitTorusRepresentative 2 y) *
        (g (unitTorusRepresentative 2 y) : ℂ)
      rw [hchar, smul_eq_mul]
      congr 1
    rw [this, integral_unitCell_eq_unitCube]
    simpa using coeff_eq_zero hgi h k
  have hur := (memLp_frozenCellTransfer hg).coeFn_toLp
  have h0 : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin 2))), u y = 0 := by
    rw [hu]; exact Lp.coeFn_zero ℂ 2 volume
  have hzero : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin 2))),
      periodicToTorus (fun x => (g x : ℂ)) y = 0 := by
    filter_upwards [hur, h0] with y hy h0
    exact hy.symm.trans h0
  rw [← coupledEnergy_torusMeasure_eq_volume] at hzero
  have hc := measurePreserving_torusQuotient_cell.quasiMeasurePreserving.ae hzero
  filter_upwards [hc, ae_restrict_mem unitCube_measurableSet] with x hx hxc
  have hmem : x ∈ unitCell 2 := by
    intro i
    have hi := hxc i (Set.mem_univ i)
    simpa using (show x i ∈ Set.Ioc (0 : ℝ) 1 from ⟨hi.1, hi.2.le⟩)
  change (g (unitTorusRepresentative 2 (toUnitTorus 2 x)) : ℂ) = 0 at hx
  rw [unitTorusRepresentative_eq_of_mem_unitCell hmem] at hx
  simpa using hx

end AVRegularity.Providers.TraceClosure
end
end
