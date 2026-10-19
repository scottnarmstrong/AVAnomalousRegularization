-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.PulseInstance
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.CycleComparison.LiftSetting.Metric
import AVRegularity.CycleComparison.Reconstruction.PulseIdentity
import AVRegularity.CycleComparison.QuietDecay.Test.MonoLift
import AVRegularity.CycleComparison.Reconstruction.ObsEdgesTested
public import AVRegularity.CycleComparison.Reconstruction.PulseTail
import AVRegularity.CycleComparison.Reconstruction.LiftSource
public import AVRegularity.CycleComparison.Reconstruction.PulseTailPeriodic
public import AVRegularity.Statements.Intermediate.Families.AtlasIsConsecutiveClosed
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The glued weak identity of a finite-rank coarse field**. For a coarse field
`a = ∑_j c_j(t) φ_j(x)` with coefficients of integral type, the triangular physical lift
`û = 𝒯a = ∑_k ϖ_k 𝒯_k a` (`gluedLift`) over the observed pulses satisfies, tested against a `C¹`
periodic `φ`, `d/dt ∫⟪û, φ⟫ = -∫⟪b_m · ∇û, φ⟫ - ν ∫ ∑_j ⟪∂_j û, ∂_j φ⟫`
`+ ∑_k (ϖ_k' ∫⟪𝒯_k a, φ⟫ + ϖ_k ℓ⁻² ∫⟪ℛ_k, φ⟫)`
(`glued_pulses_weak`), where `ℛ_k` is the rest of the pulse `k` (`labelRest`: sources, lifted
means, tail and the lift of the material derivative) read at the labels of its chart. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

/-- The physical lift of the observed pulse `k` of a finite-rank coarse field. -/
def obsLift (α q : ℝ) (Λ m : ℕ) (φs : ℝ → Vec 2 → ℝ) (hφs : IsAdmissibleStream φs)
    (ν B ρ : ℝ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) {κ : Type*} [Fintype κ]
    (cf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i) (k : ℤ) (t : ℝ) (x : Vec 2) : ∀ i, h i :=
  pulseLift (Cc k) N H (ocDStar q Λ m ν B / ρ)
    (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ)
    ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2)
    (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) t x

/-- The rest of the observed pulse `k` of a finite-rank coarse field, read at the labels. -/
def obsRest {D : ℕ} (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (φs : ℝ → Vec 2 → ℝ)
    (hφs : IsAdmissibleStream φs) (ν B ρ lam : ℝ) (edge : ℤ → ConstituentEdges D h)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) {κ : Type*} [Fintype κ]
    (cf dcf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i) (k : ℤ) (t : ℝ) (x : Vec 2) : ∀ i, h i :=
  labelRest (pulseLiftData α q Λ m ζ φs hφs ν B ρ lam k (edge k)) (Cc k) N H
    (ocDStar q Λ m ν B / ρ)
    (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ)
    (chartFieldDot cf dcf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
      (streamVel φs) (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t
    (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t x)

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
/-- The glued lift of a finite-rank coarse field is the weighted sum of the observed lifts. -/
theorem gluedLift_finiteRank_apply (α q : ℝ) (Λ m : ℕ) (φs : ℝ → Vec 2 → ℝ)
    (hφs : IsAdmissibleStream φs) (ν B ρ : ℝ) (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) {κ : Type*} [Fintype κ]
    (cf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i) (t : ℝ) (x : Vec 2) (v : ι) :
    gluedLift kset ϖ (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H Cc
        (fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
        (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
        (fun t x => ∑ j, cf j t • φ j x) t x v =
      ∑ k ∈ kset, ϖ k t • obsLift α q Λ m φs hφs ν B ρ Cc N H cf φ k t x v := by
  simp only [gluedLift, Finset.sum_apply, Pi.smul_apply]
  rfl

variable {D H N K k₀ L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}

/-- The physical lift of one pulse is `C²` at the times of its window. -/
theorem setting_pulseLift_contDiff
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k₀ L qs qf CG Cw Cj edge Θ)
    (sX sZ : ℕ) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ) {κ : Type*} [Fintype κ]
    (cf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i) (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k))
    (χ ψ : ℝ → Vec 2 → Vec 2) (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2))
    (c ρs es : ℝ) (t : ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) (ψ t)) (hs : c⁻¹ * t ∈ Icc a b) (v : ι) :
    ContDiff ℝ 2 (fun x => pulseLift Cc N H ε (chartField cf φ χ c ρs) ρs es c ψ t x v) := by
  have hbox : ∀ hh ∈ Finset.range (H + 1), IsBoxSmooth 2 2 (liftPolyField Cc N ε hh
      (fun _ => chartField cf φ χ c ρs (c⁻¹ * t)) (c⁻¹ * t)) :=
    fun hh hhm => setting_liftPolyField_box P sX sZ Cc hseq hh
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) ε _
      (chartField_contDiff cf φ hφ χ hχ c ρs _) (c⁻¹ * t) hs (by omega)
  have hL2 : ContDiff ℝ 2 (fun y => labelLift Cc N H ε (chartField cf φ χ c ρs) ρs es c t y v) := by
    have he : (fun y => labelLift Cc N H ε (chartField cf φ χ c ρs) ρs es c t y v) =
        fun y => (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
          (∑ hh ∈ Finset.range (H + 1), twoScaleSample ρs es (liftPolyField Cc N ε hh
            (fun _ => chartField cf φ χ c ρs (c⁻¹ * t)) (c⁻¹ * t)) y) := by
      funext y
      simp only [labelLift, twoScaleSample, ContinuousLinearMap.proj_apply, Finset.sum_apply]
      rfl
    rw [he]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := h) v).contDiff.comp
      (ContDiff.sum fun hh hhm => CoarseFluxDiff.contDiff_sample (hbox hh hhm) le_rfl le_rfl ρs es)
  exact hL2.comp (hψ.of_le (by simp))

/-- **The glued weak identity of a finite-rank coarse field** over the observed pulses. -/
theorem glued_pulses_weak {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseqΦ : IsOCStreamSeq α q Λ ζ Φ) (hm : 1 ≤ m) (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφs : IsAdmissibleStream (Φ (m - 1))) {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B)
    {ρ lam : ℝ} (hρ : 0 < ρ) {D : ℕ} (edge : ℤ → ConstituentEdges D h)
    {tA tZ : ℝ} (htAZ : tA ≤ tZ) (ϖ : ℤ → ℝ → ℝ) {quiet : Set ℝ} {Cpart : ℝ}
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) ϖ (ocPulseWindow α q Λ m) quiet
      (Icc tA tZ) (ocTau α q Λ m) Cpart)
    {π : ι → ℝ} {e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : ℤ → Fin 2}
    {V : ℤ → ℝ → ℝ → ℝ} {H N K k₀ L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSetting (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k (edge k)) π
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)
        e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ (par k) (V k) H N K k₀ L qs qf CG Cw Cj edgeM Θ)
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k (edge k)) sX sZ
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    {κ : Type*} [Fintype κ] (cf dcf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (φ j)) (hφp : ∀ j, IsZ2Periodic (φ j)) (A₀ B₀ : ℝ)
    (hA : A₀ ≤ tA) (hB₀ : tZ ≤ B₀) (hcf : ∀ j, IsPrimOn A₀ B₀ (cf j) (dcf j))
    (hcs : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ (n : Fin 2 → ℤ) v u d,
      ∀ γ ∈ (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k (edge k)).edge v u d,
        ∀ w t X z, γ.coeff w t (X + ρ⁻¹ • latticeShift n) z = γ.coeff w t X z)
    (v : ι) (φt : Vec 2 → h v) (hφt : ContDiff ℝ 1 φt) (hφtp : IsZ2Periodic φt) :
    IsPrimOn tA tZ
      (fun t => ∫ x in AVenhance.unitCube, inner ℝ
        (gluedLift (ocObsPulses α q Λ m tA tZ) ϖ (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m)
          (ocDStar q Λ m ν B / ρ) N H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
          (fun t x => ∑ j, cf j t • φ j x) t x v) (φt x))
      (fun t => -(∫ x in AVenhance.unitCube, inner ℝ (∑ j, streamVel (Φ m) t x j •
          fderiv ℝ (fun x' => ∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t •
            obsLift α q Λ m (Φ (m - 1)) hφs ν B ρ Cc N H cf φ k t x' v) x (basisVec j)) (φt x)) -
        ν * (∫ x in AVenhance.unitCube, ∑ j, inner ℝ
          (fderiv ℝ (fun x' => ∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t •
            obsLift α q Λ m (Φ (m - 1)) hφs ν B ρ Cc N H cf φ k t x' v) x (basisVec j))
          (fderiv ℝ φt x (basisVec j))) +
        ∑ k ∈ ocObsPulses α q Λ m tA tZ, (deriv (ϖ k) t * (∫ x in AVenhance.unitCube,
            inner ℝ (obsLift α q Λ m (Φ (m - 1)) hφs ν B ρ Cc N H cf φ k t x v) (φt x)) +
          ϖ k t * ((ocEll q Λ m ν ^ 2)⁻¹ * ∫ x in AVenhance.unitCube, inner ℝ
            (obsRest α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam edge Cc N H cf dcf φ k t x v)
            (φt x)))) := by
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of hν he
  have hc : 0 < ocEll q Λ m ν ^ 2 := by positivity
  -- the cell window of a pulse is its physical window scaled by `ℓ⁻²`
  have hscale : ∀ X : ℝ, ocEll q Λ m ν ^ 2 * (X / ocEll q Λ m ν ^ 2) = X := fun X =>
    mul_div_cancel₀ X hc.ne'
  have hcell : ∀ k : ℤ, ∀ t ∈ Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ),
      (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA /
        ocEll q Λ m ν ^ 2) (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) :=
    fun k t ht =>
      ⟨by rw [div_eq_inv_mul]; exact mul_le_mul_of_nonneg_left ht.1 (inv_nonneg.2 hc.le),
        by rw [div_eq_inv_mul]; exact mul_le_mul_of_nonneg_left ht.2 (inv_nonneg.2 hc.le)⟩
  -- the per-pulse weak identities
  have hprim : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsPrimOn (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ)
        (fun t => ∫ x in AVenhance.unitCube, inner ℝ
          (obsLift α q Λ m (Φ (m - 1)) hφs ν B ρ Cc N H cf φ k t x v) (φt x))
        (fun t => -(∫ x in AVenhance.unitCube, inner ℝ (∑ j, streamVel (Φ m) t x j •
            fderiv ℝ (fun x' => obsLift α q Λ m (Φ (m - 1)) hφs ν B ρ Cc N H cf φ k t x' v) x
              (basisVec j)) (φt x)) -
          ν * (∫ x in AVenhance.unitCube, ∑ j, inner ℝ
            (fderiv ℝ (fun x' => obsLift α q Λ m (Φ (m - 1)) hφs ν B ρ Cc N H cf φ k t x' v) x
              (basisVec j)) (fderiv ℝ φt x (basisVec j))) +
          (ocEll q Λ m ν ^ 2)⁻¹ * ∫ x in AVenhance.unitCube, inner ℝ
            (obsRest α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam edge Cc N H cf dcf φ k t x v)
            (φt x)) := by
    intro k hk
    have hkodd : Odd k := LiftSetting.obsPulse_odd hk
    have hwin : Icc (ocEll q Λ m ν ^ 2 *
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2))
        (ocEll q Λ m ν ^ 2 *
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)) ⊆
        ocPulseWindow α q Λ m k := by
      rw [hscale, hscale]
      exact Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    have hA' : A₀ ≤ ocEll q Λ m ν ^ 2 *
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2) := by
      rw [hscale]; exact hA.trans (le_max_right _ _)
    have hB' : ocEll q Λ m ν ^ 2 *
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) ≤ B₀ := by
      rw [hscale]; exact (min_le_right _ _).trans hB₀
    have hi := pulse_weak_instance hseqΦ hm hΛ hζ hφs hν hB hρ hkodd (edge k) (P k hk) hwin sX sZ
      hsX hsZ (Cc k) (hseq k hk) cf dcf φ hφ hφp A₀ B₀ hA' hB' hcf (hcs k hk) v φt hφt hφtp
    rw [hscale, hscale] at hi
    exact hi
  refine (glued_weak (ocObsPulses α q Λ m tA tZ) htAZ ϖ
    (fun k : ℤ => ((k : ℝ) - 61 / 48) * ocTau α q Λ m)
    (fun k : ℤ => ((k : ℝ) + 61 / 48) * ocTau α q Λ m) hpart.2.1 hpart.2.2.2.1
    (fun k t x => obsLift α q Λ m (Φ (m - 1)) hφs ν B ρ Cc N H cf φ k t x v)
    (streamVel (Φ m)) ν
    (fun k t => (ocEll q Λ m ν ^ 2)⁻¹ * ∫ x in AVenhance.unitCube, inner ℝ
      (obsRest α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam edge Cc N H cf dcf φ k t x v) (φt x))
    φt hφt (fun k hk t ht => ?_) (fun t _ => ?_) hprim).congr htAZ (fun t _ => ?_)
    (fun t _ => rfl)
  · -- the observed lifts are `C¹` on their windows
    have hχj := Charts.contDiff_ocChart_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)
    have hψs : ContDiff ℝ (⊤ : ℕ∞)
        (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) t) :=
      (Charts.contDiff_ocChartInv_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)).comp
        (contDiff_const.prodMk contDiff_id)
    exact (setting_pulseLift_contDiff (P k hk) sX sZ hsZ (Cc k) (hseq k hk) _ cf φ hφ _ _ hχj
      _ ρ _ t hψs (hcell k t ht) v).of_le (by norm_num)
  · -- the actual drift is continuous
    obtain ⟨hΨ', -⟩ := hseqΦ.2 (m + 1) (by omega)
    have hΨ : IsAdmissibleStream (Φ m) := hΨ'
    exact ((AVenhance.Infra.Construction.smoothPeriodic_streamVel hΨ).smooth.comp
      (contDiff_const.prodMk contDiff_id)).continuous
  · -- the tested glued lift
    simp only [gluedLift_finiteRank_apply]
end

/-! **The glued mean and material parts**. Summed with the
partition weights over the observed pulses, the mean and material parts of the pulse rests, read at
the labels and scaled by `ℓ⁻²`, are the glued lift of the coarse defect field
`∂_t a + b_{m-1} · ∇a + ∑_r 𝓜_r a` (`glued_meanPart`), where `𝓜_r` is the glued mean, provided
the weighted pulse means agree at every weighted time (the exact quiet mean) and the glued means
are `C^N` there. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
/-- The physical lift of a pulse only sees the coarse field at the physical time. -/
theorem pulsePhysicalLift_congr_time (c ρ e εc : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℝ → Vec 2 → Vec 2) {A B : ℝ → Vec 2 → ∀ i, h i} {t : ℝ} (hc : c ≠ 0)
    (hAB : A t = B t) (x : Vec 2) :
    pulsePhysicalLift c ρ e εc N H Cc chart label A t x =
      pulsePhysicalLift c ρ e εc N H Cc chart label B t x := by
  have hct : c * (c⁻¹ * t) = t := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  show labelLift Cc N H εc (fun s X => A (c * s) (chart (c * s) (ρ • X))) ρ e c t (label t x) =
    labelLift Cc N H εc (fun s X => B (c * s) (chart (c * s) (ρ • X))) ρ e c t (label t x)
  exact labelLift_congr_input Cc N H εc ρ e c t (by funext X; simp only [hct, hAB]) _

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- **The glued mean and material parts are the glued lift of the coarse defect field.** -/
theorem glued_meanPart {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΛ : 1 ≤ Λ) (hφs : IsAdmissibleStream (Φ (m - 1))) {ν B : ℝ} (hν : 0 < ν)
    {ρ lam : ℝ} (hρ : 0 < ρ) {D : ℕ} (edge : ℤ → ConstituentEdges D h)
    {tA tZ : ℝ} (ϖ : ℤ → ℝ → ℝ) {quiet : Set ℝ} {Cpart : ℝ}
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) ϖ (ocPulseWindow α q Λ m) quiet
      (Icc tA tZ) (ocTau α q Λ m) Cpart)
    {π : ι → ℝ} {e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : ℤ → Fin 2}
    {V : ℤ → ℝ → ℝ → ℝ} {H N K k₀ L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSetting (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k (edge k)) π
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)
        e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ (par k) (V k) H N K k₀ L qs qf CG Cw Cj edgeM Θ)
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k (edge k)) sX sZ
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    {κ : Type*} [Fintype κ] (cf dcf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (φ j)) {t : ℝ} (ht : t ∈ Icc tA tZ)
    (hagree : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t ≠ 0 →
      ∀ j ∈ ocObsPulses α q Λ m tA tZ, ϖ j t ≠ 0 → ∀ r ∈ Finset.range (H + 1), ∀ x,
        pulseMeanField (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r
            (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam j (edge j)) (Cc j)
            (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m j))
            (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m j))
            (fun t' x' => ∑ j', cf j' t' • φ j' x') t x =
          pulseMeanField (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r
            (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k (edge k)) (Cc k)
            (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
            (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
            (fun t' x' => ∑ j', cf j' t' • φ j' x') t x)
    (hMr : ∀ r ∈ Finset.range (H + 1), ContDiff ℝ (N : ℕ∞) (fun x =>
      gluedMean (ocObsPulses α q Λ m tA tZ) ϖ (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r
        (fun k => pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k (edge k)) Cc
        (fun k => ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
        (fun t' x' => ∑ j', cf j' t' • φ j' x') t x))
    (x : Vec 2) :
    ∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t • ((ocEll q Λ m ν ^ 2)⁻¹ •
        (restMean (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k (edge k)) (Cc k) N H
          (ocDStar q Λ m ν B / ρ)
          (chartField cf φ (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
            (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t
          (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) t x) +
        labelLift (Cc k) N H (ocDStar q Λ m ν B / ρ)
          (chartFieldDot cf dcf φ (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
            (streamVel (Φ (m - 1))) (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m)
          (ocEll q Λ m ν ^ 2) t
          (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) t x))) =
      gluedLift (ocObsPulses α q Λ m tA tZ) ϖ (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m)
        (ocDStar q Λ m ν B / ρ) N H Cc
        (fun k => ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
        (fun t' x' => (∑ j, dcf j t' • φ j x' +
            ∑ j, cf j t' • fderiv ℝ (φ j) x' (streamVel (Φ (m - 1)) t' x')) +
          ∑ r ∈ Finset.range (H + 1), gluedMean (ocObsPulses α q Λ m tA tZ) ϖ
            (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r
            (fun k => pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k (edge k)) Cc
            (fun k => ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
            (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
            (fun t'' x'' => ∑ j', cf j' t'' • φ j' x'') t' x') t x := by
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of hν he
  have hc : ocEll q Λ m ν ^ 2 ≠ 0 := pow_ne_zero 2 hℓ
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have hvel := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφs
  have hW : ContDiff ℝ (⊤ : ℕ∞) (streamVel (Φ (m - 1)) t) :=
    hvel.smooth.comp (contDiff_const.prodMk contDiff_id)
  simp only [gluedLift]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hw : ϖ k t = 0
  · rw [hw, zero_smul, zero_smul]
  refine congrArg (fun z => ϖ k t • z) ?_
  -- the cell time is in the window of the pulse
  have hwin : t ∈ ocPulseWindow α q Λ m k := hpart.2.2.2.1 k hk t hw
  have hwin' : ((k : ℝ) - 61 / 48) * ocTau α q Λ m ≤ t ∧
      t ≤ ((k : ℝ) + 61 / 48) * ocTau α q Λ m := hwin
  have hs : (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Icc
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) :=
    ⟨by rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left (max_le hwin'.1 ht.1) (inv_nonneg.2 hc0.le),
      by rw [div_eq_inv_mul]
         exact mul_le_mul_of_nonneg_left (le_min hwin'.2 ht.2) (inv_nonneg.2 hc0.le)⟩
  have hmean : ∀ r ∈ Finset.range (H + 1), ∀ x',
      pulseMeanField (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r
        (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k (edge k)) (Cc k)
        (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
        (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
        (fun t' x'' => ∑ j', cf j' t' • φ j' x'') t x' =
      gluedMean (ocObsPulses α q Λ m tA tZ) ϖ (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r
        (fun k => pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k (edge k)) Cc
        (fun k => ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
        (fun t' x'' => ∑ j', cf j' t' • φ j' x'') t x' := fun r hr x' =>
    Eq.symm (pulseMeanField_eq_gluedMean _ ϖ _ ρ _ N r _ Cc _ _ _ (hpart.2.2.1 t ht)
      (fun j hj hwj x'' => hagree k hk hw j hj hwj r hr x'') x')
  have hl := setting_pulse_meanPart_lift (P k hk) sX sZ hsX hsZ (Cc k) (hseq k hk)
    (ocDStar q Λ m ν B / ρ) cf dcf φ hφ
    (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
    (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
    (streamVel (Φ (m - 1)))
    (Charts.contDiff_ocChart_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k))
    (fun t' y => Charts.ocChartInv_ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)
      t' y) hc hρ.ne' (ocEpsilon q Λ m) t hs _ hMr hmean hW x
  rw [hl]
  refine pulsePhysicalLift_congr_time _ _ _ _ N H (Cc k) _ _ hc ?_ x
  rfl
end

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The partition term of the glued lift: the transitions of the time partition**.

The odd pulse `k` is active in `|t - kτ| < 2τ/3`; its lift window is `[(k ∓ 61/48)τ]`, and two
neighbouring windows overlap in the quiet interval `[(k + 35/48)τ, (k + 61/48)τ]`. On the window
interior the weight `ϖ_k` is locally `1` off these overlaps (`deriv_eq_zero_of_center`), so
`ϖ_k'` splits into a rising piece and a falling piece supported in the two overlaps of the window
(`trWeight`, `trWeight_add`). At any time at most two of these pieces are active
(`card_active_le_two`). The degree-zero parts of the lifts cancel in `∑_k ϖ_k' 𝒯_k a`
(`sum_deriv_eq_zero`, `partition_term_decomp`).

* `mem_ocQuietTimes_of_gap`: every pulse vanishes on `[(j + 2/3)τ, (j + 4/3)τ]`, `j` odd.
* `hasQuietEntranceTrace_start`: a zero-start lift has zero quiet entrance trace at the start of
  its window (the positive lift coefficients vanish there, `liftSequence_start_coeff_zero`).
* `decay_factor_le`: the scale arithmetic of one transition. -/

/-! ### The transition pieces of the time partition -/

/-- The lower end of the falling (`true`) or rising (`false`) transition region of the pulse
`k`, clipped to the window `[tA, tZ]`. -/
def trLo (τ tA : ℝ) (k : ℤ) : Bool → ℝ
  | true => max (((k : ℝ) + 35 / 48) * τ) tA
  | false => max (((k : ℝ) - 61 / 48) * τ) tA

/-- The upper end of the falling (`true`) or rising (`false`) transition region of the pulse
`k`, clipped to the window `[tA, tZ]`. -/
def trHi (τ tZ : ℝ) (k : ℤ) : Bool → ℝ
  | true => min (((k : ℝ) + 61 / 48) * τ) tZ
  | false => min (((k : ℝ) - 35 / 48) * τ) tZ

/-- The falling (`true`) or rising (`false`) piece of the derivative of the weight `ϖ_k`. -/
def trWeight (ϖ : ℤ → ℝ → ℝ) (τ tA tZ : ℝ) (k : ℤ) (σ : Bool) : ℝ → ℝ :=
  (Set.Icc (trLo τ tA k σ) (trHi τ tZ k σ)).indicator (deriv (ϖ k))

/-- The index `j` of the overlap `[(j + 35/48)τ, (j + 61/48)τ]` of a transition piece. -/
def trIndex : ℤ × Bool → ℤ
  | (k, true) => k
  | (k, false) => k - 2

theorem trWeight_ne_zero {ϖ : ℤ → ℝ → ℝ} {τ tA tZ : ℝ} {k : ℤ} {σ : Bool} {t : ℝ}
    (h : trWeight ϖ τ tA tZ k σ t ≠ 0) :
    t ∈ Set.Icc (trLo τ tA k σ) (trHi τ tZ k σ) ∧ deriv (ϖ k) t ≠ 0 := by
  unfold trWeight at h
  by_cases hm : t ∈ Set.Icc (trLo τ tA k σ) (trHi τ tZ k σ)
  · rw [Set.indicator_of_mem hm] at h
    exact ⟨hm, h⟩
  · rw [Set.indicator_of_notMem hm] at h
    exact absurd rfl h

theorem abs_trWeight_le (ϖ : ℤ → ℝ → ℝ) (τ tA tZ : ℝ) (k : ℤ) (σ : Bool) (t : ℝ) :
    |trWeight ϖ τ tA tZ k σ t| ≤ |deriv (ϖ k) t| := by
  unfold trWeight
  by_cases hm : t ∈ Set.Icc (trLo τ tA k σ) (trHi τ tZ k σ)
  · exact le_of_eq (by rw [Set.indicator_of_mem hm])
  · rw [Set.indicator_of_notMem hm, abs_zero]
    exact abs_nonneg _

theorem support_trWeight (ϖ : ℤ → ℝ → ℝ) (τ tA tZ : ℝ) (k : ℤ) (σ : Bool) :
    Function.support (trWeight ϖ τ tA tZ k σ) ⊆ Set.Icc (trLo τ tA k σ) (trHi τ tZ k σ) :=
  fun _ ht => (trWeight_ne_zero ht).1

theorem measurable_trWeight (ϖ : ℤ → ℝ → ℝ) (τ tA tZ : ℝ) (k : ℤ) (σ : Bool) :
    Measurable (trWeight ϖ τ tA tZ k σ) :=
  (measurable_deriv (ϖ k)).indicator measurableSet_Icc

/-- A transition region lies in the lift window of its pulse and in the observation window. -/
theorem mem_window_of_trIcc {τ tA tZ : ℝ} (hτ : 0 < τ) {k : ℤ} {σ : Bool} {t : ℝ}
    (h : t ∈ Set.Icc (trLo τ tA k σ) (trHi τ tZ k σ)) :
    t ∈ Set.Icc (((k : ℝ) - 61 / 48) * τ) (((k : ℝ) + 61 / 48) * τ) ∧ t ∈ Set.Icc tA tZ := by
  cases σ
  · have h' : t ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * τ) tA)
        (min (((k : ℝ) - 35 / 48) * τ) tZ) := h
    obtain ⟨h1, h2⟩ := h'
    have h3 := le_trans h2 (min_le_left _ _)
    refine ⟨⟨le_trans (le_max_left _ _) h1, by linarith⟩,
      ⟨le_trans (le_max_right _ _) h1, le_trans h2 (min_le_right _ _)⟩⟩
  · have h' : t ∈ Set.Icc (max (((k : ℝ) + 35 / 48) * τ) tA)
        (min (((k : ℝ) + 61 / 48) * τ) tZ) := h
    obtain ⟨h1, h2⟩ := h'
    have h3 := le_trans (le_max_left _ _) h1
    refine ⟨⟨by linarith, le_trans h2 (min_le_left _ _)⟩,
      ⟨le_trans (le_max_right _ _) h1, le_trans h2 (min_le_right _ _)⟩⟩

/-! ### The weights near a time of the window -/

/-- The derivative of a function vanishing off a closed set vanishes off the set. -/
theorem deriv_eq_zero_of_not_mem {ϖ : ℝ → ℝ} {W : Set ℝ} (hW : IsClosed W)
    (hϖ : ∀ t, ϖ t ≠ 0 → t ∈ W) {t : ℝ} (ht : t ∉ W) : deriv ϖ t = 0 := by
  have hev : ϖ =ᶠ[nhds t] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hW.isOpen_compl.mem_nhds ht) fun s hs => by
      by_contra hne
      exact hs (hϖ s hne)
  rw [hev.deriv_eq]
  simp

section Partition

variable {kset : Finset ℤ} {ϖ : ℤ → ℝ → ℝ} {τ tA tZ Cpart : ℝ} {quiet : Set ℝ}

/-- A time at which `ϖ_k'` does not vanish lies in the lift window of `k`. -/
theorem mem_window_of_deriv
    (hpart : IsLiftPartition kset ϖ (fun k => Set.Icc (((k : ℝ) - 61 / 48) * τ)
      (((k : ℝ) + 61 / 48) * τ)) quiet (Set.Icc tA tZ) τ Cpart)
    {k : ℤ} (hk : k ∈ kset) {t : ℝ} (hd : deriv (ϖ k) t ≠ 0) :
    t ∈ Set.Icc (((k : ℝ) - 61 / 48) * τ) (((k : ℝ) + 61 / 48) * τ) := by
  by_contra hw
  exact hd (deriv_eq_zero_of_not_mem isClosed_Icc (fun s hs => hpart.2.2.2.1 k hk s hs) hw)

/-- **The derivatives of the weights sum to zero** on the interior of the window. -/
theorem sum_deriv_eq_zero {win : ℤ → Set ℝ}
    (hpart : IsLiftPartition kset ϖ win quiet (Set.Icc tA tZ) τ Cpart) {t : ℝ}
    (ht : t ∈ Set.Ioo tA tZ) : ∑ k ∈ kset, deriv (ϖ k) t = 0 := by
  have hdiff : ∀ k ∈ kset, DifferentiableAt ℝ (ϖ k) t := fun k hk =>
    ((hpart.2.1 k hk).differentiable one_ne_zero) t
  rw [← deriv_sum hdiff]
  have hev : (∑ k ∈ kset, ϖ k) =ᶠ[nhds t] fun _ => (1 : ℝ) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) fun s hs => by
      rw [Finset.sum_apply]
      exact hpart.2.2.1 s (Set.Ioo_subset_Icc_self hs)
  rw [hev.deriv_eq]
  simp

/-- **Away from the overlaps the weight of a pulse is locally constant.** -/
theorem deriv_eq_zero_of_center (hodd : ∀ k ∈ kset, Odd k) (hτ : 0 < τ)
    (hpart : IsLiftPartition kset ϖ (fun k => Set.Icc (((k : ℝ) - 61 / 48) * τ)
      (((k : ℝ) + 61 / 48) * τ)) quiet (Set.Icc tA tZ) τ Cpart)
    {k : ℤ} (hk : k ∈ kset) {t : ℝ} (ht : t ∈ Set.Ioo tA tZ)
    (hc : ((k : ℝ) - 35 / 48) * τ < t ∧ t < ((k : ℝ) + 35 / 48) * τ) :
    deriv (ϖ k) t = 0 := by
  have hone : ∀ s ∈ Set.Ioo tA tZ ∩
      Set.Ioo (((k : ℝ) - 35 / 48) * τ) (((k : ℝ) + 35 / 48) * τ), ϖ k s = 1 := by
    intro s hs
    have hoff : ∀ j ∈ kset, j ≠ k → ϖ j s = 0 := by
      intro j hj hjk
      by_contra hw
      obtain ⟨hw1, hw2⟩ := hpart.2.2.2.1 j hj s hw
      obtain ⟨hc1, hc2⟩ := hs.2
      have hsplit : j + 2 ≤ k ∨ k + 2 ≤ j := by
        obtain ⟨a, ha⟩ := hodd j hj
        obtain ⟨b, hb⟩ := hodd k hk
        omega
      rcases hsplit with hjk' | hkj'
      · have h1 : (j : ℝ) + 2 ≤ k := by exact_mod_cast hjk'
        have e : ((j : ℝ) + 2) * τ ≤ (k : ℝ) * τ := mul_le_mul_of_nonneg_right h1 hτ.le
        linarith
      · have h1 : (k : ℝ) + 2 ≤ j := by exact_mod_cast hkj'
        have e : ((k : ℝ) + 2) * τ ≤ (j : ℝ) * τ := mul_le_mul_of_nonneg_right h1 hτ.le
        linarith
    have hsum := hpart.2.2.1 s (Set.Ioo_subset_Icc_self hs.1)
    rw [Finset.sum_eq_single k hoff (fun h' => absurd hk h')] at hsum
    exact hsum
  have hev : ϖ k =ᶠ[nhds t] fun _ => (1 : ℝ) :=
    Filter.eventually_of_mem ((isOpen_Ioo.inter isOpen_Ioo).mem_nhds ⟨ht, hc⟩) hone
  rw [hev.deriv_eq]
  simp

/-- **The derivative of a weight is the sum of its rising and falling pieces** on the interior
of the window. -/
theorem trWeight_add (hodd : ∀ k ∈ kset, Odd k) (hτ : 0 < τ)
    (hpart : IsLiftPartition kset ϖ (fun k => Set.Icc (((k : ℝ) - 61 / 48) * τ)
      (((k : ℝ) + 61 / 48) * τ)) quiet (Set.Icc tA tZ) τ Cpart)
    {k : ℤ} (hk : k ∈ kset) {t : ℝ} (ht : t ∈ Set.Ioo tA tZ) :
    deriv (ϖ k) t = trWeight ϖ τ tA tZ k true t + trWeight ϖ τ tA tZ k false t := by
  by_cases hd : deriv (ϖ k) t = 0
  · have h0 : ∀ σ, trWeight ϖ τ tA tZ k σ t = 0 := by
      intro σ
      unfold trWeight
      by_cases hm : t ∈ Set.Icc (trLo τ tA k σ) (trHi τ tZ k σ)
      · rw [Set.indicator_of_mem hm, hd]
      · rw [Set.indicator_of_notMem hm]
    rw [h0 true, h0 false, hd, add_zero]
  · have hwin := mem_window_of_deriv hpart hk hd
    have hnc : ¬ (((k : ℝ) - 35 / 48) * τ < t ∧ t < ((k : ℝ) + 35 / 48) * τ) := fun hc =>
      hd (deriv_eq_zero_of_center hodd hτ hpart hk ht hc)
    obtain ⟨hw1, hw2⟩ := hwin
    have ht1 : tA ≤ t := ht.1.le
    have ht2 : t ≤ tZ := ht.2.le
    rcases le_or_gt t ((k : ℝ) * τ) with hle | hlt
    · have hR : t ≤ ((k : ℝ) - 35 / 48) * τ := by
        by_contra hR'
        exact hnc ⟨not_le.1 hR', by linarith⟩
      have hmemR : t ∈ Set.Icc (trLo τ tA k false) (trHi τ tZ k false) :=
        ⟨max_le hw1 ht1, le_min hR ht2⟩
      have hnotF : t ∉ Set.Icc (trLo τ tA k true) (trHi τ tZ k true) := by
        intro hF
        have h1 : ((k : ℝ) + 35 / 48) * τ ≤ t := le_trans (le_max_left _ _) hF.1
        linarith
      unfold trWeight
      rw [Set.indicator_of_notMem hnotF, Set.indicator_of_mem hmemR, zero_add]
    · have hF : ((k : ℝ) + 35 / 48) * τ ≤ t := by
        by_contra hF'
        exact hnc ⟨by linarith, not_le.1 hF'⟩
      have hmemF : t ∈ Set.Icc (trLo τ tA k true) (trHi τ tZ k true) :=
        ⟨max_le hF ht1, le_min hw2 ht2⟩
      have hnotR : t ∉ Set.Icc (trLo τ tA k false) (trHi τ tZ k false) := by
        intro hR
        have h1 : t ≤ ((k : ℝ) - 35 / 48) * τ := le_trans hR.2 (min_le_left _ _)
        linarith
      unfold trWeight
      rw [Set.indicator_of_mem hmemF, Set.indicator_of_notMem hnotR, add_zero]

/-- **The partition term without its degree-zero part.** If on the window every pulse lift is the
coarse field `A` plus a remainder `Gk k`, then on the interior of the window
`∑_k ϖ_k' 𝒯_k = ∑_{k, σ} ψ_{k,σ} Gk k` with the rising and falling pieces `ψ_{k,σ}`. -/
theorem partition_term_decomp (hodd : ∀ k ∈ kset, Odd k) (hτ : 0 < τ)
    (hpart : IsLiftPartition kset ϖ (fun k => Set.Icc (((k : ℝ) - 61 / 48) * τ)
      (((k : ℝ) + 61 / 48) * τ)) quiet (Set.Icc tA tZ) τ Cpart)
    {t : ℝ} (ht : t ∈ Set.Ioo tA tZ) {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Lk : ℤ → E) (A : E) (Gk : ℤ → E)
    (hL : ∀ k ∈ kset, deriv (ϖ k) t ≠ 0 → Lk k = A + Gk k) :
    ∑ k ∈ kset, deriv (ϖ k) t • Lk k =
      ∑ p ∈ kset ×ˢ (Finset.univ : Finset Bool), trWeight ϖ τ tA tZ p.1 p.2 t • Gk p.1 := by
  have h1 : ∀ k ∈ kset, deriv (ϖ k) t • Lk k = deriv (ϖ k) t • A + deriv (ϖ k) t • Gk k := by
    intro k hk
    by_cases hd : deriv (ϖ k) t = 0
    · simp only [hd, zero_smul, add_zero]
    · rw [hL k hk hd, smul_add]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.sum_smul,
    sum_deriv_eq_zero hpart ht, zero_smul, zero_add, Finset.sum_product]
  refine Finset.sum_congr rfl fun k hk => ?_
  show deriv (ϖ k) t • Gk k = ∑ σ : Bool, trWeight ϖ τ tA tZ k σ t • Gk k
  rw [Fintype.sum_bool, ← add_smul, ← trWeight_add hodd hτ hpart hk ht]

end Partition

/-! ### At most two active pieces -/

theorem odd_trIndex {p : ℤ × Bool} (hp : Odd p.1) : Odd (trIndex p) := by
  obtain ⟨k, σ⟩ := p
  cases σ
  · exact Odd.sub_even hp even_two
  · exact hp

theorem mem_trIndex {τ tA tZ : ℝ} {p : ℤ × Bool} {t : ℝ}
    (hm : t ∈ Set.Icc (trLo τ tA p.1 p.2) (trHi τ tZ p.1 p.2)) :
    t ∈ Set.Icc ((((trIndex p : ℤ) : ℝ) + 35 / 48) * τ)
      ((((trIndex p : ℤ) : ℝ) + 61 / 48) * τ) := by
  obtain ⟨k, σ⟩ := p
  cases σ
  · have hm' : t ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * τ) tA)
        (min (((k : ℝ) - 35 / 48) * τ) tZ) := hm
    have h1 := le_trans (le_max_left _ _) hm'.1
    have h2 := le_trans hm'.2 (min_le_left _ _)
    show t ∈ Set.Icc ((((k - 2 : ℤ) : ℝ) + 35 / 48) * τ) ((((k - 2 : ℤ) : ℝ) + 61 / 48) * τ)
    push_cast
    exact ⟨by linarith, by linarith⟩
  · have hm' : t ∈ Set.Icc (max (((k : ℝ) + 35 / 48) * τ) tA)
        (min (((k : ℝ) + 61 / 48) * τ) tZ) := hm
    show t ∈ Set.Icc (((k : ℝ) + 35 / 48) * τ) (((k : ℝ) + 61 / 48) * τ)
    exact ⟨le_trans (le_max_left _ _) hm'.1, le_trans hm'.2 (min_le_left _ _)⟩

/-- Distinct odd overlaps are disjoint. -/
theorem trIndex_eq_of_mem {τ t : ℝ} (hτ : 0 < τ) {j j' : ℤ} (hj : Odd j) (hj' : Odd j')
    (h1 : t ∈ Set.Icc (((j : ℝ) + 35 / 48) * τ) (((j : ℝ) + 61 / 48) * τ))
    (h2 : t ∈ Set.Icc (((j' : ℝ) + 35 / 48) * τ) (((j' : ℝ) + 61 / 48) * τ)) : j = j' := by
  by_contra hne
  have hsplit : j + 2 ≤ j' ∨ j' + 2 ≤ j := by
    obtain ⟨a, ha⟩ := hj
    obtain ⟨b, hb⟩ := hj'
    omega
  obtain ⟨h11, h12⟩ := h1
  obtain ⟨h21, h22⟩ := h2
  rcases hsplit with h | h
  · have h' : (j : ℝ) + 2 ≤ j' := by exact_mod_cast h
    have e : ((j : ℝ) + 2) * τ ≤ (j' : ℝ) * τ := mul_le_mul_of_nonneg_right h' hτ.le
    linarith
  · have h' : (j' : ℝ) + 2 ≤ j := by exact_mod_cast h
    have e : ((j' : ℝ) + 2) * τ ≤ (j : ℝ) * τ := mul_le_mul_of_nonneg_right h' hτ.le
    linarith

/-- **At most two transition pieces are active at a time.** -/
theorem card_active_le_two {S : Finset (ℤ × Bool)} (hodd : ∀ p ∈ S, Odd p.1)
    (ϖ : ℤ → ℝ → ℝ) {τ : ℝ} (hτ : 0 < τ) (tA tZ t : ℝ) :
    (S.filter fun p => trWeight ϖ τ tA tZ p.1 p.2 t ≠ 0).card ≤ 2 := by
  rcases (S.filter fun p => trWeight ϖ τ tA tZ p.1 p.2 t ≠ 0).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.card_empty]
    exact Nat.zero_le _
  · obtain ⟨p₀, hp₀⟩ := hne
    have hp₀' := Finset.mem_filter.1 hp₀
    have hsub : (S.filter fun p => trWeight ϖ τ tA tZ p.1 p.2 t ≠ 0) ⊆
        {(trIndex p₀, true), (trIndex p₀ + 2, false)} := by
      intro p hp
      have hp' := Finset.mem_filter.1 hp
      have hij : trIndex p = trIndex p₀ := trIndex_eq_of_mem hτ (odd_trIndex (hodd p hp'.1))
        (odd_trIndex (hodd p₀ hp₀'.1)) (mem_trIndex (trWeight_ne_zero hp'.2).1)
        (mem_trIndex (trWeight_ne_zero hp₀'.2).1)
      obtain ⟨k, σ⟩ := p
      cases σ
      · have hk : k - 2 = trIndex p₀ := hij
        rw [Finset.mem_insert, Finset.mem_singleton]
        right
        rw [← hk, sub_add_cancel]
      · have hk : k = trIndex p₀ := hij
        rw [Finset.mem_insert]
        left
        rw [hk]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two

/-! ### The quiet gaps -/

/-- **Every pulse vanishes between two odd slots**: `[(j + 2/3)τ, (j + 4/3)τ]` is quiet. -/
theorem mem_ocQuietTimes_of_gap {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) {j : ℤ} (hj : Odd j) {t : ℝ}
    (h1 : ((j : ℝ) + 2 / 3) * ocTau α q Λ m ≤ t) (h2 : t ≤ ((j : ℝ) + 4 / 3) * ocTau α q Λ m) :
    t ∈ ocQuietTimes α q Λ ζ m := by
  have hτ : 0 < ocTau α q Λ m := Construction.Stream.ocTau_pos hΛ
  have hzero : ∀ k' : ℤ, Odd k' → ocPulse α q Λ ζ m k' t = 0 := by
    intro k' hk'
    by_contra hp
    obtain ⟨hl, hu⟩ := CycleReference.pulse_nonzero_center_distance hΛ hζ hp
    have hsplit : k' ≤ j ∨ j + 2 ≤ k' := by
      obtain ⟨a, ha⟩ := hj
      obtain ⟨b, hb⟩ := hk'
      omega
    rcases hsplit with hle | hge
    · have hle' : (k' : ℝ) ≤ j := by exact_mod_cast hle
      have e : (k' : ℝ) * ocTau α q Λ m ≤ (j : ℝ) * ocTau α q Λ m :=
        mul_le_mul_of_nonneg_right hle' hτ.le
      linarith
    · have hge' : (j : ℝ) + 2 ≤ k' := by exact_mod_cast hge
      have e : ((j : ℝ) + 2) * ocTau α q Λ m ≤ (k' : ℝ) * ocTau α q Λ m :=
        mul_le_mul_of_nonneg_right hge' hτ.le
      linarith
  have hz : ocPulseStream α q Λ ζ m t = fun _ => 0 := funext fun y => by
    unfold ocPulseStream
    refine (tsum_congr fun k' => ?_).trans tsum_zero
    rw [hzero k'.1 k'.2, zero_mul]
  intro y
  have hg : spaceGrad (fun _ : Vec 2 => (0 : ℝ)) y = 0 := by
    funext i
    simp [spaceGrad]
  show sigmaMat.mulVec (spaceGrad (ocPulseStream α q Λ ζ m t) y) = 0
  rw [hz, hg, Matrix.mulVec_zero]

/-! ### The quiet entrance of a zero-start lift -/

section Start

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

/-- **The positive-degree lift coefficients vanish at the start of the window.** -/
theorem liftSequence_start_coeff_zero {Q : LiftOperatorData ι h D} {sX sZ : ℕ} {t₀ t₁ : ℝ}
    {N H : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)
    (ht : t₀ ≤ t₁) {hh n : ℕ} (hhH : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N) {m : ℕ} (hm : m ≤ n)
    (α : DerivativeWord2 m) (X z : Vec 2) (v u : ι) : Cc hh n m α t₀ X z v u = 0 := by
  classical
  have hsymm : QuietDecay.LiftSymm (Cc hh n) := fun m' α' σ =>
    hseq.2.2.2.2.1 hh hhH n m' α' σ
  ext x
  have hsm : ContDiff ℝ (⊤ : ℕ∞)
      (fun Y : Vec 2 => QuietDecay.monoF X (List.ofFn α) Y • (Pi.single u x : ∀ i, h i)) :=
    (QuietDecay.contDiff_monoF X _ (List.ofFn α)).smul contDiff_const
  have h0 := liftSequence_start_positive hseq ht hhH hn hnN _ hsm X z
  rw [QuietDecay.liftApply_monoF hsymm n hm α (Pi.single u x) t₀ X z] at h0
  have h1 := congrFun h0 v
  simp only [Pi.smul_apply, Pi.zero_apply] at h1
  have hK : (QuietDecay.liftK α : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 (QuietDecay.one_le_liftK α))
  have h2 := (smul_eq_zero.1 h1).resolve_left hK
  rw [Finset.sum_eq_single u (fun u' _ hu' => by rw [Pi.single_eq_of_ne hu', map_zero])
    (fun hu => absurd (Finset.mem_univ u) hu), Pi.single_eq_same] at h2
  simp only [zero_apply]
  exact h2

/-- **A zero-start lift has zero quiet entrance trace at the start of its window.** -/
theorem hasQuietEntranceTrace_start (π : ι → ℝ) {Q : LiftOperatorData ι h D} {sX sZ : ℕ}
    {t₀ t₁ : ℝ} {N H : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (ht : t₀ ≤ t₁) (lam : ℝ) (K L : ℕ) :
    HasQuietEntranceTrace π Cc t₀ lam N H K L (fun _ => 0) := by
  refine ⟨fun _ _ => le_rfl, fun b hb n hn hnN m hm p _ q _ => ?_⟩
  have hz : ∀ (α : DerivativeWord2 m) (v u : ι),
      mixedCellL2Jet {t₀} p q (fun t X z => Cc b n m α t X z v u) = 0 := by
    intro α v u
    refine le_antisymm ?_ zero_le
    unfold mixedCellL2Jet
    refine iSup₂_le fun t ht' => iSup_le fun X => iSup_le fun α' => iSup_le fun β => ?_
    have htt : t = t₀ := ht'
    have hzero : ∀ X' z', Cc b n m α t X' z' v u = 0 := fun X' z' => by
      rw [htt]
      exact liftSequence_start_coeff_zero hseq ht hb hn hnN hm α X' z' v u
    simp [hzero, orderedDerivative_zero_fun]
  have hS : schurSums π (fun _ _ => ∑ _a : DerivativeWord2 m, (0 : ℝ≥0∞)) = 0 :=
    le_antisymm (max_le (iSup_le fun v => by simp) (iSup_le fun u => by simp)) zero_le
  unfold schurMixedCellL2Jet
  rw [show (fun v u => ∑ a : DerivativeWord2 m,
      mixedCellL2Jet {t₀} p q (fun t X z => Cc b n m a t X z v u)) =
      fun _ _ => ∑ _a : DerivativeWord2 m, (0 : ℝ≥0∞) from
    funext fun v => funext fun u => Finset.sum_congr rfl fun a _ => hz a v u, hS]
  exact zero_le

end Start

/-! ### The scales of one transition -/

/-- **The price of one transition at the scale of the pulse.** With `|ψ| ≤ P/τ`, a gap of length
`d ≤ τ` and a damping time `τ/48`: `C J (P/τ) ℓ √d e^{-c(τ/48)/ℓ²} ≤ C J P ℓ τ^{-1/2}
e^{-(c/48)τ/ℓ²}`. -/
theorem decay_factor_le {C J P ℓ τ d c : ℝ} (hC : 0 ≤ C) (hJ : 0 ≤ J) (hP : 0 ≤ P)
    (hℓ : 0 ≤ ℓ) (hτ : 0 < τ) (hdτ : d ≤ τ) :
    C * J * (P / τ) * ℓ * Real.sqrt d * Real.exp (-(c * (τ / 48) / ℓ ^ 2)) ≤
      C * J * P * ℓ * Real.sqrt (1 / τ) * Real.exp (-(c / 48 * τ / ℓ ^ 2)) := by
  have he : Real.exp (-(c * (τ / 48) / ℓ ^ 2)) = Real.exp (-(c / 48 * τ / ℓ ^ 2)) := by
    congr 1
    ring
  rw [he]
  have hs : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτ.le
  have h2 : P / τ * Real.sqrt τ = P * Real.sqrt (1 / τ) := by
    rw [one_div, Real.sqrt_inv]
    calc P / τ * Real.sqrt τ = P * (Real.sqrt τ / τ) := by ring
      _ = P * (Real.sqrt τ / (Real.sqrt τ * Real.sqrt τ)) := by rw [hs]
      _ = P * (Real.sqrt τ)⁻¹ := by rw [div_self_mul_self']
  have hsq : P / τ * Real.sqrt d ≤ P * Real.sqrt (1 / τ) := by
    rw [← h2]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdτ) (div_nonneg hP hτ.le)
  have hE : 0 ≤ C * J * ℓ * Real.exp (-(c / 48 * τ / ℓ ^ 2)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hJ) hℓ) (Real.exp_pos _).le
  calc C * J * (P / τ) * ℓ * Real.sqrt d * Real.exp (-(c / 48 * τ / ℓ ^ 2)) =
        (C * J * ℓ * Real.exp (-(c / 48 * τ / ℓ ^ 2))) * (P / τ * Real.sqrt d) := by ring
    _ ≤ (C * J * ℓ * Real.exp (-(c / 48 * τ / ℓ ^ 2))) * (P * Real.sqrt (1 / τ)) :=
        mul_le_mul_of_nonneg_left hsq hE
    _ = C * J * P * ℓ * Real.sqrt (1 / τ) * Real.exp (-(c / 48 * τ / ℓ ^ 2)) := by ring

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The glued edge term** (the edge term `∑_u 𝒮_{vu} û_u` of the actual equation). Summed with the
family weights over the observed pulses, the source parts of the pulse rests, scaled by `ℓ⁻²` and
tested against a `C¹` periodic `φ`, are minus the pairing with `∇φ` of the physical edge flux of the
glued lift (`glued_edges`): each pulse contributes the flux of its own lift
(`pulse_edge_tested_instance`, with the family flux identified at every weighted time by
`obs_family_flux`), and the flux is linear over the weighted sum (`physEdgeFluxVec_weighted_sum`).
-/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

/-- **The glued edge term of a finite-rank coarse field.** -/
theorem glued_edges {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {φs : ℝ → Vec 2 → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) (hφs : IsAdmissibleStream φs) {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B)
    {ρ E : ℝ} (hρ : 0 < ρ) {D : ℕ} {Pc : Type*} {Ctx : Pc → Type*}
    (F : ChartedFamily ι h D Pc Ctx) (actual : ∀ p, Ctx p) (K : ι → ℕ)
    (hdesc : F.IsDescending K) (htorus : IsTorusCompatible F actual E) (T : F.Atlas)
    {tA tZ : ℝ} (hTcons : T.IsConsecutiveClosed (Icc tA tZ))
    (hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m) (Icc tA tZ))
    (hTq : T.IsQuiet ν (ocEpsilon q Λ m) E)
    (hTact : ∀ p q' (hpq : T.adjacent p q'),
      ((F.piece p).output ∩ (F.piece q').output ∩ Icc tA tZ).Nonempty →
        T.sameCtx p q' hpq (actual p) (actual q'))
    (pp : ℤ → Pc)
    (hpp : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      (F.piece (pp k)).label = ocPulseChartIndex α q Λ m k ∧
      (∀ t, ⇑((F.piece (pp k)).material t) =
        ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) ∧
      ocPulseWindow α q Λ m k ∩ Icc tA tZ ⊆ (F.piece (pp k)).output)
    (hppinj : Set.InjOn pp ↑(ocObsPulses α q Λ m tA tZ)) {quiet : Set ℝ} {Cpart : ℝ}
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k))
      (ocPulseWindow α q Λ m) quiet (Icc tA tZ) (ocTau α q Λ m) Cpart)
    (hcov : ∀ t ∈ Icc tA tZ, ∃ p, t ∈ (F.piece p).output)
    {π : ι → ℝ} {e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : ℤ → Fin 2}
    {V : ℤ → ℝ → ℝ → ℝ} {H N K₀ k₀ L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSetting (pulseLiftData α q Λ m ζ φs hφs ν B ρ (ρ / E) k
          (F.fiber (pp k) (actual (pp k)))) π
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)
        e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ (par k) (V k) H N K₀ k₀ L qs qf CG Cw Cj edgeM Θ)
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (pulseLiftData α q Λ m ζ φs hφs ν B ρ (ρ / E) k
          (F.fiber (pp k) (actual (pp k)))) sX sZ
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    {κ : Type*} [Fintype κ] (cf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (φ j)) (hφp : ∀ j, IsZ2Periodic (φ j))
    (hcs : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ (n : Fin 2 → ℤ) v u d,
      ∀ γ ∈ (pulseLiftData α q Λ m ζ φs hφs ν B ρ (ρ / E) k
        (F.fiber (pp k) (actual (pp k)))).edge v u d, ∀ w t X z,
        γ.coeff w t (X + ρ⁻¹ • latticeShift n) z = γ.coeff w t X z)
    {t : ℝ} (ht : t ∈ Icc tA tZ) (v : ι) {φt : Vec 2 → h v} (hφt : ContDiff ℝ 1 φt)
    (hφtp : IsZ2Periodic φt) :
    ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t * ((ocEll q Λ m ν ^ 2)⁻¹ *
        ∫ x in unitCube, inner ℝ
          (restSource (pulseLiftData α q Λ m ζ φs hφs ν B ρ (ρ / E) k
              (F.fiber (pp k) (actual (pp k)))) (Cc k) N H (ocDStar q Λ m ν B / ρ)
            (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
              (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t
            (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t x) v) (φt x)) =
      -∫ x in unitCube, ∑ a₀ : Fin 2, inner ℝ
        (physEdgeFluxVec F ν (ocEpsilon q Λ m) E actual K t
          (fun y => ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t •
            obsLift α q Λ m φs hφs ν B ρ Cc N H cf φ k t y) v x a₀)
        (fderiv ℝ φt x (basisVec a₀)) := by
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  -- the per-pulse tested identities and continuity at the weighted pulses
  have hpulse : ∀ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t ≠ 0 →
      ((ocEll q Λ m ν ^ 2)⁻¹ * ∫ x in unitCube, inner ℝ
          (restSource (pulseLiftData α q Λ m ζ φs hφs ν B ρ (ρ / E) k
              (F.fiber (pp k) (actual (pp k)))) (Cc k) N H (ocDStar q Λ m ν B / ρ)
            (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
              (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t
            (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t x) v) (φt x) =
        -∫ x in unitCube, ∑ a₀ : Fin 2, inner ℝ
          (physEdgeFluxVec F ν (ocEpsilon q Λ m) E actual K t
            (fun y => obsLift α q Λ m φs hφs ν B ρ Cc N H cf φ k t y) v x a₀)
          (fderiv ℝ φt x (basisVec a₀))) ∧
      (∀ a₀ : Fin 2, Continuous (fun x => physEdgeFluxVec F ν (ocEpsilon q Λ m) E actual K t
        (fun y => obsLift α q Λ m φs hφs ν B ρ Cc N H cf φ k t y) v x a₀)) ∧
      ContDiff ℝ (D : ℕ∞) (fun y => obsLift α q Λ m φs hφs ν B ρ Cc N H cf φ k t y) := by
    intro k hk hw
    have hwin : t ∈ ocPulseWindow α q Λ m k := hpart.2.2.2.1 k hk t hw
    have hwin' : ((k : ℝ) - 61 / 48) * ocTau α q Λ m ≤ t ∧
        t ≤ ((k : ℝ) + 61 / 48) * ocTau α q Λ m := hwin
    have hs : (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Icc
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) :=
      ⟨by rw [div_eq_inv_mul]
          exact mul_le_mul_of_nonneg_left (max_le hwin'.1 ht.1) (inv_nonneg.2 hc0.le),
        by rw [div_eq_inv_mul]
           exact mul_le_mul_of_nonneg_left (le_min hwin'.2 ht.2) (inv_nonneg.2 hc0.le)⟩
    obtain ⟨hid, hcont⟩ := pulse_edge_tested_instance hΛ hφs hν hB hρ F actual K htorus (pp k)
      (hpp k hk).2.1 (P k hk) sX sZ hsZ (Cc k) (hseq k hk) cf φ hφ hφp (hcs k hk) hs v
      (fun {U} hU x a₀ => obs_family_flux hΛ hζ F ν (ocEpsilon q Λ m) E actual K hdesc T hTcons
        hTcov hTq hTact pp (fun k' hk' => (hpp k' hk').1) (fun k' hk' => (hpp k' hk').2.2)
        hppinj hpart hcov hk ht hw hU (Nat.le_succ D) v x a₀) hφt hφtp
    refine ⟨hid, hcont, ?_⟩
    have hχj := Charts.contDiff_ocChart_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)
    have hψs : ContDiff ℝ (⊤ : ℕ∞)
        (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) :=
      (Charts.contDiff_ocChartInv_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)).comp
        (contDiff_const.prodMk contDiff_id)
    exact (setting_labelLift_contDiff (P k hk) hsZ (hseq k hk) _ _ ρ (ocEpsilon q Λ m)
      (chartField_contDiff cf φ hφ _ hχj _ ρ _) hs).comp (hψs.of_le (by exact_mod_cast le_top))
  -- the flux of the glued lift is the weighted sum of the pulse fluxes
  have hpt : ∀ x, ∑ a₀ : Fin 2, inner ℝ
      (physEdgeFluxVec F ν (ocEpsilon q Λ m) E actual K t
        (fun y => ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t •
          obsLift α q Λ m φs hφs ν B ρ Cc N H cf φ k t y) v x a₀)
      (fderiv ℝ φt x (basisVec a₀)) =
      ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t * ∑ a₀ : Fin 2, inner ℝ
        (physEdgeFluxVec F ν (ocEpsilon q Λ m) E actual K t
          (fun y => obsLift α q Λ m φs hφs ν B ρ Cc N H cf φ k t y) v x a₀)
        (fderiv ℝ φt x (basisVec a₀)) := fun x => by
    rw [physEdgeFluxVec_weighted_sum F ν (ocEpsilon q Λ m) E actual K t _
      (fun k => F.weight (pp k) t)
      (fun k y => obsLift α q Λ m φs hφs ν B ρ Cc N H cf φ k t y)
      (fun k hk hw => (hpulse k hk hw).2.2) v x]
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, sum_inner,
      real_inner_smul_left, Finset.mul_sum]
    exact Finset.sum_comm
  simp only [hpt]
  rw [integral_weighted_sum _ (fun k => F.weight (pp k) t)
      (fun k x => ∑ a₀ : Fin 2, inner ℝ
        (physEdgeFluxVec F ν (ocEpsilon q Λ m) E actual K t
          (fun y => obsLift α q Λ m φs hφs ν B ρ Cc N H cf φ k t y) v x a₀)
        (fderiv ℝ φt x (basisVec a₀))) (fun k hk hw =>
      CoupledEnergy.Galerkin.continuous_cell_integrable _
        (continuous_finsetSum _ fun a₀ _ => ((hpulse k hk hw).2.1 a₀).inner
          ((hφt.continuous_fderiv one_ne_zero).clm_apply continuous_const))),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hw : F.weight (pp k) t = 0
  · rw [hw, zero_mul, zero_mul, neg_zero]
  · rw [(hpulse k hk hw).1, mul_neg]
end

/-! **The glued tail term** (the sampled tail of the lifts).
Summed with the partition weights over the observed pulses, the tails of the pulse rests, scaled
by `ℓ⁻²` and tested against a `C¹` periodic `φ`, are
`-∫ ∑_a ⟪R_a, ∂_a φ⟫ + ∫ ⟪q, φ⟫` with the glued tail flux `R = ∑_k ϖ_k R_k` and force
`q = ∑_k ϖ_k q_k` (`glued_tail`), `R_k`, `q_k` the physical tail flux and force of the pulse `k`
(`tailFluxPhys`, `tailForcePhys`: the Piola transports of the cleanup chains of its tail). -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

/-- **The glued tail term of a finite-rank coarse field.** -/
theorem glued_tail {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {φs : ℝ → Vec 2 → ℝ} (hΛ : 1 ≤ Λ)
    (hφs : IsAdmissibleStream φs) {ν B : ℝ} (hν : 0 < ν) {ρ lam : ℝ} (hρ : 0 < ρ) {D : ℕ}
    (edge : ℤ → ConstituentEdges D h) {tA tZ : ℝ} (ϖ : ℤ → ℝ → ℝ) {quiet : Set ℝ}
    {Cpart : ℝ}
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) ϖ (ocPulseWindow α q Λ m) quiet
      (Icc tA tZ) (ocTau α q Λ m) Cpart)
    {π : ι → ℝ} {e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : ℤ → Fin 2}
    {V : ℤ → ℝ → ℝ → ℝ} {H N K k₀ L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSetting (pulseLiftData α q Λ m ζ φs hφs ν B ρ lam k (edge k)) π
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)
        e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ (par k) (V k) H N K k₀ L qs qf CG Cw Cj edgeM Θ)
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (pulseLiftData α q Λ m ζ φs hφs ν B ρ lam k (edge k)) sX sZ
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    (sXc sZc Acl : ℕ) (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (hX : sXc ≤ K + D + 2) (hZ : sZc ≤ max (k₀ + 1) (L + 2))
    {κ : Type*} [Fintype κ] (cf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (φ j)) (hφp : ∀ j, IsZ2Periodic (φ j))
    (hcs : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ (n : Fin 2 → ℤ) v u d,
      ∀ γ ∈ (pulseLiftData α q Λ m ζ φs hφs ν B ρ lam k (edge k)).edge v u d,
        ∀ w t X z, γ.coeff w t (X + ρ⁻¹ • latticeShift n) z = γ.coeff w t X z)
    (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ hh, hh ≤ H →
      ∀ τ ∈ Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXc sZc Acl
        (tailScalarField (fun _ => 0) N D (ocDStar q Λ m ν B / ρ)
          (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
            (ocEll q Λ m ν ^ 2) ρ) τ)
        (tailFluxField (fun n => tailFluxCoefficient (par k)
            (pulseLiftData α q Λ m ζ φs hφs ν B ρ lam k (edge k)) (Cc k) N hh n) N D
          (ocDStar q Λ m ν B / ρ)
          (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
            (ocEll q Λ m ν ^ 2) ρ) τ)
        (fun j => Vc k hh j τ))
    {t : ℝ} (ht : t ∈ Icc tA tZ) (v : ι) (φt : Vec 2 → h v) (hφt : ContDiff ℝ 1 φt)
    (hφtp : IsZ2Periodic φt) :
    ∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t * ((ocEll q Λ m ν ^ 2)⁻¹ *
        ∫ x in unitCube, inner ℝ
          (restTail (pulseLiftData α q Λ m ζ φs hφs ν B ρ lam k (edge k)) (Cc k) N H
            (ocDStar q Λ m ν B / ρ)
            (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
              (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t
            (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t x) v) (φt x)) =
      -(∫ x in unitCube, ∑ a₀ : Fin 2, inner ℝ
          ((∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t •
            tailFluxPhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
              (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vc k) t x a₀) v)
          (fderiv ℝ φt x (basisVec a₀))) +
        ∫ x in unitCube, inner ℝ
          ((∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t •
            tailForcePhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
              (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vc k) t x) v)
          (φt x) := by
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  obtain ⟨M, hM⟩ := pulse_e_inv_nat q Λ m
  -- the per-pulse tested identities and continuity at the weighted pulses
  have hpulse : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t ≠ 0 →
      ((ocEll q Λ m ν ^ 2)⁻¹ * ∫ x in unitCube, inner ℝ
          (restTail (pulseLiftData α q Λ m ζ φs hφs ν B ρ lam k (edge k)) (Cc k) N H
            (ocDStar q Λ m ν B / ρ)
            (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
              (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t
            (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t x) v) (φt x) =
        -(∫ x in unitCube, ∑ a₀ : Fin 2, inner ℝ
            (tailFluxPhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
              (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vc k) t x a₀ v)
            (fderiv ℝ φt x (basisVec a₀))) +
          ∫ x in unitCube, inner ℝ
            (tailForcePhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
              (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vc k) t x v)
            (φt x)) ∧
      (∀ a₀ : Fin 2, Continuous (fun x =>
        tailFluxPhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vc k) t x a₀ v)) ∧
      Continuous (fun x =>
        tailForcePhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vc k) t x v) := by
    intro k hk hw
    have hwin : t ∈ ocPulseWindow α q Λ m k := hpart.2.2.2.1 k hk t hw
    have hwin' : ((k : ℝ) - 61 / 48) * ocTau α q Λ m ≤ t ∧
        t ≤ ((k : ℝ) + 61 / 48) * ocTau α q Λ m := hwin
    have hs : (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Icc
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) :=
      ⟨by rw [div_eq_inv_mul]
          exact mul_le_mul_of_nonneg_left (max_le hwin'.1 ht.1) (inv_nonneg.2 hc0.le),
        by rw [div_eq_inv_mul]
           exact mul_le_mul_of_nonneg_left (le_min hwin'.2 ht.2) (inv_nonneg.2 hc0.le)⟩
    have hχj := Charts.contDiff_ocChart_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)
    have hχs : ContDiff ℝ (⊤ : ℕ∞) (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) :=
      hχj.comp (contDiff_const.prodMk contDiff_id)
    have hψs : ContDiff ℝ (⊤ : ℕ∞)
        (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) :=
      (Charts.contDiff_ocChartInv_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)).comp
        (contDiff_const.prodMk contDiff_id)
    have hid := setting_pulse_restTail_tested (P k hk) sX sZ hsX hsZ (Cc k) (hseq k hk) sXc sZc
      Acl hAcl hXc hZc hX hZ (ocDStar q Λ m ν B / ρ) cf φ hφ hφp α q Λ m hφs
      (ocPulseChartIndex α q Λ m k) hρ he M hM
      (pulse_G_slow_invariant α q Λ m ζ hφs ν B hρ.ne' lam k (edge k)) (hcs k hk) (Vc k)
      (hV k hk) hs v φt hφt hφtp
    have hreg := setting_restTail_continuous (P k hk) sX sZ hsX hsZ (Cc k) (hseq k hk) sXc sZc
      Acl hAcl hXc hZc hX hZ (ocDStar q Λ m ν B / ρ) (ρs := ρ) (es := ocEpsilon q Λ m)
      (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
        (ocEll q Λ m ν ^ 2) ρ) (Vc k) (hV k hk) hs
      (chartField_contDiff cf φ hφ _ hχj _ ρ _) hχs hψs
      (Charts.ocChartInv_ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t)
      (Charts.ocChart_ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) v
    refine ⟨?_, hreg.1, hreg.2⟩
    rw [← hid, ← integral_const_mul]
    simp only [Pi.smul_apply, real_inner_smul_left]
  -- the glued flux and force, tested
  have hptR : ∀ x, ∑ a₀ : Fin 2, inner ℝ
      ((∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t •
        tailFluxPhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vc k) t x a₀) v)
      (fderiv ℝ φt x (basisVec a₀)) =
      ∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t * ∑ a₀ : Fin 2, inner ℝ
        (tailFluxPhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vc k) t x a₀ v)
        (fderiv ℝ φt x (basisVec a₀)) := fun x => by
    simp only [Finset.sum_apply, Pi.smul_apply, sum_inner, real_inner_smul_left, Finset.mul_sum]
    exact Finset.sum_comm
  have hptq : ∀ x, inner ℝ
      ((∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t •
        tailForcePhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vc k) t x) v)
      (φt x) =
      ∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t * inner ℝ
        (tailForcePhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vc k) t x v)
        (φt x) := fun x => by
    simp only [Finset.sum_apply, Pi.smul_apply, sum_inner, real_inner_smul_left]
  have hdφ : ∀ a₀ : Fin 2, Continuous (fun x => fderiv ℝ φt x (basisVec a₀)) := fun a₀ =>
    (hφt.continuous_fderiv one_ne_zero).clm_apply continuous_const
  simp only [hptR, hptq]
  rw [integral_weighted_sum _ (fun k => ϖ k t)
      (fun k x => ∑ a₀ : Fin 2, inner ℝ
        (tailFluxPhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vc k) t x a₀ v)
        (fderiv ℝ φt x (basisVec a₀))) (fun k hk hw =>
      CoupledEnergy.Galerkin.continuous_cell_integrable _
        (continuous_finsetSum _ fun a₀ _ => ((hpulse k hk hw).2.1 a₀).inner (hdφ a₀))),
    integral_weighted_sum _ (fun k => ϖ k t)
      (fun k x => inner ℝ
        (tailForcePhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vc k) t x v)
        (φt x)) (fun k hk hw =>
      CoupledEnergy.Galerkin.continuous_cell_integrable _
        ((hpulse k hk hw).2.2.inner hφt.continuous)),
    ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hw : ϖ k t = 0
  · rw [hw, zero_mul, zero_mul, zero_mul, neg_zero, add_zero]
  · rw [(hpulse k hk hw).1]
    ring
end

end AVRegularity.CycleComparison.Reconstruction
end
