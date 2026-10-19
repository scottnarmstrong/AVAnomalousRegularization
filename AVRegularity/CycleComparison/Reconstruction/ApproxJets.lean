-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.ReconForceCarrier
import AVRegularity.CycleComparison.Reconstruction.PulseIdentity
import AVRegularity.CycleComparison.Reconstruction.ReconChains
import AVRegularity.CycleComparison.Reconstruction.LiftSource
public import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
import AVRegularity.CycleComparison.Reconstruction.Continuity
public import AVRegularity.CycleComparison.Reconstruction.PartitionBound
public import AVRegularity.CycleComparison.Reconstruction.ReconLiftSlices
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.CycleComparison.Reconstruction.FiniteRankIdentity
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.Weighted.MetricWordCoefficientArrayBound
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance Set
open AVRegularity.CycleComparison.Lift AVRegularity.CycleComparison.LiftMeanEntrywise
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The lifted pieces of the residual force on a reconstruction window**. At a
time of the window, the physical lift of an observed pulse of a coarse field of class `C^{N}`
that is periodic at that time is periodic (`ReconWindowAt.pulseLift_periodic`, from the label
periodicity of the lift at a single time, `setting_labelLift_periodic_at`); hence so is every
glued lift with weights supported in the pulse windows (`ReconWindowAt.gluedLift_weights_periodic`),
such as the glued lift and the partition term `∑_k ϖ_k' 𝒯_k a`. -/

section Bounded

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

/-- **Jets of a glued lift with bounded weights.** If the weights at the time `t` are bounded by
`Cω` and the jets of order at most `J` of the physical lift of every pulse weighted at `t` are
bounded by `Mk k * A`, the jets of order at most `J` of the glued lift are bounded by
`(∑_k Cω Mk k) A`. -/
theorem norm_iteratedFDeriv_gluedLift_le_of_bounded (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ)
    (c ρ e εc : ℝ) (N H : ℕ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) {J : ℕ}
    {Cω : ℝ} (hCω : 0 ≤ Cω) (hϖ : ∀ k ∈ kset, |ϖ k t| ≤ Cω) (Mk : ℤ → ℝ) {A : ℝ}
    (hk : ∀ k ∈ kset, ϖ k t ≠ 0 →
      ContDiff ℝ (J : ℕ∞) (pulsePhysicalLift c ρ e εc N H (Cc k) (chart k) (label k) a t) ∧
      ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j
        (pulsePhysicalLift c ρ e εc N H (Cc k) (chart k) (label k) a t) x‖ ≤ Mk k * A)
    (hMA : ∀ k ∈ kset, 0 ≤ Mk k * A) {j : ℕ} (hj : j ≤ J) (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (gluedLift kset ϖ c ρ e εc N H Cc chart label a t) x‖ ≤
      (∑ k ∈ kset, Cω * Mk k) * A := by
  have he : gluedLift kset ϖ c ρ e εc N H Cc chart label a t = fun x =>
      ∑ k ∈ kset, ϖ k t • pulsePhysicalLift c ρ e εc N H (Cc k) (chart k) (label k) a t x :=
    rfl
  have hf : ∀ k ∈ kset, ContDiff ℝ (j : ℕ∞)
      (fun x => ϖ k t • pulsePhysicalLift c ρ e εc N H (Cc k) (chart k) (label k) a t x) := by
    intro k hks
    by_cases hw : ϖ k t = 0
    · simp only [hw, zero_smul]
      exact contDiff_const
    · exact ContDiff.const_smul (ϖ k t) ((hk k hks hw).1.of_le (by exact_mod_cast hj))
  have hb : ∀ k ∈ kset, ‖iteratedFDeriv ℝ j
      (fun x => ϖ k t • pulsePhysicalLift c ρ e εc N H (Cc k) (chart k) (label k) a t x) x‖ ≤
        (Cω * Mk k) * A := by
    intro k hks
    by_cases hw : ϖ k t = 0
    · simp only [hw, zero_smul, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      rw [mul_assoc]
      exact mul_nonneg hCω (hMA k hks)
    · have h1 := norm_iteratedFDeriv_const_smul_le_mul (ϖ k t)
        ((hk k hks hw).1.of_le (by exact_mod_cast hj)) ((hk k hks hw).2 j hj x)
      refine h1.trans ?_
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (hϖ k hks) (hMA k hks)
  rw [he]
  exact norm_iteratedFDeriv_sum_le_mul kset hf hb

end Bounded

section Setting

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
include P in
/-- **The label lift of a coarse field of class `C^N` that is slowly periodic at one time is
periodic in the label** at that time. -/
theorem setting_labelLift_periodic_at (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ) (g : ℝ → Vec 2 → ∀ i, h i)
    {ρs es c : ℝ} (M : ℕ) (hM : es⁻¹ = M) (t : ℝ) (ht : c⁻¹ * t ∈ Icc a b)
    (hg : ContDiff ℝ (N : ℕ∞) (g (c⁻¹ * t)))
    (hgp : ∀ X (n : Fin 2 → ℤ), g (c⁻¹ * t) (X + ρs⁻¹ • latticeShift n) = g (c⁻¹ * t) X)
    (hGs : ∀ (n : Fin 2 → ℤ) t X i j, Q.G t (X + ρs⁻¹ • latticeShift n) i j = Q.G t X i j)
    (hcs : ∀ (n : Fin 2 → ℤ) v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z,
      γ.coeff α t (X + ρs⁻¹ • latticeShift n) z = γ.coeff α t X z) (v : ι) :
    IsZ2Periodic (fun y => labelLift Cc N H ε g ρs es c t y v) := by
  intro n y
  simp only [labelLift_coeff_sum]
  refine Finset.sum_congr rfl fun hh hhmem => Finset.sum_congr rfl fun q' hq' => ?_
  have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhmem)
  have hq'N : q' ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq')
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  have hX : ρs⁻¹ • (y + latticeShift n) = ρs⁻¹ • y + ρs⁻¹ • latticeShift n := smul_add _ _ _
  have hz : es⁻¹ • (y + latticeShift n) =
      es⁻¹ • y + latticeShift (fun i => (M : ℤ) * n i) := by
    rw [smul_add, hM, natCast_smul_latticeShift]
  have hslow := setting_liftSequence_slowShift_invariant P sX sZ Cc hseq _ (hGs n) (hcs n) hh hhh
    q' p.1.val p.2.1 (c⁻¹ * t) ht (ρs⁻¹ • y) (es⁻¹ • y + latticeShift (fun i => (M : ℤ) * n i))
    v p.2.2
  have hfast := (hseq.2.2.2.2.2.1 hh hhh q' p.1.val p.2.1 v p.2.2 (c⁻¹ * t) ht).2 (ρs⁻¹ • y)
    (fun i => (M : ℤ) * n i) (es⁻¹ • y)
  have hpN : p.1.val ≤ N := (Nat.lt_succ_iff.1 p.1.isLt).trans hq'N
  have hjet := orderedDerivative_periodic (hg.of_le (by exact_mod_cast hpN))
    (ρs⁻¹ • latticeShift n) (fun Y => hgp Y n) p.2.1 (ρs⁻¹ • y)
  simp only at hfast
  rw [hX, hz, hslow, hfast, hjet]

end Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **The physical lift of an observed pulse is periodic** at a time of the window and of the
window of the pulse, for a coarse field of class `C^N` periodic at that time. -/
theorem ReconWindowAt.pulseLift_periodic
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {k : ℤ} (hk : k ∈ ocObsPulses α q Λ m tp (tp + Tobs)) (u : ℝ → Vec 2 → ∀ i, h i) {t : ℝ}
    (ht : t ∈ Set.Icc tp (tp + Tobs)) (hwin : t ∈ ocPulseWindow α q Λ m k)
    (hu : ContDiff ℝ (Nc : ℕ∞) (u t)) (hup : IsZ2Periodic (u t)) :
    IsZ2Periodic (pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon
        q Λ m)
        (ocDStar q Λ m ν B / ρ) Nc H (Cc k)
        (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) u t) := by
  have P := w.hsetting k hk
  have hseq := w.hseq k hk
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have hρ : 0 < ρ := P.ρ_pos
  have hcell : (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) :=
    AVRegularity.CycleComparison.Assembly.cellTime_mem_liftWindow hc0 hwin ht
  have hct : ocEll q Λ m ν ^ 2 * ((ocEll q Λ m ν ^ 2)⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul]
  obtain ⟨M, hM⟩ := pulse_e_inv_nat q Λ m
  have hψl : ∀ (n : Fin 2 → ℤ) (x : Vec 2),
      ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t (x + latticeShift n) =
        ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t x + latticeShift n :=
    fun n x => CycleReference.streamFlow_lattice_equivariant hφ _ t x n
  have hg : ContDiff ℝ (Nc : ℕ∞) (fun X => u (ocEll q Λ m ν ^ 2 * ((ocEll q Λ m ν ^ 2)⁻¹ * t))
      (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
        (ocEll q Λ m ν ^ 2 * ((ocEll q Λ m ν ^ 2)⁻¹ * t)) (ρ • X))) :=
            by
    rw [hct]
    exact hu.comp (((contDiff_ocChart hφ α q Λ m _ _).comp (contDiff_const_smul _)).of_le
      (by exact_mod_cast le_top))
  have hgp : ∀ X (n : Fin 2 → ℤ),
      u (ocEll q Λ m ν ^ 2 * ((ocEll q Λ m ν ^ 2)⁻¹ * t))
        (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
          (ocEll q Λ m ν ^ 2 * ((ocEll q Λ m ν ^ 2)⁻¹ * t))
          (ρ • (X + ρ⁻¹ • latticeShift
              n))) =
      u (ocEll q Λ m ν ^ 2 * ((ocEll q Λ m ν ^ 2)⁻¹ * t))
        (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
          (ocEll q Λ m ν ^ 2 * ((ocEll q Λ m ν ^ 2)⁻¹ * t)) (ρ • X))
              := by
    intro X n
    simp only [hct, smul_add, smul_inv_smul₀ hρ.ne',
      Charts.ocChart_latticeShift hφ α q Λ m (ocPulseChartIndex α q Λ m k) t n]
    exact hup n _
  have hL := fun v => setting_labelLift_periodic_at P (Klift + D + 2) (max (Llift + 1) (Llift + 2))
    (Cc k) hseq (ocDStar q Λ m ν B / ρ)
    (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
      (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s') (ρ • X)))
    M hM t hcell hg hgp (pulse_G_slow_invariant α q Λ m ζ hφ ν B hρ.ne' _ k _)
    (pulse_edge_slow_invariant α q Λ m ζ hφ ν B hρ.ne' k w.htorus (pp k)) v
  intro n x
  rw [pulsePhysicalLift_eq_labelLift, pulsePhysicalLift_eq_labelLift, hψl n x]
  funext v
  exact hL v n _

/-- **A glued lift with weights supported in the pulse windows is of class `C^J`** at a time of
the window, for a coarse field of class `C^{N+J}` at that time. -/
theorem ReconWindowAt.gluedLift_weights_contDiff
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (ω : ℤ → ℝ → ℝ)
    (hω : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ t ∈ Set.Icc tp (tp + Tobs), ω k t ≠ 0 →
      t ∈ ocPulseWindow α q Λ m k)
    {J : ℕ} (hJp : J ≤ Klift + Nc + 2 * D + 2) (hJq : J ≤ max Llift (Llift + 2) + 2 * D)
    (u : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs))
    (hu : ContDiff ℝ ((Nc + J : ℕ) : ℕ∞) (u t)) :
    ContDiff ℝ (J : ℕ∞) (gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) ω (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
        (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) u t) := by
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  apply gluedLift_contDiff_of_weighted
  intro k hk hw
  exact pulsePhysicalLift_contDiff (w.hsetting k hk) (Klift + D + 2) (max (Llift + 1) (Llift + 2))
    (by omega) (Cc k) (w.hseq k hk) hJp hJq hc0.ne' _ _ _
    (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
    (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) u
    (cellTime_mem_pulseLiftWindow hc0 (hω k hk t ht hw) ht)
    ((contDiff_ocChart hφ α q Λ m (ocPulseChartIndex α q Λ m k) t).of_le
      (by exact_mod_cast le_top))
    ((contDiff_ocChartInv hφ α q Λ m (ocPulseChartIndex α q Λ m k) t).of_le
      (by exact_mod_cast le_top)) hu

/-- **A glued lift with weights supported in the pulse windows is periodic** at a time of the
window, for a coarse field of class `C^N` periodic at that time. -/
theorem ReconWindowAt.gluedLift_weights_periodic
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (ω : ℤ → ℝ → ℝ)
    (hω : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ t ∈ Set.Icc tp (tp + Tobs), ω k t ≠ 0 →
      t ∈ ocPulseWindow α q Λ m k)
    (u : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs))
    (hu : ContDiff ℝ (Nc : ℕ∞) (u t)) (hup : IsZ2Periodic (u t)) :
    IsZ2Periodic (gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) ω (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
        (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) u t) :=
  isZ2Periodic_weighted_sum _ (fun k => ω k t) _ fun k hk hw =>
    w.pulseLift_periodic hk u ht (hω k hk t ht hw) hu hup

/-- **Jets of a glued lift with bounded weights supported in the pulse windows**: there is a
constant `M`, independent of the weights, of the coarse field and of the time, such that at every
time of the window the jets of order `j ≤ J` of the glued lift with weights bounded by `Cω` are
bounded by `Cω M A`, for a bound `A` of the jets of order at most `N + J` of the field. -/
theorem ReconWindowAt.gluedLift_weights_jet_le
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {J : ℕ} (hJp : J ≤ Klift + Nc + 2 * D + 2) (hJq : J ≤ max Llift (Llift + 2) + 2 * D) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ω : ℤ → ℝ → ℝ) (Cω : ℝ), 0 ≤ Cω →
      (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ t ∈ Set.Icc tp (tp + Tobs), ω k t ≠ 0 →
        t ∈ ocPulseWindow α q Λ m k) →
      ∀ (u : ℝ → Vec 2 → ∀ i, h i) (t : ℝ), t ∈ Set.Icc tp (tp + Tobs) →
      (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), |ω k t| ≤ Cω) →
      ContDiff ℝ ((Nc + J : ℕ) : ℕ∞) (u t) → ∀ A : ℝ,
      (∀ i ≤ Nc + J, ∀ y, ‖iteratedFDeriv ℝ i (u t) y‖ ≤ A) →
      ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j (gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) ω (ocEll q Λ
          m ν ^ 2)
        ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
        (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) u t) x‖ ≤ Cω * M
            * A := by
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have hCχ : 1 ≤ pulseChartD (Nc + J) * (max |(ocEpsilon q Λ (m - 1))⁻¹| 1) ^ (Nc + J) :=
    one_le_mul_of_one_le_of_one_le (one_le_pulseChartD _) (one_le_pow₀ (le_max_right _ _))
  have hMk : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∃ M : ℝ, 0 ≤ M ∧
      ∀ (u : ℝ → Vec 2 → ∀ i, h i) (t : ℝ), t ∈ Set.Icc tp (tp + Tobs) →
        t ∈ ocPulseWindow α q Λ m k → ContDiff ℝ ((Nc + J : ℕ) : ℕ∞) (u t) → ∀ A : ℝ,
        (∀ i ≤ Nc + J, ∀ y, ‖iteratedFDeriv ℝ i (u t) y‖ ≤ A) →
        ContDiff ℝ (J : ℕ∞) (pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ
            (ocEpsilon q Λ m)
          (ocDStar q Λ m ν B / ρ) Nc H (Cc k)
          (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) u t) ∧
        ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j (pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m)
          (ocDStar q Λ m ν B / ρ) Nc H (Cc k)
          (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) u t) x‖ ≤ M * A := by
    intro k hk
    obtain ⟨M, hM0, hM⟩ := pulsePhysicalLift_jet_le (w.hsetting k hk) (Klift + D + 2)
      (max (Llift + 1) (Llift + 2)) (by omega) (Cc k) (w.hseq k hk) hJp hJq hc0.ne'
      ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) hCχ hCχ
    refine ⟨M, hM0, fun u t ht hwin hu A hA => ?_⟩
    have hct := cellTime_mem_pulseLiftWindow hc0 hwin ht
    have hjk := pulseChart_jetBound α s w.hα₀ w.hα₁ w.hs₀ w.hs₁ q w.hq ζ w.hζ Λ w.hΛ Φ w.hΦ m
      w.hm hφ k hwin (Nc + J)
    have hχ : ContDiff ℝ ((Nc + J : ℕ) : ℕ∞)
        (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) :=
      (contDiff_ocChart hφ α q Λ m (ocPulseChartIndex α q Λ m k) t).of_le
        (by exact_mod_cast le_top)
    have hψ : ContDiff ℝ (J : ℕ∞)
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) :=
      (contDiff_ocChartInv hφ α q Λ m (ocPulseChartIndex α q Λ m k) t).of_le
        (by exact_mod_cast le_top)
    exact ⟨pulsePhysicalLift_contDiff (w.hsetting k hk) (Klift + D + 2)
        (max (Llift + 1) (Llift + 2)) (by omega) (Cc k) (w.hseq k hk) hJp hJq hc0.ne' _ _ _
        (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) u hct hχ hψ hu,
      hM (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) u t hct hχ
        (jetBound_le_uniform (one_le_pulseChartD _) hjk.1) hψ
        (fun i hi1 hiJ y => jetBound_le_uniform (one_le_pulseChartD _) hjk.2 i hi1 (by omega) y)
        hu A hA⟩
  choose! Mk hMk0 hMk using hMk
  refine ⟨∑ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), Mk k, Finset.sum_nonneg hMk0,
    fun ω Cω hCω hω u t ht hωb hu A hA j hj x => ?_⟩
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _) 0)
  have hb := norm_iteratedFDeriv_gluedLift_le_of_bounded (ocObsPulses α q Λ m tp (tp + Tobs)) ω
    (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B /
        ρ) Nc H Cc
    (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
    (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) u t hCω hωb Mk
    (fun k hk hw => hMk k hk u t ht (hω k hk t ht hw) hu A hA)
    (fun k hk => mul_nonneg (hMk0 k hk) hA0) hj x
  rw [← Finset.mul_sum] at hb
  exact hb

end AVRegularity.CycleComparison.Reconstruction
end
end

section
/-! **The residual flux carriers of the approximants are Cauchy at every window time**. From the difference bound (`ReconWindowAt.approxFlux_carrier_sub_mass_le`), the comparison of
a component norm with the mass-weighted norm (`norm_le_sqrt_massNormSq`) and the strong
convergence of the Galerkin cutoffs (`galerkinProj_tendsto`), the distance of two carriers is at
most `ε n + ε n'` with `ε n → 0` (`ReconWindowAt.approxFlux_carrier_cauchy`). -/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.ChartTransport AVRegularity.CycleComparison.Lift
    AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal

namespace AVRegularity.CycleComparison.Reconstruction

/-- A sequence whose distances are bounded by `ε n + ε m` with `ε → 0` is Cauchy. -/
theorem cauchySeq_of_dist_le_add {X : Type*} [PseudoMetricSpace X] (G : ℕ → X) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) (hG : ∀ n m, dist (G n) (G m) ≤ ε n + ε m) : CauchySeq G := by
  rw [Metric.cauchySeq_iff']
  intro δ hδ
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hε) (δ / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have h2 := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at h1 h2
  calc dist (G n) (G N) ≤ ε n + ε N := hG n N
    _ ≤ |ε n| + |ε N| := add_le_add (le_abs_self _) (le_abs_self _)
    _ < δ / 2 + δ / 2 := add_lt_add h1 h2
    _ = δ := by ring

/-- The triangle inequality through a third point, in the form used for Galerkin cutoffs. -/
theorem norm_sub_le_norm_sub_add_norm_sub' {X : Type*} [SeminormedAddCommGroup X] (a b c : X) :
    ‖a - c‖ ≤ ‖a - b‖ + ‖c - b‖ := by
  calc ‖a - c‖ = ‖(a - b) - (c - b)‖ := by congr 1; abel
    _ ≤ ‖a - b‖ + ‖c - b‖ := norm_sub_le _ _

/-- Squares of a sum of nonnegative terms dominate the sum of the squares. -/
theorem sum_sq_le_sq_sum {κ : Type*} (S : Finset κ) (a : κ → ℝ) (ha : ∀ k ∈ S, 0 ≤ a k) :
    ∑ k ∈ S, a k ^ 2 ≤ (∑ k ∈ S, a k) ^ 2 := by
  rw [sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum ha hk) (ha k hk)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
variable {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **The residual flux carriers of the approximants are Cauchy** at every time of the window. -/
theorem ReconWindowAt.approxFlux_carrier_cauchy
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (hSb : 0 ≤ Sb) {Acl r m' kres Nχ : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift)
    (hrL : r ≤ Llift) (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1)
    (hk : Acl + 2 + r + Nc + 1 ≤ kres) (hNχ : m' + 1 ≤ Nχ) (hNχ' : kres + 1 ≤ Nχ)
    {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ Nc →
      ∀ m'', 1 ≤ m'' → m'' ≤ n → ∀ j, j ≤ Acl + 2 + r →
        schurEnergyJet π (Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp /
            ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2))
          Llift j (Cc k hh n m'') ≤
        ENNReal.ofReal (Cg * Sb ^ hh *
          (ρ / ocEpsilon q Λ (m - 1)) ^ (n - m'' + j)))
    (Vc : ℕ → ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℕ → ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hch : ∀ n, w.IsApproxChains n (Acl + 2 + r) (r + 1) Acl (Acl + 2 + r)
      (max (Llift + 1) (Llift + 2)) (Vc n) (Vn n))
    (hkres : kres ≤ kc) (hmr : m' + 1 ≤ r₀) {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m)
    (hrsρ : rs ≤ ρ) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) (v : ι) :
    CauchySeq (fun n => carrierOf (Kc v) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v t x)) := by
  have hπ := w.hcs.mass_pos
  set P : ℝ := ∑ u, (π u)⁻¹ * (factorialWeightMax ρ (kc + 1 + (Nc +
      D)) +
    factorialWeightMax ρ kc) with hP
  have hwW : 0 ≤ factorialWeightMax ρ (kc + 1 + (Nc + D)) :=
    (factorialWeight_nonneg _ 0).trans (factorialWeight_le_max _ (0 : Fin (kc + 1 + (Nc + D) + 1)))
  have hwF : 0 ≤ factorialWeightMax ρ kc :=
    (factorialWeight_nonneg _ 0).trans (factorialWeight_le_max _ (0 : Fin (kc + 1)))
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun u _ =>
    mul_nonneg (inv_nonneg.2 (hπ u).le) (add_nonneg hwW hwF)
  have hPu : ∀ u, (π u)⁻¹ * factorialWeightMax ρ (kc + 1 + (Nc + D))
      ≤ P ∧
      (π u)⁻¹ * factorialWeightMax ρ kc ≤ P := fun u => by
    have hle : (π u)⁻¹ * (factorialWeightMax ρ (kc + 1 + (Nc + D)) +
        factorialWeightMax ρ kc) ≤ P :=
      Finset.single_le_sum (f := fun u => (π u)⁻¹ * (factorialWeightMax ρ (kc + 1 + (Nc + D)) +
        factorialWeightMax ρ kc)) (fun u _ => mul_nonneg
            (inv_nonneg.2 (hπ u).le)
          (add_nonneg hwW hwF)) (Finset.mem_univ u)
    constructor <;> nlinarith [inv_nonneg.2 (hπ u).le]
  have hCR : 0 ≤ (2 ^ (r + 1) * (3 * (tailPhysConst H Nc D Acl r m' (pulseChartD Nχ) * (((ocEll q Λ
      m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
          ((r.factorial : ℝ)) ^ 2 + liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)))) := by
    have := tailPhysConst_nonneg H Nc D Acl r m' (pulseChartD Nχ)
    have := liftPhysConst_nonneg H Nc Acl r kres Nχ (pulseChartD Nχ)
    positivity
  set Mv : ℝ := Real.sqrt (π v / factorialWeightMin rs (Kc v)) with hMv
  obtain ⟨S, hS⟩ : ∃ S : ℕ → ℝ, ∀ n, S n = ∑ u, (‖galerkinProj n (W u t) - W u t‖ +
      ‖galerkinProj n (Fc u t) - Fc u t‖) := ⟨_, fun _ => rfl⟩
  set ε : ℕ → ℝ := fun n => Mv * Real.sqrt ((2 ^ (r + 1) * (3 * (tailPhysConst H Nc D Acl r m'
      (pulseChartD Nχ) * (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
          ((r.factorial : ℝ)) ^ 2 + liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)))) * P) *
    S n with hε
  refine cauchySeq_of_dist_le_add _ ε ?_ fun n n' => ?_
  · have hs : Tendsto (fun n => ∑ u, (‖galerkinProj n (W u t) - W u t‖ +
        ‖galerkinProj n (Fc u t) - Fc u t‖)) atTop (𝓝 (∑ _u : ι, ((0 : ℝ) + 0))) :=
      tendsto_finsetSum _ fun u _ => (tendsto_iff_norm_sub_tendsto_zero.1
        (galerkinProj_tendsto (W u t))).add (tendsto_iff_norm_sub_tendsto_zero.1
          (galerkinProj_tendsto (Fc u t)))
    simp only [add_zero, Finset.sum_const_zero, ← hS] at hs
    simpa [hε] using hs.const_mul (Mv * Real.sqrt ((2 ^ (r + 1) * (3 * (tailPhysConst H Nc D Acl r
        m' (pulseChartD Nχ) * (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
          ((r.factorial : ℝ)) ^ 2 + liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)))) * P))
  · rw [dist_eq_norm]
    have hm := w.approxFlux_carrier_sub_mass_le hSb hAcl hK hrL hord hk hNχ hNχ' hCg hgr Vc Vn
      hch hkres hmr n n' ht hrs hrse hrsρ Kc hKr
    obtain ⟨a, ha⟩ : ∃ a : ι → ℝ,
        ∀ u, a u = ‖galerkinProj n (W u t) - galerkinProj n' (W u t)‖ := ⟨_, fun _ => rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : ι → ℝ,
        ∀ u, b u = ‖galerkinProj n (Fc u t) - galerkinProj n' (Fc u t)‖ := ⟨_, fun _ => rfl⟩
    have ha0 : ∀ u, 0 ≤ a u := fun u => (ha u).symm ▸ norm_nonneg _
    have hb0 : ∀ u, 0 ≤ b u := fun u => (hb u).symm ▸ norm_nonneg _
    have hrw : (∑ u, (π u)⁻¹ * (factorialWeightMax ρ (kc + 1 + (Nc +
        D)) *
          ‖galerkinProj n (W u t) - galerkinProj n' (W u t)‖ ^ 2)) +
        ∑ u, (π u)⁻¹ * (factorialWeightMax ρ kc *
          ‖galerkinProj n (Fc u t) - galerkinProj n' (Fc u t)‖ ^ 2) =
        (∑ u, (π u)⁻¹ * (factorialWeightMax ρ (kc + 1 + (Nc + D)) *
            a u ^ 2)) +
        ∑ u, (π u)⁻¹ * (factorialWeightMax ρ kc * b u ^ 2) := by
      simp only [ha, hb]
    rw [hrw] at hm
    have hsq : (∑ u, (π u)⁻¹ * (factorialWeightMax ρ (kc + 1 + (Nc +
        D)) * a u ^ 2)) +
        ∑ u, (π u)⁻¹ * (factorialWeightMax ρ kc * b u ^ 2) ≤
        P * (∑ u, (a u + b u)) ^ 2 := by
      calc (∑ u, (π u)⁻¹ * (factorialWeightMax ρ (kc + 1 + (Nc + D))
          * a u ^ 2)) +
            ∑ u, (π u)⁻¹ * (factorialWeightMax ρ kc * b u ^ 2)
          ≤ ∑ u, P * (a u + b u) ^ 2 := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_le_sum fun u _ => ?_
            have h1 := (hPu u).1
            have h2 := (hPu u).2
            have hab0 : 0 ≤ P * (a u * b u) := mul_nonneg hP0 (mul_nonneg (ha0 u) (hb0 u))
            have e1 : (π u)⁻¹ * (factorialWeightMax ρ (kc + 1 + (Nc
                + D)) * a u ^ 2) +
                (π u)⁻¹ * (factorialWeightMax ρ kc * b u ^ 2) =
                ((π u)⁻¹ * factorialWeightMax ρ (kc + 1 + (Nc + D)))
                    * a u ^ 2 +
                ((π u)⁻¹ * factorialWeightMax ρ kc) * b u ^ 2 := by
                    ring
            have e2 : P * (a u + b u) ^ 2 = P * a u ^ 2 + P * b u ^ 2 + 2 * (P * (a u * b u)) := by
              ring
            rw [e1, e2]
            have h3 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (a u))
            have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (b u))
            linarith
        _ = P * ∑ u, (a u + b u) ^ 2 := by rw [Finset.mul_sum]
        _ ≤ P * (∑ u, (a u + b u)) ^ 2 := mul_le_mul_of_nonneg_left
            (sum_sq_le_sq_sum _ _ fun u _ => add_nonneg (ha0 u) (hb0 u)) hP0
    have hdiff := norm_le_sqrt_massNormSq Kc hrs π hπ (fun u =>
      carrierOf (Kc u) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc u t x) -
      carrierOf (Kc u) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n') (Vn n') n' Fc u t x)) v
    refine hdiff.trans ?_
    have hab : ∑ u, (a u + b u) ≤ S n + S n' := by
      rw [hS n, hS n', ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun u _ => ?_
      have h1 : a u ≤ ‖galerkinProj n (W u t) - W u t‖ + ‖galerkinProj n' (W u t) - W u t‖ :=
        (ha u).trans_le (norm_sub_le_norm_sub_add_norm_sub' _ _ _)
      have h2 : b u ≤ ‖galerkinProj n (Fc u t) - Fc u t‖ +
          ‖galerkinProj n' (Fc u t) - Fc u t‖ :=
        (hb u).trans_le (norm_sub_le_norm_sub_add_norm_sub' _ _ _)
      exact (add_le_add h1 h2).trans_eq (add_add_add_comm _ _ _ _)
    have hsqrt : Real.sqrt (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := Kc)
        rs π (fun u => (carrierOf (Kc u) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc u t x) -
          carrierOf (Kc u) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n') (Vn n') n' Fc u t x)).val)) ≤
        Real.sqrt ((2 ^ (r + 1) * (3 * (tailPhysConst H Nc D Acl r m' (pulseChartD Nχ) * (((ocEll q
            Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
          ((r.factorial : ℝ)) ^ 2 + liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)))) * P) * ∑ u, (a u + b u) := by
      have hsum0 : 0 ≤ ∑ u, (a u + b u) := Finset.sum_nonneg fun u _ => add_nonneg (ha0 u) (hb0 u)
      refine (Real.sqrt_le_sqrt (hm.trans ((mul_le_mul_of_nonneg_left hsq hCR).trans_eq
        (mul_assoc _ _ _).symm))).trans_eq ?_
      rw [Real.sqrt_mul (mul_nonneg hCR hP0), Real.sqrt_sq hsum0]
    calc Mv * Real.sqrt (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := Kc)
          rs π (fun u => (carrierOf (Kc u) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B
              ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc u t x) -
            carrierOf (Kc u) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n') (Vn n') n' Fc u t x)).val))
        ≤ Mv * (Real.sqrt ((2 ^ (r + 1) * (3 * (tailPhysConst H Nc D Acl r m' (pulseChartD Nχ) *
            (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
          ((r.factorial : ℝ)) ^ 2 + liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)))) * P) * ∑ u, (a u + b u)) :=
          mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
      _ ≤ ε n + ε n' := by
          have h0 : 0 ≤ Mv * Real.sqrt ((2 ^ (r + 1) * (3 * (tailPhysConst H Nc D Acl r m'
              (pulseChartD Nχ) * (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
          ((r.factorial : ℝ)) ^ 2 + liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)))) * P) := mul_nonneg (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)
          refine (le_of_eq_of_le (mul_assoc _ _ _).symm (mul_le_mul_of_nonneg_left hab h0)).trans
            (le_of_eq ?_)
          simp only [hε]
          ring

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.ChartTransport AVRegularity.CycleComparison.Lift
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The residual flux of the physical reconstruction**. The residual flux
carriers of the approximants are a.e. strongly measurable on the window
(`ReconWindowAt.approxFlux_carrier_aesm`, from the tested measurability
`approxFlux_tested_measurable` and weak measurability), Cauchy at every window time
(`ReconWindowAt.approxFlux_carrier_cauchy`) and bounded uniformly in `n`
(`ReconWindowAt.approxFlux_carrier_mass_le_sep`); hence they converge at every window time to a
residual flux `R`, square integrable in time, with the same bound, and the distances are bounded
by functions whose integrals tend to zero (`ReconWindowAt.flux_limit`, by `exists_residual_limit`). -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
variable {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **The residual flux carriers of an approximant are a.e. strongly measurable on the window.** -/
theorem ReconWindowAt.approxFlux_carrier_aesm
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Acl r m' : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift)
    (hrL : r ≤ Llift) (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1)
    (Vc : ℕ → ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℕ → ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hch : ∀ n, w.IsApproxChains n (Acl + 2 + r) (r + 1) Acl (Acl + 2 + r)
      (max (Llift + 1) (Llift + 2)) (Vc n) (Vn n))
    (hK2 : 2 * Acl + 2 + r ≤ Klift + D + 2) (hD1 : 1 ≤ D)
    (hcm : ∀ n r', Measurable fun s => coarseCoeff n W r'
      (Set.projIcc tp (tp + Tobs) (by linarith [w.hTobs]) s))
    (hFm : ∀ n r', Measurable fun s =>
      coarseModeCoeff n (fun v => Fc v (Set.projIcc tp (tp + Tobs) (by linarith [w.hTobs]) s)) r')
    (n : ℕ) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) (v : ι) :
    AEStronglyMeasurable (fun s => carrierOf (Kc v) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B
        ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v s x))
      (volume.restrict (Set.Icc tp (tp + Tobs))) := by
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have htAZ : tp ≤ tp + Tobs := by linarith [w.hTobs]
  refine Coarse.aestronglyMeasurable_of_weak fun ψ hψ hψp => ?_
  have hmeas := approxFlux_tested_measurable hφ hΛ1 w.hν htAZ (fun k => F.weight (pp k))
    w.hpart (fun k => pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B ρ
      (ρ / ocEpsilon q Λ (m - 1)) k (F.fiber (pp k) (actual (pp
          k)))) w.hsetting Cc w.hseq
    (by omega : 1 ≤ Acl + 2 + r) (by omega : 1 ≤ r + 1) (by omega) (by omega)
    (by omega : 1 ≤ Acl + 2 + r) (by omega : 1 ≤ max (Llift + 1) (Llift + 2)) (by omega)
    (by omega) n (hcm n) (hFm n) (Vc n) (hch n).1 (Vn n) (hch n).2 v ψ hψ.continuous
  refine hmeas.aestronglyMeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
  obtain ⟨hsm, hpm⟩ := w.approxFlux_smooth hAcl hK hrL hord Vc Vn hch n hs Kc hKr
  beta_reduce
  rw [projIcc_val_of_mem htAZ hs, carrierOf_eq (Kc v) (hsm v) (hpm v)]
  unfold Coarse.tval cellInner
  refine integral_congr_ae ?_
  filter_upwards [periodicHk_value_ae (Kc v) _ (hsm v) (hpm v)] with x hx
  rw [hx]

/-- **The residual flux of the physical reconstruction.** The residual flux carriers of the
approximants converge at every window time to a residual flux `Rr`, a.e. strongly measurable and
square integrable on the window, with the per-time bound of the approximants; their distances to
`Rr` are bounded by functions whose window integrals tend to zero. -/
theorem ReconWindowAt.flux_limit
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (hSb : 0 ≤ Sb) {Acl r m' kres Nχ : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift)
    (hrL : r ≤ Llift) (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1)
    (hk : Acl + 2 + r + Nc + 1 ≤ kres) (hNχ : m' + 1 ≤ Nχ) (hNχ' : kres + 1 ≤ Nχ)
    {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ Nc →
      ∀ m'', 1 ≤ m'' → m'' ≤ n → ∀ j, j ≤ Acl + 2 + r →
        schurEnergyJet π (Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp /
            ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2))
          Llift j (Cc k hh n m'') ≤
        ENNReal.ofReal (Cg * Sb ^ hh *
          (ρ / ocEpsilon q Λ (m - 1)) ^ (n - m'' + j)))
    (Vc : ℕ → ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℕ → ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hch : ∀ n, w.IsApproxChains n (Acl + 2 + r) (r + 1) Acl (Acl + 2 + r)
      (max (Llift + 1) (Llift + 2)) (Vc n) (Vn n))
    (hK2 : 2 * Acl + 2 + r ≤ Klift + D + 2) (hD1 : 1 ≤ D)
    (hcm : ∀ n r', Measurable fun s => coarseCoeff n W r'
      (Set.projIcc tp (tp + Tobs) (by linarith [w.hTobs]) s))
    (hFm : ∀ n r', Measurable fun s =>
      coarseModeCoeff n (fun v => Fc v (Set.projIcc tp (tp + Tobs) (by linarith [w.hTobs]) s)) r')
    (hkres : kres ≤ kc) (hmr : m' + 1 ≤ r₀)
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m)
    (hrsρ : rs ≤ ρ) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r)
    (hWint : IntegrableOn (fun s => ∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m'
      (W v s).val) (Set.Icc tp (tp + Tobs)))
    (hFint : IntegrableOn (fun s => massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
      (K := fun _ => kc) ρ π (fun v => (Fc v s).val)) (Set.Icc tp
          (tp + Tobs))) :
    ∃ Rr : ℝ → ∀ v, TorusHk (Kc v) (PiLp 2 (fun _ : Fin 2 => h v)),
      (∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v, Tendsto (fun n => carrierOf (Kc v) (fun x => approxFlux α
          q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v s x))
        atTop (𝓝 (Rr s v))) ∧
      (∀ v, AEStronglyMeasurable (fun s => Rr s v) (volume.restrict (Set.Icc tp (tp + Tobs)))) ∧
      (∀ s ∈ Set.Icc tp (tp + Tobs), massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K :=
          Kc) rs π
        (fun v => (Rr s v).val) ≤ 2 ^ (r + 1) * (3 * (tailPhysConst H Nc D Acl r m' (pulseChartD Nχ)
            * (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) *
        (∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m'
            (W v s).val) +
        (((r.factorial : ℝ)) ^ 2 + liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)) *
        massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => kc)
            ρ π (fun v => (Fc v s).val)))) ∧
      (∀ v, MemLp (fun s => Rr s v) 2 (volume.restrict (Set.Icc tp (tp + Tobs)))) ∧
      ∃ c : ℕ → ℝ → ℝ, (∀ n, IntegrableOn (c n) (Set.Icc tp (tp + Tobs))) ∧
        Tendsto (fun n => ∫ s in Set.Icc tp (tp + Tobs), c n s) atTop (𝓝 0) ∧ (∀ n s, 0 ≤ c n s) ∧
        ∀ n, ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v,
          ‖carrierOf (Kc v) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v s x) - Rr s v‖ ≤ c n s :=
  exists_residual_limit measurableSet_Icc measure_Icc_lt_top Kc hrs π w.hcs.mass_pos
    (fun n s v => carrierOf (Kc v) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v s x))
    (fun n v => w.approxFlux_carrier_aesm hAcl hK hrL hord Vc Vn hch hK2 hD1 hcm hFm n Kc hKr v)
    (fun _ hs v => w.approxFlux_carrier_cauchy hSb hAcl hK hrL hord hk hNχ hNχ' hCg hgr Vc Vn
      hch hkres hmr hs hrs hrse hrsρ Kc hKr v)
    (fun s => 2 ^ (r + 1) * (3 * (tailPhysConst H Nc D Acl r m' (pulseChartD Nχ) * (((ocEll q Λ m ν
        ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) *
        (∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m'
            (W v s).val) +
        (((r.factorial : ℝ)) ^ 2 + liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)) *
        massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => kc)
            ρ π (fun v => (Fc v s).val))))
    (((hWint.const_mul (tailPhysConst H Nc D Acl r m' (pulseChartD Nχ) * (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2))).add (hFint.const_mul (((r.factorial :
              ℝ)) ^ 2 + liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)))).const_mul 3
      |>.const_mul (2 ^ (r + 1)))
    (fun n _ hs => w.approxFlux_carrier_mass_le_sep hSb hAcl hK hrL hord hk hNχ hNχ' hCg hgr Vc Vn
      hch hkres hmr n hs hrs hrse hrsρ Kc hKr)

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Carrier norms from uniform jet bounds**. The norm of the carrier of a periodic
field of class `C^K` whose jets of order at most `K` are bounded by `A` is at most the number of
jet indices times `A` (`periodicHk_norm_le_of_jet`, `carrierOf_norm_le_of_jet`); the jets of a
component are bounded by the jets of the field (`norm_iteratedFDeriv_component_le`). The square
root of the mass-weighted factorial norm is the norm of a fixed continuous linear readout of the
carriers, hence subadditive and bounded by a multiple of the carrier norms
(`sqrt_massNormSq_add_le`, `sqrt_massNormSq_le_of_norm_le`). -/

section Single

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The carrier norm of a periodic field with bounded jets.** -/
theorem periodicHk_norm_le_of_jet (K : ℕ) {f : Vec 2 → E} (hf : ContDiff ℝ (K : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ j ≤ K, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A) :
    ‖periodicHk K f hf hp‖ ≤ (Fintype.card (JetIndex2 K) : ℝ) * A := by
  refine (AVRegularity.Weighted.finitePiLp_norm_le_sum (periodicHk K f hf hp).val).trans ?_
  calc ∑ a, ‖(periodicHk K f hf hp).val a‖ ≤ ∑ _a : JetIndex2 K, A :=
        Finset.sum_le_sum fun a _ => ?_
    _ = (Fintype.card (JetIndex2 K) : ℝ) * A := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [norm_periodicHk_val]
  have hle : a.1.val ≤ K := Nat.lt_succ_iff.1 a.1.isLt
  have hfa : ContDiff ℝ (a.1.val : ℕ∞) f := hf.of_le (by exact_mod_cast hle)
  exact cellL2_le_of_bound (AVRegularity.ChartTransport.continuous_orderedDerivative a.2 hfa).aestronglyMeasurable hA
    fun x => (AVRegularity.ChartTransport.norm_orderedDerivative_le hfa a.2 x).trans (hb _ hle x)

/-- **The norm of the carrier of a periodic field with bounded jets.** -/
theorem carrierOf_norm_le_of_jet (K : ℕ) {f : Vec 2 → E} (hf : ContDiff ℝ (K : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ j ≤ K, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A) :
    ‖carrierOf K f‖ ≤ (Fintype.card (JetIndex2 K) : ℝ) * A := by
  rw [carrierOf_eq K hf hp]
  exact periodicHk_norm_le_of_jet K hf hp hA hb

end Single

section Component

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- **The jets of a component are bounded by the jets of the field.** -/
theorem norm_iteratedFDeriv_component_le {f : Vec 2 → ∀ i, h i} {j : ℕ}
    (hf : ContDiff ℝ (j : ℕ∞) f) (v : ι) (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun y => f y v) x‖ ≤ ‖iteratedFDeriv ℝ j f x‖ := by
  have hL : ‖ContinuousLinearMap.proj (R := ℝ) (φ := h) v‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => by
      rw [one_mul]
      exact norm_le_pi_norm g v
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := h) v).norm_iteratedFDeriv_comp_left
    (hf.contDiffAt (x := x)) le_rfl
  exact h1.trans (mul_le_of_le_one_left (norm_nonneg _) hL)

end Component

section Mass

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  [∀ i, CompleteSpace (E i)]

/-- **The square root of the mass-weighted factorial norm is subadditive.** -/
theorem sqrt_massNormSq_add_le (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (U V : ∀ i, TorusHk (K i) (E i)) :
    Real.sqrt (massNormSq ρ π (fun i => (U i + V i).val)) ≤
      Real.sqrt (massNormSq ρ π (fun i => (U i).val)) +
        Real.sqrt (massNormSq ρ π (fun i => (V i).val)) := by
  have h := massWeightedCarrierCLM_norm K ρ π hπ (U + V)
  rw [← massWeightedCarrierCLM_norm K ρ π hπ U, ← massWeightedCarrierCLM_norm K ρ π hπ V]
  calc Real.sqrt (massNormSq ρ π (fun i => (U i + V i).val))
      = ‖massWeightedCarrierCLM K ρ π (U + V)‖ := h.symm
    _ ≤ ‖massWeightedCarrierCLM K ρ π U‖ + ‖massWeightedCarrierCLM K ρ π V‖ := by
        rw [map_add]
        exact norm_add_le _ _

/-- **The square root of the mass-weighted factorial norm is bounded by the carrier norms.** -/
theorem sqrt_massNormSq_le_of_norm_le (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (U : ∀ i, TorusHk (K i) (E i)) {B : ℝ} (hB : 0 ≤ B) (hU : ∀ i, ‖U i‖ ≤ B) :
    Real.sqrt (massNormSq ρ π (fun i => (U i).val)) ≤
      ‖massWeightedCarrierCLM (E := E) K ρ π‖ * B := by
  rw [← massWeightedCarrierCLM_norm K ρ π hπ U]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg hB).2 hU) (norm_nonneg _))

end Mass

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Uniform jets of the Galerkin approximants**. The jets of order `i ≤ r` of a
classical representative of order `r` of a field of `H^K`, `r + 2 ≤ K`, are bounded by a fixed
multiple of the norm of the field (`classicalRep_iteratedFDeriv_le`), and those of a difference by
the norm of the difference (`classicalRep_iteratedFDeriv_sub_le`). Hence the jets of the
approximants `a_n(t) = S_n W(t)` are bounded uniformly in `n` by the norm of `W(t)`
(`coarseTraj_iteratedFDeriv_le`, Galerkin contraction), and those of `a_n(t) - a_{n'}(t)` by the
norms of the Galerkin differences (`coarseTraj_sub_iteratedFDeriv_le`). -/

section Single

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The sum of a constant over the derivative words of order `i ≤ r`. -/
theorem sum_words_const_le {i r : ℕ} (hi : i ≤ r) {c : ℝ} (hc : 0 ≤ c) :
    ∑ _w : DerivativeWord2 i, c ≤ 2 ^ r * c := by
  rw [Finset.sum_const, AVRegularity.ChartTransport.card_derivativeWord2, nsmul_eq_mul]
  push_cast
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) hc

/-- **Sup bound of the jets of a classical representative.** -/
theorem classicalRep_iteratedFDeriv_le (K r : ℕ) (hr : r + 2 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : TorusHk K E) (a : Vec 2 → E), IsClassicalRep V a r →
      ∀ i ≤ r, ∀ x, ‖iteratedFDeriv ℝ i a x‖ ≤ C * ‖V‖ := by
  obtain ⟨C, hC, hb⟩ := classicalRep_orderedDerivative_le (E := E) K r hr
  refine ⟨2 ^ r * C, by positivity, fun V a ha i hi x => ?_⟩
  have hai : ContDiff ℝ (i : ℕ∞) a := isClassicalRep_contDiff_of_le ha hi
  refine (AVRegularity.ChartTransport.norm_iteratedFDeriv_le_sum_words hai x).trans ?_
  refine (Finset.sum_le_sum fun w _ => hb V a ha i hi w x).trans ?_
  refine (sum_words_const_le hi (mul_nonneg hC (norm_nonneg V))).trans_eq ?_
  ring

/-- **Sup bound of the jets of a difference of classical representatives.** -/
theorem classicalRep_iteratedFDeriv_sub_le (K r : ℕ) (hr : r + 2 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V V' : TorusHk K E) (a a' : Vec 2 → E), IsClassicalRep V a r →
      IsClassicalRep V' a' r → ∀ i ≤ r, ∀ x,
        ‖iteratedFDeriv ℝ i (fun y => a y - a' y) x‖ ≤ C * ‖V - V'‖ := by
  obtain ⟨C, hC, hb⟩ := classicalRep_orderedDerivative_sub_le (E := E) K r hr
  refine ⟨2 ^ r * C, by positivity, fun V V' a a' ha ha' i hi x => ?_⟩
  have hai : ContDiff ℝ (i : ℕ∞) a := isClassicalRep_contDiff_of_le ha hi
  have ha'i : ContDiff ℝ (i : ℕ∞) a' := isClassicalRep_contDiff_of_le ha' hi
  refine (AVRegularity.ChartTransport.norm_iteratedFDeriv_le_sum_words (hai.sub ha'i) x).trans ?_
  refine (Finset.sum_le_sum fun w _ => ?_).trans
    ((sum_words_const_le hi (mul_nonneg hC (norm_nonneg (V - V')))).trans_eq (by ring))
  rw [orderedDerivative_sub w hai ha'i]
  exact hb V V' a a' ha ha' i hi w x

end Single

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **The jets of the approximants are bounded uniformly in `n`** by the norms of `W(t)`. -/
theorem coarseTraj_iteratedFDeriv_le {K r : ℕ} (hr : r + 2 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (W : ∀ v, ℝ → TorusHk K (h v)) (t : ℝ) {B : ℝ}, 0 ≤ B →
      (∀ v, ‖W v t‖ ≤ B) → ∀ i ≤ r, ∀ x,
        ‖iteratedFDeriv ℝ i (coarseTraj n W t) x‖ ≤ C * B := by
  choose C hC hb using fun v : ι => classicalRep_iteratedFDeriv_le (E := h v) K r hr
  refine ⟨∑ v, C v, Finset.sum_nonneg fun v _ => hC v, fun n W t B hB hW i hi x => ?_⟩
  refine norm_iteratedFDeriv_le_of_apply_le ((coarseTraj_contDiff n W t).of_le
    (by exact_mod_cast le_top)) x (mul_nonneg (Finset.sum_nonneg fun v _ => hC v) hB) fun v => ?_
  have hrep : IsClassicalRep (galerkinProj n (W v t))
      (fun y => coarseApprox n (fun u => W u t) y v) r :=
    coarseApprox_isClassicalRep n (fun u => W u t) v (by omega)
  have he : (fun y => coarseTraj n W t y v) = fun y => coarseApprox n (fun u => W u t) y v := by
    rw [coarseTraj_eq]
  rw [he]
  refine (hb v _ _ hrep i hi x).trans ?_
  refine (mul_le_mul_of_nonneg_left ((galerkinProj_norm_le n (W v t)).trans (hW v))
    (hC v)).trans ?_
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := C) (fun v _ => hC v)
    (Finset.mem_univ v)) hB

/-- **The jets of the difference of two approximants** are bounded by the norms of the Galerkin
differences. -/
theorem coarseTraj_sub_iteratedFDeriv_le {K r : ℕ} (hr : r + 2 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n n' : ℕ) (W : ∀ v, ℝ → TorusHk K (h v)) (t : ℝ) {B : ℝ}, 0 ≤ B →
      (∀ v, ‖galerkinProj n (W v t) - galerkinProj n' (W v t)‖ ≤ B) → ∀ i ≤ r, ∀ x,
        ‖iteratedFDeriv ℝ i (fun y => coarseTraj n W t y - coarseTraj n' W t y) x‖ ≤
          C * B := by
  choose C hC hb using fun v : ι => classicalRep_iteratedFDeriv_sub_le (E := h v) K r hr
  refine ⟨∑ v, C v, Finset.sum_nonneg fun v _ => hC v, fun n n' W t B hB hW i hi x => ?_⟩
  refine norm_iteratedFDeriv_le_of_apply_le (((coarseTraj_contDiff n W t).sub
    (coarseTraj_contDiff n' W t)).of_le (by exact_mod_cast le_top)) x
    (mul_nonneg (Finset.sum_nonneg fun v _ => hC v) hB) fun v => ?_
  have hrep : ∀ n₀ : ℕ, IsClassicalRep (galerkinProj n₀ (W v t))
      (fun y => coarseApprox n₀ (fun u => W u t) y v) r := fun n₀ =>
    coarseApprox_isClassicalRep n₀ (fun u => W u t) v (by omega)
  have he : (fun y => (coarseTraj n W t y - coarseTraj n' W t y) v) = fun y =>
      coarseApprox n (fun u => W u t) y v - coarseApprox n' (fun u => W u t) y v := by
    rw [coarseTraj_eq, coarseTraj_eq]
    rfl
  rw [he]
  refine (hb v _ _ _ _ (hrep n) (hrep n') i hi x).trans ?_
  refine (mul_le_mul_of_nonneg_left (hW v) (hC v)).trans ?_
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := C) (fun v _ => hC v)
    (Finset.mem_univ v)) hB

end Pi

end AVRegularity.CycleComparison.Reconstruction
end
end
