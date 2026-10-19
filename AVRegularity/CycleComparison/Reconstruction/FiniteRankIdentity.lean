-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.ApproxMeasurableTail
public import AVRegularity.CycleComparison.Reconstruction.GluedTail
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.CycleComparison.Assembly.OcDiagonal
import AVRegularity.CycleComparison.Reconstruction.ObsEdgesTested
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.CycleComparison.LiftSetting.Main
import AVRegularity.CycleComparison.Reconstruction.FrozenMeasure
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The tested glued lift of a field in cleanup form**. For a field `f` that is
continuous and `ℤ²`-periodic at the time `t`, and cleanup chains `Vn k hh n` of the positive
degrees of the lifts of its chart-frame fields on the observed pulses, the glued lift `𝒯f`
tested against a `C¹` periodic field on the cell is the tested field itself (the degree zero of
every pulse lift is the identity and the weights sum to one) minus the tested glued cleanup flux
plus the tested glued cleanup force (`glued_liftFlux`), by `setting_labelLift_cleanup_tested`
on every weighted pulse. Applied to the coarse flux divergence, the tested field is integrated by
parts into the identity flux `(F_c, 0)`. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

/-- **The tested glued lift of a field in cleanup form.** -/
theorem glued_liftFlux {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {φs : ℝ → Vec 2 → ℝ} (hΛ : 1 ≤ Λ)
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
    (sX sZ : ℕ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (pulseLiftData α q Λ m ζ φs hφs ν B ρ lam k (edge k)) sX sZ
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    (sXc sZc Acl : ℕ) (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (f : ℝ → Vec 2 → ∀ i, h i)
    (hcs : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ (n : Fin 2 → ℤ) v u d,
      ∀ γ ∈ (pulseLiftData α q Λ m ζ φs hφs ν B ρ lam k (edge k)).edge v u d,
        ∀ w t X z, γ.coeff w t (X + ρ⁻¹ • latticeShift n) z = γ.coeff w t X z)
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ hh, hh ≤ H → ∀ n, n < N →
      ∀ τ ∈ Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXc sZc Acl
        (liftApply (n + 1) (Cc k hh (n + 1)) (fun s X => f (ocEll q Λ m ν ^ 2 * s)
          (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s)
            (ρ • X))) τ)
        (fun _ _ _ => 0) (fun j => Vn k hh n j τ))
    {t : ℝ} (ht : t ∈ Icc tA tZ) (hf : Continuous (f t)) (hfp : IsZ2Periodic (f t))
    (v : ι) (φt : Vec 2 → h v) (hφt : ContDiff ℝ 1 φt) (hφtp : IsZ2Periodic φt) :
    ∫ x in unitCube, inner ℝ
        (gluedLift (ocObsPulses α q Λ m tA tZ) ϖ (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m)
          (ocDStar q Λ m ν B / ρ) N H Cc
          (fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) f t x v) (φt x) =
      (∫ x in unitCube, inner ℝ (f t x v) (φt x))
        - (∫ x in unitCube, ∑ a₀ : Fin 2, inner ℝ
          ((∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t •
            liftFluxPhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
              (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) t x a₀) v)
          (fderiv ℝ φt x (basisVec a₀)))
        + ∫ x in unitCube, inner ℝ
          ((∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t •
            liftForcePhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
              (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) t x) v)
          (φt x) := by
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  obtain ⟨M, hM⟩ := pulse_e_inv_nat q Λ m
  have hsum : ∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t = 1 := hpart.2.2.1 t ht
  -- the per-pulse tested identities and continuity at the weighted pulses
  have hpulse : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t ≠ 0 →
      ((∫ x in unitCube, inner ℝ
          (pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H
            (Cc k) (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
            (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) f t x v) (φt x)) =
        (∫ x in unitCube, inner ℝ (f t x v) (φt x))
          - (∫ x in unitCube, ∑ a₀ : Fin 2, inner ℝ
            (liftFluxPhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
              (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) t x a₀ v)
            (fderiv ℝ φt x (basisVec a₀)))
          + ∫ x in unitCube, inner ℝ
            (liftForcePhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
              (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) t x v)
            (φt x)) ∧
      (∀ a₀ : Fin 2, Continuous (fun x =>
        liftFluxPhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) t x a₀ v)) ∧
      Continuous (fun x =>
        liftForcePhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) t x v) ∧
      Continuous (fun x =>
        pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H
          (Cc k) (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
          (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) f t x v) := by
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
    have hχs : ContDiff ℝ (⊤ : ℕ∞) (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) :=
      (Charts.contDiff_ocChart_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)).comp
        (contDiff_const.prodMk contDiff_id)
    have hψs : ContDiff ℝ (⊤ : ℕ∞)
        (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) :=
      (Charts.contDiff_ocChartInv_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)).comp
        (contDiff_const.prodMk contDiff_id)
    have hψl : ∀ (n : Fin 2 → ℤ) (x : Vec 2),
        ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t (x + latticeShift n) =
          ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t x + latticeShift n :=
      fun n x => CycleReference.streamFlow_lattice_equivariant hφs _ t x n
    -- the chart-frame field at the cell time
    have hAeq : (fun (s : ℝ) (X : Vec 2) => f (ocEll q Λ m ν ^ 2 * s)
        (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s) (ρ • X)))
        ((ocEll q Λ m ν ^ 2)⁻¹ * t) =
        fun X => f t (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t (ρ • X)) := by
      funext X
      show f (ocEll q Λ m ν ^ 2 * ((ocEll q Λ m ν ^ 2)⁻¹ * t))
        (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)
          (ocEll q Λ m ν ^ 2 * ((ocEll q Λ m ν ^ 2)⁻¹ * t)) (ρ • X)) = _
      rw [mul_inv_cancel_left₀ hc0.ne' t]
    have hAc : Continuous ((fun (s : ℝ) (X : Vec 2) => f (ocEll q Λ m ν ^ 2 * s)
        (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s) (ρ • X)))
        ((ocEll q Λ m ν ^ 2)⁻¹ * t)) := by
      rw [hAeq]
      exact hf.comp (hχs.continuous.comp (continuous_const_smul ρ))
    have hAp : ∀ (n : Fin 2 → ℤ) (X : Vec 2),
        (fun (s : ℝ) (X : Vec 2) => f (ocEll q Λ m ν ^ 2 * s)
          (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s)
            (ρ • X))) ((ocEll q Λ m ν ^ 2)⁻¹ * t) (X + ρ⁻¹ • latticeShift n) =
        (fun (s : ℝ) (X : Vec 2) => f (ocEll q Λ m ν ^ 2 * s)
          (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s)
            (ρ • X))) ((ocEll q Λ m ν ^ 2)⁻¹ * t) X := by
      intro n X
      rw [hAeq]
      show f t (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t
        (ρ • (X + ρ⁻¹ • latticeShift n))) = _
      rw [smul_add, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul,
        Charts.ocChart_latticeShift hφs α q Λ m (ocPulseChartIndex α q Λ m k) t n (ρ • X)]
      exact hfp n _
    have hid := setting_labelLift_cleanup_tested (P k hk) sX sZ (Cc k) (hseq k hk) sXc sZc Acl
      hAcl hXc hZc (ocDStar q Λ m ν B / ρ) hc0.ne' hρ.ne' he _ (Vn k) (hV k hk) hs hAc hχs hψs
      (Charts.ocChartInv_ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t)
      (Charts.ocChart_ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t)
      (Charts.ocChart_det hφs α q Λ m (ocPulseChartIndex α q Λ m k) t) hψl M hM
      (pulse_G_slow_invariant α q Λ m ζ hφs ν B hρ.ne' lam k (edge k)) (hcs k hk) hAp v φt hφt
      hφtp
    -- the field read at the label of `x` is the field at `x`
    have hfx : ∀ x, (fun (s : ℝ) (X : Vec 2) => f (ocEll q Λ m ν ^ 2 * s)
        (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s) (ρ • X)))
        ((ocEll q Λ m ν ^ 2)⁻¹ * t)
        (ρ⁻¹ • ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t x) = f t x := by
      intro x
      rw [hAeq]
      show f t (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t
        (ρ • ρ⁻¹ • ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t x)) = _
      rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul,
        Charts.ocChart_ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t x]
    simp only [hfx] at hid
    exact hid
  -- the glued lift, flux and force, tested
  have hptL : ∀ x, inner ℝ
      (gluedLift (ocObsPulses α q Λ m tA tZ) ϖ (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m)
        (ocDStar q Λ m ν B / ρ) N H Cc
        (fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
        (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) f t x v) (φt x) =
      ∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t * inner ℝ
        (pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H
          (Cc k) (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
          (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) f t x v) (φt x) := fun x => by
    simp only [gluedLift, Finset.sum_apply, Pi.smul_apply, sum_inner, real_inner_smul_left]
  have hptR : ∀ x, ∑ a₀ : Fin 2, inner ℝ
      ((∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t •
        liftFluxPhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) t x a₀) v)
      (fderiv ℝ φt x (basisVec a₀)) =
      ∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t * ∑ a₀ : Fin 2, inner ℝ
        (liftFluxPhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) t x a₀ v)
        (fderiv ℝ φt x (basisVec a₀)) := fun x => by
    simp only [Finset.sum_apply, Pi.smul_apply, sum_inner, real_inner_smul_left, Finset.mul_sum]
    exact Finset.sum_comm
  have hptq : ∀ x, inner ℝ
      ((∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t •
        liftForcePhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) t x) v)
      (φt x) =
      ∑ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t * inner ℝ
        (liftForcePhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) t x v)
        (φt x) := fun x => by
    simp only [Finset.sum_apply, Pi.smul_apply, sum_inner, real_inner_smul_left]
  have hdφ : ∀ a₀ : Fin 2, Continuous (fun x => fderiv ℝ φt x (basisVec a₀)) := fun a₀ =>
    (hφt.continuous_fderiv one_ne_zero).clm_apply continuous_const
  simp only [hptL, hptR, hptq]
  rw [integral_weighted_sum _ (fun k => ϖ k t)
      (fun k x => inner ℝ
        (pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H
          (Cc k) (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
          (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) f t x v) (φt x))
      (fun k hk hw => CoupledEnergy.Galerkin.continuous_cell_integrable _
        ((hpulse k hk hw).2.2.2.inner hφt.continuous)),
    integral_weighted_sum _ (fun k => ϖ k t)
      (fun k x => ∑ a₀ : Fin 2, inner ℝ
        (liftFluxPhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) t x a₀ v)
        (fderiv ℝ φt x (basisVec a₀))) (fun k hk hw =>
      CoupledEnergy.Galerkin.continuous_cell_integrable _
        (continuous_finsetSum _ fun a₀ _ => ((hpulse k hk hw).2.1 a₀).inner (hdφ a₀))),
    integral_weighted_sum _ (fun k => ϖ k t)
      (fun k x => inner ℝ
        (liftForcePhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) t x v)
        (φt x)) (fun k hk hw =>
      CoupledEnergy.Galerkin.continuous_cell_integrable _
        ((hpulse k hk hw).2.2.1.inner hφt.continuous))]
  have hk_eq : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t * (∫ x in unitCube, inner ℝ
        (pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H
          (Cc k) (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
          (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) f t x v) (φt x)) =
      ϖ k t * (∫ x in unitCube, inner ℝ (f t x v) (φt x))
        - ϖ k t * (∫ x in unitCube, ∑ a₀ : Fin 2, inner ℝ
          (liftFluxPhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
            (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) t x a₀ v)
          (fderiv ℝ φt x (basisVec a₀)))
        + ϖ k t * ∫ x in unitCube, inner ℝ
          (liftForcePhys (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) H N Acl
            (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) t x v)
          (φt x) := by
    intro k hk
    by_cases hw : ϖ k t = 0
    · simp only [hw, zero_mul, sub_zero, add_zero]
    · rw [(hpulse k hk hw).1]
      ring
  rw [Finset.sum_congr rfl hk_eq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hsum, one_mul]

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The weighted pulse means agree at every weighted time** (the hypothesis
`hagree` of `glued_meanPart`).

The time partition transitions on trimmed quiet overlaps, where `w = 0` and all independent
source coefficients are fast independent.

At a time `t` of the window at which two distinct observed pulses `j ≠ k` are weighted, `t` is a
quiet time of both pulse windows and only the pieces `pp j`, `pp k` carry weight
(`active_pieces`). There the means of both pulse lifts are the same explicit physical operators
(`quiet_mean_zero`, `quiet_mean_one`, `quiet_mean_high`): `-ν Δa` in grade zero, minus the physical
divergence of the family edge flux of `a` in grade one, zero in the grades `2 ≤ r ≤ H`.

* `pulse_isQuietOn`: the lift data of an odd pulse is `IsQuietOn` at the cell times whose
  physical time is a quiet time of the window and an output time of the piece (the pulse drift
  vanishes by `ocPulse_eq_zero_of_quiet`; the lifted fluxes are fast independent).
* `pulseChartIndex_consecutive`: neighbouring odd pulses have equal or consecutive renewal
  charts, so their pieces are adjacent in a consecutive-closed atlas.
* `edgeFlux_quiet_overlap_atlas_target_of_contDiff`: on a quiet overlap of an adjacent pair
  `p, q` the family edge flux is also the transported label flux of the *second* piece `q`
  (`pieceFlux_transition_of_contDiff`).
* `pulse_quiet_means`: the three quiet means of one pulse, given the flux of its piece.
* `obs_pulse_means_agree`: the means of two weighted observed pulses agree. -/

/-! ### Scale identities -/

/-- `√η ε_c = e ρ⁻¹`, from `ε_c √η = c ν e⁻¹ρ⁻¹` and `c ν = e²`. -/
theorem quiet_scale_sqrt {s d ρ c ν e : ℝ} (he : e ≠ 0) (hsq : c * ν = e ^ 2)
    (h2 : d / ρ * s = c * ν * e⁻¹ * ρ⁻¹) : s * (d / ρ) = e * ρ⁻¹ := by
  have hb : e * e⁻¹ = 1 := mul_inv_cancel₀ he
  linear_combination h2 + (e⁻¹ * ρ⁻¹) * hsq + (e * ρ⁻¹) * hb

/-- `c⁻¹ e (e/ν) = 1`, from `c ν = e²`. -/
theorem quiet_scale_time {c ν e : ℝ} (hc : c ≠ 0) (hν : ν ≠ 0) (hsq : c * ν = e ^ 2) :
    c⁻¹ * (e * (e / ν)) = 1 := by
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  have hνν : ν * ν⁻¹ = 1 := mul_inv_cancel₀ hν
  linear_combination (-(c⁻¹ * ν⁻¹)) * hsq + (ν * ν⁻¹) * hcc + hνν

/-! ### Neighbouring pulses -/

/-- **Neighbouring odd pulses have equal or consecutive renewal charts.** For `j < k ≤ j + 2`
the chart index of `k` is that of `j` or the next one (`2τ_m ≤ 2τ_m''/25 < τ_m''`). -/
theorem pulseChartIndex_consecutive (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) {j k : ℤ}
    (hjk : j < k) (hkj : k ≤ j + 2) :
    ocPulseChartIndex α q Λ m k = ocPulseChartIndex α q Λ m j + 1 ∨
      ocPulseChartIndex α q Λ m k = ocPulseChartIndex α q Λ m j := by
  have hh : 0 < ocTauPP α q Λ m := AVRegularity.Construction.Stream.ocTauPP_pos hΛ
  have hτ0 : 0 < ocTau α q Λ m := AVRegularity.Construction.Stream.ocTau_pos hΛ
  have hτ : ocTau α q Λ m ≤ ocTauPP α q Λ m / 25 := LiftSetting.ocTau_le_div α q hΛ m
  obtain ⟨hj1, hj2⟩ := LiftSetting.pulseChartIndex_bounds α q hΛ m j
  obtain ⟨hk1, hk2⟩ := LiftSetting.pulseChartIndex_bounds α q hΛ m k
  have hjk' : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk.le
  have hkj' : (k : ℝ) ≤ (j : ℝ) + 2 := by exact_mod_cast hkj
  have e1 : (j : ℝ) * ocTau α q Λ m ≤ (k : ℝ) * ocTau α q Λ m :=
    mul_le_mul_of_nonneg_right hjk' hτ0.le
  have e2 : (k : ℝ) * ocTau α q Λ m ≤ ((j : ℝ) + 2) * ocTau α q Λ m :=
    mul_le_mul_of_nonneg_right hkj' hτ0.le
  have hlow : ((ocPulseChartIndex α q Λ m j : ℝ) - 1 / 2) * ocTauPP α q Λ m <
      ((ocPulseChartIndex α q Λ m k : ℝ) + 1 / 2) * ocTauPP α q Λ m :=
    lt_of_le_of_lt (hj1.trans e1) hk2
  have hupp : ((ocPulseChartIndex α q Λ m k : ℝ) - 1 / 2) * ocTauPP α q Λ m <
      ((ocPulseChartIndex α q Λ m j : ℝ) + 3 / 2) * ocTauPP α q Λ m := by linarith
  have hlow' : (ocPulseChartIndex α q Λ m j : ℝ) - 1 / 2 <
      (ocPulseChartIndex α q Λ m k : ℝ) + 1 / 2 := lt_of_mul_lt_mul_right hlow hh.le
  have hupp' : (ocPulseChartIndex α q Λ m k : ℝ) - 1 / 2 <
      (ocPulseChartIndex α q Λ m j : ℝ) + 3 / 2 := lt_of_mul_lt_mul_right hupp hh.le
  have h1 : (ocPulseChartIndex α q Λ m j : ℝ) < (ocPulseChartIndex α q Λ m k : ℝ) + 1 := by
    linarith
  have h2 : (ocPulseChartIndex α q Λ m k : ℝ) < (ocPulseChartIndex α q Λ m j : ℝ) + 2 := by
    linarith
  have h1Z : ocPulseChartIndex α q Λ m j < ocPulseChartIndex α q Λ m k + 1 := by
    exact_mod_cast h1
  have h2Z : ocPulseChartIndex α q Λ m k < ocPulseChartIndex α q Λ m j + 2 := by
    exact_mod_cast h2
  omega

/-- A time of the window of a pulse and of the observation window is, in cell time, in the
clipped lift window of the pulse. -/
theorem cellTime_mem_pulseLiftWindow {α q : ℝ} {Λ m : ℕ} {k : ℤ} {c tA tZ t : ℝ} (hc : 0 < c)
    (htk : t ∈ ocPulseWindow α q Λ m k) (ht : t ∈ Set.Icc tA tZ) :
    c⁻¹ * t ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / c)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / c) := by
  have htk' : t ∈ Set.Icc (((k : ℝ) - 61 / 48) * ocTau α q Λ m)
      (((k : ℝ) + 61 / 48) * ocTau α q Λ m) := htk
  exact AVRegularity.CycleComparison.Assembly.cellTime_mem_liftWindow hc htk' ht

/-! ### Quiet lift data of a pulse -/

section Quiet

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {Pc : Type*} {Ctx : Pc → Type*}

/-- **(A) The lift data of an odd pulse is quiet at quiet cell times.** Let `S` be a set of cell
times whose physical times `ℓ²s` are trimmed quiet times of the window `W` and output times of the
piece `p`, and let the family be fast independent on the trimmed quiet times of `W`. Then the
drift of the lift data of the odd pulse `k` over the fiber of `p` vanishes on `S` and its source
coefficients are fast independent on `S`. -/
theorem pulse_isQuietOn {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (ν B ρ lam : ℝ) {k : ℤ} (hk : Odd k)
    (F : ChartedFamily ι h D Pc Ctx) (p : Pc) (ctx : Ctx p) {W : Set ℝ}
    (hquiet : F.IsFastIndependentOn (ocTrimmedQuietTimes α q Λ ζ m ∩ W)) {S : Set ℝ}
    (hS : ∀ s ∈ S,
      ocEll q Λ m ν ^ 2 * s ∈ ocTrimmedQuietTimes α q Λ ζ m ∩ W ∩ (F.piece p).output) :
    IsQuietOn (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k (F.fiber p ctx)).edge
      (fun t z => Real.sqrt (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k (F.fiber p ctx)).η •
        (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k (F.fiber p ctx)).v t z) S := by
  refine ⟨?_, ?_⟩
  · intro s hs z
    have h0 : ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * s) = 0 :=
      AVRegularity.CycleComparison.Assembly.ocPulse_eq_zero_of_quiet hΛ hζ hk
        (ocTrimmedQuietTimes_subset_quiet hΛ ζ m (hS s hs).1.1)
    show Real.sqrt (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k (F.fiber p ctx)).η •
      ((ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) •
        (ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * s) •
          ocShearVel α q Λ m k (ocEpsilon q Λ m • z))) = 0
    simp only [h0, zero_smul, smul_zero]
  · intro v u d γ hγ w s hs X z z'
    have hγ' : γ ∈ liftEdges (ocEll q Λ m ν ^ 2) lam (F.fiber p ctx) v u d := hγ
    obtain ⟨γ₀, -, -, hc⟩ := LiftSetting.mem_liftEdges_fiber hγ'
    rw [hc]
    exact hquiet p ctx v u γ₀ d.1 w (ocEll q Λ m ν ^ 2 * s) (hS s hs) (lam • X) z z'

/-- A time of the window of a lift partition by family weights is an output time of a piece
(some weight is nonzero there, and a piece has weight only at its output times). -/
theorem exists_output_of_partition (F : ChartedFamily ι h D Pc Ctx) (pp : ℤ → Pc)
    {kset : Finset ℤ} {win : ℤ → Set ℝ} {quiet I : Set ℝ} {τ Cpart : ℝ}
    (hpart : IsLiftPartition kset (fun k => F.weight (pp k)) win quiet I τ Cpart) {t : ℝ}
    (ht : t ∈ I) : ∃ p, t ∈ (F.piece p).output := by
  by_contra hne
  have hsum : ∑ k ∈ kset, F.weight (pp k) t = 1 := hpart.2.2.1 t ht
  have h0 : ∑ k ∈ kset, F.weight (pp k) t = 0 :=
    Finset.sum_eq_zero fun k _ => F.weight_zero (pp k) t fun hmem => hne ⟨pp k, hmem⟩
  rw [h0] at hsum
  exact zero_ne_one hsum

end Quiet

/-! ### The edge flux on a quiet overlap, in the chart of the second piece -/

section Flux

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {Pc : Type*} {Ctx : Pc → Type*}

/-- **The physical edge flux on a quiet overlap, read in the second chart.** In the situation of
`edgeFlux_quiet_overlap_atlas_of_contDiff` (an adjacent pair `p ≠ p'` of the atlas, the only
active pieces at the quiet time `t`, with weights summing to one), the flux term of the actual
equation is also the transported label flux of the second piece `p'`: the transported label
fluxes of the two pieces agree on the overlap (`pieceFlux_transition_of_contDiff`). -/
theorem edgeFlux_quiet_overlap_atlas_target_of_contDiff (F : ChartedFamily ι h D Pc Ctx)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (K : ι → ℕ) (hdesc : F.IsDescending K) (T : F.Atlas)
    {quiet W : Set ℝ} (hTcov : T.CoversQuiet quiet W) (hTq : T.IsQuiet ν e E) {t : ℝ}
    {p p' : Pc} (hpq : p ≠ p') (hadj : T.adjacent p p')
    (hctx : T.sameCtx p p' hadj (actual p) (actual p'))
    (ht : t ∈ quiet ∩ W ∩ (F.piece p).output ∩ (F.piece p').output)
    (hw : ∀ p₁, F.weight p₁ t ≠ 0 → p₁ = p ∨ p₁ = p')
    (hsum : F.weight p t + F.weight p' t = 1) {r : ℕ} {U : Vec 2 → ∀ i, h i}
    (hU : ContDiff ℝ (r : ℕ∞) U) (hrD : D ≤ r + 1) (i : ι) (x : Vec 2) (a₀ : Fin 2) :
    ∑ i' : ι, ∑ d : admissibleOrders K D i i',
        edgeCoefficient F ν e E actual K i i' d t x
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => U y i') x) a₀ =
      ∑ j : Fin 2, chartInvJacobian ⇑((F.piece p').material t).symm x a₀ j •
        labelEdgeFlux F ν e E p' (actual p') t (fun y => U ((F.piece p').material t y)) i
          (((F.piece p').material t).symm x) j :=
  (edgeFlux_quiet_overlap_atlas_of_contDiff F ν e E actual K hdesc T hTcov hTq hpq hadj hctx ht
    hw hsum hU hrD i x a₀).trans
    (pieceFlux_transition_of_contDiff F ν e E (hTq p p' hadj (actual p) (actual p') hctx) hU
      hrD i x (hTcov p p' hadj t ht (((F.piece p').material t).symm x)) a₀).symm

end Flux

/-! ### The quiet means of the observed pulses -/

section Means

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K₀ k₀ L qs qf : ℕ} {π : ι → ℝ} {e₀ ν₀ B₀ ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {bE : ι → ι → ℝ} {Θ : ℝ} {Pc : Type*} {Ctx : Pc → Type*}

/-- **The quiet means of one pulse.** Let `Q` be the lift data of the odd pulse `k` over the
fiber of a piece `p₀` whose material map at the time `t` is the renewal chart of the pulse, in a
lift setting with a lift sequence and the slow ratio `lam ρ⁻¹ = E⁻¹`. Let `t` be a quiet time
of the window `W`, an output time of `p₀`, with cell time `ℓ⁻²t` in the lift window, and let
`a(t, ·)` be smooth. If the family edge flux of `a` at `t` is the Piola transport of the label
edge flux of `p₀` (`hflux`), then

* the mean of grade `0` is `-ν Δa(t, x)`;
* if `1 ≤ H`, the mean of grade `1` is minus the physical divergence of the family edge flux of
  `a`;
* the means of the grades `2 ≤ r ≤ H` vanish. -/
theorem pulse_quiet_means {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {φ : ℝ → Vec 2 → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) (hφ : IsAdmissibleStream φ) {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B)
    {ρ lam E : ℝ} (hρ : 0 < ρ) (hlam : lam * ρ⁻¹ = E⁻¹) (F : ChartedFamily ι h D Pc Ctx)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) {W : Set ℝ}
    (hquiet : F.IsFastIndependentOn (ocTrimmedQuietTimes α q Λ ζ m ∩ W)) {k : ℤ} (hk : Odd k)
    (p₀ : Pc) {t₀ t₁ : ℝ} {par : Fin 2} {Vsh : ℝ → ℝ → ℝ}
    (P : IsLiftSetting (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k (F.fiber p₀ (actual p₀))) π
      t₀ t₁ e₀ ν₀ B₀ ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ par Vsh H N K₀ k₀ L qs qf CG Cw Cj bE Θ)
    (hDsZ : D ≤ max (k₀ + 1) (L + 2)) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k (F.fiber p₀ (actual p₀)))
      (K₀ + D + 2) (max (k₀ + 1) (L + 2)) t₀ t₁ N H Cc)
    (a : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (hs : (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc t₀ t₁)
    (htq : t ∈ ocTrimmedQuietTimes α q Λ ζ m ∩ W ∩ (F.piece p₀).output)
    (hmat : ⇑((F.piece p₀).material t) =
      ocChart α q Λ m φ hφ (ocPulseChartIndex α q Λ m k) t)
    (ha : ContDiff ℝ (⊤ : ℕ∞) (a t))
    (hflux : ∀ (v : ι) (x' : Vec 2) (a₀ : Fin 2),
      ∑ i' : ι, ∑ d : admissibleOrders K D v i',
        edgeCoefficient F ν (ocEpsilon q Λ m) E actual K v i' d t x'
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => a t y i') x') a₀ =
      ∑ i₀ : Fin 2, chartInvJacobian ⇑((F.piece p₀).material t).symm x' a₀ i₀ •
        labelEdgeFlux F ν (ocEpsilon q Λ m) E p₀ (actual p₀) t
          (fun y => a t ((F.piece p₀).material t y)) v (((F.piece p₀).material t).symm x') i₀)
    (x : Vec 2) :
    (pulseMeanField (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N 0
        (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k (F.fiber p₀ (actual p₀))) Cc
        (ocChart α q Λ m φ hφ (ocPulseChartIndex α q Λ m k))
        (ocChartInv α q Λ m φ hφ (ocPulseChartIndex α q Λ m k)) a t x =
      -ν • ∑ i : Fin 2, fderiv ℝ (fun x' => fderiv ℝ (a t) x' (basisVec i)) x (basisVec i)) ∧
    (1 ≤ H → ∀ v : ι, pulseMeanField (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N 1
        (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k (F.fiber p₀ (actual p₀))) Cc
        (ocChart α q Λ m φ hφ (ocPulseChartIndex α q Λ m k))
        (ocChartInv α q Λ m φ hφ (ocPulseChartIndex α q Λ m k)) a t x v =
      -∑ a₀ : Fin 2, fderiv ℝ (fun x' => ∑ i' : ι, ∑ d : admissibleOrders K D v i',
        edgeCoefficient F ν (ocEpsilon q Λ m) E actual K v i' d t x'
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => a t y i') x') a₀) x (basisVec a₀)) ∧
    ∀ r : ℕ, 2 ≤ r → r ≤ H →
      pulseMeanField (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r
        (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k (F.fiber p₀ (actual p₀))) Cc
        (ocChart α q Λ m φ hφ (ocPulseChartIndex α q Λ m k))
        (ocChartInv α q Λ m φ hφ (ocPulseChartIndex α q Λ m k)) a t x = 0 := by
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of hν he
  have hc : ocEll q Λ m ν ^ 2 ≠ 0 := pow_ne_zero 2 hℓ
  have hsq : ocEll q Λ m ν ^ 2 * ν = ocEpsilon q Λ m ^ 2 := ocEll_sq_mul hν
  -- the single cell time `ℓ⁻²t` is quiet
  have hS : ({(ocEll q Λ m ν ^ 2)⁻¹ * t} : Set ℝ) ⊆ Set.Icc t₀ t₁ :=
    Set.singleton_subset_iff.2 hs
  have htS : (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ ({(ocEll q Λ m ν ^ 2)⁻¹ * t} : Set ℝ) :=
    Set.mem_singleton _
  have hq : IsQuietOn (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k (F.fiber p₀ (actual p₀))).edge
      (fun s z => Real.sqrt (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k
          (F.fiber p₀ (actual p₀))).η •
        (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k (F.fiber p₀ (actual p₀))).v s z)
      {(ocEll q Λ m ν ^ 2)⁻¹ * t} :=
    pulse_isQuietOn hΛ hζ hφ ν B ρ lam hk F p₀ (actual p₀) hquiet fun s hs' => by
      rw [Set.mem_singleton_iff.1 hs', mul_inv_cancel_left₀ hc t]
      exact htq
  -- the renewal chart of the pulse at the time `t`
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (ocChart α q Λ m φ hφ (ocPulseChartIndex α q Λ m k) t) :=
    (Charts.contDiff_ocChart_joint hφ α q Λ m (ocPulseChartIndex α q Λ m k)).comp
      (contDiff_const.prodMk contDiff_id)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (ocChartInv α q Λ m φ hφ (ocPulseChartIndex α q Λ m k) t) :=
    (Charts.contDiff_ocChartInv_joint hφ α q Λ m (ocPulseChartIndex α q Λ m k)).comp
      (contDiff_const.prodMk contDiff_id)
  have hψχ : ∀ y, ocChartInv α q Λ m φ hφ (ocPulseChartIndex α q Λ m k) t
      (ocChart α q Λ m φ hφ (ocPulseChartIndex α q Λ m k) t y) = y := fun y =>
    Charts.ocChartInv_ocChart α q Λ m φ hφ (ocPulseChartIndex α q Λ m k) t y
  have hχψ : ∀ x', ocChart α q Λ m φ hφ (ocPulseChartIndex α q Λ m k) t
      (ocChartInv α q Λ m φ hφ (ocPulseChartIndex α q Λ m k) t x') = x' := fun x' =>
    Charts.ocChart_ocChartInv α q Λ m φ hφ (ocPulseChartIndex α q Λ m k) t x'
  have hd : ∀ y,
      (jacMatrix (ocChart α q Λ m φ hφ (ocPulseChartIndex α q Λ m k) t) y).det = 1 :=
    Charts.ocChart_det hφ α q Λ m (ocPulseChartIndex α q Λ m k) t
  -- the labels of the piece are the inverse renewal chart
  have hψeq : ocChartInv α q Λ m φ hφ (ocPulseChartIndex α q Λ m k) t =
      ⇑((F.piece p₀).material t).symm := by
    funext x'
    apply ((F.piece p₀).material t).injective
    rw [Homeomorph.apply_symm_apply, hmat, Charts.ocChart_ocChartInv]
  -- the source edges of the lift data are the lifted fiber of the piece
  have hQe : (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k (F.fiber p₀ (actual p₀))).edge =
      liftEdges (ocEll q Λ m ν ^ 2) lam (F.fiber p₀ (actual p₀)) := rfl
  refine ⟨?_, fun hH v => ?_, fun r hr hrH => ?_⟩
  · exact pulseMeanField_quiet_zero P hDsZ hseq hS hq hc hρ.ne'
      (pulse_scale_h3 α q Λ m ζ hφ hν hB ρ lam k (F.fiber p₀ (actual p₀)))
      (ocChart α q Λ m φ hφ (ocPulseChartIndex α q Λ m k))
      (ocChartInv α q Λ m φ hφ (ocPulseChartIndex α q Λ m k)) a htS hχ
      (hψ.differentiable (by simp)) hψχ hχψ hd
      (fun y => pulse_G_chart α q Λ m ζ hφ ν B hρ.ne' lam k (F.fiber p₀ (actual p₀)) hℓ t y)
      ha x
  · exact pulseMeanField_quiet_one P F ν (ocEpsilon q Λ m) E actual K p₀ hQe hc he hν.ne'
      hρ.ne'
      (quiet_scale_sqrt he hsq
        (pulse_scale_h2 α q Λ m ζ hφ hν hB he ρ lam k (F.fiber p₀ (actual p₀))))
      hlam (quiet_scale_time hc hν.ne' hsq) hDsZ hseq hH hS hq
      (ocChart α q Λ m φ hφ (ocPulseChartIndex α q Λ m k))
      (ocChartInv α q Λ m φ hφ (ocPulseChartIndex α q Λ m k)) a htS hχ hψ hψχ hχψ hd ha v
      (fun x' a₀ => by
        rw [hψeq, hmat.symm]
        exact hflux v x' a₀) x
  · exact pulseMeanField_quiet_high P hDsZ hseq hS hq (ocEll q Λ m ν ^ 2) ρ
      (ocDStar q Λ m ν B / ρ) hc (ocChart α q Λ m φ hφ (ocPulseChartIndex α q Λ m k))
      (ocChartInv α q Λ m φ hφ (ocPulseChartIndex α q Λ m k)) a htS hr hrH hχ ha x

/-- **The means of two neighbouring observed pulses agree on their quiet overlap.** For observed
pulses `j < k`, at a quiet time `t` of both pulse windows at which only the pieces `pp j ≠ pp k`
carry weight, with weights summing to one, the pulse means of every grade `r ≤ H` of a field
smooth at the time `t` coincide. The pieces are adjacent in the consecutive-closed atlas
(`pulseChartIndex_consecutive`), so the family edge flux is the transported label flux of either
piece. -/
theorem obs_pulse_means_agree_of_lt {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (hφs : IsAdmissibleStream (Φ (m - 1))) {ν B : ℝ}
    (hν : 0 < ν) (hB : 0 < B) {ρ lam E : ℝ} (hρ : 0 < ρ) (hlam : lam * ρ⁻¹ = E⁻¹)
    (F : ChartedFamily ι h D Pc Ctx) (actual : ∀ p, Ctx p) (K : ι → ℕ)
    (hdesc : F.IsDescending K) {tA tZ : ℝ}
    (hquiet : F.IsFastIndependentOn (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tA tZ)) (T : F.Atlas)
    (hTcons : T.IsConsecutiveClosed (Set.Icc tA tZ))
    (hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m) (Set.Icc tA tZ))
    (hTq : T.IsQuiet ν (ocEpsilon q Λ m) E)
    (hTact : ∀ p p' (hpq : T.adjacent p p'),
      ((F.piece p).output ∩ (F.piece p').output ∩ Set.Icc tA tZ).Nonempty →
        T.sameCtx p p' hpq (actual p) (actual p'))
    (pp : ℤ → Pc)
    (hpp : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      (F.piece (pp k)).label = ocPulseChartIndex α q Λ m k ∧
      (∀ t, ⇑((F.piece (pp k)).material t) =
        ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) t) ∧
      ocPulseWindow α q Λ m k ∩ Set.Icc tA tZ ⊆ (F.piece (pp k)).output)
    {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
    (P : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSetting (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k
          (F.fiber (pp k) (actual (pp k)))) π
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)
        e₀ ν₀ B₀ ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ (par k) (V k) H N K₀ k₀ L qs qf CG Cw Cj bE Θ)
    (hDsZ : D ≤ max (k₀ + 1) (L + 2)) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k
          (F.fiber (pp k) (actual (pp k)))) (K₀ + D + 2) (max (k₀ + 1) (L + 2))
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    (a : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (ht : t ∈ Set.Icc tA tZ)
    (ha : ContDiff ℝ (⊤ : ℕ∞) (a t)) {j k : ℤ} (hj : j ∈ ocObsPulses α q Λ m tA tZ)
    (hk : k ∈ ocObsPulses α q Λ m tA tZ) (hjk : j < k) (htq : t ∈ ocQuietTimes α q Λ ζ m)
    (htj : t ∈ ocPulseWindow α q Λ m j) (htk : t ∈ ocPulseWindow α q Λ m k)
    (hsum : F.weight (pp j) t + F.weight (pp k) t = 1)
    (honly : ∀ p, F.weight p t ≠ 0 → p = pp j ∨ p = pp k) (hne : pp j ≠ pp k) {r : ℕ}
    (hr : r ≤ H) (x : Vec 2) :
    pulseMeanField (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r
        (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam j (F.fiber (pp j) (actual (pp j))))
        (Cc j) (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m j))
        (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m j)) a t x =
      pulseMeanField (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r
        (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k (F.fiber (pp k) (actual (pp k))))
        (Cc k) (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
        (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) a t x := by
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 :=
    lt_of_le_of_ne (sq_nonneg (ocEll q Λ m ν)) (pow_ne_zero 2 hℓ).symm
  have hjodd : Odd j := LiftSetting.obsPulse_odd hj
  have hkodd : Odd k := LiftSetting.obsPulse_odd hk
  have houtj : t ∈ (F.piece (pp j)).output := (hpp j hj).2.2 ⟨htj, ht⟩
  have houtk : t ∈ (F.piece (pp k)).output := (hpp k hk).2.2 ⟨htk, ht⟩
  have hmeet : ((F.piece (pp j)).output ∩ (F.piece (pp k)).output ∩ Set.Icc tA tZ).Nonempty :=
    ⟨t, ⟨houtj, houtk⟩, ht⟩
  -- the two pulses are neighbours, so their pieces are adjacent in the atlas
  have hle : k ≤ j + 2 := by
    by_contra hfar
    have hfar' : j + 4 ≤ k := by
      obtain ⟨a', ha'⟩ := hjodd
      obtain ⟨b', hb'⟩ := hkodd
      omega
    exact not_mem_two_windows_far hΛ hfar' htj htk
  have hlab : (F.piece (pp k)).label = (F.piece (pp j)).label + 1 ∨
      (F.piece (pp k)).label = (F.piece (pp j)).label := by
    rw [(hpp k hk).1, (hpp j hj).1]
    exact pulseChartIndex_consecutive α q hΛ m hjk hle
  have hadj : T.adjacent (pp j) (pp k) := hTcons (pp j) (pp k) hne hlab hmeet
  have hctx : T.sameCtx (pp j) (pp k) hadj (actual (pp j)) (actual (pp k)) :=
    hTact (pp j) (pp k) hadj hmeet
  have ht4 : t ∈ ocQuietTimes α q Λ ζ m ∩ Set.Icc tA tZ ∩ (F.piece (pp j)).output ∩
      (F.piece (pp k)).output := ⟨⟨⟨htq, ht⟩, houtj⟩, houtk⟩
  -- a time of two neighbouring pulse windows is a trimmed quiet time
  have htt : t ∈ ocTrimmedQuietTimes α q Λ ζ m := by
    have hτ := Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
    have hjk2 : (j : ℝ) + 2 ≤ k := by
      have : j + 2 ≤ k := by
        obtain ⟨a', ha'⟩ := hjodd
        obtain ⟨b', hb'⟩ := hkodd
        omega
      exact_mod_cast this
    have htk1 : ((k : ℝ) - 61 / 48) * ocTau α q Λ m ≤ t := htk.1
    have htj2 : t ≤ ((j : ℝ) + 61 / 48) * ocTau α q Λ m := htj.2
    refine odd_trimmed_gap hΛ hζ hjodd ?_ ?_
    · exact (mul_le_mul_of_nonneg_right (by linarith) hτ.le).trans htk1
    · exact htj2.trans (mul_le_mul_of_nonneg_right (by linarith) hτ.le)
  -- the family edge flux is the transported label flux of either piece
  have hfluxj : ∀ (v : ι) (x' : Vec 2) (a₀ : Fin 2),
      ∑ i' : ι, ∑ d : admissibleOrders K D v i',
        edgeCoefficient F ν (ocEpsilon q Λ m) E actual K v i' d t x'
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => a t y i') x') a₀ =
      ∑ i₀ : Fin 2, chartInvJacobian ⇑((F.piece (pp j)).material t).symm x' a₀ i₀ •
        labelEdgeFlux F ν (ocEpsilon q Λ m) E (pp j) (actual (pp j)) t
          (fun y => a t ((F.piece (pp j)).material t y)) v
          (((F.piece (pp j)).material t).symm x') i₀ := fun v x' a₀ =>
    edgeFlux_quiet_overlap_atlas_of_contDiff F ν (ocEpsilon q Λ m) E actual K hdesc T hTcov hTq
      hne hadj hctx ht4 honly hsum (r := D) (ha.of_le (by exact_mod_cast le_top))
      (Nat.le_succ D) v x' a₀
  have hfluxk : ∀ (v : ι) (x' : Vec 2) (a₀ : Fin 2),
      ∑ i' : ι, ∑ d : admissibleOrders K D v i',
        edgeCoefficient F ν (ocEpsilon q Λ m) E actual K v i' d t x'
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => a t y i') x') a₀ =
      ∑ i₀ : Fin 2, chartInvJacobian ⇑((F.piece (pp k)).material t).symm x' a₀ i₀ •
        labelEdgeFlux F ν (ocEpsilon q Λ m) E (pp k) (actual (pp k)) t
          (fun y => a t ((F.piece (pp k)).material t y)) v
          (((F.piece (pp k)).material t).symm x') i₀ := fun v x' a₀ =>
    edgeFlux_quiet_overlap_atlas_target_of_contDiff F ν (ocEpsilon q Λ m) E actual K hdesc T
      hTcov hTq hne hadj hctx ht4 honly hsum (r := D) (ha.of_le (by exact_mod_cast le_top))
      (Nat.le_succ D) v x' a₀
  -- both pulses have the explicit quiet means
  obtain ⟨hj0, hj1, hj2⟩ := pulse_quiet_means hΛ hζ hφs hν hB hρ hlam F actual K hquiet hjodd
    (pp j) (P j hj) hDsZ (hseq j hj) a (cellTime_mem_pulseLiftWindow hc0 htj ht)
    ⟨⟨htt, ht⟩, houtj⟩ ((hpp j hj).2.1 t) ha hfluxj x
  obtain ⟨hk0, hk1, hk2⟩ := pulse_quiet_means hΛ hζ hφs hν hB hρ hlam F actual K hquiet hkodd
    (pp k) (P k hk) hDsZ (hseq k hk) a (cellTime_mem_pulseLiftWindow hc0 htk ht)
    ⟨⟨htt, ht⟩, houtk⟩ ((hpp k hk).2.1 t) ha hfluxk x
  have hr3 : r = 0 ∨ r = 1 ∨ 2 ≤ r := by omega
  rcases hr3 with rfl | rfl | hr2
  · exact hj0.trans hk0.symm
  · funext v
    exact (hj1 hr v).trans (hk1 hr v).symm
  · exact (hj2 r hr2 hr).trans (hk2 r hr2 hr).symm

/-- **(B) The weighted pulse means agree** (the hypothesis `hagree` of `glued_meanPart`, with
`edge k = F.fiber (pp k) (actual (pp k))` and `ϖ k = F.weight (pp k)`). At a time `t` of the
window, for observed pulses `k`, `j` of nonzero weight, the pulse means of every grade
`r ≤ H` of a field smooth at the time `t` coincide: either `j = k`, or `t` lies in a quiet
overlap of the two pulse windows on which only the pieces `pp k`, `pp j` are weighted
(`active_pieces`), and both means are the explicit quiet means (`pulse_quiet_means`). -/
theorem obs_pulse_means_agree {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (hφs : IsAdmissibleStream (Φ (m - 1))) {ν B : ℝ}
    (hν : 0 < ν) (hB : 0 < B) {ρ lam E : ℝ} (hρ : 0 < ρ) (hlam : lam * ρ⁻¹ = E⁻¹)
    (F : ChartedFamily ι h D Pc Ctx) (actual : ∀ p, Ctx p) (K : ι → ℕ)
    (hdesc : F.IsDescending K) {tA tZ : ℝ}
    (hquiet : F.IsFastIndependentOn (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tA tZ)) (T : F.Atlas)
    (hTcons : T.IsConsecutiveClosed (Set.Icc tA tZ))
    (hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m) (Set.Icc tA tZ))
    (hTq : T.IsQuiet ν (ocEpsilon q Λ m) E)
    (hTact : ∀ p p' (hpq : T.adjacent p p'),
      ((F.piece p).output ∩ (F.piece p').output ∩ Set.Icc tA tZ).Nonempty →
        T.sameCtx p p' hpq (actual p) (actual p'))
    (pp : ℤ → Pc)
    (hpp : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      (F.piece (pp k)).label = ocPulseChartIndex α q Λ m k ∧
      (∀ t, ⇑((F.piece (pp k)).material t) =
        ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) t) ∧
      ocPulseWindow α q Λ m k ∩ Set.Icc tA tZ ⊆ (F.piece (pp k)).output)
    (hppinj : Set.InjOn pp (↑(ocObsPulses α q Λ m tA tZ) : Set ℤ)) {Cpart : ℝ}
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k))
      (ocPulseWindow α q Λ m) (ocQuietTimes α q Λ ζ m) (Set.Icc tA tZ) (ocTau α q Λ m) Cpart)
    {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
    (P : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSetting (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k
          (F.fiber (pp k) (actual (pp k)))) π
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)
        e₀ ν₀ B₀ ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ (par k) (V k) H N K₀ k₀ L qs qf CG Cw Cj bE Θ)
    (hDsZ : D ≤ max (k₀ + 1) (L + 2)) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k
          (F.fiber (pp k) (actual (pp k)))) (K₀ + D + 2) (max (k₀ + 1) (L + 2))
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    (a : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (ht : t ∈ Set.Icc tA tZ)
    (ha : ContDiff ℝ (⊤ : ℕ∞) (a t)) {k : ℤ} (hk : k ∈ ocObsPulses α q Λ m tA tZ)
    (hwk : F.weight (pp k) t ≠ 0) {j : ℤ} (hj : j ∈ ocObsPulses α q Λ m tA tZ)
    (hwj : F.weight (pp j) t ≠ 0) {r : ℕ} (hr : r ∈ Finset.range (H + 1)) (x : Vec 2) :
    pulseMeanField (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r
        (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam j (F.fiber (pp j) (actual (pp j))))
        (Cc j) (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m j))
        (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m j)) a t x =
      pulseMeanField (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r
        (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k (F.fiber (pp k) (actual (pp k))))
        (Cc k) (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
        (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) a t x := by
  have hrH : r ≤ H := Nat.le_of_lt_succ (Finset.mem_range.1 hr)
  by_cases hjk : j = k
  · subst hjk
    rfl
  have hcov : ∀ t' ∈ Set.Icc tA tZ, ∃ p, t' ∈ (F.piece p).output := fun _ ht' =>
    exists_output_of_partition F pp hpart ht'
  obtain h1 | ⟨j', hj', -, htq, htj, htk, hsum, honly⟩ :=
    active_pieces hΛ hζ F pp hppinj hpart hcov hk ht hwk
  · -- the piece `pp k` alone is weighted: impossible, `pp j ≠ pp k` is weighted too
    exact absurd (h1.2 (pp j) fun hpe => hjk (hppinj hj hk hpe)) hwj
  · -- the other weighted pulse is `j`
    have hjj : j' = j := by
      rcases honly (pp j) hwj with hpe | hpe
      · exact absurd (hppinj hj hk hpe) hjk
      · exact (hppinj hj hj' hpe).symm
    rw [hjj] at htj hsum honly
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · exact obs_pulse_means_agree_of_lt hΛ hζ hφs hν hB hρ hlam F actual K hdesc hquiet T hTcons
        hTcov hTq hTact pp hpp P hDsZ Cc hseq a ht ha hj hk hlt htq htj htk
        ((add_comm _ _).trans hsum) (fun p hp => (honly p hp).symm)
        (fun hpe => hjk (hppinj hj hk hpe)) hrH x
    · exact (obs_pulse_means_agree_of_lt hΛ hζ hφs hν hB hρ hlam F actual K hdesc hquiet T
        hTcons hTcov hTq hTact pp hpp P hDsZ Cc hseq a ht ha hk hj hgt htq htk htj hsum honly
        (fun hpe => hjk (hppinj hj hk hpe.symm)) hrH x).symm

end Means

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The weak identity of the glued lift of a finite-rank coarse field** (the gluing identity).
For a coarse
field `a = ∑_j c_j(t) φ_j(x)` with coefficients of integral type, the glued lift `û = 𝒯a` over
the observed pulses satisfies, tested against a `C¹` periodic `φ`,
`d/dt ∫⟪û, φ⟫ = -∫⟪b_m · ∇û, φ⟫ - ν ∫ ∑_j ⟪∂_j û, ∂_j φ⟫ - ∫ ∑_a ⟪𝒮û_a + R_a, ∂_a φ⟫`
`+ ∫⟪q + 𝒯(𝔡a), φ⟫ + ∑_k ϖ_k' ∫⟪𝒯_k a, φ⟫` (`glued_finiteRank_identity`), where `𝒮û` is the
physical edge flux of the glued lift, `(R, q)` the glued tail flux and force, and
`𝔡a = ∂_t a + b_{m-1} · ∇a + ∑_r 𝓜_r a` the coarse defect field with the glued means `𝓜_r`.
It combines the glued weak identity (`glued_pulses_weak`), the split of the pulse rests
(`labelRest_split`) and the glued edge, mean and tail terms (`glued_edges`, `glued_meanPart`,
`glued_tail`). -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] in
/-- The cell-time density of the chart-frame field is smooth in the slow variable. -/
theorem chartFieldDot_contDiff {κ : Type*} [Fintype κ] (cf dcf : κ → ℝ → ℝ)
    (φ : κ → Vec 2 → ∀ i, h i) (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (χ W : ℝ → Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2))
    (hW : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => W p.1 p.2)) (c ρ s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (chartFieldDot cf dcf φ χ W c ρ s) := by
  rw [chartFieldDot_eq_sum]
  refine ContDiff.sum fun j _ => ContDiff.const_smul _ ?_
  rcases j with k | k
  · exact (chartMode_contDiff φ hφ χ hχ c ρ k).comp (contDiff_const.prodMk contDiff_id)
  · exact (chartModeDot_contDiff φ hφ χ W hχ hW c ρ k).comp (contDiff_const.prodMk contDiff_id)

/-- **The weak identity of the glued lift of a finite-rank coarse field.** -/
theorem glued_finiteRank_identity {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseqΦ : IsOCStreamSeq α q Λ ζ Φ) (hm : 1 ≤ m) (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφs : IsAdmissibleStream (Φ (m - 1))) {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B) {ρ E : ℝ}
    (hρ : 0 < ρ) {D : ℕ} {Pc : Type*} {Ctx : Pc → Type*} (F : ChartedFamily ι h D Pc Ctx)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (htorus : IsTorusCompatible F actual E) (T : F.Atlas) {tA tZ : ℝ} (htAZ : tA ≤ tZ)
    (hTcons : T.IsConsecutiveClosed (Icc tA tZ))
    (hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m) (Icc tA tZ))
    (hTq : T.IsQuiet ν (ocEpsilon q Λ m) E)
    (hTact : ∀ p q' (hpq : T.adjacent p q'),
      ((F.piece p).output ∩ (F.piece q').output ∩ Icc tA tZ).Nonempty →
        T.sameCtx p q' hpq (actual p) (actual q'))
    (pp : ℤ → Pc)
    (hpp : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      (F.piece (pp k)).label = ocPulseChartIndex α q Λ m k ∧
      (∀ t, ⇑((F.piece (pp k)).material t) = ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q
        Λ m k) t) ∧
      ocPulseWindow α q Λ m k ∩ Icc tA tZ ⊆ (F.piece (pp k)).output)
    (hppinj : Set.InjOn pp ↑(ocObsPulses α q Λ m tA tZ)) {quiet : Set ℝ} {Cpart : ℝ}
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k))
      (ocPulseWindow α q Λ m) quiet (Icc tA tZ) (ocTau α q Λ m) Cpart)
    (hcov : ∀ t ∈ Icc tA tZ, ∃ p, t ∈ (F.piece p).output)
    {π : ι → ℝ} {e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : ℤ → Fin 2}
    {V : ℤ → ℝ → ℝ → ℝ} {H N K₀ k₀ L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSetting (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k)
        (actual (pp k)))) π
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)
        e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ (par k) (V k) H N K₀ k₀ L qs qf CG Cw Cj edgeM Θ)
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k)
        (actual (pp k)))) sX sZ
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    (sXc sZc Acl : ℕ) (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (hX : sXc ≤ K₀ + D + 2) (hZ : sZc ≤ max (k₀ + 1) (L + 2))
    {κ : Type*} [Fintype κ] (cf dcf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (φ j)) (hφp : ∀ j, IsZ2Periodic (φ j)) (A₀ B₀ : ℝ)
    (hA : A₀ ≤ tA) (hB₀ : tZ ≤ B₀) (hcf : ∀ j, IsPrimOn A₀ B₀ (cf j) (dcf j))
    (hcs : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ (n : Fin 2 → ℤ) v u d,
      ∀ γ ∈ (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual (pp
        k)))).edge v u d,
        ∀ w t X z, γ.coeff w t (X + ρ⁻¹ • latticeShift n) z = γ.coeff w t X z)
    (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ hh, hh ≤ H →
      ∀ τ ∈ Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXc sZc Acl
        (tailScalarField (fun _ => 0) N D (ocDStar q Λ m ν B / ρ) (chartField cf φ (ocChart α q Λ m
          (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ) τ)
        (tailFluxField (fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ (Φ (m - 1))
          hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual (pp k)))) (Cc k) N hh n) N D
          (ocDStar q Λ m ν B / ρ) (chartField cf φ (ocChart α q Λ m (Φ (m - 1)) hφs
            (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ) τ)
        (fun j => Vc k hh j τ))
    (hagree : ∀ t ∈ Icc tA tZ, ∀ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t ≠ 0 →
      ∀ j ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp j) t ≠ 0 → ∀ r ∈ Finset.range (H + 1), ∀ x,
        pulseMeanField (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r (pulseLiftData α q Λ m ζ
          (Φ (m - 1)) hφs ν B ρ (ρ / E) j (F.fiber (pp j) (actual (pp j)))) (Cc j) (ocChart α q Λ m
          (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m j)) (ocChartInv α q Λ m (Φ (m - 1)) hφs
          (ocPulseChartIndex α q Λ m j)) (fun t' x' => ∑ j', cf j' t' • φ j' x') t x =
          pulseMeanField (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r (pulseLiftData α q Λ m ζ
            (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual (pp k)))) (Cc k) (ocChart α q Λ
            m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocChartInv α q Λ m (Φ (m - 1)) hφs
            (ocPulseChartIndex α q Λ m k)) (fun t' x' => ∑ j', cf j' t' • φ j' x') t x)
    (hMr : ∀ t ∈ Icc tA tZ, ∀ r ∈ Finset.range (H + 1), ContDiff ℝ (N : ℕ∞) (fun x =>
      gluedMean (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k)) (ocEll q Λ m ν ^ 2) ρ
        (ocDStar q Λ m ν B / ρ) N r (fun k => pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E)
        k (F.fiber (pp k) (actual (pp k)))) Cc (fun k => ocChart α q Λ m (Φ (m - 1)) hφs
        (ocPulseChartIndex α q Λ m k)) (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs
        (ocPulseChartIndex α q Λ m k)) (fun t'' x'' => ∑ j', cf j' t'' • φ j' x'') t x))
    (v : ι) (φt : Vec 2 → h v) (hφt : ContDiff ℝ 1 φt) (hφtp : IsZ2Periodic φt) :
    IsPrimOn tA tZ
      (fun t => ∫ x in unitCube, inner ℝ (gluedLift (ocObsPulses α q Λ m tA tZ) (fun k => F.weight
        (pp k)) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H Cc (fun k =>
        ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun k => ocChartInv α q Λ m
        (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun t x => ∑ j, cf j t • φ j x) t x v) (φt
        x))
      (fun t => -(∫ x in unitCube, inner ℝ (∑ j, streamVel (Φ m) t x j • fderiv ℝ (fun x' => ∑ k ∈
        ocObsPulses α q Λ m tA tZ, F.weight (pp k) t • obsLift α q Λ m (Φ (m - 1)) hφs ν B ρ Cc N H
        cf φ k t x' v) x (basisVec j)) (φt x)) -
        ν * (∫ x in unitCube, ∑ j, inner ℝ (fderiv ℝ (fun x' => ∑ k ∈ ocObsPulses α q Λ m tA tZ,
          F.weight (pp k) t • obsLift α q Λ m (Φ (m - 1)) hφs ν B ρ Cc N H cf φ k t x' v) x
          (basisVec j)) (fderiv ℝ φt x (basisVec j))) +
        ((-∫ x in unitCube, ∑ a₀ : Fin 2, inner ℝ (physEdgeFluxVec F ν (ocEpsilon q Λ m) E actual K
          t (fun y => ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t • obsLift α q Λ m (Φ (m -
          1)) hφs ν B ρ Cc N H cf φ k t y) v x a₀) (fderiv ℝ φt x (basisVec a₀))) +
          (-(∫ x in unitCube, ∑ a₀ : Fin 2, inner ℝ ((∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp
            k) t • tailFluxPhys (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)
            t) H N Acl (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vc k) t x
            a₀) v) (fderiv ℝ φt x (basisVec a₀))) + ∫ x in unitCube, inner ℝ ((∑ k ∈ ocObsPulses α
            q Λ m tA tZ, F.weight (pp k) t • tailForcePhys (ocChartInv α q Λ m (Φ (m - 1)) hφs
            (ocPulseChartIndex α q Λ m k) t) H N Acl (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ
            (ocEpsilon q Λ m) (Vc k) t x) v) (φt x)) +
          (∫ x in unitCube, inner ℝ (gluedLift (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp
            k)) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H Cc (fun k =>
            ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun k => ocChartInv α q
            Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun t' x' => (∑ j, dcf j t' • φ j
            x' + ∑ j, cf j t' • fderiv ℝ (φ j) x' (streamVel (Φ (m - 1)) t' x')) + ∑ r ∈
            Finset.range (H + 1), gluedMean (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k))
            (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r (fun k => pulseLiftData α q Λ m ζ (Φ
            (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual (pp k)))) Cc (fun k => ocChart α q
            Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun k => ocChartInv α q Λ m (Φ (m -
            1)) hφs (ocPulseChartIndex α q Λ m k)) (fun t'' x'' => ∑ j', cf j' t'' • φ j' x'') t'
            x') t x v) (φt x)) +
          (∑ k ∈ ocObsPulses α q Λ m tA tZ, deriv (fun s => F.weight (pp k) s) t * (∫ x in
            unitCube, inner ℝ (obsLift α q Λ m (Φ (m - 1)) hφs ν B ρ Cc N H cf φ k t x v) (φt
            x))))) := by
  classical
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of hν he
  have hc : ocEll q Λ m ν ^ 2 ≠ 0 := pow_ne_zero 2 hℓ
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have hvel := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφs
  have hsq := ocEll_sq_mul (q := q) (Λ := Λ) (m := m) hν
  have hlam : ρ / E * ρ⁻¹ = E⁻¹ := by
    rw [div_mul_eq_mul_div, mul_inv_cancel₀ hρ.ne', one_div]
  have hee : ocEpsilon q Λ m * (ocEpsilon q Λ m / ν) = ocEll q Λ m ν ^ 2 := by
    rw [← mul_div_assoc, ← sq, ← hsq, mul_div_assoc, div_self hν.ne', mul_one]
  have hsc : (ocEll q Λ m ν ^ 2)⁻¹ * (ocEpsilon q Λ m * (ocEpsilon q Λ m / ν)) = 1 := by
    rw [hee, inv_mul_cancel₀ hc]
  have hpw := glued_pulses_weak hseqΦ hm hΛ hζ hφs hν hB hρ (fun k => F.fiber (pp k) (actual (pp
    k))) htAZ
    (fun k => F.weight (pp k)) hpart P sX sZ hsX hsZ Cc hseq cf dcf φ hφ hφp A₀ B₀ hA hB₀ hcf hcs v
    φt hφt hφtp
  refine hpw.congr htAZ (fun t _ => rfl) (fun t ht => ?_)
  -- the glued edge, tail and mean terms at the time `t`
  have hE := glued_edges hΛ hζ hφs hν hB hρ F actual K hdesc htorus T hTcons hTcov hTq hTact pp
    hpp hppinj hpart hcov P sX sZ (by omega) Cc hseq cf φ hφ hφp hcs ht v hφt hφtp
  have hT := glued_tail hΛ hφs hν hρ (fun k => F.fiber (pp k) (actual (pp k)))
    (fun k => F.weight (pp k)) hpart P sX sZ hsX hsZ Cc hseq sXc sZc Acl hAcl hXc hZc hX hZ cf φ
    hφ hφp hcs Vc hV ht v φt hφt hφtp
  have hM := fun x => glued_meanPart hΛ hφs hν hρ (fun k => F.fiber (pp k) (actual (pp k)))
    (fun k => F.weight (pp k)) hpart P sX sZ hsX hsZ Cc hseq cf dcf φ hφ ht (hagree t ht)
    (hMr t ht) x
  -- continuity of the parts of the rests of the weighted pulses
  have hparts : ∀ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t ≠ 0 →
      Continuous (fun x => restSource (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k
        (F.fiber (pp k) (actual (pp k)))) (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartField cf φ
        (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ) ρ
        (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs
        (ocPulseChartIndex α q Λ m k) t x) v) ∧
      Continuous (fun x => (restMean (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k
        (F.fiber (pp k) (actual (pp k)))) (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartField cf φ
        (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ) ρ
        (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs
        (ocPulseChartIndex α q Λ m k) t x) +
        labelLift (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartFieldDot cf dcf φ (ocChart α q Λ m (Φ (m
          - 1)) hφs (ocPulseChartIndex α q Λ m k)) (streamVel (Φ (m - 1))) (ocEll q Λ m ν ^ 2) ρ) ρ
          (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs
          (ocPulseChartIndex α q Λ m k) t x)) v) ∧
      Continuous (fun x => restTail (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k
        (F.fiber (pp k) (actual (pp k)))) (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartField cf φ
        (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ) ρ
        (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs
        (ocPulseChartIndex α q Λ m k) t x) v) := by
    intro k hk hw
    have hwin : t ∈ ocPulseWindow α q Λ m k := hpart.2.2.2.1 k hk t hw
    have hwin' : ((k : ℝ) - 61 / 48) * ocTau α q Λ m ≤ t ∧
        t ≤ ((k : ℝ) + 61 / 48) * ocTau α q Λ m := hwin
    have hs : (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll
      q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) :=
      ⟨by rw [div_eq_inv_mul]
          exact mul_le_mul_of_nonneg_left (max_le hwin'.1 ht.1) (inv_nonneg.2 hc0.le),
        by rw [div_eq_inv_mul]
           exact mul_le_mul_of_nonneg_left (le_min hwin'.2 ht.2) (inv_nonneg.2 hc0.le)⟩
    have hχj := Charts.contDiff_ocChart_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)
    have hψc : Continuous (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) t) :=
      ((Charts.contDiff_ocChartInv_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)).comp
        (contDiff_const.prodMk contDiff_id)).continuous
    have hf : ContDiff ℝ (⊤ : ℕ∞) (chartField cf φ (ocChart α q Λ m (Φ (m - 1)) hφs
      (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ ((ocEll q Λ m ν ^ 2)⁻¹ * t)) :=
      chartField_contDiff cf φ hφ _ hχj _ ρ _
    have hdf : ContDiff ℝ (N : ℕ∞) (chartFieldDot cf dcf φ (ocChart α q Λ m (Φ (m - 1)) hφs
      (ocPulseChartIndex α q Λ m k)) (streamVel (Φ (m - 1))) (ocEll q Λ m ν ^ 2) ρ ((ocEll q Λ m ν
      ^ 2)⁻¹ * t)) :=
      (chartFieldDot_contDiff cf dcf φ hφ _ _ hχj hvel.smooth _ ρ _).of_le
        (by exact_mod_cast le_top)
    have hscale : Real.sqrt (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp
      k) (actual (pp k)))).η * (ocDStar q Λ m ν B / ρ) = ocEpsilon q Λ m * ρ⁻¹ := by
      rw [mul_comm, pulse_scale_h2 α q Λ m ζ hφs hν hB he ρ (ρ / E) k _, hsq, sq,
        mul_assoc (ocEpsilon q Λ m), mul_inv_cancel₀ he, mul_one]
    refine ⟨?_, ?_, ?_⟩
    · exact (setting_labelSourcePart_continuous (P k hk) F ν (ocEpsilon q Λ m) E (pp k) (actual (pp
      k))
        rfl hc he hν.ne' hscale hlam hsc (by omega) (hseq k hk) _ hf hs v).comp hψc
    · exact (setting_restMean_lift_continuous (P k hk) sX sZ hsX hsZ (Cc k) (hseq k hk) _ _ _ ρ
        (ocEpsilon q Λ m) hs hf hdf v).comp hψc
    · exact (continuous_apply v).comp ((setting_restTail_label_continuous (P k hk) sX sZ hsX hsZ
        (Cc k) (hseq k hk) sXc sZc Acl hAcl hXc hZc hX hZ _ hc hρ.ne' he _ (Vc k) (hV k hk) hs
        hf).comp hψc)
  -- the tested rest of a weighted pulse splits into its three parts
  have hsplit : ∀ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t ≠ 0 →
      ((ocEll q Λ m ν ^ 2)⁻¹ * ∫ x in unitCube, inner ℝ (obsRest α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ
        / E) (fun k => F.fiber (pp k) (actual (pp k))) Cc N H cf dcf φ k t x v) (φt x)) =
      ((ocEll q Λ m ν ^ 2)⁻¹ * ∫ x in unitCube, inner ℝ (restSource (pulseLiftData α q Λ m ζ (Φ (m
        - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual (pp k)))) (Cc k) N H (ocDStar q Λ m ν B /
        ρ) (chartField cf φ (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll
        q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1))
        hφs (ocPulseChartIndex α q Λ m k) t x) v) (φt x)) +
      (∫ x in unitCube, inner ℝ (((ocEll q Λ m ν ^ 2)⁻¹ • (restMean (pulseLiftData α q Λ m ζ (Φ (m
        - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual (pp k)))) (Cc k) N H (ocDStar q Λ m ν B /
        ρ) (chartField cf φ (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll
        q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1))
        hφs (ocPulseChartIndex α q Λ m k) t x) + labelLift (Cc k) N H (ocDStar q Λ m ν B / ρ)
        (chartFieldDot cf dcf φ (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
        (streamVel (Φ (m - 1))) (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t
        (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) t x))) v) (φt x)) +
      ((ocEll q Λ m ν ^ 2)⁻¹ * ∫ x in unitCube, inner ℝ (restTail (pulseLiftData α q Λ m ζ (Φ (m -
        1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual (pp k)))) (Cc k) N H (ocDStar q Λ m ν B /
        ρ) (chartField cf φ (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll
        q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1))
        hφs (ocPulseChartIndex α q Λ m k) t x) v) (φt x)) := by
    intro k hk hw
    obtain ⟨hcS, hcM, hcT⟩ := hparts k hk hw
    have hpt : ∀ x, obsRest α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) (fun k => F.fiber (pp k)
      (actual (pp k))) Cc N H cf dcf φ k t x v =
        restSource (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual
          (pp k)))) (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartField cf φ (ocChart α q Λ m (Φ (m -
          1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll
          q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) t x) v +
        (restMean (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual
          (pp k)))) (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartField cf φ (ocChart α q Λ m (Φ (m -
          1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll
          q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) t x) +
          labelLift (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartFieldDot cf dcf φ (ocChart α q Λ m (Φ
            (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (streamVel (Φ (m - 1))) (ocEll q Λ m ν ^ 2)
            ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs
            (ocPulseChartIndex α q Λ m k) t x)) v +
        restTail (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual
          (pp k)))) (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartField cf φ (ocChart α q Λ m (Φ (m -
          1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll
          q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) t x) v
          := fun x => by
      have h1 := congrFun (labelRest_split (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k
        (F.fiber (pp k) (actual (pp k)))) (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartField cf φ
        (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ)
        (chartFieldDot cf dcf φ (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
          (streamVel (Φ (m - 1))) (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t
          (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) t x)) v
      simp only [Pi.add_apply] at h1 ⊢
      refine h1.trans ?_
      abel
    have hiS := CoupledEnergy.Galerkin.continuous_cell_integrable _ (hcS.inner hφt.continuous)
    have hiM := CoupledEnergy.Galerkin.continuous_cell_integrable _ (hcM.inner hφt.continuous)
    have hiT := CoupledEnergy.Galerkin.continuous_cell_integrable _ (hcT.inner hφt.continuous)
    simp only [hpt, inner_add_left, Pi.smul_apply, real_inner_smul_left]
    rw [integral_add (hiS.fun_add hiM) hiT, integral_add hiS hiM, integral_const_mul]
    ring
  -- the glued mean and material parts
  have hC : ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t * (∫ x in unitCube, inner ℝ (((ocEll
    q Λ m ν ^ 2)⁻¹ • (restMean (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber
    (pp k) (actual (pp k)))) (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartField cf φ (ocChart α q Λ m
    (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m)
    (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) t x) +
    labelLift (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartFieldDot cf dcf φ (ocChart α q Λ m (Φ (m -
    1)) hφs (ocPulseChartIndex α q Λ m k)) (streamVel (Φ (m - 1))) (ocEll q Λ m ν ^ 2) ρ) ρ
    (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex
    α q Λ m k) t x))) v) (φt x)) =
      (∫ x in unitCube, inner ℝ (gluedLift (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k))
        (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H Cc (fun k => ocChart α
        q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun k => ocChartInv α q Λ m (Φ (m -
        1)) hφs (ocPulseChartIndex α q Λ m k)) (fun t' x' => (∑ j, dcf j t' • φ j x' + ∑ j, cf j t'
        • fderiv ℝ (φ j) x' (streamVel (Φ (m - 1)) t' x')) + ∑ r ∈ Finset.range (H + 1), gluedMean
        (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k)) (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m
        ν B / ρ) N r (fun k => pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp
        k) (actual (pp k)))) Cc (fun k => ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ
        m k)) (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun t''
        x'' => ∑ j', cf j' t'' • φ j' x'') t' x') t x v) (φt x)) := by
    have hptC : ∀ x, inner ℝ (gluedLift (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k))
      (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H Cc (fun k => ocChart α q
      Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun k => ocChartInv α q Λ m (Φ (m - 1))
      hφs (ocPulseChartIndex α q Λ m k)) (fun t' x' => (∑ j, dcf j t' • φ j x' + ∑ j, cf j t' •
      fderiv ℝ (φ j) x' (streamVel (Φ (m - 1)) t' x')) + ∑ r ∈ Finset.range (H + 1), gluedMean
      (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k)) (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν
      B / ρ) N r (fun k => pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k)
      (actual (pp k)))) Cc (fun k => ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
      (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun t'' x'' => ∑
      j', cf j' t'' • φ j' x'') t' x') t x v) (φt x) =
        ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t * inner ℝ (((ocEll q Λ m ν ^ 2)⁻¹ •
          (restMean (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k)
            (actual (pp k)))) (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartField cf φ (ocChart α q Λ m
            (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ
            m) (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m
            k) t x) + labelLift (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartFieldDot cf dcf φ (ocChart
            α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (streamVel (Φ (m - 1))) (ocEll q
            Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1))
            hφs (ocPulseChartIndex α q Λ m k) t x))) v) (φt x) := fun x => by
      rw [← hM x]
      simp only [Finset.sum_apply, Pi.smul_apply, sum_inner, real_inner_smul_left]
    simp only [hptC]
    refine (integral_weighted_sum _ (fun k => F.weight (pp k) t)
      (fun k x => inner ℝ (((ocEll q Λ m ν ^ 2)⁻¹ •
        (restMean (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual
          (pp k)))) (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartField cf φ (ocChart α q Λ m (Φ (m -
          1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll
          q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) t x) +
          labelLift (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartFieldDot cf dcf φ (ocChart α q Λ m (Φ
          (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (streamVel (Φ (m - 1))) (ocEll q Λ m ν ^ 2)
          ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs
          (ocPulseChartIndex α q Λ m k) t x))) v) (φt x)) (fun k hk hw => ?_)).symm
    exact CoupledEnergy.Galerkin.continuous_cell_integrable _
      ((((hparts k hk hw).2.1).const_smul (ocEll q Λ m ν ^ 2)⁻¹).inner hφt.continuous)
  -- conclusion
  have hsum : ∑ k ∈ ocObsPulses α q Λ m tA tZ,
      (deriv (fun s => F.weight (pp k) s) t * (∫ x in unitCube, inner ℝ (obsLift α q Λ m (Φ (m -
        1)) hφs ν B ρ Cc N H cf φ k t x v) (φt x)) +
        F.weight (pp k) t * ((ocEll q Λ m ν ^ 2)⁻¹ * ∫ x in unitCube, inner ℝ (obsRest α q Λ m ζ (Φ
          (m - 1)) hφs ν B ρ (ρ / E) (fun k => F.fiber (pp k) (actual (pp k))) Cc N H cf dcf φ k t
          x v) (φt x))) =
      ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t * ((ocEll q Λ m ν ^ 2)⁻¹ * ∫ x in
        unitCube, inner ℝ (restSource (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k
        (F.fiber (pp k) (actual (pp k)))) (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartField cf φ
        (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ) ρ
        (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs
        (ocPulseChartIndex α q Λ m k) t x) v) (φt x)) +
        ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t * ((ocEll q Λ m ν ^ 2)⁻¹ * ∫ x in
          unitCube, inner ℝ (restTail (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k
          (F.fiber (pp k) (actual (pp k)))) (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartField cf φ
          (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ) ρ
          (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs
          (ocPulseChartIndex α q Λ m k) t x) v) (φt x)) +
        ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t * (∫ x in unitCube, inner ℝ (((ocEll q Λ
          m ν ^ 2)⁻¹ • (restMean (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber
          (pp k) (actual (pp k)))) (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartField cf φ (ocChart α q
          Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q
          Λ m) (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m
          k) t x) + labelLift (Cc k) N H (ocDStar q Λ m ν B / ρ) (chartFieldDot cf dcf φ (ocChart α
          q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (streamVel (Φ (m - 1))) (ocEll q Λ m
          ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t (ocChartInv α q Λ m (Φ (m - 1)) hφs
          (ocPulseChartIndex α q Λ m k) t x))) v) (φt x)) +
        (∑ k ∈ ocObsPulses α q Λ m tA tZ, deriv (fun s => F.weight (pp k) s) t * (∫ x in unitCube,
          inner ℝ (obsLift α q Λ m (Φ (m - 1)) hφs ν B ρ Cc N H cf φ k t x v) (φt x))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    by_cases hw : F.weight (pp k) t = 0
    · simp only [hw, zero_mul, zero_add, add_zero]
    · rw [hsplit k hk hw]
      ring
  rw [hE, hT, hC] at hsum
  exact congrArg (fun z => -(∫ x in unitCube, inner ℝ (∑ j, streamVel (Φ m) t x j • fderiv ℝ (fun
    x' => ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t • obsLift α q Λ m (Φ (m - 1)) hφs ν B
    ρ Cc N H cf φ k t x' v) x (basisVec j)) (φt x)) - ν * (∫ x in unitCube, ∑ j, inner ℝ (fderiv ℝ
    (fun x' => ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t • obsLift α q Λ m (Φ (m - 1)) hφs
    ν B ρ Cc N H cf φ k t x' v) x (basisVec j)) (fderiv ℝ φt x (basisVec j))) + z) hsum

end AVRegularity.CycleComparison.Reconstruction
end
