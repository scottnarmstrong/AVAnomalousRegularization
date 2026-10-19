-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.JointSourceCongruence
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! Actual fast-only pulse and slow-only metric fields retain their finite derivative budgets as joint sources. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def fastIndependentJointSourceReserve (H : ℕ) (f : ℝ → Vec 2 → E)
    (hr : ∀ t, ContDiff ℝ (H : ℕ∞) (f t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (f t))
    (hm : Measurable (Function.uncurry f))
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hb : ∀ n ≤ H, ∀ t z, ‖iteratedFDeriv ℝ n (f t) z‖ ≤ B n) :
    JointSourceReserve H (fun t z _ => f t z) where
  regular t := (hr t).comp (contDiff_fst)
  periodic t _ := hp t
  measurable _ := hm
  budget := B
  budget_nonneg := hB
  derivative_bound n hn t X := by
    let L : (Vec 2 × Vec 2) →L[ℝ] Vec 2 := ContinuousLinearMap.fst ℝ (Vec 2) (Vec 2)
    have hL : ‖L‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound L zero_le_one
      intro U
      change ‖U.1‖ ≤ 1 * ‖U‖
      simpa only [one_mul] using norm_fst_le U
    have hh := finite_realWordJet_affine_derivative_bound (f t) 0 n
      ((hr t).of_le (by exact_mod_cast (show 0 + n ≤ H by omega))) Fin.elim0 (fun i => Fin.elim0 i) L hL 0 X
    have he : (fun U => realWordJet (f t) 0 Fin.elim0 (L U + 0)) =
        fun U : Vec 2 × Vec 2 => f t U.1 := by
      funext U
      rw [realWordJet, iteratedFDeriv_zero_apply, add_zero]
      rfl
    rw [he, Nat.zero_add, add_zero] at hh
    exact hh.trans (hb n hn t X.1)

def slowIndependentJointSourceReserve (H : ℕ) (f : ℝ → Vec 2 → E)
    (hr : ∀ t, ContDiff ℝ (H : ℕ∞) (f t))
    (hm : ∀ Y, Measurable (fun t => f t Y))
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hb : ∀ n ≤ H, ∀ t Y, ‖iteratedFDeriv ℝ n (f t) Y‖ ≤ B n) :
    JointSourceReserve H (fun t _ Y => f t Y) where
  regular t := (hr t).comp (contDiff_snd)
  periodic _ _ _ _ := rfl
  measurable Y := (hm Y).comp measurable_fst
  budget := B
  budget_nonneg := hB
  derivative_bound n hn t X := by
    let L : (Vec 2 × Vec 2) →L[ℝ] Vec 2 := ContinuousLinearMap.snd ℝ (Vec 2) (Vec 2)
    have hL : ‖L‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound L zero_le_one
      intro U
      change ‖U.2‖ ≤ 1 * ‖U‖
      simpa only [one_mul] using norm_snd_le U
    have hh := finite_realWordJet_affine_derivative_bound (f t) 0 n
      ((hr t).of_le (by exact_mod_cast (show 0 + n ≤ H by omega))) Fin.elim0 (fun i => Fin.elim0 i) L hL 0 X
    have he : (fun U => realWordJet (f t) 0 Fin.elim0 (L U + 0)) =
        fun U : Vec 2 × Vec 2 => f t U.2 := by
      funext U
      rw [realWordJet, iteratedFDeriv_zero_apply, add_zero]
      rfl
    rw [he, Nat.zero_add, add_zero] at hh
    exact hh.trans (hb n hn t X.2)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Filter Topology
namespace AVRegularity.EntryWeakProofs

/-! Uniform genuine local models give a global source reserve without choosing models continuously. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

def jointSourceReserveOfLocalModels (H : ℕ) (f : ℝ → Vec 2 → Vec 2 → E)
    (g : Vec 2 → ℝ → Vec 2 → Vec 2 → E)
    (Q : ∀ Y, JointSourceReserve H (g Y)) (B : ℝ) (hB : 0 ≤ B)
    (hbudget : ∀ Y n, n ≤ H → (Q Y).budget n ≤ B)
    (hpoint : ∀ Y t z, f t z Y = g Y t z Y)
    (hgerm : ∀ Y t z, (fun X : Vec 2 × Vec 2 => f t X.1 X.2) =ᶠ[𝓝 (z, Y)]
      (fun X : Vec 2 × Vec 2 => g Y t X.1 X.2)) : JointSourceReserve H f where
  regular t := contDiff_iff_contDiffAt.mpr fun X =>
    ((Q X.2).regular t).contDiffAt.congr_of_eventuallyEq (hgerm X.2 t X.1)
  periodic t Y := by
    have he : (fun z => f t z Y) = fun z => g Y t z Y := funext (hpoint Y t)
    rw [he]
    exact (Q Y).periodic t Y
  measurable Y := by
    have he : (fun a : ℝ × Vec 2 => f a.1 a.2 Y) = fun a => g Y a.1 a.2 Y :=
      funext fun a => hpoint Y a.1 a.2
    rw [he]
    exact (Q Y).measurable Y
  budget _ := B
  budget_nonneg _ := hB
  derivative_bound n hn t X := by
    rw [((hgerm X.2 t X.1).iteratedFDeriv ℝ n).eq_of_nhds]
    exact ((Q X.2).derivative_bound n hn t X).trans (hbudget X.2 n hn)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! Genuine finite source reserves are preserved by the literal linear forcing operations. -/

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

def JointSourceReserve.map {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (L : E →L[ℝ] F) :
    JointSourceReserve H (fun t z Y => L (f t z Y)) where
  regular t := L.contDiff.comp (Q.regular t)
  periodic t Y n z := congrArg L (Q.periodic t Y n z)
  measurable Y := L.continuous.measurable.comp (Q.measurable Y)
  budget n := ‖L‖ * Q.budget n
  budget_nonneg n := mul_nonneg (norm_nonneg L) (Q.budget_nonneg n)
  derivative_bound n hn t X := by
    have hb := L.norm_iteratedFDeriv_comp_left (Q.regular t).contDiffAt
      (by exact_mod_cast hn) (x := X)
    exact hb.trans (mul_le_mul_of_nonneg_left (Q.derivative_bound n hn t X) (norm_nonneg L))

def JointSourceReserve.add {H : ℕ} {f g : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (R : JointSourceReserve H g) :
    JointSourceReserve H (fun t z Y => f t z Y + g t z Y) where
  regular t := (Q.regular t).add (R.regular t)
  periodic t Y n z := congrArg₂ (fun x y : E => x + y)
    (Q.periodic t Y n z) (R.periodic t Y n z)
  measurable Y := (Q.measurable Y).add (R.measurable Y)
  budget n := Q.budget n + R.budget n
  budget_nonneg n := add_nonneg (Q.budget_nonneg n) (R.budget_nonneg n)
  derivative_bound n hn t X := by
    change ‖iteratedFDeriv ℝ n
      ((fun U : Vec 2 × Vec 2 => f t U.1 U.2) + (fun U : Vec 2 × Vec 2 => g t U.1 U.2)) X‖ ≤ _
    rw [iteratedFDeriv_add_apply ((Q.regular t).contDiffAt.of_le (by exact_mod_cast hn))
      ((R.regular t).contDiffAt.of_le (by exact_mod_cast hn))]
    exact (norm_add_le _ _).trans (add_le_add
      (Q.derivative_bound n hn t X) (R.derivative_bound n hn t X))

def JointSourceReserve.mono {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (H' : ℕ) (hH : H' ≤ H) : JointSourceReserve H' f where
  regular t := (Q.regular t).of_le (by exact_mod_cast hH)
  periodic := Q.periodic
  measurable := Q.measurable
  budget := Q.budget
  budget_nonneg := Q.budget_nonneg
  derivative_bound n hn := Q.derivative_bound n (hn.trans hH)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The same genuine joint source budget controls the slow slices used by the parameter inverse. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]

theorem JointSourceReserve.slow_derivative_bound {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (n : ℕ) (hn : n ≤ H) (t : ℝ) (z Y : Vec 2) :
    ‖iteratedFDeriv ℝ n (f t z) Y‖ ≤ Q.budget n := by
  let L := ContinuousLinearMap.inr ℝ (Vec 2) (Vec 2)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp only [L, ContinuousLinearMap.inr_apply, Prod.norm_def, norm_zero,
      max_eq_right (norm_nonneg x), one_mul]
    exact le_rfl
  have hb := finite_realWordJet_affine_derivative_bound
    (fun X : Vec 2 × Vec 2 => f t X.1 X.2) 0 n
    ((Q.regular t).of_le (by exact_mod_cast (show 0 + n ≤ H by omega))) Fin.elim0 (fun i => Fin.elim0 i)
    L hL (z, 0) Y
  have he : (fun x => realWordJet (fun X : Vec 2 × Vec 2 => f t X.1 X.2)
      0 Fin.elim0 (L x + (z, 0))) = f t z := by
    funext x
    rw [realWordJet, iteratedFDeriv_zero_apply]
    simp only [L, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero]
  rw [he] at hb
  have hx : L Y + (z, 0) = (z, Y) := by
    simp only [L, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero]
  rw [zero_add, hx] at hb
  exact hb.trans (Q.derivative_bound n hn t (z, Y))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open scoped Matrix Matrix.Norms.Elementwise
namespace AVRegularity.EntryWeakProofs

/-! Each planar matrix entry inherits the genuine full mixed matrix norm bound. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem matrix_entry_derivative_norm_le (F : P → Matrix (Fin 2) (Fin 2) ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (n : ℕ) (Y : P) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun Z => F Z i j) Y‖ ≤ ‖iteratedFDeriv ℝ n F Y‖ := by
  let L : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] (Fin 2 → ℝ))
  have he := L.iteratedFDeriv_comp_left (hF.contDiffAt (x := Y)) (i := n) (by simp)
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro w
  have hev := congrArg (fun G => G w) he
  change iteratedFDeriv ℝ n (fun Z => F Z i j) Y w = (iteratedFDeriv ℝ n F Y w) i j at hev
  rw [hev]
  exact ((norm_le_pi_norm (iteratedFDeriv ℝ n F Y w i) j).trans
    (norm_le_pi_norm (iteratedFDeriv ℝ n F Y w) i)).trans
    ((iteratedFDeriv ℝ n F Y).le_opNorm w)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Fixed L² Fourier readouts, independent of choices of higher Sobolev representatives. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Heat AVenhance.Infra.Torus
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.Analysis.Convolution

local instance sobolevCellFourierMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance sobolevCellFourierAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance sobolevCellFourierProbTorus : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVRegularity.EntryWeakProofs

def torusFourierCoeffCLM (k : Frequency) : TorusL2 2 →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : Frequency => ℂ) 2 k).comp
    UnitAddTorus.mFourierBasis.repr.toLinearIsometry.toContinuousLinearMap

def cellFourierCoeffCLM (k : Frequency) :
    Lp ℂ 2 (volume.restrict AVenhance.unitCube) →L[ℝ] ℂ :=
  let L : TorusL2 2 →L[ℝ] ℂ := (torusFourierCoeffCLM k).restrictScalars ℝ
  let J : Lp ℂ 2 (volume.restrict AVenhance.unitCube) →L[ℝ] TorusL2 2 :=
    cellToTorus.toContinuousLinearMap
  L.comp J

theorem cellFourierCoeffCLM_apply (k : Frequency)
    (u : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) :
    cellFourierCoeffCLM k u = UnitAddTorus.mFourierCoeff (cellToTorus u) k := by
  change UnitAddTorus.mFourierBasis.repr (cellToTorus u) k = _
  exact UnitAddTorus.mFourierBasis_repr _ _

def complexifyCellClass : Lp ℝ 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
    Lp ℂ 2 (volume.restrict AVenhance.unitCube) :=
  Complex.ofRealCLM.compLpL 2 (volume.restrict AVenhance.unitCube)

theorem realJet_torusClass (K : ℕ) (f : TorusHk K ℝ) (a : JetIndex2 K) :
    frozenCellToTorusL2 (f.toFunction.hasPeriodicWeakJet.2.1 a) =
      cellToTorus (complexifyCellClass (f.val a)) := by
  apply Lp.ext
  have ht := (memLp_frozenCellTransfer (f.toFunction.hasPeriodicWeakJet.2.1 a)).coeFn_toLp
  have hcast := ContinuousLinearMap.coeFn_compLpL (L := Complex.ofRealCLM) (f.val a)
  have hr := (periodicJetRepresentative_ae f.val a).fun_comp Complex.ofReal
  have he := measurePreserving_unitTorusRepresentative_cell.quasiMeasurePreserving.ae
    (hr.trans hcast.symm)
  rw [coupledEnergy_torusMeasure_eq_volume] at he
  have hc := cellToTorus_ae (complexifyCellClass (f.val a))
  change (cellToTorus (complexifyCellClass (f.val a)) : UnitAddTorus (Fin 2) → ℂ) =ᵐ[volume]
    periodicToTorus (complexifyCellClass (f.val a)) at hc
  filter_upwards [ht, he, hc] with y hy hz hw
  exact hy.trans (hz.trans hw.symm)

theorem realJetFourier_eq_cellCoeff (K : ℕ) (f : TorusHk K ℝ) (a : JetIndex2 K) (k : Frequency) :
    realJetFourier K f a k = cellFourierCoeffCLM k (complexifyCellClass (f.val a)) := by
  rw [cellFourierCoeffCLM_apply]
  change UnitAddTorus.mFourierBasis.repr _ k = _
  rw [UnitAddTorus.mFourierBasis_repr, realJet_torusClass]
  rfl

end AVRegularity.EntryWeakProofs
end
end
