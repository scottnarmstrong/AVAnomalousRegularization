-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.JointSourceDiagonalSample
import AVRegularity.EntryWeak.MolecularUlFluxNormBound

section
section
/-! Genuine independent-parameter source jets restrict to the planar production API at no extra cost. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

structure IndependentParameterSourceReserve (H : ℕ) (f : ℝ → Vec 2 → P → E) where
  regular : ∀ t, ContDiff ℝ (H : ℕ∞) (fun X : Vec 2 × P => f t X.1 X.2)
  periodic : ∀ t Y, AVenhance.IsZ2Periodic (fun z => f t z Y)
  measurable : ∀ Y, Measurable (fun a : ℝ × Vec 2 => f a.1 a.2 Y)
  budget : ℕ → ℝ
  budget_nonneg : ∀ n, 0 ≤ budget n
  derivative_bound : ∀ n, n ≤ H → ∀ t X,
    ‖iteratedFDeriv ℝ n (fun X : Vec 2 × P => f t X.1 X.2) X‖ ≤ budget n

def IndependentParameterSourceReserve.affineSlice {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (a : P) :
    JointSourceReserve H (fun t z Y => f t z (L Y + a)) := by
  let T : (Vec 2 × Vec 2) →L[ℝ] (Vec 2 × P) :=
    (ContinuousLinearMap.id ℝ (Vec 2)).prodMap L
  have hT : ‖T‖ ≤ 1 := by
    apply T.opNorm_le_bound zero_le_one
    intro X
    change ‖(X.1, L X.2)‖ ≤ 1 * ‖X‖
    rw [one_mul, Prod.norm_def, Prod.norm_def]
    apply max_le
    · exact le_max_left _ _
    · exact (L.le_opNorm X.2).trans
        (((mul_le_mul_of_nonneg_right hL (norm_nonneg X.2)).trans_eq (one_mul _)).trans
          (le_max_right _ _))
  refine ⟨?_, fun t Y => Q.periodic t (L Y + a),
    fun Y => Q.measurable (L Y + a), Q.budget, Q.budget_nonneg, ?_⟩
  · intro t
    have hh := (Q.regular t).comp
      (T.contDiff.add (contDiff_const (c := (0, a))))
    change ContDiff ℝ (H : ℕ∞) (fun X : Vec 2 × Vec 2 => f t (X.1 + 0) (L X.2 + a)) at hh
    simpa only [add_zero] using hh
  · intro n hn t X
    have hh := (finite_affine_derivative_norm_le
      (fun Z : Vec 2 × P => f t Z.1 Z.2) n
      ((Q.regular t).of_le (by exact_mod_cast hn)) T hT (0, a) X).trans
      (Q.derivative_bound n hn t (T X + (0, a)))
    change ‖iteratedFDeriv ℝ n
      (fun Y : Vec 2 × Vec 2 => f t (Y.1 + 0) (L Y.2 + a)) X‖ ≤ Q.budget n at hh
    simpa only [add_zero] using hh

end AVRegularity.EntryWeakProofs
end
end

section
/-! Phase lattice equivalence preserves every finite real-chain geometry literally. -/
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.EntryWeakProofs

def childPhaseLatticeEquivalent (c d : ChainChild) : Prop :=
  c.center = d.center ∧ ∃ n : Fin 2 → ℤ, c.phase = d.phase + latticeShift n

theorem geomAux_phase_lattice_congr (D : OCData) (hΛ : 1 ≤ D.Λ)
    (cs ds : List ChainChild) (hcs : List.Forall₂ childPhaseLatticeEquivalent cs ds)
    (k : ℕ) (slots : List ℤ) (hp : ∀ p ∈ slots, Odd p) (g : ChainGeom) :
    D.geomAux k slots cs g = D.geomAux k slots ds g := by
  induction hcs generalizing k slots g with
  | nil => rfl
  | @cons c d cs ds hcd htail ih =>
    rcases hcd with ⟨hc, n, hn⟩
    cases slots with
    | nil => rfl
    | cons p slots =>
      cases slots with
      | nil => rfl
      | cons p' rest =>
        change D.geomAux (k + 1) (p' :: rest) cs (D.childGeom k p (D.slotAnchor (k + 1) p') c g) =
          D.geomAux (k + 1) (p' :: rest) ds (D.childGeom k p (D.slotAnchor (k + 1) p') d g)
        rw [childGeom_eq_of_phase_lattice D hΛ k p (hp p List.mem_cons_self) _ c d g hc n hn]
        exact ih (k + 1) (p' :: rest) (fun q hq => hp q (List.mem_cons_of_mem _ hq)) _

theorem realChain_geom_eq_of_phase_lattice (D : OCData) (hΛ : 1 ≤ D.Λ)
    (A B : RealChain) (hlevel : A.baseLevel = B.baseLevel) (hslots : A.slots = B.slots)
    (hbase : A.base = B.base) (hp : ∀ p ∈ B.slots, Odd p)
    (hchildren : List.Forall₂ childPhaseLatticeEquivalent A.children B.children) :
    A.geom D = B.geom D := by
  unfold RealChain.geom
  rw [hlevel, hslots, hbase]
  exact geomAux_phase_lattice_congr D hΛ A.children B.children hchildren _ _ hp _

end AVRegularity.EntryWeakProofs
end
end

section
/-! A genuine fast-only source retains its full derivative price for any independent family space. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

def independentFastOnlySourceReserve (H : ℕ) (f : ℝ → Vec 2 → E)
    (hr : ∀ t, ContDiff ℝ (H : ℕ∞) (f t)) (hp : ∀ t, AVenhance.IsZ2Periodic (f t))
    (hm : Measurable (Function.uncurry f)) (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hb : ∀ n ≤ H, ∀ t z, ‖iteratedFDeriv ℝ n (f t) z‖ ≤ B n) :
    IndependentParameterSourceReserve H (fun t z (_ : P) => f t z) where
  regular t := (hr t).comp contDiff_fst
  periodic t _ := hp t
  measurable _ := hm
  budget := B
  budget_nonneg := hB
  derivative_bound n hn t X := by
    let L : (Vec 2 × P) →L[ℝ] Vec 2 := ContinuousLinearMap.fst ℝ _ _
    have hL : ‖L‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro Y
      change ‖Y.1‖ ≤ 1 * ‖Y‖
      simpa only [one_mul] using norm_fst_le Y
    have hh := finite_affine_derivative_norm_le (f t) n ((hr t).of_le (by exact_mod_cast hn)) L hL 0 X
    simp only [add_zero] at hh
    exact hh.trans (hb n hn t X.1)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Literal forcing identities preserve every numeric entry of the source reserve. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def IndependentParameterSourceReserve.congrSource {H : ℕ} {f g : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (he : f = g) : IndependentParameterSourceReserve H g := he ▸ Q

omit [BorelSpace E] [SecondCountableTopology E] in
theorem IndependentParameterSourceReserve.congrSource_budget {H : ℕ} {f g : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (he : f = g) (n : ℕ) :
    (Q.congrSource he).budget n = Q.budget n := by
  subst g
  rfl

end AVRegularity.EntryWeakProofs
end
end

section
/-! Constant initial tests carry exactly the diagonal grade-zero weight. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def IndependentParameterSourceReserve.const (H : ℕ) (c : E) :
    IndependentParameterSourceReserve H (fun (_ : ℝ) (_ : Vec 2) (_ : P) => c) where
  regular _ := contDiff_const
  periodic _ _ _ _ := rfl
  measurable _ := measurable_const
  budget n := if n = 0 then ‖c‖ else 0
  budget_nonneg n := by
    by_cases hn : n = 0
    · rw [ite_eq_left hn]
      exact norm_nonneg _
    · rw [ite_eq_right hn]
  derivative_bound n _ _ X := by
    by_cases hn : n = 0
    · subst n
      simp only [norm_iteratedFDeriv_zero, ite_true, le_refl]
    · rw [iteratedFDeriv_const_of_ne hn]
      simp only [Pi.zero_apply, norm_zero, ite_eq_right hn, le_refl]

omit [BorelSpace E] [SecondCountableTopology E] in
theorem IndependentParameterSourceReserve.const_budget_le (H : ℕ) (c : E) (r : ℕ) :
    (IndependentParameterSourceReserve.const (P := P) H c).budget r ≤ ‖c‖ := by
  change (if r = 0 then ‖c‖ else 0) ≤ ‖c‖
  split_ifs
  · exact le_refl _
  · exact norm_nonneg _

end AVRegularity.EntryWeakProofs
end
end

section
/-! A fixed fast sample preserves the entire independent parameter reserve and its budget. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

def IndependentParameterSourceReserve.freezeFast {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (z : Vec 2) :
    IndependentParameterSourceReserve H (fun t _ Y => f t z Y) := by
  let T : (Vec 2 × P) →L[ℝ] (Vec 2 × P) :=
    (0 : Vec 2 →L[ℝ] Vec 2).prodMap (ContinuousLinearMap.id ℝ P)
  have hT : ‖T‖ ≤ 1 := by
    apply T.opNorm_le_bound zero_le_one
    intro X
    change ‖((0 : Vec 2), X.2)‖ ≤ 1 * ‖X‖
    rw [one_mul, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), Prod.norm_def]
    exact le_max_right _ _
  refine ⟨?_, fun _ _ _ _ => rfl, ?_, Q.budget, Q.budget_nonneg, ?_⟩
  · intro t
    have hh := (Q.regular t).comp (T.contDiff.add (contDiff_const (c := (z, (0 : P)))))
    change ContDiff ℝ (H : ℕ∞) (fun X : Vec 2 × P => f t (0 + z) (X.2 + 0)) at hh
    simpa only [zero_add, add_zero] using hh
  · intro Y
    exact (Q.measurable Y).comp (measurable_fst.prodMk measurable_const)
  · intro n hn t X
    have hh := (finite_affine_derivative_norm_le (fun Z : Vec 2 × P => f t Z.1 Z.2) n
      ((Q.regular t).of_le (by exact_mod_cast hn)) T hT (z, 0) X).trans
      (Q.derivative_bound n hn t (T X + (z, 0)))
    change ‖iteratedFDeriv ℝ n (fun Z : Vec 2 × P => f t (0 + z) (Z.2 + 0)) X‖ ≤ Q.budget n at hh
    simpa only [zero_add, add_zero] using hh

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine finite source reserves are preserved by the literal linear forcing operations. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

def IndependentParameterSourceReserve.map {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (L : E →L[ℝ] F) :
    IndependentParameterSourceReserve H (fun t z Y => L (f t z Y)) where
  regular t := L.contDiff.comp (Q.regular t)
  periodic t Y n z := congrArg L (Q.periodic t Y n z)
  measurable Y := L.continuous.measurable.comp (Q.measurable Y)
  budget n := ‖L‖ * Q.budget n
  budget_nonneg n := mul_nonneg (norm_nonneg L) (Q.budget_nonneg n)
  derivative_bound n hn t X := by
    have hb := L.norm_iteratedFDeriv_comp_left (Q.regular t).contDiffAt
      (by exact_mod_cast hn) (x := X)
    exact hb.trans (mul_le_mul_of_nonneg_left (Q.derivative_bound n hn t X) (norm_nonneg L))

def IndependentParameterSourceReserve.add {H : ℕ} {f g : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (R : IndependentParameterSourceReserve H g) :
    IndependentParameterSourceReserve H (fun t z Y => f t z Y + g t z Y) where
  regular t := (Q.regular t).add (R.regular t)
  periodic t Y n z := congrArg₂ (fun x y : E => x + y)
    (Q.periodic t Y n z) (R.periodic t Y n z)
  measurable Y := (Q.measurable Y).add (R.measurable Y)
  budget n := Q.budget n + R.budget n
  budget_nonneg n := add_nonneg (Q.budget_nonneg n) (R.budget_nonneg n)
  derivative_bound n hn t X := by
    change ‖iteratedFDeriv ℝ n
      ((fun U : Vec 2 × P => f t U.1 U.2) + (fun U : Vec 2 × P => g t U.1 U.2)) X‖ ≤ _
    rw [iteratedFDeriv_add_apply ((Q.regular t).contDiffAt.of_le (by exact_mod_cast hn))
      ((R.regular t).contDiffAt.of_le (by exact_mod_cast hn))]
    exact (norm_add_le _ _).trans (add_le_add
      (Q.derivative_bound n hn t X) (R.derivative_bound n hn t X))

end AVRegularity.EntryWeakProofs
end
end

section
/-! Fixed physical dimensions and source amplitudes preserve full independent reserves linearly. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def IndependentParameterSourceReserve.constSmul {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (c : ℝ) :
    IndependentParameterSourceReserve H (fun t z Y => c • f t z Y) where
  regular t := (Q.regular t).const_smul c
  periodic t Y k z := congrArg (fun v : E => c • v) (Q.periodic t Y k z)
  measurable Y := measurable_const.smul (Q.measurable Y)
  budget n := |c| * Q.budget n
  budget_nonneg n := mul_nonneg (abs_nonneg c) (Q.budget_nonneg n)
  derivative_bound n hn t X := by
    have hf : ContDiff ℝ (n : ℕ∞) (fun Z : Vec 2 × P => f t Z.1 Z.2) :=
      (Q.regular t).of_le (by exact_mod_cast hn)
    rw [iteratedFDeriv_const_smul_apply' hf.contDiffAt, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (Q.derivative_bound n hn t X) (abs_nonneg c)

theorem IndependentParameterSourceReserve.constSmul_budget {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (c : ℝ) (n : ℕ) :
    (Q.constSmul c).budget n = |c| * Q.budget n := rfl

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual regular molecular traces retain uniform higher bounds with divergence forcing. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational AVenhance.Infra.ODE

namespace AVRegularity.EntryWeakProofs

theorem dataRegular_flux_exists_uniform {a b : ℝ} (hlt : a < b)
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ} {initial : ComplexCellL2}
    {flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (hsm : Measurable (Function.uncurry src))
    (hfm : Measurable (Function.uncurry flux))
    (hsp : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hfp : MemLp (Function.uncurry flux) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hdiv : IsCellDrift P.v) (hm : cellMean initial = 0)
    (hsrc : ∀ᵐ t ∂volume.restrict (Icc a b), cellMean (cellSourceSlice src t) = 0)
    (K : ℕ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (S : ℝ → TorusHk K ℂ) (hs : ∀ᵐ t ∂volume.restrict (Icc a b),
      (S t).val (valueIndex2 K) = cellSourceSlice src t)
    (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hf : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
        2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)) =
          cellSourceSlice (fun s x => flux s x j) t)
    (u₀ : TorusHk K ℂ) (hinit : initial = torusHkValueCLM u₀)
    (hsmall : (∑ j : Fin (K + 1), factorialRootWeight 1 j.val *
      finiteTransportBudget (E := ℂ) K Cv j) ≤ 1 / 8)
    (B : ℝ) (hB : 0 ≤ B)
    (hshort : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → t - s ≤ 1 →
      (∫ r in s..t, 4 * (factorialNormSq 1 (S r).val + factorialNormSq 1 (F r).val)) ≤ B) :
    ∃ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      Continuous u ∧ CellWeakHilbertCurve a b u slice
        (fun t => dataDualDerivative P t (slice t) (cellSourceSlice src t)
          (fun j => cellSourceSlice (fun s x => flux s x j) t)) ∧
      u a = initial ∧
      (∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ, torusHkValueCLM w = u t ∧
        ‖w‖ ≤ Real.sqrt ((factorialNormSq 1 u₀.val +
          B / (1 - Real.exp (-(1 / 2))) + B) / factorialWeightMin 1 K)) := by
  have hab := hlt.le
  obtain ⟨D⟩ := dataGalerkin_limit_data hab P src flux hsm hfm
    (cellProduct_cellNormSq_finite (Icc a b) src hsp)
    (cellProduct_cellNormSq_finite (Icc a b) flux hfp) initial
  obtain ⟨U, hU, hi⟩ := D.exists_continuous_trace hlt hsp hfp
  let u := extendCurve hab U
  refine ⟨u, D.limit, continuous_extendCurve hab U, hU, hi, ?_⟩
  exact D.higher_flux_trace_uniform_bound hsp hfp K _
    (D.uniform_ul_flux_norm_bound hdiv hm hsrc K Cv hCv hv hp hb S hs F hS hF hf
      u₀ hinit hsmall B hB hshort) u hU hi

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine independent source reserves extend from a measurable time window with their budgets unchanged. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped Classical
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def independentTimeWindowSource (I : Set ℝ) (f : ℝ → Vec 2 → P → E)
    (t : ℝ) (z : Vec 2) (Y : P) : E := if t ∈ I then f t z Y else 0

def windowIndependentSourceReserve (H : ℕ) (I : Set ℝ) (hI : MeasurableSet I)
    (f : ℝ → Vec 2 → P → E)
    (hr : ∀ t ∈ I, ContDiff ℝ (H : ℕ∞) (fun X : Vec 2 × P => f t X.1 X.2))
    (hp : ∀ t ∈ I, ∀ Y, AVenhance.IsZ2Periodic (fun z => f t z Y))
    (hm : ∀ Y, Measurable (fun X : ℝ × Vec 2 => f X.1 X.2 Y))
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hb : ∀ n, n ≤ H → ∀ t ∈ I, ∀ X : Vec 2 × P,
      ‖iteratedFDeriv ℝ n (fun U : Vec 2 × P => f t U.1 U.2) X‖ ≤ B n) :
    IndependentParameterSourceReserve H (independentTimeWindowSource I f) where
  regular t := by
    by_cases ht : t ∈ I
    · simpa only [independentTimeWindowSource, ite_eq_left ht] using hr t ht
    · simpa only [independentTimeWindowSource, ite_eq_right ht] using
        (contDiff_const : ContDiff ℝ (H : ℕ∞) (fun _ : Vec 2 × P => (0 : E)))
  periodic t Y := by
    by_cases ht : t ∈ I
    · simpa only [independentTimeWindowSource, ite_eq_left ht] using hp t ht Y
    · intro v z
      simp only [independentTimeWindowSource, ite_eq_right ht]
  measurable Y := by
    exact (hm Y).ite (hI.preimage measurable_fst) measurable_const
  budget := B
  budget_nonneg := hB
  derivative_bound n hn t X := by
    by_cases ht : t ∈ I
    · simpa only [independentTimeWindowSource, ite_eq_left ht] using hb n hn t ht X
    · simpa only [independentTimeWindowSource, ite_eq_right ht, iteratedFDeriv_fun_zero,
        Pi.zero_apply, norm_zero] using hB n

end AVRegularity.EntryWeakProofs
end
end

section
/-! Independent slow word jets preserve genuine mixed source reserves. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem independent_parameter_word_eq_joint_word (f : Vec 2 → P → E) (n : ℕ)
    (hf : ContDiff ℝ (n : ℕ∞) (fun Z : Vec 2 × P => f Z.1 Z.2))
    (w : Fin n → P) (z : Vec 2) (Y : P) :
    realWordJet (f z) n w Y =
      realWordJet (fun Z : Vec 2 × P => f Z.1 Z.2) n (fun i => (0, w i)) (z, Y) := by
  have hh := finite_realWordJet_affine_eq
    (fun Z : Vec 2 × P => f Z.1 Z.2) n hf
    (ContinuousLinearMap.inr ℝ (Vec 2) P) (z, 0) w Y
  simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero] using hh

def IndependentParameterSourceReserve.wordJet {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (n R : ℕ) (hR : n + R ≤ H)
    (w : Fin n → P) (hw : ∀ i, ‖w i‖ ≤ 1) :
    IndependentParameterSourceReserve R (fun t z Y => realWordJet (f t z) n w Y) := by
  have he (t : ℝ) : (fun Z : Vec 2 × P => realWordJet (f t Z.1) n w Z.2) =
      realWordJet (fun Z : Vec 2 × P => f t Z.1 Z.2) n (fun i => (0, w i)) := by
    funext Z
    exact independent_parameter_word_eq_joint_word (f t) n
      ((Q.regular t).of_le (by exact_mod_cast (show n ≤ H by omega))) w Z.1 Z.2
  refine ⟨?_, ?_, ?_, fun r => Q.budget (n + r), fun r => Q.budget_nonneg _, ?_⟩
  · intro t
    rw [he]
    exact finite_realWordJet_contDiff _ n R
      ((Q.regular t).of_le (by exact_mod_cast hR)) _
  · intro t Y k z
    have hf : f t (z + AVenhance.latticeShift k) = f t z := by
      funext X
      exact Q.periodic t X k z
    dsimp only
    rw [hf]
  · intro Y
    apply finite_independentParameterWordJet_measurable (fun a : ℝ × Vec 2 => f a.1 a.2) n
    · intro a
      exact ((Q.regular a.1).of_le
        (by exact_mod_cast (show n ≤ H by omega))).comp₂ contDiff_const contDiff_id
    · exact Q.measurable
  · intro r hr t Z
    rw [he]
    exact (finite_realWordJet_derivative_bound _ n r
      ((Q.regular t).of_le (by exact_mod_cast (show n + r ≤ H by omega))) _
      (fun i => by simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using hw i) Z).trans
      (Q.derivative_bound _ (by omega) t Z)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Scalar coordinates of a produced vector keep its exact reserve budget. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {d H : ℕ}

def IndependentParameterSourceReserve.coordinate {f : ℝ → Vec 2 → P → Vec d}
    (Q : IndependentParameterSourceReserve H f) (a : Fin d) :
    IndependentParameterSourceReserve H (fun t z Y => f t z Y a) := by
  let L : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj a
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro Y
    exact (norm_le_pi_norm Y a).trans_eq (one_mul _).symm
  let R := Q.map L
  exact { R with
    budget := Q.budget
    budget_nonneg := Q.budget_nonneg
    derivative_bound := fun n hn t X => (R.derivative_bound n hn t X).trans
      (mul_le_of_le_one_left (Q.budget_nonneg n) hL) }

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine fast directional words spend only their actual finite joint derivative reserve. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def independentSourceFastWord (f : ℝ → Vec 2 → P → E) (n : ℕ) (w : Fin n → Vec 2)
    (t : ℝ) (z : Vec 2) (Y : P) : E := realWordJet (fun x => f t x Y) n w z

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem independentSourceFastWord_eq_jointWord (f : ℝ → Vec 2 → P → E) (n : ℕ)
    (hf : ∀ t, ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 × P => f t X.1 X.2))
    (w : Fin n → Vec 2) (t : ℝ) (X : Vec 2 × P) :
    independentSourceFastWord f n w t X.1 X.2 =
      realWordJet (fun U : Vec 2 × P => f t U.1 U.2) n (fun i => (w i, 0)) X := by
  have he := finite_realWordJet_affine_eq (fun U : Vec 2 × P => f t U.1 U.2) n
    (hf t) (ContinuousLinearMap.inl ℝ (Vec 2) P) (0, X.2) w X.1
  simpa only [independentSourceFastWord, ContinuousLinearMap.inl_apply, Prod.mk_add_mk,
    zero_add, add_zero, Prod.mk.eta] using he

def IndependentParameterSourceReserve.fastWordReserve {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (n r : ℕ) (hnr : n + r ≤ H)
    (w : Fin n → Vec 2) (hw : ∀ i, ‖w i‖ ≤ 1) :
    IndependentParameterSourceReserve r (independentSourceFastWord f n w) := by
  have he (t : ℝ) : (fun X : Vec 2 × P => independentSourceFastWord f n w t X.1 X.2) =
      realWordJet (fun U : Vec 2 × P => f t U.1 U.2) n (fun i => (w i, 0)) :=
    funext (independentSourceFastWord_eq_jointWord f n
      (fun t => (Q.regular t).of_le (by exact_mod_cast (show n ≤ H by omega))) w t)
  have hword : ∀ i, ‖(w i, (0 : P))‖ ≤ 1 := by
    intro i
    simpa only [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)] using hw i
  refine ⟨?_, ?_, ?_, (fun j => Q.budget (n + j)), (fun j => Q.budget_nonneg _), ?_⟩
  · intro t
    rw [he]
    exact finite_realWordJet_contDiff _ n r ((Q.regular t).of_le (by exact_mod_cast hnr)) _
  · intro t Y k z
    have ht : (fun x => f t (x + AVenhance.latticeShift k) Y) = fun x => f t x Y :=
      funext (Q.periodic t Y k)
    have hd := congrArg (fun g => iteratedFDeriv ℝ n g z) ht
    have hshift : iteratedFDeriv ℝ n (fun x => f t (x + AVenhance.latticeShift k) Y) z =
        iteratedFDeriv ℝ n (fun x => f t x Y) (z + AVenhance.latticeShift k) :=
      iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun y => f t y Y) n
        (AVenhance.latticeShift k) z
    rw [hshift] at hd
    exact congrArg (fun A => A w) hd
  · intro Y
    exact finite_realParameterWordJet_measurable_joint (fun t z => f t z Y) n
      (fun t => ((Q.regular t).comp₂ contDiff_id contDiff_const).of_le (by exact_mod_cast (show n ≤ H by omega)))
      (Q.measurable Y) w
  · intro j hj t X
    rw [he]
    exact (finite_realWordJet_derivative_bound _ n j
      ((Q.regular t).of_le (by exact_mod_cast (show n + j ≤ H by omega))) _ hword X).trans
      (Q.derivative_bound (n + j) (by omega) t X)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Literal bilinear path-forcing products retain genuine finite source reserves. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs
variable {P E F V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

def IndependentParameterSourceReserve.bilinear {H : ℕ} {f : ℝ → Vec 2 → P → E}
    {g : ℝ → Vec 2 → P → F} (Q : IndependentParameterSourceReserve H f) (R : IndependentParameterSourceReserve H g)
    (T : E →L[ℝ] F →L[ℝ] V) : IndependentParameterSourceReserve H (fun t z Y => T (f t z Y) (g t z Y)) where
  regular t := (T.contDiff.comp (Q.regular t)).clm_apply (R.regular t)
  periodic t Y n z := congrArg₂ (fun x y => T x y) (Q.periodic t Y n z) (R.periodic t Y n z)
  measurable Y := T.isBoundedBilinearMap.continuous.measurable.comp
    ((Q.measurable Y).prodMk (R.measurable Y))
  budget n := ‖T‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Q.budget i * R.budget (n - i)
  budget_nonneg n := mul_nonneg (norm_nonneg T) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Q.budget_nonneg i)) (R.budget_nonneg _))
  derivative_bound n hn t X := by
    apply (T.norm_iteratedFDeriv_le_of_bilinear (Q.regular t) (R.regular t) X
      (by exact_mod_cast hn)).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ H := by have := Finset.mem_range.mp hi; omega
    have hni : n - i ≤ H := by omega
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (Q.derivative_bound i hi' t X) (Nat.cast_nonneg _))
      (R.derivative_bound (n - i) hni t X) (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (Q.budget_nonneg i))

end AVRegularity.EntryWeakProofs
end
end

section
/-! Cutoffs turn genuine local parameter jets into global jets without assuming global field bounds. -/
@[expose] public noncomputable section
open Filter Set Topology
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ P] in
theorem independent_cutoff_eventually_zero (χ : P → ℝ) (f : P → E) (X : P)
    (hX : X ∉ tsupport χ) : (fun Y => χ Y • f Y) =ᶠ[𝓝 X] 0 := by
  have hh : χ =ᶠ[𝓝 X] 0 := notMem_tsupport_iff_eventuallyEq.mp hX
  filter_upwards [hh] with Y hY
  simp only [hY, Pi.zero_apply, zero_smul]

theorem independent_cutoff_jet_bound (χ : P → ℝ) (f : P → E) (H n : ℕ)
    (hχ : ContDiff ℝ (H : ℕ∞) χ) (hf : ContDiff ℝ (H : ℕ∞) f) (hn : n ≤ H)
    (U : Set P) (hs : tsupport χ ⊆ U) (A B : ℕ → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (hbχ : ∀ i ≤ H, ∀ Y, ‖iteratedFDeriv ℝ i χ Y‖ ≤ A i)
    (hbf : ∀ i ≤ H, ∀ Y ∈ U, ‖iteratedFDeriv ℝ i f Y‖ ≤ B i) (X : P) :
    ‖iteratedFDeriv ℝ n (fun Y => χ Y • f Y) X‖ ≤
      ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)‖ *
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i * B (n - i) := by
  by_cases hX : X ∈ U
  · let T : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
    apply (T.norm_iteratedFDeriv_le_of_bilinear hχ hf X (by exact_mod_cast hn)).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
    apply Finset.sum_le_sum
    intro i hi
    have hiH : i ≤ H := by have := Finset.mem_range.mp hi; omega
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hbχ i hiH X) (Nat.cast_nonneg _))
      (hbf (n - i) (by omega) X hX) (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (hA i))
  · have hz := independent_cutoff_eventually_zero χ f X (fun hh => hX (hs hh))
    rw [(hz.iteratedFDeriv ℝ n).self_of_nhds]
    change ‖iteratedFDeriv ℝ n (fun _ : P => (0 : E)) X‖ ≤ _
    rw [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _))

end AVRegularity.EntryWeakProofs
end
end

section
/-! A genuine independent metric entry supplies its literal fast-independent forcing reserve. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def IndependentParameterMetricReserve.entrySource {H : ℕ}
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve H G) (i j : Fin 2) :
    IndependentParameterSourceReserve H (fun t (_ : Vec 2) Y => G t Y i j) where
  regular t := ((Q.regular t i j).of_le (by simp)).comp contDiff_snd
  periodic _ _ _ _ := rfl
  measurable Y := (Q.measurable Y i j).comp measurable_fst
  budget := Q.budget
  budget_nonneg := Q.budget_nonneg
  derivative_bound n hn t X := by
    have hL : ‖ContinuousLinearMap.snd ℝ (Vec 2) P‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun U => by
        change ‖U.2‖ ≤ 1 * ‖U‖
        rw [one_mul]
        exact norm_snd_le U)
    have hb := finite_affine_derivative_norm_le (fun Y => G t Y i j) n
      ((Q.regular t i j).of_le (by simp)) (ContinuousLinearMap.snd ℝ (Vec 2) P) hL 0 X
    have he : (fun U : Vec 2 × P => G t (U.2 + 0) i j) = fun U : Vec 2 × P => G t U.2 i j := by
      funext U
      rw [add_zero]
    change ‖iteratedFDeriv ℝ n (fun U : Vec 2 × P => G t (U.2 + 0) i j) X‖ ≤ _ at hb
    rw [he] at hb
    exact hb.trans (Q.derivative_bound n hn t (X.2 + 0) i j)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine independent-parameter jets give uniform metric and source differences. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

omit [MeasurableSpace E] in
theorem independent_parameter_lipschitz (f : P → E) (hf : ContDiff ℝ 1 f)
    (C : ℝ) (hC : ∀ Y, ‖fderiv ℝ f Y‖ ≤ C) (X Y : P) :
    ‖f Y - f X‖ ≤ C * ‖Y - X‖ :=
  convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun Z _ => (hf.differentiable (by norm_num)) Z) (fun Z _ => hC Z)
    (mem_univ X) (mem_univ Y)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] in
theorem IndependentParameterMetricReserve.entry_lipschitz {H : ℕ}
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve H G) (hH : 1 ≤ H)
    (t : ℝ) (i j : Fin 2) (X Y : P) :
    |G t Y i j - G t X i j| ≤ Q.budget 1 * ‖Y - X‖ := by
  apply independent_parameter_lipschitz (fun Z => G t Z i j)
    ((Q.regular t i j).of_le (by simp))
  intro Z
  simpa only [norm_iteratedFDeriv_one] using Q.derivative_bound 1 hH t Z i j

theorem IndependentParameterSourceReserve.parameter_lipschitz {H : ℕ}
    {f : ℝ → Vec 2 → P → E} (Q : IndependentParameterSourceReserve H f)
    (hH : 1 ≤ H) (t : ℝ) (z : Vec 2) (X Y : P) :
    ‖f t z Y - f t z X‖ ≤ Q.budget 1 * ‖Y - X‖ := by
  have hh := independent_parameter_lipschitz
    (fun Z : Vec 2 × P => f t Z.1 Z.2)
    ((Q.regular t).of_le (by exact_mod_cast hH)) (Q.budget 1)
    (fun Z => by simpa only [norm_iteratedFDeriv_one] using Q.derivative_bound 1 hH t Z)
    (z, X) (z, Y)
  simpa only [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using hh

end AVRegularity.EntryWeakProofs
end
end

section
/-! Independent primitive reserves retain their exact budgets when the requested order decreases. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

def IndependentParameterSourceReserve.restrictOrder {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (K : ℕ) (hK : K ≤ H) :
    IndependentParameterSourceReserve K f where
  regular := fun t => (Q.regular t).of_le (by exact_mod_cast hK)
  periodic := Q.periodic
  measurable := Q.measurable
  budget := Q.budget
  budget_nonneg := Q.budget_nonneg
  derivative_bound := fun n hn => Q.derivative_bound n (hn.trans hK)

def IndependentParameterMetricReserve.restrictOrder {H : ℕ}
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve H G) (K : ℕ) (hK : K ≤ H) :
    IndependentParameterMetricReserve K G where
  regular := Q.regular
  measurable := Q.measurable
  metric := Q.metric
  budget := Q.budget
  budget_nonneg := Q.budget_nonneg
  derivative_bound := fun n hn => Q.derivative_bound n (hn.trans hK)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Independent parameter derivatives of a source use its genuine joint reserve. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

theorem IndependentParameterSourceReserve.parameter_derivative_bound {H : ℕ}
    {f : ℝ → Vec 2 → P → E} (Q : IndependentParameterSourceReserve H f)
    (n : ℕ) (hn : n ≤ H) (t : ℝ) (z : Vec 2) (Y : P) :
    ‖iteratedFDeriv ℝ n (f t z) Y‖ ≤ Q.budget n := by
  have hh := finite_affine_derivative_norm_le
    (fun Z : Vec 2 × P => f t Z.1 Z.2) n
    ((Q.regular t).of_le (by exact_mod_cast hn))
    (ContinuousLinearMap.inr ℝ (Vec 2) P) (ContinuousLinearMap.norm_inr_le_one ℝ (Vec 2) P) (z, 0) Y
  have hb := hh.trans (Q.derivative_bound n hn t ((0, Y) + (z, 0)))
  simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero] using hb

end AVRegularity.EntryWeakProofs
end
end

section
/-! Literal bilinear source budgets multiply the stored amplitudes exactly. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E F V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

omit [SecondCountableTopology E] [SecondCountableTopology V] in
theorem IndependentParameterSourceReserve.bilinear_budget_le {H : ℕ}
    {f : ℝ → Vec 2 → P → E} {g : ℝ → Vec 2 → P → F}
    (Q : IndependentParameterSourceReserve H f) (R : IndependentParameterSourceReserve H g)
    (T : E →L[ℝ] F →L[ℝ] V) (θ φ B C : ℝ)
    (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (hQ : ∀ i ≤ H, Q.budget i ≤ θ * B) (hR : ∀ i ≤ H, R.budget i ≤ φ * C)
    (n : ℕ) (hn : n ≤ H) :
    (Q.bilinear R T).budget n ≤ (θ * φ) * (‖T‖ * 2 ^ n * B * C) := by
  change ‖T‖ * (∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * Q.budget i * R.budget (n - i)) ≤ _
  have hb : (∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * Q.budget i * R.budget (n - i)) ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (θ * B) * (φ * C) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ H := by have := Finset.mem_range.mp hi; omega
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hQ i hi') (Nat.cast_nonneg _))
      (hR (n - i) (by omega)) (R.budget_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hθ hB))
  have hchoose : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  have he : ‖T‖ * (∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (θ * B) * (φ * C)) =
      (θ * φ) * (‖T‖ * 2 ^ n * B * C) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
    ring
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg T)).trans_eq he

end AVRegularity.EntryWeakProofs
end
end

section
/-! Finite literal sums preserve independent source reserves and their exact budget sums. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def IndependentParameterSourceReserve.zero (H : ℕ) : IndependentParameterSourceReserve H (fun (_ : ℝ) (_ : Vec 2) (_ : P) => (0 : E)) where
  regular _ := contDiff_const
  periodic _ _ _ _ := rfl
  measurable _ := measurable_const
  budget _ := 0
  budget_nonneg _ := le_rfl
  derivative_bound _ _ _ _ := by
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, le_refl]

theorem independentSourceReserve_sum_with_budget {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ℕ) (f : ι → ℝ → Vec 2 → P → E)
    (Q : ∀ i, IndependentParameterSourceReserve H (f i)) :
    ∃ R : IndependentParameterSourceReserve H (fun t z Y => ∑ i ∈ s, f i t z Y),
      ∀ n, R.budget n = ∑ i ∈ s, (Q i).budget n := by
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨IndependentParameterSourceReserve.zero H, ?_⟩
      intro n
      simp only [IndependentParameterSourceReserve.zero, Finset.sum_empty]
  | @insert i s hi ih =>
      obtain ⟨R, hR⟩ := ih
      have he : (fun t z Y => ∑ j ∈ insert i s, f j t z Y) =
          fun t z Y => f i t z Y + ∑ j ∈ s, f j t z Y := by
        funext t z Y
        exact Finset.sum_insert hi
      rw [he]
      refine ⟨(Q i).add R, ?_⟩
      intro n
      change (Q i).budget n + R.budget n = _
      rw [hR, Finset.sum_insert hi]

def IndependentParameterSourceReserve.fintypeSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ℕ) (f : ι → ℝ → Vec 2 → P → E)
    (Q : ∀ i, IndependentParameterSourceReserve H (f i)) :
    IndependentParameterSourceReserve H (fun t z Y => ∑ i, f i t z Y) :=
  Classical.choose (independentSourceReserve_sum_with_budget Finset.univ H f Q)

theorem IndependentParameterSourceReserve.fintypeSum_budget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ℕ) (f : ι → ℝ → Vec 2 → P → E)
    (Q : ∀ i, IndependentParameterSourceReserve H (f i)) (n : ℕ) :
    (IndependentParameterSourceReserve.fintypeSum H f Q).budget n = ∑ i, (Q i).budget n :=
  Classical.choose_spec (independentSourceReserve_sum_with_budget Finset.univ H f Q) n

def IndependentParameterSourceReserve.finsetSum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ℕ) (f : ι → ℝ → Vec 2 → P → E)
    (Q : ∀ i ∈ s, IndependentParameterSourceReserve H (f i)) :
    IndependentParameterSourceReserve H (fun t z Y => ∑ i ∈ s, f i t z Y) := by
  have he : (fun t z Y => ∑ i : s, f i.val t z Y) =
      fun t z Y => ∑ i ∈ s, f i t z Y := by
    funext t z Y
    exact Finset.sum_attach s (fun i => f i t z Y)
  exact (IndependentParameterSourceReserve.fintypeSum H (fun i : s => f i.val)
    (fun i => Q i.val i.property)).congrSource he

theorem IndependentParameterSourceReserve.finsetSum_budget {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ℕ) (f : ι → ℝ → Vec 2 → P → E)
    (Q : ∀ i ∈ s, IndependentParameterSourceReserve H (f i)) (n : ℕ) :
    (IndependentParameterSourceReserve.finsetSum s H f Q).budget n = ∑ i : s, (Q i.val i.property).budget n := by
  unfold IndependentParameterSourceReserve.finsetSum
  rw [IndependentParameterSourceReserve.congrSource_budget, IndependentParameterSourceReserve.fintypeSum_budget]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual zeroth fast-jet reserves supply a windowed independent source. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set
namespace AVRegularity.EntryWeakProofs
variable {d : ℕ}

def windowIndependentReserveOfZeroFastJets (S : ℕ) (I : Set ℝ) (hI : MeasurableSet I)
    (f : ℝ → Vec d → Vec 2 → ℝ)
    (hr : ∀ t ∈ I, ContDiff ℝ (S : ℕ∞) (fun X : Vec d × Vec 2 => iteratedFDeriv ℝ 0 (f t X.1) X.2))
    (hp : ∀ t ∈ I, ∀ Y, AVenhance.IsZ2Periodic (f t Y))
    (hm : ∀ Y, Measurable (fun X : ℝ × Vec 2 => f X.1 Y X.2))
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hb : ∀ n, n ≤ S → ∀ t ∈ I, ∀ X : Vec d × Vec 2,
      ‖iteratedFDeriv ℝ n (fun X : Vec d × Vec 2 => iteratedFDeriv ℝ 0 (f t X.1) X.2) X‖ ≤ B n) :
    IndependentParameterSourceReserve S (independentTimeWindowSource I (fun t z Y => f t Y z)) := by
  apply windowIndependentSourceReserve S I hI
    (fun t z Y => f t Y z)
    _ _ hm B hB _
  · intro t ht
    have hh := zero_fast_jet_field_contDiff
      (f t) S
      (hr t ht)
    exact hh.comp (contDiff_snd.prodMk contDiff_fst)
  · intro t ht Y
    exact hp t ht Y
  · intro n hn t ht X
    let e := LinearIsometryEquiv.prodComm ℝ (Vec 2) (Vec d)
    change ‖iteratedFDeriv ℝ n
      ((Function.uncurry (f t)) ∘ e) X‖ ≤ B n
    rw [e.norm_iteratedFDeriv_comp_right]
    rw [← norm_joint_zero_fast_jet (f t) n (e X)]
    exact hb n hn t ht (e X)

end AVRegularity.EntryWeakProofs
end
end
end

section
@[expose] public noncomputable section
open Filter Set Topology
namespace AVRegularity.EntryWeakProofs

/-! Local genuine field reserves extend globally while retaining their literal native germs. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def independentCutoffExtension (χ : P → ℝ) (f : P → E) (e : E) (X : P) : E :=
  e + χ X • (f X - e)

theorem independentCutoffExtension_jet_bound (χ : P → ℝ) (f : P → E) (e : E) (H n : ℕ)
    (hχ : ContDiff ℝ (H : ℕ∞) χ) (hf : ContDiff ℝ (H : ℕ∞) f) (hn : n ≤ H)
    (U : Set P) (hs : tsupport χ ⊆ U) (A B : ℕ → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (hbχ : ∀ i ≤ H, ∀ Y, ‖iteratedFDeriv ℝ i χ Y‖ ≤ A i)
    (hbf : ∀ i ≤ H, ∀ Y ∈ U, ‖iteratedFDeriv ℝ i f Y‖ ≤ B i) (X : P) :
    ‖iteratedFDeriv ℝ n (independentCutoffExtension χ f e) X‖ ≤
      ‖e‖ + ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)‖ *
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i * (B (n - i) + ‖e‖) := by
  have he : ∀ i Y, ‖iteratedFDeriv ℝ i (fun _ : P => e) Y‖ ≤ ‖e‖ := by
    intro i Y
    cases i with
    | zero => simp only [norm_iteratedFDeriv_zero]; exact le_rfl
    | succ i => rw [iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, norm_zero]; exact norm_nonneg e
  let g := fun Y : P => f Y - e
  have hg : ContDiff ℝ (H : ℕ∞) g := hf.sub contDiff_const
  have hbg : ∀ i ≤ H, ∀ Y ∈ U, ‖iteratedFDeriv ℝ i g Y‖ ≤ B i + ‖e‖ := by
    intro i hi Y hY
    change ‖iteratedFDeriv ℝ i (f - fun _ : P => e) Y‖ ≤ B i + ‖e‖
    rw [iteratedFDeriv_sub_apply (hf.contDiffAt.of_le (by exact_mod_cast hi))
      (contDiff_const.contDiffAt (n := (i : ℕ∞)))]
    exact (norm_sub_le _ _).trans (add_le_add (hbf i hi Y hY) (he i Y))
  have hb := independent_cutoff_jet_bound χ g H n hχ hg hn U hs A (fun i => B i + ‖e‖)
    hA (fun i => add_nonneg (hB i) (norm_nonneg e)) hbχ hbg X
  have hprod : ContDiff ℝ (H : ℕ∞) (fun Y => χ Y • g Y) := hχ.smul hg
  change ‖iteratedFDeriv ℝ n ((fun _ : P => e) + fun Y => χ Y • g Y) X‖ ≤ _
  rw [iteratedFDeriv_add_apply (contDiff_const.contDiffAt (n := (n : ℕ∞)))
    (hprod.contDiffAt.of_le (by exact_mod_cast hn))]
  exact (norm_add_le _ _).trans (add_le_add (he n X) hb)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! A native slow block varies inside full independent coordinates while every stored parameter stays fixed. -/

def independentIntrinsicSlowEmbedding (d : ℕ) : Vec 2 →L[ℝ] Vec (2 + d) :=
  ContinuousLinearMap.pi (Fin.addCases
    (fun i : Fin 2 => ContinuousLinearMap.proj i)
    (fun _ : Fin d => (0 : Vec 2 →L[ℝ] ℝ)))

def independentIntrinsicSlowProjection (d : ℕ) : Vec (2 + d) →L[ℝ] Vec 2 :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (i.castAdd d))

def independentStoredParameterProjection (d : ℕ) : Vec (2 + d) →L[ℝ] Vec d :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (i.natAdd 2))

theorem independentIntrinsicSlowEmbedding_norm_le (d : ℕ) :
    ‖independentIntrinsicSlowEmbedding d‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro X
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg X)).2
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [independentIntrinsicSlowEmbedding, ContinuousLinearMap.pi_apply,
      Fin.addCases_left, ContinuousLinearMap.proj_apply] using norm_le_pi_norm X j
  · simp only [independentIntrinsicSlowEmbedding, ContinuousLinearMap.pi_apply,
      Fin.addCases_right, zero_apply, norm_zero]
    exact norm_nonneg X

theorem independentIntrinsicSlowProjection_embedding (d : ℕ) (X : Vec 2) :
    independentIntrinsicSlowProjection d (independentIntrinsicSlowEmbedding d X) = X := by
  funext i
  simp only [independentIntrinsicSlowProjection, independentIntrinsicSlowEmbedding,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, Fin.addCases_left]

theorem independentStoredParameterProjection_embedding (d : ℕ) (X : Vec 2) :
    independentStoredParameterProjection d (independentIntrinsicSlowEmbedding d X) = 0 := by
  funext i
  simp only [independentStoredParameterProjection, independentIntrinsicSlowEmbedding,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, Fin.addCases_right,
    zero_apply, Pi.zero_apply]

def independentIntrinsicSliceOffset (d : ℕ) (Y : Vec (2 + d)) : Vec (2 + d) :=
  Y - independentIntrinsicSlowEmbedding d (independentIntrinsicSlowProjection d Y)

theorem independentIntrinsicSliceOffset_base (d : ℕ) (Y : Vec (2 + d)) :
    independentIntrinsicSlowEmbedding d (independentIntrinsicSlowProjection d Y) +
      independentIntrinsicSliceOffset d Y = Y := by
  dsimp only [independentIntrinsicSliceOffset]
  abel

theorem independentIntrinsicSlowProjection_slice (d : ℕ) (Y : Vec (2 + d)) (X : Vec 2) :
    independentIntrinsicSlowProjection d
      (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y) = X := by
  rw [map_add, independentIntrinsicSliceOffset, map_sub,
    independentIntrinsicSlowProjection_embedding, independentIntrinsicSlowProjection_embedding,
    sub_self, add_zero]

theorem independentStoredParameterProjection_slice (d : ℕ) (Y : Vec (2 + d)) (X : Vec 2) :
    independentStoredParameterProjection d
      (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y) =
      independentStoredParameterProjection d Y := by
  rw [map_add, independentIntrinsicSliceOffset, map_sub,
    independentStoredParameterProjection_embedding, independentStoredParameterProjection_embedding,
    sub_zero, zero_add]

/-! Centered parameter-jet differences retain the small displacement factor. -/

section
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem independent_parameter_jet_difference_bound (f : P → E) (n : ℕ)
    (hf : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) f) (C : ℝ)
    (hb : ∀ Y, ‖iteratedFDeriv ℝ (n + 1) f Y‖ ≤ C) (X Y : P) :
    ‖iteratedFDeriv ℝ n f Y - iteratedFDeriv ℝ n f X‖ ≤ C * ‖Y - X‖ := by
  have hg : ContDiff ℝ 1 (iteratedFDeriv ℝ n f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast (show 1 + n ≤ n + 1 by omega))
  exact independent_parameter_lipschitz _ hg C (fun Y => by
    rw [norm_fderiv_iteratedFDeriv]
    exact hb Y) X Y
end

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
namespace AVRegularity.EntryWeakProofs

/-! Genuine independent-parameter reserves yield continuity in the exact inverse data norms. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] in
theorem IndependentParameterMetricReserve.norm_difference_tendsto_zero {H : ℕ}
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve H G) (hH : 1 ≤ H) (X : P) :
    Tendsto (fun Y => cellMetricSupNorm (fun t (_ : Vec 2) => G t Y - G t X))
      (𝓝 X) (𝓝 0) := by
  have hb (Y : P) : cellMetricSupNorm (fun t (_ : Vec 2) => G t Y - G t X) ≤
      ENNReal.ofReal (Q.budget 1 * ‖Y - X‖) := by
    apply iSup_le
    intro t
    apply iSup_le
    intro z
    apply iSup_le
    intro i
    apply iSup_le
    intro j
    change ‖G t Y i j - G t X i j‖ₑ ≤ _
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (Q.entry_lipschitz hH t i j X Y)
  have ht : Tendsto (fun Y : P => ENNReal.ofReal (Q.budget 1 * ‖Y - X‖))
      (𝓝 X) (𝓝 0) := by
    have hc : Continuous (fun Y : P => ENNReal.ofReal (Q.budget 1 * ‖Y - X‖)) :=
      ENNReal.continuous_ofReal.comp ((continuous_id.sub continuous_const).norm.const_mul (Q.budget 1))
    simpa only [sub_self, norm_zero, mul_zero, ENNReal.ofReal_zero] using hc.tendsto X
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) hb

theorem IndependentParameterSourceReserve.norm_difference_tendsto_zero {H : ℕ}
    {f : ℝ → Vec 2 → P → E} (Q : IndependentParameterSourceReserve H f)
    (hH : 1 ≤ H) (X : P) :
    Tendsto (fun Y => cellUlNorm univ (fun t z => f t z Y - f t z X))
      (𝓝 X) (𝓝 0) := by
  have hb (Y : P) : cellUlNorm univ (fun t z => f t z Y - f t z X) ≤
      ENNReal.ofReal (Q.budget 1 * ‖Y - X‖) :=
    cell_source_ulNorm_le_pointwise (fun t z => f t z Y - f t z X)
      ((Q.measurable Y).sub (Q.measurable X)) _
      (fun t z => Q.parameter_lipschitz hH t z X Y)
  have ht : Tendsto (fun Y : P => ENNReal.ofReal (Q.budget 1 * ‖Y - X‖))
      (𝓝 X) (𝓝 0) := by
    have hc : Continuous (fun Y : P => ENNReal.ofReal (Q.budget 1 * ‖Y - X‖)) :=
      ENNReal.continuous_ofReal.comp ((continuous_id.sub continuous_const).norm.const_mul (Q.budget 1))
    simpa only [sub_self, norm_zero, mul_zero, ENNReal.ofReal_zero] using hc.tendsto X
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) hb

end AVRegularity.EntryWeakProofs
end
end
