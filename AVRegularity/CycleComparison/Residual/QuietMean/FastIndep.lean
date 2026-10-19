-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.TimeIntegration
public import AVRegularity.Statements.Intermediate.CycleComparison.SourceCoeff
public import AVRegularity.Statements.Intermediate.CycleComparison.CellB2
import AVRegularity.CycleComparison.Residual.QuietMean.CellMean
public import AVRegularity.Statements.Intermediate.CycleComparison.FieldCellMean
public import AVRegularity.Statements.Intermediate.CycleComparison.IsBoxSmooth
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.RingTheory.Finiteness.Prod

@[expose] public section

section
open Homogenization Filter Topology
namespace AVRegularity

/-! A box-smooth field of orders `(m, m)` is jointly `C^m`. -/

universe u

theorem vec_eq_sum_basis (v : Vec 2) : v = ∑ i, v i • basisVec i := by
  funext j
  simp [basisVec, Pi.single_apply]

section Dir
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E}

theorem IsBoxSmooth.slowDir (hf : IsBoxSmooth (sX + 1) sZ f) (v : Vec 2) :
    IsBoxSmooth sX sZ (fun X z => fderiv ℝ (fun X' => f X' z) X v) := by
  have : (fun X z => fderiv ℝ (fun X' => f X' z) X v) =
      fun X z => ∑ i, v i • AVRegularity.slowPartial i f X z := by
    funext X z
    conv_lhs => rw [vec_eq_sum_basis v]
    simp [map_smul, AVRegularity.slowPartial]
  rw [this]
  exact IsBoxSmooth.sum _ fun i _ => (hf.slowPartial i).const_smul (v i)

theorem IsBoxSmooth.fastDir (hf : IsBoxSmooth sX (sZ + 1) f) (v : Vec 2) :
    IsBoxSmooth sX sZ (fun X z => fderiv ℝ (f X) z v) :=
  hf.fderiv_fast.map_clm (ContinuousLinearMap.apply ℝ E v)

end Dir

theorem IsBoxSmooth.contDiff_uncurry_aux (m : ℕ) : ∀ (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : Vec 2 → Vec 2 → E), IsBoxSmooth m m f →
      ContDiff ℝ (m : ℕ∞) (Function.uncurry f) := by
  induction m with
  | zero =>
    intro E _ _ f hf
    have h := hf.2.2 0 0 le_rfl le_rfl
    have hT : ∀ p : Vec 2 × Vec 2, f p.1 p.2 =
        (continuousMultilinearCurryFin0 ℝ (Vec 2) E)
          ((continuousMultilinearCurryFin0 ℝ (Vec 2) _)
            (iteratedFDeriv ℝ 0 (fun X' => iteratedFDeriv ℝ 0 (f X') p.2) p.1)) := by
      intro p; simp [iteratedFDeriv_zero_eq_comp]
    have hc : Continuous (Function.uncurry f) := by
      have : Function.uncurry f = fun p : Vec 2 × Vec 2 =>
        (continuousMultilinearCurryFin0 ℝ (Vec 2) E)
          ((continuousMultilinearCurryFin0 ℝ (Vec 2) _)
            (iteratedFDeriv ℝ 0 (fun X' => iteratedFDeriv ℝ 0 (f X') p.2) p.1)) := by
        funext p; exact hT p
      rw [this]
      exact (continuousMultilinearCurryFin0 ℝ (Vec 2) E).continuous.comp
        ((continuousMultilinearCurryFin0 ℝ (Vec 2) _).continuous.comp h)
    simpa [contDiff_zero] using hc
  | succ m ih =>
    intro E _ _ f hf
    have hdiff : ∀ u : Vec 2 × Vec 2, HasFDerivAt (Function.uncurry f)
        ((fderiv ℝ (fun X => f X u.2) u.1).coprod (fderiv ℝ (f u.1) u.2)) u := fun u =>
      hf.hasFDerivAt_uncurry (by omega) (by omega) u
    rw [show (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) = ((m : ℕ∞) : WithTop ℕ∞) + 1 by norm_cast,
      contDiff_succ_iff_fderiv]
    refine ⟨fun u => (hdiff u).differentiableAt, by simp, ?_⟩
    rw [contDiff_clm_apply_iff]
    intro w
    have e : (fun u : Vec 2 × Vec 2 => fderiv ℝ (Function.uncurry f) u w) =
        fun u => fderiv ℝ (fun X => f X u.2) u.1 w.1 + fderiv ℝ (f u.1) u.2 w.2 := by
      funext u; rw [(hdiff u).fderiv]; simp
    rw [e]
    have h1 := ih E _ (hf.slowDir w.1 |>.mono (by omega) (by omega))
    have h2 := ih E _ (hf.fastDir w.2 |>.mono (by omega) (by omega))
    exact h1.add h2

theorem IsBoxSmooth.contDiff_uncurry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m sX sZ : ℕ} {f : Vec 2 → Vec 2 → E} (hf : IsBoxSmooth sX sZ f) (hX : m ≤ sX) (hZ : m ≤ sZ) :
    ContDiff ℝ (m : ℕ∞) (Function.uncurry f) :=
  IsBoxSmooth.contDiff_uncurry_aux m _ f (hf.mono hX hZ)

end AVRegularity
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! Fast independence is preserved by `D_ε`, by the source operator and its Taylor coefficients
(at a quiet time), and by `ℬ₂`; the cell mean of a fast independent field is its value at `z = 0`. -/

section ZInd
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fast independence of a two-scale field. -/
def FastIndep (Ψ : Vec 2 → Vec 2 → E) : Prop := ∀ X z z', Ψ X z = Ψ X z'

theorem FastIndep.fastPartial {Ψ : Vec 2 → Vec 2 → E} (h : FastIndep Ψ) (i : Fin 2) (X z : Vec 2) :
    AVRegularity.fastPartial i Ψ X z = 0 := by
  have : (fun z' => Ψ X z') = fun _ => Ψ X 0 := funext fun z' => h X z' 0
  unfold AVRegularity.fastPartial
  rw [this]
  simp

theorem FastIndep.slowPartial {Ψ : Vec 2 → Vec 2 → E} (h : FastIndep Ψ) (i : Fin 2) (X z z' : Vec 2) :
    AVRegularity.slowPartial i Ψ X z = AVRegularity.slowPartial i Ψ X z' := by
  have : (fun X' => Ψ X' z) = fun X' => Ψ X' z' := funext fun X' => h X' z z'
  unfold AVRegularity.slowPartial
  rw [this]

theorem FastIndep.dEps {Ψ : Vec 2 → Vec 2 → E} (h : FastIndep Ψ) (η ε : ℝ) (i : Fin 2) :
    FastIndep (AVRegularity.dEps η ε i Ψ) := fun X z z' => by
  simp [AVRegularity.dEps, h.fastPartial, h.slowPartial i X z z']

theorem FastIndep.foldl (η ε : ℝ) (l : List (Fin 2)) :
    ∀ {Ψ : Vec 2 → Vec 2 → E}, FastIndep Ψ →
      FastIndep (l.foldl (fun Ψ' i => AVRegularity.dEps η ε i Ψ') Ψ) := by
  induction l with
  | nil => intro Ψ h; exact h
  | cons i l ih => intro Ψ h; exact ih (h.dEps η ε i)

theorem FastIndep.dEpsWord {Ψ : Vec 2 → Vec 2 → E} (h : FastIndep Ψ) (η ε : ℝ) {m : ℕ}
    (α : DerivativeWord2 m) : FastIndep (AVRegularity.dEpsWord η ε α Ψ) :=
  FastIndep.foldl η ε (List.ofFn α) h

end ZInd

section Source
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceFlux_fastIndep (edge : ConstituentEdges D h) (η ε t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : FastIndep Φ) (k : Fin 2) :
    FastIndep (sourceFlux edge η ε t Φ k) := fun X z z' => by
  funext v
  simp only [sourceFlux]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun d _ => ?_
  congr 1
  refine List.map_congr_left fun γ hγ => ?_
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [hquiet v u d γ hγ α X z z', (hΦ.dEpsWord η ε α) X z z']

theorem sourceOp_fastIndep (edge : ConstituentEdges D h) (η ε t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : FastIndep Φ) :
    FastIndep (sourceOp edge η ε t Φ) := fun X z z' => by
  simp only [sourceOp]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact ((sourceFlux_fastIndep edge η ε t hquiet hΦ k).dEps η ε k) X z z'

theorem sourceCoeff_fastIndep (edge : ConstituentEdges D h) (η t : ℝ) (j : ℕ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : FastIndep Φ) :
    FastIndep (sourceCoeff edge η j t Φ) := fun X z z' => by
  simp only [sourceCoeff]
  congr 2
  funext ε
  exact sourceOp_fastIndep edge η ε t hquiet hΦ X z z'

end Source

theorem FastIndep.cellB2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ) {Φ : Vec 2 → Vec 2 → E} (hΦ : FastIndep Φ) :
    FastIndep (AVRegularity.cellB2 η G t Φ) := fun X z z' => by
  have h1 : ∀ i j : Fin 2, AVRegularity.slowPartial i (fun X' z' => G t X' i j • AVRegularity.slowPartial j Φ X' z') X z =
      AVRegularity.slowPartial i (fun X' z' => G t X' i j • AVRegularity.slowPartial j Φ X' z') X z' := fun i j => by
    have : FastIndep (fun X' z' => G t X' i j • AVRegularity.slowPartial j Φ X' z') := fun X' a b => by
      simp only [hΦ.slowPartial j X' a b]
    exact this.slowPartial i X z z'
  simp only [AVRegularity.cellB2, h1]

theorem fieldCellMean_fastIndep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {Ψ : Vec 2 → Vec 2 → E} (hΨ : FastIndep Ψ) (X : Vec 2) :
    fieldCellMean (Ψ X) = Ψ X 0 := by
  have : Ψ X = fun _ => Ψ X 0 := funext fun z => hΨ X z 0
  rw [this]
  exact fieldCellMean_const _

end AVRegularity
end
