-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.Jets.Lift
public import AVRegularity.CycleComparison.Residual.TailJets
import AVRegularity.CycleComparison.Residual.QuietMean.EpsPoly
public import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public noncomputable section

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! Pointwise mixed jets `srcJp` of two-scale fields (the integrand of `srcPtJet`) and their
calculus: the partial derivatives shift the jet orders by one, and the jets of sums, constant
multiples, continuous linear images and slow-scalar multiples are controlled by those of the
factors. -/

section Defs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The pointwise mixed jet: the `p`-th slow derivative of the `q`-th fast jet, in operator norm. -/
def srcJp (Ψ : Vec 2 → Vec 2 → E) (X : Vec 2) (p q : ℕ) (z : Vec 2) : ℝ :=
  ‖iteratedFDeriv ℝ p (fun X' => iteratedFDeriv ℝ q (Ψ X') z) X‖

/-- The `L²(unit cube)` norm in the fast variable of the pointwise mixed jet (same body as
`ptJet` of the jet calculus). -/
def srcPtJet (Ψ : Vec 2 → Vec 2 → E) (X : Vec 2) (p q : ℕ) : ℝ≥0∞ :=
  eLpNorm (fun z => ‖iteratedFDeriv ℝ p (fun X' => iteratedFDeriv ℝ q (Ψ X') z) X‖) 2
    (volume.restrict AVenhance.unitCube)

theorem srcJp_nonneg (Ψ : Vec 2 → Vec 2 → E) (X : Vec 2) (p q : ℕ) (z : Vec 2) :
    0 ≤ srcJp Ψ X p q z := norm_nonneg _

/-- Regularity needed for the jets: smoothness of the fast slices and of the slow dependence of
the fast jets, without the joint continuity of `IsBoxSmooth`. -/
def RegBox (sX sZ : ℕ) (f : Vec 2 → Vec 2 → E) : Prop :=
  (∀ X, ContDiff ℝ (sZ : ℕ∞) (f X)) ∧
  ∀ b, b ≤ sZ → ∀ z, ContDiff ℝ (sX : ℕ∞) (fun X => iteratedFDeriv ℝ b (f X) z)

theorem IsBoxSmooth.regBox {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E} (h : IsBoxSmooth sX sZ f) :
    RegBox sX sZ f := ⟨h.1, h.2.1⟩

theorem RegBox.mono {sX sZ sX' sZ' : ℕ} {f : Vec 2 → Vec 2 → E} (h : RegBox sX sZ f)
    (hX : sX' ≤ sX) (hZ : sZ' ≤ sZ) : RegBox sX' sZ' f :=
  ⟨fun X => (h.1 X).of_le (by exact_mod_cast hZ), fun b hb z =>
    (h.2 b (hb.trans hZ) z).of_le (by exact_mod_cast hX)⟩

theorem RegBox.contDiffAt_fast {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E} (h : RegBox sX sZ f)
    {q : ℕ} (hq : q ≤ sZ) (X z : Vec 2) : ContDiffAt ℝ (q : ℕ∞) (f X) z :=
  ((h.1 X).of_le (by exact_mod_cast hq)).contDiffAt

theorem RegBox.contDiffAt_slow {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E} (h : RegBox sX sZ f)
    {p q : ℕ} (hp : p ≤ sX) (hq : q ≤ sZ) (X z : Vec 2) :
    ContDiffAt ℝ (p : ℕ∞) (fun X' => iteratedFDeriv ℝ q (f X') z) X :=
  ((h.2 q hq z).of_le (by exact_mod_cast hp)).contDiffAt

theorem RegBox.zero {sX sZ : ℕ} : RegBox sX sZ (fun (_ _ : Vec 2) => (0 : E)) :=
  ⟨fun _ => contDiff_const, fun b _ z => by simp [iteratedFDeriv_fun_zero, contDiff_const]⟩

end Defs

section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem srcJp_zero (X : Vec 2) (p q : ℕ) (z : Vec 2) :
    srcJp (fun (_ _ : Vec 2) => (0 : E)) X p q z = 0 := by
  simp [srcJp, iteratedFDeriv_fun_zero]

theorem RegBox.add {sX sZ : ℕ} {f g : Vec 2 → Vec 2 → E} (hf : RegBox sX sZ f)
    (hg : RegBox sX sZ g) : RegBox sX sZ (fun X z => f X z + g X z) := by
  refine ⟨fun X => (hf.1 X).add (hg.1 X), fun b hb z => ?_⟩
  have : (fun X => iteratedFDeriv ℝ b (fun z' => f X z' + g X z') z) =
      fun X => iteratedFDeriv ℝ b (f X) z + iteratedFDeriv ℝ b (g X) z := funext fun X =>
    iteratedFDeriv_add_apply (hf.contDiffAt_fast hb X z) (hg.contDiffAt_fast hb X z)
  rw [this]
  exact (hf.2 b hb z).add (hg.2 b hb z)

theorem srcJp_add {sX sZ : ℕ} {f g : Vec 2 → Vec 2 → E} (hf : RegBox sX sZ f)
    (hg : RegBox sX sZ g) {p q : ℕ} (hp : p ≤ sX) (hq : q ≤ sZ) (X z : Vec 2) :
    srcJp (fun X z => f X z + g X z) X p q z ≤ srcJp f X p q z + srcJp g X p q z := by
  have : (fun X' => iteratedFDeriv ℝ q (fun z' => f X' z' + g X' z') z) =
      fun X' => iteratedFDeriv ℝ q (f X') z + iteratedFDeriv ℝ q (g X') z := funext fun X' =>
    iteratedFDeriv_add_apply (hf.contDiffAt_fast hq X' z) (hg.contDiffAt_fast hq X' z)
  unfold srcJp
  rw [this]
  have e := iteratedFDeriv_add_apply (i := p)
    (f := fun X' => iteratedFDeriv ℝ q (f X') z) (g := fun X' => iteratedFDeriv ℝ q (g X') z)
    (hf.contDiffAt_slow hp hq X z) (hg.contDiffAt_slow hp hq X z)
  rw [show (fun X' => iteratedFDeriv ℝ q (f X') z + iteratedFDeriv ℝ q (g X') z) =
    (fun X' => iteratedFDeriv ℝ q (f X') z) + fun X' => iteratedFDeriv ℝ q (g X') z from rfl, e]
  exact norm_add_le _ _

theorem RegBox.const_smul {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E} (hf : RegBox sX sZ f) (c : ℝ) :
    RegBox sX sZ (fun X z => c • f X z) := by
  refine ⟨fun X => (contDiff_const (c := c)).smul (hf.1 X), fun b hb z => ?_⟩
  have : (fun X => iteratedFDeriv ℝ b (fun z' => c • f X z') z) =
      fun X => c • iteratedFDeriv ℝ b (f X) z := funext fun X =>
    iteratedFDeriv_const_smul_apply' (a := c) (hf.contDiffAt_fast hb X z)
  rw [this]
  exact (contDiff_const (c := c)).smul (hf.2 b hb z)

theorem srcJp_const_smul {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E} (hf : RegBox sX sZ f) (c : ℝ)
    {p q : ℕ} (hp : p ≤ sX) (hq : q ≤ sZ) (X z : Vec 2) :
    srcJp (fun X z => c • f X z) X p q z = |c| * srcJp f X p q z := by
  have : (fun X' => iteratedFDeriv ℝ q (fun z' => c • f X' z') z) =
      fun X' => c • iteratedFDeriv ℝ q (f X') z := funext fun X' =>
    iteratedFDeriv_const_smul_apply' (a := c) (hf.contDiffAt_fast hq X' z)
  unfold srcJp
  rw [this, iteratedFDeriv_const_smul_apply' (a := c) (hf.contDiffAt_slow hp hq X z), norm_smul,
    Real.norm_eq_abs]

/-- A continuous linear map applied to a field. -/
theorem RegBox.clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {sX sZ : ℕ}
    {f : Vec 2 → Vec 2 → E} (hf : RegBox sX sZ f) (L : E →L[ℝ] F) :
    RegBox sX sZ (fun X z => L (f X z)) := by
  refine ⟨fun X => L.contDiff.comp (hf.1 X), fun b hb z => ?_⟩
  have : (fun X => iteratedFDeriv ℝ b (fun z' => L (f X z')) z) =
      fun X => L.compContinuousMultilinearMap (iteratedFDeriv ℝ b (f X) z) := funext fun X =>
    L.iteratedFDeriv_comp_left (hf.contDiffAt_fast hb X z) le_rfl
  rw [this]
  exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin b => Vec 2) E F
    L).contDiff.comp (hf.2 b hb z)

theorem srcJp_clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {sX sZ : ℕ}
    {f : Vec 2 → Vec 2 → E} (hf : RegBox sX sZ f) (L : E →L[ℝ] F)
    {p q : ℕ} (hp : p ≤ sX) (hq : q ≤ sZ) (X z : Vec 2) :
    srcJp (fun X z => L (f X z)) X p q z ≤ ‖L‖ * srcJp f X p q z := by
  set T := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin q => Vec 2) E F L
    with hT
  have hTn : ‖T‖ ≤ ‖L‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun m =>
    ContinuousLinearMap.norm_compContinuousMultilinearMap_le L m
  have : (fun X' => iteratedFDeriv ℝ q (fun z' => L (f X' z')) z) =
      T ∘ fun X' => iteratedFDeriv ℝ q (f X') z := funext fun X' =>
    L.iteratedFDeriv_comp_left (hf.contDiffAt_fast hq X' z) le_rfl
  unfold srcJp
  rw [this]
  refine (T.norm_iteratedFDeriv_comp_left (hf.contDiffAt_slow hp hq X z) (by exact_mod_cast le_rfl)).trans ?_
  gcongr

end Calculus

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization
open scoped ENNReal NNReal
namespace AVRegularity.QuietDecay

/-! Jets of partial derivatives, slow-scalar multiples, finite and list sums, and the passage from
a pointwise bound by continuous atoms to `srcPtJet`. -/

section
section Partial
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_jetApply_le (b : ℕ) (k : Fin 2) (f : ContinuousMultilinearMap ℝ
    (fun _ : Fin (b + 1) => Vec 2) E) : ‖jetApply b (basisVec k) f‖ ≤ ‖f‖ := by
  have e : jetApply b (basisVec k) f =
      (ContinuousLinearMap.apply ℝ E (basisVec k)).compContinuousMultilinearMap
        (continuousMultilinearCurryRightEquiv' ℝ b (Vec 2) E f) := rfl
  rw [e]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  have h1 : ‖ContinuousLinearMap.apply ℝ E (basisVec k)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => by
      rw [ContinuousLinearMap.apply_apply, one_mul]
      simpa [norm_basisVec] using g.le_opNorm (basisVec k)
  rw [LinearIsometryEquiv.norm_map]
  calc _ ≤ 1 * ‖f‖ := by gcongr
    _ = ‖f‖ := one_mul _

theorem opNorm_jetApply_le (b : ℕ) (k : Fin 2) :
    ‖(jetApply b (basisVec k) : ContinuousMultilinearMap ℝ (fun _ : Fin (b + 1) => Vec 2) E →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin b => Vec 2) E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [one_mul]; exact norm_jetApply_le b k f

/-- The slow derivative of a field shifts the slow order of the mixed jet. -/
theorem srcJp_slowPartial {sX sZ : ℕ} {Ψ : Vec 2 → Vec 2 → E} (h : IsBoxSmooth sX sZ Ψ)
    (k : Fin 2) {p q : ℕ} (hp : p + 1 ≤ sX) (hq : q ≤ sZ) (X z : Vec 2) :
    srcJp (slowPartial k Ψ) X p q z ≤ srcJp Ψ X (p + 1) q z := by
  have h1 : IsBoxSmooth 1 q Ψ := h.mono (by omega) hq
  have hin : (fun X' => iteratedFDeriv ℝ q (slowPartial k Ψ X') z) =
      fun X' => fderiv ℝ (fun X'' => iteratedFDeriv ℝ q (Ψ X'') z) X' (basisVec k) :=
    funext fun X' => (slowDir_aux q E Ψ h1 (basisVec k) X').2 z
  have hG : ContDiffAt ℝ ((p + 1 : ℕ) : WithTop ℕ∞) (fun X'' => iteratedFDeriv ℝ q (Ψ X'') z) X :=
    ((h.2.1 q hq z).of_le (by exact_mod_cast hp)).contDiffAt
  unfold srcJp
  rw [hin, iteratedFDeriv_fderiv_apply hG (basisVec k)]
  exact norm_jetApply_le p k _

/-- The fast derivative of a field shifts the fast order of the mixed jet. -/
theorem srcJp_fastPartial {sX sZ : ℕ} {Ψ : Vec 2 → Vec 2 → E} (h : RegBox sX sZ Ψ)
    (k : Fin 2) {p q : ℕ} (hp : p ≤ sX) (hq : q + 1 ≤ sZ) (X z : Vec 2) :
    srcJp (fastPartial k Ψ) X p q z ≤ srcJp Ψ X p (q + 1) z := by
  have hin : (fun X' => iteratedFDeriv ℝ q (fastPartial k Ψ X') z) =
      fun X' => jetApply q (basisVec k) (iteratedFDeriv ℝ (q + 1) (Ψ X') z) := by
    funext X'
    have hc : ContDiffAt ℝ ((q + 1 : ℕ) : WithTop ℕ∞) (Ψ X') z :=
      ((h.1 X').of_le (by exact_mod_cast hq)).contDiffAt
    exact iteratedFDeriv_fderiv_apply hc (basisVec k)
  have hJ : ContDiffAt ℝ (p : ℕ∞) (fun X' => iteratedFDeriv ℝ (q + 1) (Ψ X') z) X :=
    h.contDiffAt_slow hp hq X z
  unfold srcJp
  rw [hin]
  refine ((jetApply (F := E) q (basisVec k)).norm_iteratedFDeriv_comp_left hJ
    (by exact_mod_cast le_rfl)).trans ?_
  calc _ ≤ 1 * ‖iteratedFDeriv ℝ p (fun X' => iteratedFDeriv ℝ (q + 1) (Ψ X') z) X‖ := by
        gcongr; exact opNorm_jetApply_le q k
    _ = _ := one_mul _

/-- Slow multiplication by a scalar function. -/
theorem RegBox.mulX {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E} (hf : RegBox sX sZ f) {a : Vec 2 → ℝ}
    (ha : ContDiff ℝ (sX : ℕ∞) a) : RegBox sX sZ (fun X z => a X • f X z) := by
  refine ⟨fun X => contDiff_const.smul (hf.1 X), fun b hb z => ?_⟩
  have : (fun X => iteratedFDeriv ℝ b (fun z' => a X • f X z') z) =
      fun X => a X • iteratedFDeriv ℝ b (f X) z := funext fun X =>
    iteratedFDeriv_const_smul_apply' (a := a X) (hf.contDiffAt_fast hb X z)
  rw [this]
  exact ha.smul (hf.2 b hb z)

theorem srcJp_mulX {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E} (hf : RegBox sX sZ f) {a : Vec 2 → ℝ}
    {p q : ℕ} (ha : ContDiff ℝ (p : ℕ∞) a) (hp : p ≤ sX) (hq : q ≤ sZ) (X z : Vec 2) :
    srcJp (fun X z => a X • f X z) X p q z ≤
      ∑ i ∈ Finset.range (p + 1), (p.choose i : ℝ) * ‖iteratedFDeriv ℝ i a X‖ *
        srcJp f X (p - i) q z := by
  have hin : (fun X' => iteratedFDeriv ℝ q (fun z' => a X' • f X' z') z) =
      fun X' => a X' • iteratedFDeriv ℝ q (f X') z := funext fun X' =>
    iteratedFDeriv_const_smul_apply' (a := a X') (hf.contDiffAt_fast hq X' z)
  have hg : ContDiff ℝ (p : ℕ∞) (fun X' => iteratedFDeriv ℝ q (f X') z) :=
    (hf.2 q hq z).of_le (by exact_mod_cast hp)
  unfold srcJp
  rw [hin]
  exact norm_iteratedFDeriv_smul_le ha hg X (by exact_mod_cast le_rfl)

/-- The jets of the slow directional derivative of a scalar function. -/
theorem norm_iteratedFDeriv_slowDir_le {a : Vec 2 → ℝ} {i : ℕ}
    (ha : ContDiff ℝ ((i + 1 : ℕ) : ℕ∞) a) (k : Fin 2) (X : Vec 2) :
    ‖iteratedFDeriv ℝ i (fun Y => fderiv ℝ a Y (basisVec k)) X‖ ≤
      ‖iteratedFDeriv ℝ (i + 1) a X‖ := by
  rw [iteratedFDeriv_fderiv_apply (by exact_mod_cast ha.contDiffAt) (basisVec k)]
  exact norm_jetApply_le i k _

theorem contDiff_slowDir {a : Vec 2 → ℝ} {i : ℕ}
    (ha : ContDiff ℝ ((i + 1 : ℕ) : ℕ∞) a) (k : Fin 2) :
    ContDiff ℝ (i : ℕ∞) (fun Y => fderiv ℝ a Y (basisVec k)) :=
  (ha.fderiv_right (m := (i : ℕ∞)) (by norm_cast)).clm_apply contDiff_const

end Partial

section Sums
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem RegBox.sum {κ : Type*} (s : Finset κ) {sX sZ : ℕ} {f : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ s, RegBox sX sZ (f i)) : RegBox sX sZ (fun X z => ∑ i ∈ s, f i X z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (RegBox.zero (sX := sX) (sZ := sZ) (E := E))
  | insert a s ha ih =>
    have := (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using this

theorem RegBox.list_sum {κ : Type*} (l : List κ) {sX sZ : ℕ} {f : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ l, RegBox sX sZ (f i)) : RegBox sX sZ (fun X z => (l.map fun i => f i X z).sum) := by
  induction l with
  | nil => simpa using (RegBox.zero (sX := sX) (sZ := sZ) (E := E))
  | cons a l ih =>
    have := (h a List.mem_cons_self).add (ih fun i hi => h i (List.mem_cons_of_mem _ hi))
    simpa using this

theorem srcJp_sum {κ : Type*} (s : Finset κ) {sX sZ : ℕ} {f : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ s, RegBox sX sZ (f i)) {p q : ℕ} (hp : p ≤ sX) (hq : q ≤ sZ) (X z : Vec 2) :
    srcJp (fun X z => ∑ i ∈ s, f i X z) X p q z ≤ ∑ i ∈ s, srcJp (f i) X p q z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [srcJp_zero]
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 : RegBox sX sZ (fun X z => ∑ i ∈ s, f i X z) :=
      RegBox.sum s fun i hi => h i (Finset.mem_insert_of_mem hi)
    have := srcJp_add h1 h2 hp hq X z
    simp only [Finset.sum_insert ha]
    exact this.trans (by gcongr; exact ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem srcJp_list_sum {κ : Type*} (l : List κ) {sX sZ : ℕ} {f : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ l, RegBox sX sZ (f i)) {p q : ℕ} (hp : p ≤ sX) (hq : q ≤ sZ) (X z : Vec 2) :
    srcJp (fun X z => (l.map fun i => f i X z).sum) X p q z ≤
      (l.map fun i => srcJp (f i) X p q z).sum := by
  induction l with
  | nil => simp [srcJp_zero]
  | cons a l ih =>
    have h1 := h a List.mem_cons_self
    have h2 : RegBox sX sZ (fun X z => (l.map fun i => f i X z).sum) :=
      RegBox.list_sum l fun i hi => h i (List.mem_cons_of_mem _ hi)
    have := srcJp_add h1 h2 hp hq X z
    simp only [List.map_cons, List.sum_cons]
    exact this.trans (by gcongr; exact ih fun i hi => h i (List.mem_cons_of_mem _ hi))

end Sums
end

/-! Continuity in the fast variable of the mixed jets (`JCont`): the integrand of `srcPtJet` is
measurable, and this is stable under sums, constant multiples and slow-scalar multiples of
box-smooth fields. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuity in `z` of the mixed jet at `X`. -/
def JCont (Ψ : Vec 2 → Vec 2 → E) (X : Vec 2) (p q : ℕ) : Prop :=
  Continuous fun z => iteratedFDeriv ℝ p (fun X' => iteratedFDeriv ℝ q (Ψ X') z) X

theorem JCont.srcJp {Ψ : Vec 2 → Vec 2 → E} {X : Vec 2} {p q : ℕ} (h : JCont Ψ X p q) :
    Continuous (AVRegularity.QuietDecay.srcJp Ψ X p q) := h.norm

theorem JCont.aestronglyMeasurable {Ψ : Vec 2 → Vec 2 → E} {X : Vec 2} {p q : ℕ}
    (h : JCont Ψ X p q) (μ : Measure (Vec 2)) :
    AEStronglyMeasurable (AVRegularity.QuietDecay.srcJp Ψ X p q) μ :=
  h.srcJp.aestronglyMeasurable

theorem JCont.of_isBoxSmooth {sX sZ : ℕ} {Ψ : Vec 2 → Vec 2 → E} (h : IsBoxSmooth sX sZ Ψ)
    {p q : ℕ} (hp : p ≤ sX) (hq : q ≤ sZ) (X : Vec 2) : JCont Ψ X p q := by
  have hz : Continuous (fun z : Vec 2 => (X, z)) := continuous_const.prodMk continuous_id
  exact (h.2.2 p q hp hq).comp hz

theorem JCont.zero (X : Vec 2) (p q : ℕ) : JCont (fun (_ _ : Vec 2) => (0 : E)) X p q := by
  exact JCont.of_isBoxSmooth (sX := p) (sZ := q) IsBoxSmooth.zero le_rfl le_rfl X

theorem JCont.add {sX sZ : ℕ} {f g : Vec 2 → Vec 2 → E} (hf : RegBox sX sZ f)
    (hg : RegBox sX sZ g) {p q : ℕ} (hp : p ≤ sX) (hq : q ≤ sZ) {X : Vec 2}
    (h1 : JCont f X p q) (h2 : JCont g X p q) : JCont (fun X z => f X z + g X z) X p q := by
  unfold JCont at *
  have : (fun z => iteratedFDeriv ℝ p
      (fun X' => iteratedFDeriv ℝ q (fun z' => f X' z' + g X' z') z) X) = fun z =>
      iteratedFDeriv ℝ p (fun X' => iteratedFDeriv ℝ q (f X') z) X +
        iteratedFDeriv ℝ p (fun X' => iteratedFDeriv ℝ q (g X') z) X := by
    funext z
    have e1 : (fun X' => iteratedFDeriv ℝ q (fun z' => f X' z' + g X' z') z) =
        (fun X' => iteratedFDeriv ℝ q (f X') z) + fun X' => iteratedFDeriv ℝ q (g X') z :=
      funext fun X' => iteratedFDeriv_add_apply (hf.contDiffAt_fast hq X' z)
        (hg.contDiffAt_fast hq X' z)
    rw [e1]
    exact iteratedFDeriv_add_apply (hf.contDiffAt_slow hp hq X z) (hg.contDiffAt_slow hp hq X z)
  rw [this]
  exact h1.add h2

theorem JCont.const_smul {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E} (hf : RegBox sX sZ f) (c : ℝ)
    {p q : ℕ} (hp : p ≤ sX) (hq : q ≤ sZ) {X : Vec 2} (h1 : JCont f X p q) :
    JCont (fun X z => c • f X z) X p q := by
  unfold JCont at *
  have : (fun z => iteratedFDeriv ℝ p
      (fun X' => iteratedFDeriv ℝ q (fun z' => c • f X' z') z) X) = fun z =>
      c • iteratedFDeriv ℝ p (fun X' => iteratedFDeriv ℝ q (f X') z) X := by
    funext z
    have e1 : (fun X' => iteratedFDeriv ℝ q (fun z' => c • f X' z') z) =
        fun X' => c • iteratedFDeriv ℝ q (f X') z :=
      funext fun X' => iteratedFDeriv_const_smul_apply' (a := c) (hf.contDiffAt_fast hq X' z)
    rw [e1]
    exact iteratedFDeriv_const_smul_apply' (a := c) (hf.contDiffAt_slow hp hq X z)
  rw [this]
  exact h1.const_smul c

theorem JCont.sum {κ : Type*} (s : Finset κ) {sX sZ : ℕ} {f : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ s, RegBox sX sZ (f i)) {p q : ℕ} (hp : p ≤ sX) (hq : q ≤ sZ) {X : Vec 2}
    (hc : ∀ i ∈ s, JCont (f i) X p q) : JCont (fun X z => ∑ i ∈ s, f i X z) X p q := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using JCont.zero (E := E) X p q
  | insert a s ha ih =>
    have h2 : RegBox sX sZ (fun X z => ∑ i ∈ s, f i X z) :=
      RegBox.sum s fun i hi => h i (Finset.mem_insert_of_mem hi)
    have := JCont.add (h a (Finset.mem_insert_self a s)) h2 hp hq (hc a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
        (fun i hi => hc i (Finset.mem_insert_of_mem hi)))
    simpa [Finset.sum_insert ha] using this

theorem JCont.list_sum {κ : Type*} (l : List κ) {sX sZ : ℕ} {f : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ l, RegBox sX sZ (f i)) {p q : ℕ} (hp : p ≤ sX) (hq : q ≤ sZ) {X : Vec 2}
    (hc : ∀ i ∈ l, JCont (f i) X p q) :
    JCont (fun X z => (l.map fun i => f i X z).sum) X p q := by
  induction l with
  | nil => simpa using JCont.zero (E := E) X p q
  | cons a l ih =>
    have h2 : RegBox sX sZ (fun X z => (l.map fun i => f i X z).sum) :=
      RegBox.list_sum l fun i hi => h i (List.mem_cons_of_mem _ hi)
    have := JCont.add (h a List.mem_cons_self) h2 hp hq (hc a List.mem_cons_self)
      (ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
        (fun i hi => hc i (List.mem_cons_of_mem _ hi)))
    simpa using this

/-- The slow-scalar multiple of a box-smooth field has continuous mixed jets. -/
theorem JCont.mulX {sX sZ : ℕ} {G : Vec 2 → Vec 2 → E} (hG : IsBoxSmooth sX sZ G)
    {a : Vec 2 → ℝ} {p q : ℕ} (ha : ContDiff ℝ (p : ℕ∞) a) (hp : p ≤ sX) (hq : q ≤ sZ)
    (X : Vec 2) : JCont (fun X z => a X • G X z) X p q := by
  have hK : IsSlowSmooth p (fun X z => iteratedFDeriv ℝ q (G X) z) :=
    ((isBoxSmooth_iff.mp hG).2 q hq).mono hp
  have hc := IsSlowSmooth.clm_comp (G := ℝ →L[ℝ] (Vec 2 [×q]→L[ℝ] E)) hK
    (ContinuousLinearMap.smulRightL ℝ ℝ (Vec 2 [×q]→L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ))
  have hs := hc.clm_apply ha
  have hcont := hs.2 p le_rfl
  have hG' : RegBox sX sZ G := IsBoxSmooth.regBox hG
  unfold JCont
  have : (fun z => iteratedFDeriv ℝ p
      (fun X' => iteratedFDeriv ℝ q (fun z' => a X' • G X' z') z) X) =
      fun z => iteratedFDeriv ℝ p
        (fun X' => (ContinuousLinearMap.smulRightL ℝ ℝ (Vec 2 [×q]→L[ℝ] E)
          (ContinuousLinearMap.id ℝ ℝ) (iteratedFDeriv ℝ q (G X') z)) (a X')) X := by
    funext z
    congr 1
    funext X'
    rw [iteratedFDeriv_const_smul_apply' (a := a X') (hG'.contDiffAt_fast hq X' z)]
    rfl
  rw [this]
  have hz : Continuous (fun z : Vec 2 => (X, z)) := continuous_const.prodMk continuous_id
  exact hcont.comp hz
end

/-! The `ε`-coefficients of the word derivatives `D_ε^α Φ = ∑_{i ≤ |α|} ε^i W_i`. The coefficient
sequence is computed letter by letter: `W_i ↦ ∂_{z_k} W_i + √η ∂_{X_k} W_{i-1}` (`seqStep`). The
coefficient `W_i` is a sum of mixed partial derivatives of `Φ` with `i` slow and `|α| - i` fast
letters, weighted by `(√η)^i`; the mixed jets satisfy
`srcJp W_i p q ≤ 2^{|α|} srcJp Φ (p+i) (q+|α|-i)` when `√η ≤ 1`. -/

section
section Seq
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiability of a two-scale field in each variable separately. -/
def DiffF (Ψ : Vec 2 → Vec 2 → E) : Prop :=
  (∀ X, Differentiable ℝ (Ψ X)) ∧ ∀ z, Differentiable ℝ (fun X => Ψ X z)

theorem IsBoxSmooth.diffF {sX sZ : ℕ} {Ψ : Vec 2 → Vec 2 → E} (h : IsBoxSmooth sX sZ Ψ)
    (hX : 1 ≤ sX) (hZ : 1 ≤ sZ) : DiffF Ψ :=
  ⟨fun X => (h.1 X).differentiable (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hZ),
    fun z => (h.contDiff_slow z).differentiable (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hX)⟩

/-- One letter of the word on the `ε`-coefficient sequences. -/
def seqStep (η : ℝ) (k : Fin 2) (P : ℕ → Vec 2 → Vec 2 → E) : ℕ → Vec 2 → Vec 2 → E
  | 0 => fastPartial k (P 0)
  | j + 1 => fun X z => fastPartial k (P (j + 1)) X z + Real.sqrt η • slowPartial k (P j) X z

/-- The coefficient sequence of the constant family `ε ↦ Φ`. -/
def seqInit (Φ : Vec 2 → Vec 2 → E) : ℕ → Vec 2 → Vec 2 → E
  | 0 => Φ
  | _ + 1 => fun _ _ => 0

/-- The `ε`-coefficients of the word derivative along `l` (first letter applied first). -/
def seqWord (η : ℝ) (l : List (Fin 2)) (Φ : Vec 2 → Vec 2 → E) : ℕ → Vec 2 → Vec 2 → E :=
  l.foldl (fun P k => seqStep η k P) (seqInit Φ)

theorem seqWord_nil (η : ℝ) (Φ : Vec 2 → Vec 2 → E) : seqWord η [] Φ = seqInit Φ := rfl

theorem seqWord_concat (η : ℝ) (l : List (Fin 2)) (k : Fin 2) (Φ : Vec 2 → Vec 2 → E) :
    seqWord η (l ++ [k]) Φ = seqStep η k (seqWord η l Φ) := by
  simp [seqWord, List.foldl_append]

theorem seqWord_eq_zero (η : ℝ) (l : List (Fin 2)) (Φ : Vec 2 → Vec 2 → E) :
    ∀ i, l.length < i → seqWord η l Φ i = fun _ _ => 0 := by
  induction l using List.reverseRecOn with
  | nil =>
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by simp at hi; omega⟩
    rfl
  | append_singleton l k ih =>
    intro i hi
    rw [seqWord_concat]
    simp only [List.length_append, List.length_singleton] at hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    funext X z
    simp only [seqStep, ih (j + 1) (by omega), ih j (by omega), fastPartial_zero, slowPartial_zero,
      smul_zero, add_zero]

theorem isBoxSmooth_seqWord (η : ℝ) (l : List (Fin 2)) {Φ : Vec 2 → Vec 2 → E} {s : ℕ}
    (hΦ : IsBoxSmooth s s Φ) (hl : l.length ≤ s) :
    ∀ i, IsBoxSmooth (s - l.length) (s - l.length) (seqWord η l Φ i) := by
  induction l using List.reverseRecOn with
  | nil =>
    intro i
    cases i with
    | zero => simpa [seqWord_nil, seqInit] using hΦ
    | succ j => exact IsBoxSmooth.zero
  | append_singleton l k ih =>
    intro i
    simp only [List.length_append, List.length_singleton] at hl ⊢
    have ih' := ih (by omega)
    rw [seqWord_concat]
    have hf : ∀ i, IsBoxSmooth (s - (l.length + 1)) (s - (l.length + 1))
        (fastPartial k (seqWord η l Φ i)) := fun i => by
      have h1 : IsBoxSmooth (s - l.length) ((s - (l.length + 1)) + 1) (seqWord η l Φ i) :=
        (ih' i).mono le_rfl (by omega)
      exact (h1.fastPartial k).mono (by omega) le_rfl
    have hs : ∀ i, IsBoxSmooth (s - (l.length + 1)) (s - (l.length + 1))
        (slowPartial k (seqWord η l Φ i)) := fun i => by
      have h1 : IsBoxSmooth ((s - (l.length + 1)) + 1) (s - l.length) (seqWord η l Φ i) :=
        (ih' i).mono (by omega) le_rfl
      exact (h1.slowPartial k).mono le_rfl (by omega)
    cases i with
    | zero => simpa [seqStep] using hf 0
    | succ j => exact (hf (j + 1)).add ((hs j).const_smul _)

end Seq

section Poly
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fastPartial_fun_sum_smul {κ : Type*} (s : Finset κ) (c : κ → ℝ)
    (P : κ → Vec 2 → Vec 2 → E) (hP : ∀ i ∈ s, ∀ X, Differentiable ℝ (P i X)) (k : Fin 2)
    (X z : Vec 2) :
    fastPartial k (fun X z => ∑ i ∈ s, c i • P i X z) X z =
      ∑ i ∈ s, c i • fastPartial k (P i) X z := by
  have hd : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => c i • P i X z') z := fun i hi =>
    ((hP i hi X) z).const_smul (c i)
  simp only [fastPartial]
  rw [fderiv_fun_sum hd]
  simp only [sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [fderiv_fun_const_smul ((hP i hi X) z)]
  rfl

theorem slowPartial_fun_sum_smul {κ : Type*} (s : Finset κ) (c : κ → ℝ)
    (P : κ → Vec 2 → Vec 2 → E) (hP : ∀ i ∈ s, ∀ z, Differentiable ℝ (fun X => P i X z))
    (k : Fin 2) (X z : Vec 2) :
    slowPartial k (fun X z => ∑ i ∈ s, c i • P i X z) X z =
      ∑ i ∈ s, c i • slowPartial k (P i) X z := by
  have hd : ∀ i ∈ s, DifferentiableAt ℝ (fun X' => c i • P i X' z) X := fun i hi =>
    ((hP i hi z) X).const_smul (c i)
  simp only [slowPartial]
  rw [fderiv_fun_sum hd]
  simp only [sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [fderiv_fun_const_smul ((hP i hi z) X)]
  rfl

/-- `D_ε` of a polynomial in `ε`: the coefficients are updated by `seqStep`. -/
theorem dEps_poly (η ε : ℝ) (k : Fin 2) (n : ℕ) (c : ℕ → Vec 2 → Vec 2 → E)
    (hc : ∀ i, DiffF (c i)) (hz : c (n + 1) = fun _ _ => 0) :
    dEps η ε k (fun X z => ∑ i ∈ Finset.range (n + 1), ε ^ i • c i X z) =
      fun X z => ∑ i ∈ Finset.range (n + 2), ε ^ i • seqStep η k c i X z := by
  funext X z
  have hdz : ∀ i ∈ Finset.range (n + 1), ∀ X, Differentiable ℝ (c i X) := fun i _ X => (hc i).1 X
  have hdx : ∀ i ∈ Finset.range (n + 1), ∀ z, Differentiable ℝ (fun X => c i X z) :=
    fun i _ z => (hc i).2 z
  simp only [dEps]
  rw [fastPartial_fun_sum_smul _ _ _ hdz, slowPartial_fun_sum_smul _ _ _ hdx]
  have hA : ∑ i ∈ Finset.range (n + 2), ε ^ i • fastPartial k (c i) X z =
      ∑ i ∈ Finset.range (n + 1), ε ^ i • fastPartial k (c i) X z := by
    rw [Finset.sum_range_succ _ (n + 1), hz]; simp [fastPartial]
  have hB : ∑ i ∈ Finset.range (n + 2),
      ε ^ i • (match i with | 0 => (0 : E) | j + 1 => Real.sqrt η • slowPartial k (c j) X z) =
      (Real.sqrt η * ε) • ∑ i ∈ Finset.range (n + 1), ε ^ i • slowPartial k (c i) X z := by
    rw [Finset.sum_range_succ', Finset.smul_sum]
    simp only [smul_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    ring
  have hsplit : ∀ i, seqStep η k c i X z = fastPartial k (c i) X z +
      (match i with | 0 => (0 : E) | j + 1 => Real.sqrt η • slowPartial k (c j) X z) := by
    intro i; cases i <;> simp [seqStep]
  simp only [hsplit, smul_add, Finset.sum_add_distrib]
  rw [hA, hB]

theorem dEps_foldl_eq (η ε : ℝ) (l : List (Fin 2)) {Φ : Vec 2 → Vec 2 → E} {s : ℕ}
    (hΦ : IsBoxSmooth s s Φ) (hl : l.length ≤ s) :
    l.foldl (fun Ψ' i => dEps η ε i Ψ') Φ =
      fun X z => ∑ i ∈ Finset.range (l.length + 1), ε ^ i • seqWord η l Φ i X z := by
  induction l using List.reverseRecOn with
  | nil => funext X z; simp [seqWord_nil, seqInit]
  | append_singleton l k ih =>
    simp only [List.length_append, List.length_singleton] at hl ⊢
    rw [List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    have hc : ∀ i, DiffF (seqWord η l Φ i) := fun i =>
      IsBoxSmooth.diffF (isBoxSmooth_seqWord η l hΦ (by omega) i) (by omega) (by omega)
    rw [dEps_poly η ε k l.length _ hc (seqWord_eq_zero η l Φ _ (by omega))]
    simp only [seqWord_concat]

end Poly

section Jet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isBoxSmooth_fastPartial_step {m : ℕ} {f : Vec 2 → Vec 2 → E}
    (h : IsBoxSmooth (m + 1) (m + 1) f) (k : Fin 2) : IsBoxSmooth m m (fastPartial k f) :=
  (h.fastPartial k).mono (by omega) le_rfl

theorem isBoxSmooth_slowPartial_step {m : ℕ} {f : Vec 2 → Vec 2 → E}
    (h : IsBoxSmooth (m + 1) (m + 1) f) (k : Fin 2) : IsBoxSmooth m m (slowPartial k f) :=
  (h.slowPartial k).mono le_rfl (by omega)

end Jet
end

/-! Box-smooth variant of the word coefficients: for `Φ` box smooth of slow order `sX` and fast
order `sZ`, the coefficient `W_i` of a word of length `n` costs `i` slow orders and `n - i` fast
orders, and its mixed jets satisfy the same bound `2^n srcJp Φ (p+i) (q+n-i)` as soon as
`p + n ≤ sX` and `q + n ≤ sZ`. -/

section
section BoxSeq
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isBoxSmooth_seqWord_box (η : ℝ) (l : List (Fin 2)) {Φ : Vec 2 → Vec 2 → E} {sX sZ : ℕ}
    (hΦ : IsBoxSmooth sX sZ Φ) (hX : l.length ≤ sX) (hZ : l.length ≤ sZ) :
    ∀ i, IsBoxSmooth (sX - min i l.length) (sZ - (l.length - i)) (seqWord η l Φ i) := by
  induction l using List.reverseRecOn with
  | nil =>
    intro i
    cases i with
    | zero => simpa [seqWord_nil, seqInit] using hΦ
    | succ j => exact IsBoxSmooth.zero
  | append_singleton l k ih =>
    simp only [List.length_append, List.length_singleton] at hX hZ ⊢
    have ih' := ih (by omega) (by omega)
    have hz := seqWord_eq_zero η l Φ
    have hfast : ∀ j, IsBoxSmooth (sX - min j (l.length + 1)) (sZ - (l.length + 1 - j))
        (fastPartial k (seqWord η l Φ j)) := fun j => by
      by_cases hj : j ≤ l.length
      · have h := ih' j
        have e1 : min j l.length = min j (l.length + 1) := by omega
        have e2 : sZ - (l.length - j) = (sZ - (l.length + 1 - j)) + 1 := by omega
        rw [e1, e2] at h
        exact IsBoxSmooth.fastPartial h k
      · rw [hz j (by omega), fastPartial_zero]; exact IsBoxSmooth.zero
    have hslow : ∀ j, IsBoxSmooth (sX - min (j + 1) (l.length + 1))
        (sZ - (l.length + 1 - (j + 1))) (slowPartial k (seqWord η l Φ j)) := fun j => by
      by_cases hj : j ≤ l.length
      · have h := ih' j
        have e1 : sX - min j l.length = (sX - min (j + 1) (l.length + 1)) + 1 := by omega
        have e2 : sZ - (l.length - j) = sZ - (l.length + 1 - (j + 1)) := by omega
        rw [e1, e2] at h
        exact IsBoxSmooth.slowPartial h k
      · rw [hz j (by omega), slowPartial_zero]; exact IsBoxSmooth.zero
    intro i
    rw [seqWord_concat]
    cases i with
    | zero => simpa [seqStep] using hfast 0
    | succ j => exact (hfast (j + 1)).add ((hslow j).const_smul _)

theorem regBox_fast_of_box {a b p q : ℕ} {f : Vec 2 → Vec 2 → E} (h : IsBoxSmooth a b f)
    (k : Fin 2) (hp : p ≤ a) (hq : q + 1 ≤ b) : RegBox p q (fastPartial k f) :=
  IsBoxSmooth.regBox ((IsBoxSmooth.fastPartial (h.mono le_rfl hq) k).mono hp le_rfl)

theorem regBox_slow_of_box {a b p q : ℕ} {f : Vec 2 → Vec 2 → E} (h : IsBoxSmooth a b f)
    (k : Fin 2) (hp : p + 1 ≤ a) (hq : q ≤ b) : RegBox p q (slowPartial k f) :=
  IsBoxSmooth.regBox ((IsBoxSmooth.slowPartial (h.mono hp le_rfl) k).mono le_rfl hq)

/-- The mixed jets of the `ε`-coefficients of a word derivative, for box smooth fields. -/
theorem srcJp_seqWord_le_box (η : ℝ) (hη : Real.sqrt η ≤ 1) (l : List (Fin 2))
    {Φ : Vec 2 → Vec 2 → E} {sX sZ : ℕ} (hΦ : IsBoxSmooth sX sZ Φ) :
    ∀ (p q : ℕ), p + l.length ≤ sX → q + l.length ≤ sZ → ∀ (i : ℕ) (X z : Vec 2),
      srcJp (seqWord η l Φ i) X p q z ≤
        2 ^ l.length * srcJp Φ X (p + i) (q + l.length - i) z := by
  induction l using List.reverseRecOn with
  | nil =>
    intro p q _ _ i X z
    cases i with
    | zero => simp [seqWord_nil, seqInit]
    | succ j =>
      have : seqWord η [] Φ (j + 1) = fun _ _ => 0 := rfl
      rw [this, srcJp_zero]
      simp only [List.length_nil, pow_zero, one_mul]
      exact srcJp_nonneg _ _ _ _ _
  | append_singleton l k ih =>
    intro p q hp hq i X z
    simp only [List.length_append, List.length_singleton] at hp hq ⊢
    set n := l.length with hn
    have hc := isBoxSmooth_seqWord_box η l hΦ (by omega) (by omega)
    rw [seqWord_concat]
    by_cases hi : n + 1 < i
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have h1 : seqWord η l Φ (j + 1) = fun _ _ => 0 := seqWord_eq_zero η l Φ _ (by omega)
      have h2 : seqWord η l Φ j = fun _ _ => 0 := seqWord_eq_zero η l Φ _ (by omega)
      have h3 : seqStep η k (seqWord η l Φ) (j + 1) = fun _ _ => 0 := by
        funext X z
        simp [seqStep, h1, h2, fastPartial_zero, slowPartial_zero]
      rw [h3, srcJp_zero]
      exact mul_nonneg (by positivity) (srcJp_nonneg _ _ _ _ _)
    · have hA0 : 0 ≤ srcJp Φ X (p + i) (q + (n + 1) - i) z := srcJp_nonneg _ _ _ _ _
      cases i with
      | zero =>
        have e : q + 1 + n - 0 = q + (n + 1) - 0 := by omega
        have h1 := srcJp_fastPartial (IsBoxSmooth.regBox (hc 0)) k (p := p) (q := q)
          (by omega) (by omega) X z
        have h2 := ih p (q + 1) (by omega) (by omega) 0 X z
        rw [e] at h2
        show srcJp (fastPartial k (seqWord η l Φ 0)) X p q z ≤ _
        calc _ ≤ srcJp (seqWord η l Φ 0) X p (q + 1) z := h1
          _ ≤ 2 ^ n * srcJp Φ X (p + 0) (q + (n + 1) - 0) z := h2
          _ ≤ 2 ^ (n + 1) * srcJp Φ X (p + 0) (q + (n + 1) - 0) z := by
            rw [pow_succ]; nlinarith [pow_pos (two_pos (α := ℝ)) n]
      | succ j =>
        have rf := regBox_fast_of_box (hc (j + 1)) k (p := p) (q := q) (by omega) (by omega)
        have rs := regBox_slow_of_box (hc j) k (p := p) (q := q) (by omega) (by omega)
        have hadd := srcJp_add rf (rs.const_smul (Real.sqrt η)) (p := p) (q := q) le_rfl
          le_rfl X z
        have hsm := srcJp_const_smul rs (Real.sqrt η) (p := p) (q := q) le_rfl le_rfl X z
        have hF := srcJp_fastPartial (IsBoxSmooth.regBox (hc (j + 1))) k (p := p) (q := q)
          (by omega) (by omega) X z
        have hS := srcJp_slowPartial (hc j) k (p := p) (q := q) (by omega) (by omega) X z
        have eF : q + 1 + n - (j + 1) = q + (n + 1) - (j + 1) := by omega
        have eS : p + 1 + j = p + (j + 1) := by omega
        have eS' : q + n - j = q + (n + 1) - (j + 1) := by omega
        have h2F := ih p (q + 1) (by omega) (by omega) (j + 1) X z
        have h2S := ih (p + 1) q (by omega) (by omega) j X z
        rw [eF] at h2F
        rw [eS, eS'] at h2S
        have hη0 : |Real.sqrt η| ≤ 1 := by rw [abs_of_nonneg (Real.sqrt_nonneg η)]; exact hη
        show srcJp (fun X z => fastPartial k (seqWord η l Φ (j + 1)) X z +
          Real.sqrt η • slowPartial k (seqWord η l Φ j) X z) X p q z ≤ _
        calc _ ≤ _ := hadd
          _ = srcJp (fastPartial k (seqWord η l Φ (j + 1))) X p q z +
              |Real.sqrt η| * srcJp (slowPartial k (seqWord η l Φ j)) X p q z := by rw [hsm]
          _ ≤ 2 ^ n * srcJp Φ X (p + (j + 1)) (q + (n + 1) - (j + 1)) z +
              1 * (2 ^ n * srcJp Φ X (p + (j + 1)) (q + (n + 1) - (j + 1)) z) := by
            exact add_le_add (hF.trans h2F)
              (mul_le_mul hη0 (hS.trans h2S) (srcJp_nonneg _ _ _ _ _) zero_le_one)
          _ = 2 ^ (n + 1) * srcJp Φ X (p + (j + 1)) (q + (n + 1) - (j + 1)) z := by
            rw [pow_succ]; ring

end BoxSeq
end

/-! Linearity of the partial derivatives and of `D_ε` over finite and list sums, the product rule
for a slow scalar multiple of a continuous linear image, and the componentwise evaluation of
`D_ε` for `Pi`-valued fields. -/

section
section Linear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem DiffF.zero : DiffF (fun (_ _ : Vec 2) => (0 : E)) :=
  ⟨fun _ => differentiable_const _, fun _ => differentiable_const _⟩

theorem DiffF.add {f g : Vec 2 → Vec 2 → E} (hf : DiffF f) (hg : DiffF g) :
    DiffF (fun X z => f X z + g X z) :=
  ⟨fun X => (hf.1 X).add (hg.1 X), fun z => (hf.2 z).add (hg.2 z)⟩

theorem DiffF.const_smul {f : Vec 2 → Vec 2 → E} (hf : DiffF f) (c : ℝ) :
    DiffF (fun X z => c • f X z) :=
  ⟨fun X => (hf.1 X).const_smul c, fun z => (hf.2 z).const_smul c⟩

theorem DiffF.clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Vec 2 → Vec 2 → E}
    (hf : DiffF f) (L : E →L[ℝ] F) : DiffF (fun X z => L (f X z)) :=
  ⟨fun X => L.differentiable.comp (hf.1 X), fun z => L.differentiable.comp (hf.2 z)⟩

theorem DiffF.mulX {f : Vec 2 → Vec 2 → E} (hf : DiffF f) {a : Vec 2 → ℝ}
    (ha : Differentiable ℝ a) : DiffF (fun X z => a X • f X z) :=
  ⟨fun X => (differentiable_const _).smul (hf.1 X), fun z => ha.smul (hf.2 z)⟩

theorem DiffF.sum {κ : Type*} (s : Finset κ) {f : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ s, DiffF (f i)) : DiffF (fun X z => ∑ i ∈ s, f i X z) :=
  ⟨fun X => Differentiable.fun_sum fun i hi => (h i hi).1 X,
    fun z => Differentiable.fun_sum fun i hi => (h i hi).2 z⟩

theorem DiffF.list_sum {κ : Type*} (l : List κ) {f : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ l, DiffF (f i)) : DiffF (fun X z => (l.map fun i => f i X z).sum) := by
  induction l with
  | nil => simpa using (DiffF.zero (E := E))
  | cons a l ih =>
    have := (h a List.mem_cons_self).add (ih fun i hi => h i (List.mem_cons_of_mem _ hi))
    simpa using this

theorem fastPartial_add' {f g : Vec 2 → Vec 2 → E} (k : Fin 2) (X z : Vec 2)
    (hf : DifferentiableAt ℝ (f X) z) (hg : DifferentiableAt ℝ (g X) z) :
    fastPartial k (fun X z => f X z + g X z) X z = fastPartial k f X z + fastPartial k g X z := by
  simp only [fastPartial]
  rw [fderiv_fun_add hf hg]
  rfl

theorem slowPartial_add' {f g : Vec 2 → Vec 2 → E} (k : Fin 2) (X z : Vec 2)
    (hf : DifferentiableAt ℝ (fun X' => f X' z) X) (hg : DifferentiableAt ℝ (fun X' => g X' z) X) :
    slowPartial k (fun X z => f X z + g X z) X z = slowPartial k f X z + slowPartial k g X z := by
  simp only [slowPartial]
  rw [fderiv_fun_add hf hg]
  rfl

theorem fastPartial_finset_sum {κ : Type*} (s : Finset κ) {f : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ s, DiffF (f i)) (k : Fin 2) (X z : Vec 2) :
    fastPartial k (fun X z => ∑ i ∈ s, f i X z) X z = ∑ i ∈ s, fastPartial k (f i) X z := by
  have hd : ∀ i ∈ s, DifferentiableAt ℝ (f i X) z := fun i hi => (h i hi).1 X z
  simp only [fastPartial]
  rw [fderiv_fun_sum hd]
  simp [sum_apply]

theorem slowPartial_finset_sum {κ : Type*} (s : Finset κ) {f : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ s, DiffF (f i)) (k : Fin 2) (X z : Vec 2) :
    slowPartial k (fun X z => ∑ i ∈ s, f i X z) X z = ∑ i ∈ s, slowPartial k (f i) X z := by
  have hd : ∀ i ∈ s, DifferentiableAt ℝ (fun X' => f i X' z) X := fun i hi => (h i hi).2 z X
  simp only [slowPartial]
  rw [fderiv_fun_sum hd]
  simp [sum_apply]

theorem fastPartial_list_sum {κ : Type*} (l : List κ) {f : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ l, DiffF (f i)) (k : Fin 2) (X z : Vec 2) :
    fastPartial k (fun X z => (l.map fun i => f i X z).sum) X z =
      (l.map fun i => fastPartial k (f i) X z).sum := by
  induction l with
  | nil => simp [fastPartial]
  | cons a l ih =>
    have h1 := h a List.mem_cons_self
    have h2 := DiffF.list_sum l fun i hi => h i (List.mem_cons_of_mem _ hi)
    have := fastPartial_add' (f := f a) (g := fun X z => (l.map fun i => f i X z).sum) k X z
      (h1.1 X z) (h2.1 X z)
    simp only [List.map_cons, List.sum_cons]
    rw [this, ih fun i hi => h i (List.mem_cons_of_mem _ hi)]

theorem slowPartial_list_sum {κ : Type*} (l : List κ) {f : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ l, DiffF (f i)) (k : Fin 2) (X z : Vec 2) :
    slowPartial k (fun X z => (l.map fun i => f i X z).sum) X z =
      (l.map fun i => slowPartial k (f i) X z).sum := by
  induction l with
  | nil => simp [slowPartial]
  | cons a l ih =>
    have h1 := h a List.mem_cons_self
    have h2 := DiffF.list_sum l fun i hi => h i (List.mem_cons_of_mem _ hi)
    have := slowPartial_add' (f := f a) (g := fun X z => (l.map fun i => f i X z).sum) k X z
      (h1.2 z X) (h2.2 z X)
    simp only [List.map_cons, List.sum_cons]
    rw [this, ih fun i hi => h i (List.mem_cons_of_mem _ hi)]

theorem dEps_finset_sum {κ : Type*} (s : Finset κ) {f : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ s, DiffF (f i)) (η ε : ℝ) (k : Fin 2) (X z : Vec 2) :
    dEps η ε k (fun X z => ∑ i ∈ s, f i X z) X z = ∑ i ∈ s, dEps η ε k (f i) X z := by
  simp only [dEps, fastPartial_finset_sum s h, slowPartial_finset_sum s h, Finset.smul_sum,
    Finset.sum_add_distrib]

theorem dEps_list_sum {κ : Type*} (l : List κ) {f : κ → Vec 2 → Vec 2 → E}
    (h : ∀ i ∈ l, DiffF (f i)) (η ε : ℝ) (k : Fin 2) (X z : Vec 2) :
    dEps η ε k (fun X z => (l.map fun i => f i X z).sum) X z =
      (l.map fun i => dEps η ε k (f i) X z).sum := by
  simp only [dEps, fastPartial_list_sum l h, slowPartial_list_sum l h]
  clear h
  induction l with
  | nil => simp
  | cons a l ih => simp [smul_add, ih, add_add_add_comm]

/-- The partial derivatives commute with continuous linear maps. -/
theorem slowPartial_clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    {G : Vec 2 → Vec 2 → E} (i : Fin 2) (X z : Vec 2)
    (hG : DifferentiableAt ℝ (fun X' => G X' z) X) :
    slowPartial i (fun X' z' => L (G X' z')) X z = L (slowPartial i G X z) := by
  have := L.hasFDerivAt.comp X hG.hasFDerivAt
  simp only [slowPartial]
  have h2 : (fun X' => L (G X' z)) = L ∘ (fun X' => G X' z) := rfl
  rw [h2, this.fderiv]
  rfl

theorem fastPartial_clm' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    {G : Vec 2 → Vec 2 → E} (i : Fin 2) (X z : Vec 2) (hG : DifferentiableAt ℝ (G X) z) :
    fastPartial i (fun X' z' => L (G X' z')) X z = L (fastPartial i G X z) := by
  have := L.hasFDerivAt.comp z hG.hasFDerivAt
  simp only [fastPartial]
  have h2 : (fun z' => L (G X z')) = L ∘ G X := rfl
  rw [h2, this.fderiv]
  rfl

theorem dEps_clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    {G : Vec 2 → Vec 2 → E} (hG : DiffF G) (η ε : ℝ) (k : Fin 2) (X z : Vec 2) :
    dEps η ε k (fun X' z' => L (G X' z')) X z = L (dEps η ε k G X z) := by
  simp only [dEps, fastPartial_clm' L k X z (hG.1 X z), slowPartial_clm L k X z (hG.2 z X),
    map_add, map_smul]

/-- Product rule: fast derivative of a slow scalar multiple of a linear image. -/
theorem fastPartial_mulX_clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    (a : Vec 2 → ℝ) {W : Vec 2 → Vec 2 → E} (hW : DiffF W) (k : Fin 2) (X z : Vec 2) :
    fastPartial k (fun X z => a X • L (W X z)) X z = a X • L (fastPartial k W X z) := by
  have h1 : DifferentiableAt ℝ (fun z' => L (W X z')) z := L.differentiable.differentiableAt.comp z (hW.1 X z)
  simp only [fastPartial]
  rw [fderiv_fun_const_smul h1]
  have := fastPartial_clm' L k X z (hW.1 X z)
  simp only [fastPartial] at this
  simp only [smul_apply]
  rw [this]

/-- Product rule: slow derivative of a slow scalar multiple of a linear image. -/
theorem slowPartial_mulX_clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    {a : Vec 2 → ℝ} (ha : Differentiable ℝ a) {W : Vec 2 → Vec 2 → E} (hW : DiffF W) (k : Fin 2)
    (X z : Vec 2) :
    slowPartial k (fun X z => a X • L (W X z)) X z =
      fderiv ℝ a X (basisVec k) • L (W X z) + a X • L (slowPartial k W X z) := by
  have h1 : DifferentiableAt ℝ (fun X' => L (W X' z)) X :=
    L.differentiable.differentiableAt.comp X (hW.2 z X)
  simp only [slowPartial]
  rw [fderiv_fun_smul (ha X) h1]
  have := slowPartial_clm L k X z (hW.2 z X)
  simp only [slowPartial] at this
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [this]
  abel

end Linear
end

/-! One term of the source flux: `D_ε` of `a(X) · L(∑_i ε^i W_i)` is an explicit polynomial in `ε`
whose `ε^j` coefficient is `srcTerm η k a L W j`. -/

section
section Term
variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂]

/-- The `ε^j` coefficient of `D_{ε,k}` applied to `a(X) · L(∑_i ε^i W_i)`:
`a ∂_{z_k} L W_j + √η (∂_{X_k} a · L W_{j-1} + a · L ∂_{X_k} W_{j-1})`. -/
def srcTerm (η : ℝ) (k : Fin 2) (a : Vec 2 → ℝ) (L : E₁ →L[ℝ] E₂)
    (W : ℕ → Vec 2 → Vec 2 → E₁) : ℕ → Vec 2 → Vec 2 → E₂
  | 0 => fun X z => a X • L (fastPartial k (W 0) X z)
  | j + 1 => fun X z => a X • L (fastPartial k (W (j + 1)) X z) +
      Real.sqrt η • (fderiv ℝ a X (basisVec k) • L (W j X z) + a X • L (slowPartial k (W j) X z))

theorem seqStep_mulX_clm (η : ℝ) (k : Fin 2) {a : Vec 2 → ℝ} (ha : Differentiable ℝ a)
    (L : E₁ →L[ℝ] E₂) {W : ℕ → Vec 2 → Vec 2 → E₁} (hW : ∀ i, DiffF (W i)) (i : ℕ) :
    seqStep η k (fun i X z => a X • L (W i X z)) i = srcTerm η k a L W i := by
  cases i with
  | zero =>
    funext X z
    simp only [seqStep, srcTerm]
    exact fastPartial_mulX_clm L a (hW 0) k X z
  | succ j =>
    funext X z
    simp only [seqStep, srcTerm]
    rw [fastPartial_mulX_clm L a (hW (j + 1)) k X z, slowPartial_mulX_clm L ha (hW j) k X z]

theorem srcTerm_eq_zero (η : ℝ) (k : Fin 2) (a : Vec 2 → ℝ) (L : E₁ →L[ℝ] E₂)
    {W : ℕ → Vec 2 → Vec 2 → E₁} {n : ℕ} (hz : ∀ i, n < i → W i = fun _ _ => 0) {j : ℕ}
    (hj : n + 1 < j) : srcTerm η k a L W j = fun _ _ => 0 := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  funext X z
  simp [srcTerm, hz (j' + 1) (by omega), hz j' (by omega), fastPartial_zero, slowPartial_zero]

theorem dEps_term_poly (η ε : ℝ) (k : Fin 2) {a : Vec 2 → ℝ} (ha : Differentiable ℝ a)
    (L : E₁ →L[ℝ] E₂) (n : ℕ) {W : ℕ → Vec 2 → Vec 2 → E₁} (hW : ∀ i, DiffF (W i))
    (hz : ∀ i, n < i → W i = fun _ _ => 0) {N : ℕ} (hN : n + 2 ≤ N) :
    dEps η ε k (fun X z => a X • L (∑ i ∈ Finset.range (n + 1), ε ^ i • W i X z)) =
      fun X z => ∑ i ∈ Finset.range N, ε ^ i • srcTerm η k a L W i X z := by
  have e1 : (fun X z => a X • L (∑ i ∈ Finset.range (n + 1), ε ^ i • W i X z)) =
      fun X z => ∑ i ∈ Finset.range (n + 1), ε ^ i • (a X • L (W i X z)) := by
    funext X z
    simp only [map_sum, map_smul, Finset.smul_sum, smul_comm (a X)]
  have hg : ∀ i, DiffF (fun X z => a X • L (W i X z)) := fun i => ((hW i).clm L).mulX ha
  have hz' : (fun X z => a X • L (W (n + 1) X z)) = fun _ _ => 0 := by
    funext X z; simp [hz (n + 1) (by omega)]
  rw [e1, dEps_poly η ε k n (fun i X z => a X • L (W i X z)) hg hz']
  funext X z
  have e2 : ∀ i, seqStep η k (fun i X z => a X • L (W i X z)) i X z = srcTerm η k a L W i X z :=
    fun i => by rw [seqStep_mulX_clm η k ha L hW i]
  simp only [e2]
  refine Finset.sum_subset (Finset.range_subset_range.mpr hN) fun i hi hni => ?_
  have : n + 1 < i := by
    simp only [Finset.mem_range] at hi hni; omega
  rw [srcTerm_eq_zero η k a L hz this]
  simp

end Term
end

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.QuietDecay

/-! Words of `D_ε` on `Pi`-valued fields in components, and the explicit flux terms. -/

section Word
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem seqStep_clm (η : ℝ) (k : Fin 2) (L : E →L[ℝ] F) {P : ℕ → Vec 2 → Vec 2 → E}
    (hP : ∀ i, DiffF (P i)) (i : ℕ) :
    seqStep η k (fun i X z => L (P i X z)) i = fun X z => L (seqStep η k P i X z) := by
  cases i with
  | zero =>
    funext X z
    simp only [seqStep]
    exact fastPartial_clm' L k X z ((hP 0).1 X z)
  | succ j =>
    funext X z
    simp only [seqStep, map_add, map_smul]
    rw [fastPartial_clm' L k X z ((hP (j + 1)).1 X z), slowPartial_clm L k X z ((hP j).2 z X)]

theorem seqWord_clm (η : ℝ) (L : E →L[ℝ] F) (l : List (Fin 2)) {Φ : Vec 2 → Vec 2 → E} {s : ℕ}
    (hΦ : IsBoxSmooth s s Φ) (hl : l.length ≤ s) :
    ∀ i, seqWord η l (fun X z => L (Φ X z)) i = fun X z => L (seqWord η l Φ i X z) := by
  induction l using List.reverseRecOn with
  | nil =>
    intro i
    cases i with
    | zero => rfl
    | succ j => funext X z; simp [seqWord_nil, seqInit]
  | append_singleton l k ih =>
    intro i
    simp only [List.length_append, List.length_singleton] at hl
    have ih' : seqWord η l (fun X z => L (Φ X z)) =
        fun i X z => L (seqWord η l Φ i X z) := funext fun i => ih (by omega) i
    rw [seqWord_concat, seqWord_concat, ih']
    have hP : ∀ i, DiffF (seqWord η l Φ i) := fun i =>
      IsBoxSmooth.diffF (isBoxSmooth_seqWord η l hΦ (by omega) i) (by omega) (by omega)
    exact seqStep_clm η k L hP i

end Word

section Components
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The `ε`-coefficients of the word derivative `D_ε^α` of the `u`-component of `Φ`. -/
def srcW (η : ℝ) (u : ι) {m : ℕ} (α : DerivativeWord2 m) (Φ : Vec 2 → Vec 2 → ∀ i, h i) :
    ℕ → Vec 2 → Vec 2 → h u :=
  seqWord η (List.ofFn α) (fun X z => Φ X z u)

omit [Fintype ι] in
theorem srcW_eq_zero (η : ℝ) (u : ι) {m : ℕ} (α : DerivativeWord2 m)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) {i : ℕ} (hi : m < i) :
    srcW η u α Φ i = fun _ _ => 0 := by
  have := seqWord_eq_zero η (List.ofFn α) (fun X z => Φ X z u) i (by simpa using hi)
  exact this

theorem isBoxSmooth_srcW (η : ℝ) (u : ι) {m : ℕ} (α : DerivativeWord2 m)
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {s : ℕ} (hΦ : IsBoxSmooth s s Φ) (hm : m ≤ s) (i : ℕ) :
    IsBoxSmooth (s - m) (s - m) (srcW η u α Φ i) := by
  have h1 : IsBoxSmooth s s (fun X z => Φ X z u) :=
    hΦ.map_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) u)
  have := isBoxSmooth_seqWord η (List.ofFn α) h1 (by simpa using hm) i
  unfold srcW
  simpa using this

theorem diffF_srcW (η : ℝ) (u : ι) {m : ℕ} (α : DerivativeWord2 m)
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {s : ℕ} (hΦ : IsBoxSmooth s s Φ) (hm : m + 1 ≤ s) (i : ℕ) :
    DiffF (srcW η u α Φ i) :=
  IsBoxSmooth.diffF (isBoxSmooth_srcW η u α hΦ (by omega) i) (by omega) (by omega)

/-- The word derivative of a component, as a polynomial in `ε`. -/
theorem dEpsWord_apply_eq (η ε : ℝ) {m : ℕ} (α : DerivativeWord2 m)
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {s : ℕ} (hΦ : IsBoxSmooth s s Φ) (hm : m ≤ s) (u : ι)
    (X z : Vec 2) :
    dEpsWord η ε α Φ X z u =
      ∑ i ∈ Finset.range (m + 1), ε ^ i • srcW η u α Φ i X z := by
  have h1 := dEps_foldl_eq η ε (List.ofFn α) hΦ (by simpa using hm)
  have h2 := congrFun (congrFun h1 X) z
  simp only [List.length_ofFn] at h2
  have h3 : dEpsWord η ε α Φ X z = _ := h2
  rw [h3]
  have h4 : seqWord η (List.ofFn α) (fun X z => (ContinuousLinearMap.proj (R := ℝ) (φ := h) u)
      (Φ X z)) = _ := funext fun i => seqWord_clm η (ContinuousLinearMap.proj (R := ℝ) (φ := h) u)
    (List.ofFn α) hΦ (by simpa using hm) i
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h5 := congrFun (congrFun (congrFun h4 i) X) z
  simp only [ContinuousLinearMap.proj_apply] at h5
  simp only [srcW]
  rw [h5]

end Components

end AVRegularity.QuietDecay
end
