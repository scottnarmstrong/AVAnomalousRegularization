-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.TimeIntegration
import AVRegularity.CycleComparison.Residual.Jets.Lift
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Order.CompletePartialOrder
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.TailJets

@[expose] public noncomputable section

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! Pointwise mixed jets `ptJet Ψ X p q` of a two-scale field `Ψ(X,z)`: the cell `L²` norm (in the
fast variable) of the `p`-th slow derivative at `X` of the `q`-th fast derivative.  This file sets up
the definition, the continuity of the jet in the fast variable for box smooth fields, the transfer of
pointwise (in `z`) inequalities to `ptJet`, and the linear calculus (sums, scalar multiples,
continuous linear maps). -/

section
section Def

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `p`-th slow jet at `X` of the `q`-th fast jet at `z`, as a multilinear map. -/
def jetAt (Ψ : Vec 2 → Vec 2 → E) (X z : Vec 2) (p q : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin p => Vec 2)
      (ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) E) :=
  iteratedFDeriv ℝ p (fun X' => iteratedFDeriv ℝ q (Ψ X') z) X

/-- Cell `L²` norm of the `p`-th slow derivative of the `q`-th fast derivative at the slow point
`X`. -/
def ptJet (Ψ : Vec 2 → Vec 2 → E) (X : Vec 2) (p q : ℕ) : ℝ≥0∞ :=
  eLpNorm (fun z => ‖iteratedFDeriv ℝ p (fun X' => iteratedFDeriv ℝ q (Ψ X') z) X‖) 2
    (volume.restrict AVenhance.unitCube)

theorem ptJet_eq (Ψ : Vec 2 → Vec 2 → E) (X : Vec 2) (p q : ℕ) :
    ptJet Ψ X p q =
      eLpNorm (fun z => ‖jetAt Ψ X z p q‖) 2 (volume.restrict AVenhance.unitCube) := rfl

/-- The jet is continuous in the fast variable for box smooth fields. -/
theorem _root_.AVRegularity.IsBoxSmooth.continuous_jetAt {sX sZ : ℕ} {Ψ : Vec 2 → Vec 2 → E}
    (hΨ : IsBoxSmooth sX sZ Ψ) {p q : ℕ} (hp : p ≤ sX) (hq : q ≤ sZ) (X : Vec 2) :
    Continuous fun z => jetAt Ψ X z p q :=
  (hΨ.2.2 p q hp hq).comp (Continuous.prodMk_right X)

/-- The norm of the jet is continuous in the fast variable for box smooth fields. -/
theorem _root_.AVRegularity.IsBoxSmooth.continuous_norm_jetAt {sX sZ : ℕ} {Ψ : Vec 2 → Vec 2 → E}
    (hΨ : IsBoxSmooth sX sZ Ψ) {p q : ℕ} (hp : p ≤ sX) (hq : q ≤ sZ) (X : Vec 2) :
    Continuous fun z => ‖jetAt Ψ X z p q‖ :=
  Continuous.norm (f := fun z => jetAt Ψ X z p q) (by exact hΨ.continuous_jetAt hp hq X)

end Def

/-- Transfer of a pointwise inequality `‖f z‖ ≤ ∑ c_k J_k z` to `L²` norms. -/
theorem eLpNorm_le_sum_mul_real {α V κ : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup V] {f : α → V} (hf : AEStronglyMeasurable f μ)
    (s : Finset κ) {J : κ → α → ℝ} (c : κ → ℝ)
    (hc : ∀ k ∈ s, 0 ≤ c k) (h : ∀ z, ‖f z‖ ≤ ∑ k ∈ s, c k * J k z) :
    eLpNorm f 2 μ ≤ ∑ k ∈ s, ENNReal.ofReal (c k) * eLpNorm (J k) 2 μ := by
  have h1 : eLpNorm f 2 μ ≤ eLpNorm (∑ k ∈ s, fun z => c k * J k z) 2 μ := by
    refine eLpNorm_mono_real hf fun z => ?_
    simpa [Finset.sum_apply] using h z
  refine h1.trans ((eLpNorm_sum_le (by norm_num)).trans (Finset.sum_le_sum fun k hk => ?_))
  have e : (fun z => c k * J k z) = c k • J k := rfl
  rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal (hc k hk)]

section Transfer

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']

/-- Transfer of a pointwise bound on jets to `ptJet`. -/
theorem ptJet_le_sum {Φ : Vec 2 → Vec 2 → E} {X : Vec 2} {p q : ℕ}
    (hΦ : Continuous fun z => ‖jetAt Φ X z p q‖) {κ : Type*} (s : Finset κ)
    {Ψ : κ → Vec 2 → Vec 2 → E'} {p' q' : κ → ℕ} (c : κ → ℝ)
    (hc : ∀ k ∈ s, 0 ≤ c k)
    (h : ∀ z, ‖jetAt Φ X z p q‖ ≤ ∑ k ∈ s, c k * ‖jetAt (Ψ k) X z (p' k) (q' k)‖) :
    ptJet Φ X p q ≤ ∑ k ∈ s, ENNReal.ofReal (c k) * ptJet (Ψ k) X (p' k) (q' k) := by
  have hmeas : AEStronglyMeasurable (fun z => ‖jetAt Φ X z p q‖)
      (volume.restrict AVenhance.unitCube) := hΦ.aestronglyMeasurable
  have h1 := eLpNorm_le_sum_mul_real (μ := volume.restrict AVenhance.unitCube) hmeas s
    (J := fun k z => ‖jetAt (Ψ k) X z (p' k) (q' k)‖) c hc (fun z => (norm_norm (jetAt Φ X z p q)).le.trans (h z))
  simpa [ptJet_eq] using h1

/-- Single-term version of `ptJet_le_sum`. -/
theorem ptJet_le_mul {Φ : Vec 2 → Vec 2 → E} {Ψ : Vec 2 → Vec 2 → E'} {X : Vec 2}
    {p q p' q' : ℕ} (hΦ : Continuous fun z => ‖jetAt Φ X z p q‖) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ z, ‖jetAt Φ X z p q‖ ≤ c * ‖jetAt Ψ X z p' q'‖) :
    ptJet Φ X p q ≤ ENNReal.ofReal c * ptJet Ψ X p' q' := by
  have hmeas : AEStronglyMeasurable (fun z => ‖jetAt Φ X z p q‖)
      (volume.restrict AVenhance.unitCube) := hΦ.aestronglyMeasurable
  have h1 : eLpNorm (fun z => ‖jetAt Φ X z p q‖) 2 (volume.restrict AVenhance.unitCube) ≤
      eLpNorm (c • fun z => ‖jetAt Ψ X z p' q'‖) 2 (volume.restrict AVenhance.unitCube) :=
    eLpNorm_mono_real hmeas fun z => (norm_norm (jetAt Φ X z p q)).le.trans (h z)
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hc] at h1
  exact h1

end Transfer
end

/-! Linear calculus of the pointwise mixed jets: continuous linear maps, scalar multiples, sums
and differences. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem norm_compCMML_le (n : ℕ) (L : E →L[ℝ] F) :
    ‖ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Vec 2) E F L‖ ≤
      ‖L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun c => by
    rw [ContinuousLinearMap.compContinuousMultilinearMapL_apply]
    exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le L c

/-- The fast jet of a continuous linear image. -/
theorem iteratedFDeriv_fast_clm {Ψ : Vec 2 → Vec 2 → E} {sZ q : ℕ} (hZ : ∀ X, ContDiff ℝ (sZ : ℕ∞) (Ψ X))
    (hq : q ≤ sZ) (L : E →L[ℝ] F) (X z : Vec 2) :
    iteratedFDeriv ℝ q (fun z' => L (Ψ X z')) z =
      ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin q => Vec 2) E F L
        (iteratedFDeriv ℝ q (Ψ X) z) :=
  L.iteratedFDeriv_comp_left ((hZ X).contDiffAt) (by exact_mod_cast hq)

theorem norm_jetAt_clm_le {sX sZ p q : ℕ} {Ψ : Vec 2 → Vec 2 → E} (hΨ : IsBoxSmooth sX sZ Ψ)
    (hp : p ≤ sX) (hq : q ≤ sZ) (L : E →L[ℝ] F) (X z : Vec 2) :
    ‖jetAt (fun X z => L (Ψ X z)) X z p q‖ ≤ ‖L‖ * ‖jetAt Ψ X z p q‖ := by
  have e : (fun X' => iteratedFDeriv ℝ q (fun z' => L (Ψ X' z')) z) =
      (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin q => Vec 2) E F L) ∘
        (fun X' => iteratedFDeriv ℝ q (Ψ X') z) :=
    funext fun X' => iteratedFDeriv_fast_clm hΨ.1 hq L X' z
  have hc : ContDiffAt ℝ (p : ℕ∞) (fun X' => iteratedFDeriv ℝ q (Ψ X') z) X :=
    ((hΨ.2.1 q hq z).of_le (by exact_mod_cast hp)).contDiffAt
  unfold jetAt
  rw [e]
  exact (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ hc (by exact_mod_cast le_rfl)).trans
    (mul_le_mul_of_nonneg_right (norm_compCMML_le q L) (norm_nonneg _))

/-- Continuous linear maps: `ptJet (L ∘ Ψ) ≤ ‖L‖ ptJet Ψ`. -/
theorem ptJet_clm_le {sX sZ : ℕ} {Ψ : Vec 2 → Vec 2 → E} (hΨ : IsBoxSmooth sX sZ Ψ) {p q : ℕ}
    (hp : p ≤ sX) (hq : q ≤ sZ) (L : E →L[ℝ] F) (X : Vec 2) :
    ptJet (fun X z => L (Ψ X z)) X p q ≤ ‖L‖ₑ * ptJet Ψ X p q := by
  rw [← ofReal_norm]
  exact ptJet_le_mul ((hΨ.clm_comp L).continuous_norm_jetAt hp hq X) _ (norm_nonneg _)
    (norm_jetAt_clm_le hΨ hp hq L X)

/-- Scalar multiples. -/
theorem ptJet_const_smul_le {sX sZ : ℕ} {Ψ : Vec 2 → Vec 2 → E} (hΨ : IsBoxSmooth sX sZ Ψ)
    {p q : ℕ} (hp : p ≤ sX) (hq : q ≤ sZ) (c : ℝ) (X : Vec 2) :
    ptJet (fun X z => c • Ψ X z) X p q ≤ ‖c‖ₑ * ptJet Ψ X p q := by
  have h := ptJet_clm_le hΨ hp hq (c • ContinuousLinearMap.id ℝ E) X
  refine h.trans (mul_le_mul_left ?_ _)
  rw [← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  refine (norm_smul_le c (ContinuousLinearMap.id ℝ E)).trans ?_
  simpa using mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
    (norm_nonneg c)

/-- Negation. -/
theorem ptJet_neg_le {sX sZ : ℕ} {Ψ : Vec 2 → Vec 2 → E} (hΨ : IsBoxSmooth sX sZ Ψ)
    {p q : ℕ} (hp : p ≤ sX) (hq : q ≤ sZ) (X : Vec 2) :
    ptJet (fun X z => -Ψ X z) X p q ≤ ptJet Ψ X p q := by
  have h := ptJet_const_smul_le hΨ hp hq (-1) X
  simpa using h

/-- The jet of a finite sum is the sum of the jets. -/
theorem jetAt_sum {κ : Type*} (s : Finset κ) {Ψ : κ → Vec 2 → Vec 2 → E} {sX sZ p q : ℕ}
    (hΨ : ∀ k ∈ s, IsBoxSmooth sX sZ (Ψ k)) (hp : p ≤ sX) (hq : q ≤ sZ) (X z : Vec 2) :
    jetAt (fun X z => ∑ k ∈ s, Ψ k X z) X z p q = ∑ k ∈ s, jetAt (Ψ k) X z p q := by
  have e : (fun X' => iteratedFDeriv ℝ q (fun z' => ∑ k ∈ s, Ψ k X' z') z) =
      fun X' => ∑ k ∈ s, iteratedFDeriv ℝ q (Ψ k X') z := by
    funext X'
    exact iteratedFDeriv_fun_sum_apply (f := fun k z' => Ψ k X' z') (u := s) (n := q) (x := z)
      fun k hk => ((hΨ k hk).1 X').contDiffAt.of_le (by exact_mod_cast hq)
  unfold jetAt
  rw [e]
  exact iteratedFDeriv_fun_sum_apply (f := fun k X' => iteratedFDeriv ℝ q (Ψ k X') z)
    (u := s) (n := p) (x := X) fun k hk =>
      (((hΨ k hk).2.1 q hq z).of_le (by exact_mod_cast hp)).contDiffAt

/-- Finite sums. -/
theorem ptJet_sum_le {κ : Type*} (s : Finset κ) {Ψ : κ → Vec 2 → Vec 2 → E} {sX sZ p q : ℕ}
    (hΨ : ∀ k ∈ s, IsBoxSmooth sX sZ (Ψ k)) (hp : p ≤ sX) (hq : q ≤ sZ) (X : Vec 2) :
    ptJet (fun X z => ∑ k ∈ s, Ψ k X z) X p q ≤ ∑ k ∈ s, ptJet (Ψ k) X p q := by
  have h := ptJet_le_sum (p' := fun _ => p) (q' := fun _ => q)
    ((IsBoxSmooth.sum s hΨ).continuous_norm_jetAt hp hq X) s (fun _ => (1 : ℝ))
    (fun _ _ => zero_le_one) (Ψ := Ψ) (fun z => by
      rw [jetAt_sum s hΨ hp hq X z]
      simpa using norm_sum_le s fun k => jetAt (Ψ k) X z p q)
  simpa using h

theorem ptJet_add_le {sX sZ p q : ℕ} {Ψ₁ Ψ₂ : Vec 2 → Vec 2 → E} (h₁ : IsBoxSmooth sX sZ Ψ₁)
    (h₂ : IsBoxSmooth sX sZ Ψ₂) (hp : p ≤ sX) (hq : q ≤ sZ) (X : Vec 2) :
    ptJet (fun X z => Ψ₁ X z + Ψ₂ X z) X p q ≤ ptJet Ψ₁ X p q + ptJet Ψ₂ X p q := by
  have h := ptJet_sum_le (Finset.univ : Finset (Fin 2)) (Ψ := ![Ψ₁, Ψ₂])
    (fun k _ => by fin_cases k <;> simpa) hp hq X
  simpa [Fin.sum_univ_two] using h

theorem ptJet_sub_le {sX sZ p q : ℕ} {Ψ₁ Ψ₂ : Vec 2 → Vec 2 → E} (h₁ : IsBoxSmooth sX sZ Ψ₁)
    (h₂ : IsBoxSmooth sX sZ Ψ₂) (hp : p ≤ sX) (hq : q ≤ sZ) (X : Vec 2) :
    ptJet (fun X z => Ψ₁ X z - Ψ₂ X z) X p q ≤ ptJet Ψ₁ X p q + ptJet Ψ₂ X p q := by
  have h := ptJet_add_le h₁ h₂.neg hp hq X
  have h' := ptJet_neg_le h₂ hp hq X
  simp only [← sub_eq_add_neg] at h
  exact h.trans (add_le_add le_rfl h')
end

/-! The partial derivatives shift the orders of the pointwise mixed jets by one:
`ptJet (slowPartial i Ψ) X p q ≤ ptJet Ψ X (p+1) q` and
`ptJet (fastPartial i Ψ) X p q ≤ ptJet Ψ X p (q+1)`. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_jetApply_le_self (b : ℕ) (k : Fin 2)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin (b + 1) => Vec 2) E) :
    ‖jetApply b (basisVec k) f‖ ≤ ‖f‖ := by
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

theorem opNorm_jetApply_le_one (b : ℕ) (k : Fin 2) :
    ‖(jetApply b (basisVec k) : ContinuousMultilinearMap ℝ (fun _ : Fin (b + 1) => Vec 2) E →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin b => Vec 2) E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [one_mul]; exact norm_jetApply_le_self b k f

/-- Pointwise: the slow partial shifts the slow order. -/
theorem norm_jetAt_slowPartial_le {sX sZ : ℕ} {Ψ : Vec 2 → Vec 2 → E} (h : IsBoxSmooth sX sZ Ψ)
    (k : Fin 2) {p q : ℕ} (hp : p + 1 ≤ sX) (hq : q ≤ sZ) (X z : Vec 2) :
    ‖jetAt (slowPartial k Ψ) X z p q‖ ≤ ‖jetAt Ψ X z (p + 1) q‖ := by
  have h1 : IsBoxSmooth 1 q Ψ := h.mono (by omega) hq
  have hin : (fun X' => iteratedFDeriv ℝ q (slowPartial k Ψ X') z) =
      fun X' => fderiv ℝ (fun X'' => iteratedFDeriv ℝ q (Ψ X'') z) X' (basisVec k) :=
    funext fun X' => (slowDir_aux q E Ψ h1 (basisVec k) X').2 z
  have hG : ContDiffAt ℝ ((p + 1 : ℕ) : WithTop ℕ∞) (fun X'' => iteratedFDeriv ℝ q (Ψ X'') z) X :=
    ((h.2.1 q hq z).of_le (by exact_mod_cast hp)).contDiffAt
  unfold jetAt
  rw [hin, iteratedFDeriv_fderiv_apply hG (basisVec k)]
  exact norm_jetApply_le_self p k _

/-- The slow partial derivative shifts the slow order of `ptJet`. -/
theorem ptJet_slowPartial_le {sX sZ : ℕ} {Ψ : Vec 2 → Vec 2 → E} (h : IsBoxSmooth sX sZ Ψ)
    (k : Fin 2) {p q : ℕ} (hp : p + 1 ≤ sX) (hq : q ≤ sZ) (X : Vec 2) :
    ptJet (slowPartial k Ψ) X p q ≤ ptJet Ψ X (p + 1) q := by
  have hs : IsBoxSmooth p sZ (slowPartial k Ψ) := (h.mono hp le_rfl).slowPartial k
  have := ptJet_le_mul (Φ := slowPartial k Ψ) (Ψ := Ψ) (p := p) (q := q) (p' := p + 1) (q' := q)
    (hs.continuous_norm_jetAt le_rfl hq X) 1 zero_le_one
    (fun z => by simpa using norm_jetAt_slowPartial_le h k hp hq X z)
  simpa using this

/-- Pointwise: the fast partial shifts the fast order. -/
theorem norm_jetAt_fastPartial_le {sX sZ : ℕ} {Ψ : Vec 2 → Vec 2 → E} (h : IsBoxSmooth sX sZ Ψ)
    (k : Fin 2) {p q : ℕ} (hp : p ≤ sX) (hq : q + 1 ≤ sZ) (X z : Vec 2) :
    ‖jetAt (fastPartial k Ψ) X z p q‖ ≤ ‖jetAt Ψ X z p (q + 1)‖ := by
  have hin : (fun X' => iteratedFDeriv ℝ q (fastPartial k Ψ X') z) =
      fun X' => jetApply q (basisVec k) (iteratedFDeriv ℝ (q + 1) (Ψ X') z) := by
    funext X'
    have hc : ContDiffAt ℝ ((q + 1 : ℕ) : WithTop ℕ∞) (Ψ X') z :=
      ((h.1 X').of_le (by exact_mod_cast hq)).contDiffAt
    exact iteratedFDeriv_fderiv_apply hc (basisVec k)
  have hJ : ContDiffAt ℝ (p : ℕ∞) (fun X' => iteratedFDeriv ℝ (q + 1) (Ψ X') z) X :=
    ((h.2.1 (q + 1) hq z).of_le (by exact_mod_cast hp)).contDiffAt
  unfold jetAt
  rw [hin]
  refine ((jetApply (F := E) q (basisVec k)).norm_iteratedFDeriv_comp_left hJ
    (by exact_mod_cast le_rfl)).trans ?_
  calc _ ≤ 1 * ‖iteratedFDeriv ℝ p (fun X' => iteratedFDeriv ℝ (q + 1) (Ψ X') z) X‖ := by
        gcongr; exact opNorm_jetApply_le_one q k
    _ = _ := one_mul _

/-- The fast partial derivative shifts the fast order of `ptJet`. -/
theorem ptJet_fastPartial_le {sX sZ : ℕ} {Ψ : Vec 2 → Vec 2 → E} (h : IsBoxSmooth sX sZ Ψ)
    (k : Fin 2) {p q : ℕ} (hp : p ≤ sX) (hq : q + 1 ≤ sZ) (X : Vec 2) :
    ptJet (fastPartial k Ψ) X p q ≤ ptJet Ψ X p (q + 1) := by
  have hs : IsBoxSmooth sX q (fastPartial k Ψ) := (h.mono le_rfl hq).fastPartial k
  have := ptJet_le_mul (Φ := fastPartial k Ψ) (Ψ := Ψ) (p := p) (q := q) (p' := p) (q' := q + 1)
    (hs.continuous_norm_jetAt hp le_rfl X) 1 zero_le_one
    (fun z => by simpa using norm_jetAt_fastPartial_le h k hp hq X z)
  simpa using this
end

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! Word derivatives versus the pointwise mixed jets: the `L²` norm of a slow word derivative of a
fast word derivative is at most `ptJet`, and `ptJet` is at most `2 ^ (p + q)` times the supremum over
words.  Consequences for the word based `mixedCellL2Jet` and `schurMixedCellL2Jet`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The word derivative is the jet evaluated on the (reversed) basis words. -/
theorem orderedDerivative_orderedDerivative_eq_jetAt {sX sZ p q : ℕ} {Ψ : Vec 2 → Vec 2 → E}
    (hΨ : IsBoxSmooth sX sZ Ψ) (hp : p ≤ sX) (hq : q ≤ sZ) (α : DerivativeWord2 p)
    (β : DerivativeWord2 q) (X z : Vec 2) :
    orderedDerivative α (fun X' => orderedDerivative β (Ψ X') z) X =
      jetAt Ψ X z p q (fun i => basisVec (α (Fin.rev i))) (fun j => basisVec (β (Fin.rev j))) := by
  let ev : ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) E →L[ℝ] E :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) E
      (fun j => basisVec (β (Fin.rev j)))
  have hin : (fun X' => orderedDerivative β (Ψ X') z) =
      fun X' => ev (iteratedFDeriv ℝ q (Ψ X') z) := by
    funext X'
    rw [orderedDerivative_eq_iteratedFDeriv β ((hΨ.1 X').of_le (by exact_mod_cast hq))]
    rfl
  have hΨq : ContDiff ℝ (p : ℕ∞) (fun X' => iteratedFDeriv ℝ q (Ψ X') z) :=
    (hΨ.2.1 q hq z).of_le (by exact_mod_cast hp)
  have hc : ContDiff ℝ (p : ℕ∞) (fun X' => ev (iteratedFDeriv ℝ q (Ψ X') z)) :=
    ev.contDiff.comp hΨq
  rw [hin, orderedDerivative_eq_iteratedFDeriv α hc]
  have h := ev.iteratedFDeriv_comp_left (hΨq.contDiffAt (x := X)) (i := p)
    (by exact_mod_cast le_rfl)
  have h' := congrArg (fun T => T (fun i => basisVec (α (Fin.rev i)))) h
  exact h'

theorem continuous_orderedDerivative_orderedDerivative {sX sZ p q : ℕ} {Ψ : Vec 2 → Vec 2 → E}
    (hΨ : IsBoxSmooth sX sZ Ψ) (hp : p ≤ sX) (hq : q ≤ sZ) (α : DerivativeWord2 p)
    (β : DerivativeWord2 q) (X : Vec 2) :
    Continuous fun z => orderedDerivative α (fun X' => orderedDerivative β (Ψ X') z) X := by
  have h1 : (fun z => orderedDerivative α (fun X' => orderedDerivative β (Ψ X') z) X) =
      fun z => jetAt Ψ X z p q (fun i => basisVec (α (Fin.rev i)))
        (fun j => basisVec (β (Fin.rev j))) :=
    funext fun z => orderedDerivative_orderedDerivative_eq_jetAt hΨ hp hq α β X z
  rw [h1]
  have hT := hΨ.continuous_jetAt hp hq X
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) E
    (fun j => basisVec (β (Fin.rev j)))).continuous.comp
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin p => Vec 2)
      (ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) E)
      (fun i => basisVec (α (Fin.rev i)))).continuous.comp hT)

/-- Pointwise: a word derivative is bounded by the norm of the jet. -/
theorem norm_orderedDerivative_orderedDerivative_le {sX sZ p q : ℕ} {Ψ : Vec 2 → Vec 2 → E}
    (hΨ : IsBoxSmooth sX sZ Ψ) (hp : p ≤ sX) (hq : q ≤ sZ) (α : DerivativeWord2 p)
    (β : DerivativeWord2 q) (X z : Vec 2) :
    ‖orderedDerivative α (fun X' => orderedDerivative β (Ψ X') z) X‖ ≤
      ‖jetAt Ψ X z p q‖ := by
  rw [orderedDerivative_orderedDerivative_eq_jetAt hΨ hp hq α β X z]
  have h1 := (jetAt Ψ X z p q (fun i => basisVec (α (Fin.rev i)))).le_opNorm
    (fun j => basisVec (β (Fin.rev j)))
  have h2 := (jetAt Ψ X z p q).le_opNorm (fun i => basisVec (α (Fin.rev i)))
  have e1 : ∏ j : Fin q, ‖(basisVec (β (Fin.rev j)) : Vec 2)‖ = 1 := by simp [norm_basisVec]
  have e2 : ∏ i : Fin p, ‖(basisVec (α (Fin.rev i)) : Vec 2)‖ = 1 := by simp [norm_basisVec]
  rw [e1, mul_one] at h1
  rw [e2, mul_one] at h2
  exact h1.trans h2

/-- Word derivatives are bounded in `L²` by `ptJet`. -/
theorem eLpNorm_orderedDerivative_le_ptJet {sX sZ p q : ℕ} {Ψ : Vec 2 → Vec 2 → E}
    (hΨ : IsBoxSmooth sX sZ Ψ) (hp : p ≤ sX) (hq : q ≤ sZ) (α : DerivativeWord2 p)
    (β : DerivativeWord2 q) (X : Vec 2) :
    eLpNorm (fun z => orderedDerivative α (fun X' => orderedDerivative β (Ψ X') z) X) 2
      (volume.restrict AVenhance.unitCube) ≤ ptJet Ψ X p q :=
  eLpNorm_mono_real
    (continuous_orderedDerivative_orderedDerivative hΨ hp hq α β X).aestronglyMeasurable
    fun z => norm_orderedDerivative_orderedDerivative_le hΨ hp hq α β X z

/-- Pointwise: the jet norm is at most the sum of the norms of all word derivatives. -/
theorem norm_jetAt_le_sum_words {sX sZ p q : ℕ} {Ψ : Vec 2 → Vec 2 → E}
    (hΨ : IsBoxSmooth sX sZ Ψ) (hp : p ≤ sX) (hq : q ≤ sZ) (X z : Vec 2) :
    ‖jetAt Ψ X z p q‖ ≤ ∑ α : DerivativeWord2 p, ∑ β : DerivativeWord2 q,
      ‖orderedDerivative α (fun X' => orderedDerivative β (Ψ X') z) X‖ := by
  have h1 := norm_le_sum_basisVec (jetAt Ψ X z p q)
  have h2 : ∀ w : DerivativeWord2 p, ‖jetAt Ψ X z p q (fun i => basisVec (w i))‖ ≤
      ∑ u : DerivativeWord2 q, ‖jetAt Ψ X z p q (fun i => basisVec (w i)) (fun j => basisVec (u j))‖ :=
    fun w => norm_le_sum_basisVec _
  refine h1.trans ((Finset.sum_le_sum fun w _ => h2 w).trans (le_of_eq ?_))
  rw [← Equiv.sum_comp (wordRev p)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Equiv.sum_comp (wordRev q)]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [orderedDerivative_orderedDerivative_eq_jetAt hΨ hp hq α β X z]
  rfl

/-- `ptJet` is controlled by `2 ^ (p + q)` times a common bound of all word derivatives. -/
theorem ptJet_le_of_words_le {sX sZ p q : ℕ} {Ψ : Vec 2 → Vec 2 → E}
    (hΨ : IsBoxSmooth sX sZ Ψ) (hp : p ≤ sX) (hq : q ≤ sZ) (X : Vec 2) {S : ℝ≥0∞}
    (hS : ∀ (α : DerivativeWord2 p) (β : DerivativeWord2 q),
      eLpNorm (fun z => orderedDerivative α (fun X' => orderedDerivative β (Ψ X') z) X) 2
        (volume.restrict AVenhance.unitCube) ≤ S) :
    ptJet Ψ X p q ≤ 2 ^ (p + q) * S := by
  set μ := volume.restrict AVenhance.unitCube with hμ
  have hmeas : AEStronglyMeasurable (fun z => ‖jetAt Ψ X z p q‖) μ :=
    (hΨ.continuous_norm_jetAt hp hq X).aestronglyMeasurable
  have h1 : ptJet Ψ X p q ≤ eLpNorm (∑ α : DerivativeWord2 p, ∑ β : DerivativeWord2 q,
      fun z => ‖orderedDerivative α (fun X' => orderedDerivative β (Ψ X') z) X‖) 2 μ := by
    refine eLpNorm_mono_real hmeas fun z => ?_
    refine (norm_norm (jetAt Ψ X z p q)).le.trans ?_
    simp only [Finset.sum_apply]
    exact norm_jetAt_le_sum_words hΨ hp hq X z
  refine h1.trans ?_
  refine (eLpNorm_sum_le (by norm_num)).trans ?_
  have hterm : ∀ (α : DerivativeWord2 p), eLpNorm (∑ β : DerivativeWord2 q,
      fun z => ‖orderedDerivative α (fun X' => orderedDerivative β (Ψ X') z) X‖) 2 μ ≤
      2 ^ q * S := by
    intro α
    refine (eLpNorm_sum_le (by norm_num)).trans ?_
    calc ∑ β : DerivativeWord2 q,
          eLpNorm (fun z => ‖orderedDerivative α (fun X' => orderedDerivative β (Ψ X') z) X‖) 2 μ
        ≤ ∑ _β : DerivativeWord2 q, S := Finset.sum_le_sum fun β _ => by
          rw [eLpNorm_norm _ (continuous_orderedDerivative_orderedDerivative hΨ hp hq α β X
            |>.aestronglyMeasurable)]
          exact hS α β
      _ = 2 ^ q * S := by rw [Finset.sum_const, card_derivativeWord2]; simp
  calc ∑ α : DerivativeWord2 p, eLpNorm (∑ β : DerivativeWord2 q,
          fun z => ‖orderedDerivative α (fun X' => orderedDerivative β (Ψ X') z) X‖) 2 μ
      ≤ ∑ _α : DerivativeWord2 p, 2 ^ q * S := Finset.sum_le_sum fun α _ => hterm α
    _ = 2 ^ (p + q) * S := by
        rw [Finset.sum_const, card_derivativeWord2, pow_add]; simp [mul_assoc]

/-- `ptJet` is at most `2 ^ (p + q)` times the supremum over all word derivatives. -/
theorem ptJet_le_two_pow_mul_iSup {sX sZ p q : ℕ} {Ψ : Vec 2 → Vec 2 → E}
    (hΨ : IsBoxSmooth sX sZ Ψ) (hp : p ≤ sX) (hq : q ≤ sZ) (X : Vec 2) :
    ptJet Ψ X p q ≤ 2 ^ (p + q) * ⨆ (α : DerivativeWord2 p) (β : DerivativeWord2 q),
      eLpNorm (fun z => orderedDerivative α (fun X' => orderedDerivative β (Ψ X') z) X) 2
        (volume.restrict AVenhance.unitCube) :=
  ptJet_le_of_words_le hΨ hp hq X fun α β => le_iSup₂_of_le α β le_rfl

section Mixed

/-- The word based `mixedCellL2Jet` is at most any uniform bound of the `ptJet`s. -/
theorem mixedCellL2Jet_le_of_ptJet_le {I : Set ℝ} {p q : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (hf : ∀ t ∈ I, IsBoxSmooth p q (f t)) {M : ℝ≥0∞}
    (h : ∀ t ∈ I, ∀ X, ptJet (f t) X p q ≤ M) : mixedCellL2Jet I p q f ≤ M := by
  unfold mixedCellL2Jet
  refine iSup₂_le fun t ht => iSup_le fun X => iSup_le fun α => iSup_le fun β => ?_
  exact (eLpNorm_orderedDerivative_le_ptJet (hf t ht) le_rfl le_rfl α β X).trans (h t ht X)

/-- The Schur form: a uniform bound of the `ptJet`s of the coefficient blocks bounds the weighted
Schur sums of `mixedCellL2Jet`. -/
theorem schurMixedCellL2Jet_le_of_ptJet_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {κ : Type*} [Fintype κ]
    (π : ι → ℝ) (I : Set ℝ) {p q : ℕ} (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v)
    (hc : ∀ a v u, ∀ t ∈ I, IsBoxSmooth p q (fun X z => c a t X z v u))
    {M : κ → ι → ι → ℝ≥0∞}
    (hM : ∀ a v u, ∀ t ∈ I, ∀ X, ptJet (fun X z => c a t X z v u) X p q ≤ M a v u) :
    schurMixedCellL2Jet π I p q c ≤ schurSums π fun v u => ∑ a, M a v u := by
  unfold schurMixedCellL2Jet
  refine schurSums_mono π fun v u => Finset.sum_le_sum fun a _ => ?_
  exact mixedCellL2Jet_le_of_ptJet_le (fun t ht => hc a v u t ht) (hM a v u)

end Mixed

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! Leibniz rule for the pointwise mixed jets of `B (g X) (Ψ X z)` with a slow-only factor `g`
and a bounded bilinear map `B`; the scalar (`g X • Ψ X z`) and operator (`g X (Ψ X z)`) cases. -/

section
variable {G E F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A bilinear map lifted to act on `n`-fold multilinear maps through the target. -/
def bilinJet (n : ℕ) (B : G →L[ℝ] E →L[ℝ] F) : G →L[ℝ]
    ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) E →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) F :=
  (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Vec 2) E F).comp B

theorem iteratedFDeriv_fast_bilin {Ψ : Vec 2 → Vec 2 → E} {sZ q : ℕ}
    (hZ : ∀ X, ContDiff ℝ (sZ : ℕ∞) (Ψ X)) (hq : q ≤ sZ) (B : G →L[ℝ] E →L[ℝ] F)
    (g : Vec 2 → G) (X z : Vec 2) :
    iteratedFDeriv ℝ q (fun z' => B (g X) (Ψ X z')) z =
      bilinJet q B (g X) (iteratedFDeriv ℝ q (Ψ X) z) :=
  iteratedFDeriv_fast_clm hZ hq (B (g X)) X z

/-- Box smoothness of `B (g X) (Ψ X z)` for a smooth slow factor `g`. -/
theorem _root_.AVRegularity.IsBoxSmooth.bilin {sX sZ : ℕ} {Ψ : Vec 2 → Vec 2 → E}
    (hΨ : IsBoxSmooth sX sZ Ψ) (B : G →L[ℝ] E →L[ℝ] F) {g : Vec 2 → G}
    (hg : ContDiff ℝ (sX : ℕ∞) g) : IsBoxSmooth sX sZ (fun X z => B (g X) (Ψ X z)) := by
  rw [isBoxSmooth_iff]
  refine ⟨fun X => (B (g X)).contDiff.comp (hΨ.1 X), fun b hb => ?_⟩
  have hs : IsSlowSmooth sX (fun X z => (bilinJet b B).flip (iteratedFDeriv ℝ b (Ψ X) z) (g X)) :=
    IsSlowSmooth.clm_apply (((isBoxSmooth_iff.mp hΨ).2 b hb).clm_comp (bilinJet b B).flip) hg
  have e : (fun X z => iteratedFDeriv ℝ b (fun z' => B (g X) (Ψ X z')) z) =
      fun X z => (bilinJet b B).flip (iteratedFDeriv ℝ b (Ψ X) z) (g X) := by
    funext X z
    rw [iteratedFDeriv_fast_bilin hΨ.1 hb B g X z]
    rfl
  rw [e]
  exact hs

/-- A nested multilinear map is bounded by `K` as soon as all its values on tuples of vectors are
bounded by `K` times the product of the norms of the arguments. -/
theorem norm_le_of_apply_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {p q : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => Vec 2)
      (ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) V)) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ (v : Fin p → Vec 2) (w : Fin q → Vec 2),
      ‖T v w‖ ≤ K * (∏ i, ‖v i‖) * ∏ j, ‖w j‖) : ‖T‖ ≤ K :=
  ContinuousMultilinearMap.opNorm_le_bound hK fun v =>
    ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun w => h v w

theorem norm_apply_clm_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (q : ℕ)
    (w : Fin q → Vec 2) :
    ‖ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) V w‖ ≤ ∏ j, ‖w j‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (Finset.prod_nonneg fun _ _ => norm_nonneg _) fun f => by
    rw [mul_comm]; exact f.le_opNorm w

/-- Pointwise Leibniz bound for the mixed jet of `B (g X) (Ψ X z)`. -/
theorem norm_jetAt_bilin_le {sX sZ p q : ℕ} {Ψ : Vec 2 → Vec 2 → E} (hΨ : IsBoxSmooth sX sZ Ψ)
    (hp : p ≤ sX) (hq : q ≤ sZ) (B : G →L[ℝ] E →L[ℝ] F) {g : Vec 2 → G}
    (hg : ContDiff ℝ (sX : ℕ∞) g) (X z : Vec 2) :
    ‖jetAt (fun X z => B (g X) (Ψ X z)) X z p q‖ ≤
      ∑ i ∈ Finset.range (p + 1), (‖B‖ * ((p.choose i : ℝ) * ‖iteratedFDeriv ℝ i g X‖)) *
        ‖jetAt Ψ X z (p - i) q‖ := by
  refine norm_le_of_apply_le _ (Finset.sum_nonneg fun i _ => by positivity) fun v w => ?_
  have hΨq : ContDiff ℝ (p : ℕ∞) (fun X' => iteratedFDeriv ℝ q (Ψ X') z) :=
    (hΨ.2.1 q hq z).of_le (by exact_mod_cast hp)
  have hgp : ContDiff ℝ (p : ℕ∞) g := hg.of_le (by exact_mod_cast hp)
  have hΦq : ContDiff ℝ (p : ℕ∞)
      (fun X' => iteratedFDeriv ℝ q (fun z' => B (g X') (Ψ X' z')) z) :=
    (((hΨ.bilin B hg).2.1 q hq z).of_le (by exact_mod_cast hp))
  set W : ℝ := ∏ j, ‖w j‖ with hW
  set V : ℝ := ∏ i, ‖v i‖ with hV
  have hW0 : 0 ≤ W := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hV0 : 0 ≤ V := Finset.prod_nonneg fun _ _ => norm_nonneg _
  let ev : ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) F →L[ℝ] F :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) F w
  let ev' : ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) E →L[ℝ] E :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) E w
  -- evaluation on the fast arguments commutes with the slow jet
  have e1 : jetAt (fun X z => B (g X) (Ψ X z)) X z p q v w =
      iteratedFDeriv ℝ p (fun y => B (g y) (ev' (iteratedFDeriv ℝ q (Ψ y) z))) X v := by
    have h := ev.iteratedFDeriv_comp_left (hΦq.contDiffAt (x := X)) (i := p)
      (by exact_mod_cast le_rfl)
    have hfun : (⇑ev ∘ fun X' => iteratedFDeriv ℝ q (fun z' => B (g X') (Ψ X' z')) z) =
        fun y => B (g y) (ev' (iteratedFDeriv ℝ q (Ψ y) z)) := by
      funext y
      exact congrArg ev (iteratedFDeriv_fast_clm hΨ.1 hq (B (g y)) y z)
    rw [hfun] at h
    exact (congrArg (fun T => T v) h).symm
  have hev' : ContDiff ℝ (p : ℕ∞) (fun y => ev' (iteratedFDeriv ℝ q (Ψ y) z)) :=
    ev'.contDiff.comp hΨq
  have h2 := ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear B hgp hev' X (n := p) (by exact_mod_cast le_rfl)
  have h3 : ∀ k ≤ p, ‖iteratedFDeriv ℝ k (fun y => ev' (iteratedFDeriv ℝ q (Ψ y) z)) X‖ ≤
      W * ‖jetAt Ψ X z k q‖ := by
    intro k hk
    have := ev'.norm_iteratedFDeriv_comp_left (hΨq.contDiffAt (x := X)) (n := k)
      (by exact_mod_cast hk)
    refine this.trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_apply_clm_le q w) (norm_nonneg _) |>.trans_eq (mul_comm _ _)
  have h4 : ‖iteratedFDeriv ℝ p (fun y => B (g y) (ev' (iteratedFDeriv ℝ q (Ψ y) z))) X‖ ≤
      ∑ i ∈ Finset.range (p + 1), (‖B‖ * ((p.choose i : ℝ) * ‖iteratedFDeriv ℝ i g X‖)) *
        (W * ‖jetAt Ψ X z (p - i) q‖) := by
    refine h2.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have := h3 (p - i) (Nat.sub_le _ _)
    calc ‖B‖ * ((p.choose i : ℝ) * ‖iteratedFDeriv ℝ i g X‖ *
          ‖iteratedFDeriv ℝ (p - i) (fun y => ev' (iteratedFDeriv ℝ q (Ψ y) z)) X‖)
        ≤ ‖B‖ * ((p.choose i : ℝ) * ‖iteratedFDeriv ℝ i g X‖ * (W * ‖jetAt Ψ X z (p - i) q‖)) := by
          gcongr
      _ = _ := by ring
  rw [e1]
  calc ‖iteratedFDeriv ℝ p (fun y => B (g y) (ev' (iteratedFDeriv ℝ q (Ψ y) z))) X v‖
      ≤ ‖iteratedFDeriv ℝ p (fun y => B (g y) (ev' (iteratedFDeriv ℝ q (Ψ y) z))) X‖ * V :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ (∑ i ∈ Finset.range (p + 1), (‖B‖ * ((p.choose i : ℝ) * ‖iteratedFDeriv ℝ i g X‖)) *
        (W * ‖jetAt Ψ X z (p - i) q‖)) * V := mul_le_mul_of_nonneg_right h4 hV0
    _ = (∑ i ∈ Finset.range (p + 1), (‖B‖ * ((p.choose i : ℝ) * ‖iteratedFDeriv ℝ i g X‖)) *
        ‖jetAt Ψ X z (p - i) q‖) * V * W := by
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- Leibniz rule for `ptJet` of `B (g X) (Ψ X z)` with a slow-only factor `g`. -/
theorem ptJet_bilin_le {sX sZ p q : ℕ} {Ψ : Vec 2 → Vec 2 → E} (hΨ : IsBoxSmooth sX sZ Ψ)
    (hp : p ≤ sX) (hq : q ≤ sZ) (B : G →L[ℝ] E →L[ℝ] F) {g : Vec 2 → G}
    (hg : ContDiff ℝ (sX : ℕ∞) g) (X : Vec 2) :
    ptJet (fun X z => B (g X) (Ψ X z)) X p q ≤
      ‖B‖ₑ * ∑ i ∈ Finset.range (p + 1),
        (p.choose i : ℝ≥0∞) * ‖iteratedFDeriv ℝ i g X‖ₑ * ptJet Ψ X (p - i) q := by
  have h := ptJet_le_sum (p' := fun i => p - i) (q' := fun _ => q)
    ((hΨ.bilin B hg).continuous_norm_jetAt hp hq X) (Finset.range (p + 1))
    (fun i => ‖B‖ * ((p.choose i : ℝ) * ‖iteratedFDeriv ℝ i g X‖)) (Ψ := fun _ => Ψ)
    (fun i _ => by positivity) (norm_jetAt_bilin_le hΨ hp hq B hg X)
  rw [Finset.mul_sum]
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [ENNReal.ofReal_mul (norm_nonneg B), ENNReal.ofReal_mul (by positivity), ofReal_norm B,
    ofReal_norm (iteratedFDeriv ℝ i g X), ENNReal.ofReal_natCast]
  ring

/-- Leibniz rule with an explicit bound `‖B g e‖ ≤ C ‖g‖ ‖e‖` on the bilinear map. -/
theorem ptJet_bilin_le_of_bound {sX sZ p q : ℕ} {Ψ : Vec 2 → Vec 2 → E}
    (hΨ : IsBoxSmooth sX sZ Ψ) (hp : p ≤ sX) (hq : q ≤ sZ) (B : G →L[ℝ] E →L[ℝ] F) {C : ℝ}
    (hC : 0 ≤ C) (hB : ∀ (a : G) (e : E), ‖B a e‖ ≤ C * ‖a‖ * ‖e‖) {g : Vec 2 → G}
    (hg : ContDiff ℝ (sX : ℕ∞) g) (X : Vec 2) :
    ptJet (fun X z => B (g X) (Ψ X z)) X p q ≤
      ENNReal.ofReal C * ∑ i ∈ Finset.range (p + 1),
        (p.choose i : ℝ≥0∞) * ‖iteratedFDeriv ℝ i g X‖ₑ * ptJet Ψ X (p - i) q := by
  refine (ptJet_bilin_le hΨ hp hq B hg X).trans (mul_le_mul_left ?_ _)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (ContinuousLinearMap.opNorm_le_bound₂ B hC hB)

section Special

/-- Leibniz rule for multiplication by a slow-only real function. -/
theorem ptJet_smul_le {sX sZ p q : ℕ} {Ψ : Vec 2 → Vec 2 → E} (hΨ : IsBoxSmooth sX sZ Ψ)
    (hp : p ≤ sX) (hq : q ≤ sZ) {g : Vec 2 → ℝ} (hg : ContDiff ℝ (sX : ℕ∞) g) (X : Vec 2) :
    ptJet (fun X z => g X • Ψ X z) X p q ≤
      ∑ i ∈ Finset.range (p + 1),
        (p.choose i : ℝ≥0∞) * ‖iteratedFDeriv ℝ i g X‖ₑ * ptJet Ψ X (p - i) q := by
  have h := ptJet_bilin_le_of_bound hΨ hp hq (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
    zero_le_one (fun a e => by simp [norm_smul]) hg X
  simpa using h

end Special
end

/-! Operator-norm form of the pointwise mixed jet bound for one component of a lift action. -/

section
section Lift

variable {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, NormedSpace ℝ (H i)]

theorem _root_.AVRegularity.IsBoxSmooth.apply_slow {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {sX sZ : ℕ}
    {Ψ : Vec 2 → Vec 2 → (E →L[ℝ] F)} (hΨ : IsBoxSmooth sX sZ Ψ) {g : Vec 2 → E}
    (hg : ContDiff ℝ (sX : ℕ∞) g) : IsBoxSmooth sX sZ (fun X z => Ψ X z (g X)) :=
  hΨ.bilin (ContinuousLinearMap.apply ℝ F : E →L[ℝ] (E →L[ℝ] F) →L[ℝ] F) hg

end Lift
end

/-! Pointwise mixed jets of the cell cross operators `cellB1` and `cellB2` at a time where the drift
term vanishes and the metric is slow-only with bounded derivatives. -/

section
section Comb

theorem sum_choose_mul_le (n : ℕ) (f : ℕ → ℝ≥0∞) :
    ∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ≥0∞) * f (n - l) ≤
      2 ^ n * ∑ m ∈ Finset.range (n + 1), f m := by
  calc ∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ≥0∞) * f (n - l)
      ≤ ∑ l ∈ Finset.range (n + 1), 2 ^ n * f (n - l) := Finset.sum_le_sum fun l _ =>
        mul_le_mul_left (by exact_mod_cast Nat.choose_le_two_pow n l) _
    _ = 2 ^ n * ∑ l ∈ Finset.range (n + 1), f (n - l) := (Finset.mul_sum _ _ _).symm
    _ = 2 ^ n * ∑ m ∈ Finset.range (n + 1), f m := by
        congr 1
        simpa using Finset.sum_range_reflect f (n + 1)

theorem sum_range_succ_shift_le (n : ℕ) (f : ℕ → ℝ≥0∞) :
    ∑ m ∈ Finset.range (n + 1), f (m + 1) ≤ ∑ m ∈ Finset.range (n + 2), f m := by
  rw [Finset.sum_range_succ' f (n + 1)]
  exact le_self_add

end Comb

section Smul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem _root_.AVRegularity.IsBoxSmooth.smul_slow {sX sZ : ℕ} {Ψ : Vec 2 → Vec 2 → E}
    (hΨ : IsBoxSmooth sX sZ Ψ) {g : Vec 2 → ℝ} (hg : ContDiff ℝ (sX : ℕ∞) g) :
    IsBoxSmooth sX sZ (fun X z => g X • Ψ X z) := by
  simpa using hΨ.bilin (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) hg

theorem enorm_le_ofReal_of_norm_le {V : Type*} [SeminormedAddCommGroup V] {x : V} {Γ : ℝ}
    (h : ‖x‖ ≤ Γ) : ‖x‖ₑ ≤ ENNReal.ofReal Γ := by
  rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal h

/-- The first-type term of `ℬ₁`: `g ∂_{z_i} ∂_{X_j} Φ`. -/
theorem ptJet_cellB1_fast_le {p q : ℕ} {Φ : Vec 2 → Vec 2 → E}
    (hΦ : IsBoxSmooth (p + 1) (q + 1) Φ) {g : Vec 2 → ℝ} (hg : ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) g)
    {Γ : ℝ} (X : Vec 2) (hΓ : ∀ l, l ≤ p + 1 → ‖iteratedFDeriv ℝ l g X‖ ≤ Γ) (i j : Fin 2) :
    ptJet (fun X z => g X • fastPartial i (slowPartial j Φ) X z) X p q ≤
      ENNReal.ofReal Γ * (2 ^ p * ∑ m ∈ Finset.range (p + 2), ptJet Φ X m (q + 1)) := by
  have hΦs : IsBoxSmooth p (q + 1) (slowPartial j Φ) := hΦ.slowPartial j
  have hΨ : IsBoxSmooth p q (fastPartial i (slowPartial j Φ)) := hΦs.fastPartial i
  have h1 := ptJet_smul_le hΨ le_rfl le_rfl (hg.of_le (by exact_mod_cast Nat.le_succ p)) X
  refine h1.trans ?_
  have h2 : ∀ l ∈ Finset.range (p + 1),
      (p.choose l : ℝ≥0∞) * ‖iteratedFDeriv ℝ l g X‖ₑ *
        ptJet (fastPartial i (slowPartial j Φ)) X (p - l) q ≤
      ENNReal.ofReal Γ * ((p.choose l : ℝ≥0∞) * ptJet Φ X ((p - l) + 1) (q + 1)) := by
    intro l hl
    have hl' : l ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have e1 := ptJet_fastPartial_le hΦs i (p := p - l) (q := q) (Nat.sub_le _ _) le_rfl X
    have e2 := ptJet_slowPartial_le hΦ j (p := p - l) (q := q + 1) (by omega) le_rfl X
    have e3 := enorm_le_ofReal_of_norm_le (hΓ l (by omega))
    calc (p.choose l : ℝ≥0∞) * ‖iteratedFDeriv ℝ l g X‖ₑ *
          ptJet (fastPartial i (slowPartial j Φ)) X (p - l) q
        ≤ (p.choose l : ℝ≥0∞) * ENNReal.ofReal Γ * ptJet Φ X ((p - l) + 1) (q + 1) :=
          mul_le_mul' (mul_le_mul' le_rfl e3) (e1.trans e2)
      _ = _ := by ring
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul' le_rfl ?_
  refine (sum_choose_mul_le p (fun m => ptJet Φ X (m + 1) (q + 1))).trans ?_
  exact mul_le_mul' le_rfl (sum_range_succ_shift_le p (fun m => ptJet Φ X m (q + 1)))

/-- The second-type term of `ℬ₁`: `∂_{X_i}(g ∂_{z_j} Φ)`. -/
theorem ptJet_cellB1_slow_le {p q : ℕ} {Φ : Vec 2 → Vec 2 → E}
    (hΦ : IsBoxSmooth (p + 1) (q + 1) Φ) {g : Vec 2 → ℝ} (hg : ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) g)
    {Γ : ℝ} (X : Vec 2) (hΓ : ∀ l, l ≤ p + 1 → ‖iteratedFDeriv ℝ l g X‖ ≤ Γ) (i j : Fin 2) :
    ptJet (slowPartial i (fun X' z' => g X' • fastPartial j Φ X' z')) X p q ≤
      ENNReal.ofReal Γ * (2 ^ (p + 1) * ∑ m ∈ Finset.range (p + 2), ptJet Φ X m (q + 1)) := by
  have hΦf : IsBoxSmooth (p + 1) q (fastPartial j Φ) := hΦ.fastPartial j
  have hin : IsBoxSmooth (p + 1) q (fun X' z' => g X' • fastPartial j Φ X' z') :=
    hΦf.smul_slow hg
  have h0 := ptJet_slowPartial_le hin i (p := p) (q := q) le_rfl le_rfl X
  have h1 := ptJet_smul_le hΦf le_rfl le_rfl hg X
  refine h0.trans (h1.trans ?_)
  have h2 : ∀ l ∈ Finset.range (p + 1 + 1),
      ((p + 1).choose l : ℝ≥0∞) * ‖iteratedFDeriv ℝ l g X‖ₑ *
        ptJet (fastPartial j Φ) X (p + 1 - l) q ≤
      ENNReal.ofReal Γ * (((p + 1).choose l : ℝ≥0∞) * ptJet Φ X (p + 1 - l) (q + 1)) := by
    intro l hl
    have hl' : l ≤ p + 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have e1 := ptJet_fastPartial_le hΦ j (p := p + 1 - l) (q := q) (Nat.sub_le _ _) le_rfl X
    have e3 := enorm_le_ofReal_of_norm_le (hΓ l hl')
    calc ((p + 1).choose l : ℝ≥0∞) * ‖iteratedFDeriv ℝ l g X‖ₑ *
          ptJet (fastPartial j Φ) X (p + 1 - l) q
        ≤ ((p + 1).choose l : ℝ≥0∞) * ENNReal.ofReal Γ * ptJet Φ X (p + 1 - l) (q + 1) :=
          mul_le_mul' (mul_le_mul' le_rfl e3) e1
      _ = _ := by ring
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul' le_rfl (sum_choose_mul_le (p + 1) (fun m => ptJet Φ X m (q + 1)))

theorem cellB1_eq_of_drift {η : ℝ} {G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t : ℝ} (hv : ∀ z, Real.sqrt η • v t z = 0) (Φ : Vec 2 → Vec 2 → E) :
    cellB1 η G v t Φ = fun X z => (-Real.sqrt η) • ∑ i : Fin 2, ∑ j : Fin 2,
      (G t X i j • fastPartial i (slowPartial j Φ) X z
        + slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z') X z) := by
  funext X z
  have h0 : ∀ k : Fin 2, Real.sqrt η * v t z k = 0 := fun k => by
    simpa using congrFun (hv z) k
  have hz : ∑ k : Fin 2, (Real.sqrt η * v t z k) • slowPartial k Φ X z = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [h0 k, zero_smul]
  show (∑ k : Fin 2, (Real.sqrt η * v t z k) • slowPartial k Φ X z) - _ = _
  rw [hz, zero_sub, neg_smul]

theorem cellB2_eq {η : ℝ} {G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ} {t : ℝ}
    (Φ : Vec 2 → Vec 2 → E) :
    cellB2 η G t Φ = fun X z => (-η) • ∑ i : Fin 2, ∑ j : Fin 2,
      slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z') X z := by
  funext X z
  show -(η • _) = _
  rw [neg_smul]

/-- `ptJet` of `ℬ₁` at a time where the drift vanishes: constant `12 * 2 ^ p`. -/
theorem ptJet_cellB1_le {η : ℝ} {G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t : ℝ} {Φ : Vec 2 → Vec 2 → E} {p q : ℕ} (hΦ : IsBoxSmooth (p + 1) (q + 1) Φ)
    (hv : ∀ z, Real.sqrt η • v t z = 0)
    (hG : ∀ i j, ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun X => G t X i j)) {Γ : ℝ} (X : Vec 2)
    (hΓ : ∀ i j l, l ≤ p + 1 → ‖iteratedFDeriv ℝ l (fun X' => G t X' i j) X‖ ≤ Γ) :
    ptJet (cellB1 η G v t Φ) X p q ≤
      (12 * 2 ^ p) * ENNReal.ofReal (Real.sqrt η) * ENNReal.ofReal Γ *
        ∑ i ∈ Finset.range (p + 2), ptJet Φ X i (q + 1) := by
  rw [cellB1_eq_of_drift hv Φ]
  set J : ℝ≥0∞ := ∑ m ∈ Finset.range (p + 2), ptJet Φ X m (q + 1) with hJ
  have hbox : ∀ i j : Fin 2, IsBoxSmooth p q (fun X z =>
      G t X i j • fastPartial i (slowPartial j Φ) X z
        + slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z') X z) := by
    intro i j
    have hΦs : IsBoxSmooth p (q + 1) (slowPartial j Φ) := hΦ.slowPartial j
    have hA : IsBoxSmooth p q (fun X z => G t X i j • fastPartial i (slowPartial j Φ) X z) :=
      (hΦs.fastPartial i).smul_slow ((hG i j).of_le (by exact_mod_cast Nat.le_succ p))
    have hΦf : IsBoxSmooth (p + 1) q (fastPartial j Φ) := hΦ.fastPartial j
    have hB : IsBoxSmooth p q (slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z')) :=
      (hΦf.smul_slow (hG i j)).slowPartial i
    exact hA.add hB
  have hrow : ∀ i : Fin 2, IsBoxSmooth p q (fun X z => ∑ j : Fin 2,
      (G t X i j • fastPartial i (slowPartial j Φ) X z
        + slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z') X z)) :=
    fun i => IsBoxSmooth.sum _ fun j _ => hbox i j
  have hS := IsBoxSmooth.sum (Finset.univ : Finset (Fin 2)) fun i _ => hrow i
  have h1 := ptJet_const_smul_le hS le_rfl le_rfl (-Real.sqrt η) X
  have hterm : ∀ i j : Fin 2, ptJet (fun X z =>
      G t X i j • fastPartial i (slowPartial j Φ) X z
        + slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z') X z) X p q ≤
      ENNReal.ofReal Γ * (3 * 2 ^ p * J) := by
    intro i j
    have hA := ptJet_cellB1_fast_le hΦ (hG i j) X (hΓ i j) i j
    have hB := ptJet_cellB1_slow_le hΦ (hG i j) X (hΓ i j) i j
    have hΦs : IsBoxSmooth p (q + 1) (slowPartial j Φ) := hΦ.slowPartial j
    have hA' : IsBoxSmooth p q (fun X z => G t X i j • fastPartial i (slowPartial j Φ) X z) :=
      (hΦs.fastPartial i).smul_slow ((hG i j).of_le (by exact_mod_cast Nat.le_succ p))
    have hB' : IsBoxSmooth p q (slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z')) :=
      ((hΦ.fastPartial j).smul_slow (hG i j)).slowPartial i
    refine (ptJet_add_le hA' hB' le_rfl le_rfl X).trans ((add_le_add hA hB).trans (le_of_eq ?_))
    rw [pow_succ]; ring
  have hsum : ptJet (fun X z => ∑ i : Fin 2, ∑ j : Fin 2,
      (G t X i j • fastPartial i (slowPartial j Φ) X z
        + slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z') X z)) X p q ≤
      4 * (ENNReal.ofReal Γ * (3 * 2 ^ p * J)) := by
    refine (ptJet_sum_le _ (fun i _ => hrow i) le_rfl le_rfl X).trans ?_
    have : ∀ i : Fin 2, ptJet (fun X z => ∑ j : Fin 2,
        (G t X i j • fastPartial i (slowPartial j Φ) X z
          + slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z') X z)) X p q ≤
        2 * (ENNReal.ofReal Γ * (3 * 2 ^ p * J)) := fun i =>
      (ptJet_sum_le _ (fun j _ => hbox i j) le_rfl le_rfl X).trans (by
        rw [Fin.sum_univ_two]
        calc _ ≤ ENNReal.ofReal Γ * (3 * 2 ^ p * J) + ENNReal.ofReal Γ * (3 * 2 ^ p * J) :=
              add_le_add (hterm i 0) (hterm i 1)
          _ = _ := by ring)
    rw [Fin.sum_univ_two]
    calc _ ≤ 2 * (ENNReal.ofReal Γ * (3 * 2 ^ p * J)) + 2 * (ENNReal.ofReal Γ * (3 * 2 ^ p * J)) :=
          add_le_add (this 0) (this 1)
      _ = _ := by ring
  refine h1.trans ?_
  have hn : ‖-Real.sqrt η‖ₑ = ENNReal.ofReal (Real.sqrt η) := by
    rw [enorm_neg, Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]
  rw [hn]
  calc ENNReal.ofReal (Real.sqrt η) * _ ≤ ENNReal.ofReal (Real.sqrt η) *
        (4 * (ENNReal.ofReal Γ * (3 * 2 ^ p * J))) := mul_le_mul' le_rfl hsum
    _ = _ := by ring

/-- `ptJet` of `ℬ₂`: constant `8 * 2 ^ p`. -/
theorem ptJet_cellB2_le {η : ℝ} {G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ} {t : ℝ}
    {Φ : Vec 2 → Vec 2 → E} {p q : ℕ} (hΦ : IsBoxSmooth (p + 2) q Φ)
    (hG : ∀ i j, ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun X => G t X i j)) {Γ : ℝ} (X : Vec 2)
    (hΓ : ∀ i j l, l ≤ p + 1 → ‖iteratedFDeriv ℝ l (fun X' => G t X' i j) X‖ ≤ Γ) :
    ptJet (cellB2 η G t Φ) X p q ≤
      (8 * 2 ^ p) * ‖η‖ₑ * ENNReal.ofReal Γ * ∑ i ∈ Finset.range (p + 3), ptJet Φ X i q := by
  rw [cellB2_eq]
  set J : ℝ≥0∞ := ∑ m ∈ Finset.range (p + 3), ptJet Φ X m q with hJ
  have hbox' : ∀ j : Fin 2, IsBoxSmooth (p + 1) q (slowPartial j Φ) := fun j => hΦ.slowPartial j
  have hbox : ∀ i j : Fin 2, IsBoxSmooth p q
      (slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z')) := fun i j =>
    (((hbox' j).smul_slow (hG i j))).slowPartial i
  have hterm : ∀ i j : Fin 2, ptJet
      (slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z')) X p q ≤
      2 * (ENNReal.ofReal Γ * (2 ^ p * J)) := by
    intro i j
    have h0 := ptJet_slowPartial_le ((hbox' j).smul_slow (hG i j)) i (p := p) (q := q) le_rfl
      le_rfl X
    have h1 := ptJet_smul_le (hbox' j) le_rfl le_rfl (hG i j) X
    refine h0.trans (h1.trans ?_)
    have h2 : ∀ l ∈ Finset.range (p + 1 + 1),
        ((p + 1).choose l : ℝ≥0∞) * ‖iteratedFDeriv ℝ l (fun X' => G t X' i j) X‖ₑ *
          ptJet (slowPartial j Φ) X (p + 1 - l) q ≤
        ENNReal.ofReal Γ * (((p + 1).choose l : ℝ≥0∞) * ptJet Φ X ((p + 1 - l) + 1) q) := by
      intro l hl
      have hl' : l ≤ p + 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
      have e1 := ptJet_slowPartial_le hΦ j (p := p + 1 - l) (q := q) (by omega) le_rfl X
      have e3 := enorm_le_ofReal_of_norm_le (hΓ i j l hl')
      calc ((p + 1).choose l : ℝ≥0∞) * ‖iteratedFDeriv ℝ l (fun X' => G t X' i j) X‖ₑ *
            ptJet (slowPartial j Φ) X (p + 1 - l) q
          ≤ ((p + 1).choose l : ℝ≥0∞) * ENNReal.ofReal Γ * ptJet Φ X ((p + 1 - l) + 1) q :=
            mul_le_mul' (mul_le_mul' le_rfl e3) e1
        _ = _ := by ring
    refine (Finset.sum_le_sum h2).trans ?_
    rw [← Finset.mul_sum]
    have h3 := (sum_choose_mul_le (p + 1) (fun m => ptJet Φ X (m + 1) q)).trans
      (mul_le_mul' le_rfl (sum_range_succ_shift_le (p + 1) (fun m => ptJet Φ X m q)))
    refine (mul_le_mul' le_rfl h3).trans (le_of_eq ?_)
    rw [pow_succ]; ring
  have hrow : ∀ i : Fin 2, IsBoxSmooth p q (fun X z => ∑ j : Fin 2,
      slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z') X z) :=
    fun i => IsBoxSmooth.sum _ fun j _ => hbox i j
  have hS := IsBoxSmooth.sum (Finset.univ : Finset (Fin 2)) fun i _ => hrow i
  have h1 := ptJet_const_smul_le hS le_rfl le_rfl (-η) X
  have hsum : ptJet (fun X z => ∑ i : Fin 2, ∑ j : Fin 2,
      slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z') X z) X p q ≤
      4 * (2 * (ENNReal.ofReal Γ * (2 ^ p * J))) := by
    refine (ptJet_sum_le _ (fun i _ => hrow i) le_rfl le_rfl X).trans ?_
    have : ∀ i : Fin 2, ptJet (fun X z => ∑ j : Fin 2,
        slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z') X z) X p q ≤
        2 * (2 * (ENNReal.ofReal Γ * (2 ^ p * J))) := fun i =>
      (ptJet_sum_le _ (fun j _ => hbox i j) le_rfl le_rfl X).trans (by
        rw [Fin.sum_univ_two]
        calc _ ≤ 2 * (ENNReal.ofReal Γ * (2 ^ p * J)) + 2 * (ENNReal.ofReal Γ * (2 ^ p * J)) :=
              add_le_add (hterm i 0) (hterm i 1)
          _ = _ := by ring)
    rw [Fin.sum_univ_two]
    calc _ ≤ 2 * (2 * (ENNReal.ofReal Γ * (2 ^ p * J))) +
          2 * (2 * (ENNReal.ofReal Γ * (2 ^ p * J))) := add_le_add (this 0) (this 1)
      _ = _ := by ring
  refine h1.trans ?_
  rw [enorm_neg]
  calc ‖η‖ₑ * _ ≤ ‖η‖ₑ * (4 * (2 * (ENNReal.ofReal Γ * (2 ^ p * J)))) :=
        mul_le_mul' le_rfl hsum
    _ = _ := by ring

end Smul
end

end AVRegularity.QuietDecay
end
