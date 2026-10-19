-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.TimeIntegration
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.Jets.Lift

section
/-! Slow cell-`L²` jets along a cleanup chain:
each antidivergence costs the factor `(4π²)⁻¹` and each slow divergence one slow derivative, so
the `m`-th jet of `V_j` is bounded by the `(m+j)`-th jet of `V_0`, and `V_0 = F₀ + 𝒜_z f₀`.
The jets are word sums of fibrewise `L²_y` norms at a fixed slow point `X`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Word-summed fibrewise `L²_y` slow jet of order `m` of a vector field at `X`. -/
def vecJet (W : Vec 2 → Vec 2 → Fin 2 → E) (m : ℕ) (X : Vec 2) : ℝ≥0∞ :=
  ∑ β : DerivativeWord2 m, ∫⁻ y in AVenhance.unitCube,
    ∑ k : Fin 2, ‖orderedDerivative β (fun X' => W X' y k) X‖ₑ ^ 2

/-- Word-summed fibrewise `L²_y` slow jet of order `m` of a scalar field at `X`. -/
def scalJet (g : Vec 2 → Vec 2 → E) (m : ℕ) (X : Vec 2) : ℝ≥0∞ :=
  ∑ β : DerivativeWord2 m, ∫⁻ y in AVenhance.unitCube,
    ‖orderedDerivative β (fun X' => g X' y) X‖ₑ ^ 2

/-- The antidivergence constant `(4π²)⁻¹`. -/
def antidivConst : ℝ≥0∞ := ENNReal.ofReal ((4 * Real.pi ^ 2)⁻¹)

/-- The first letter of a word is the innermost derivative. -/
theorem orderedDerivative_cons {j : ℕ} (k : Fin 2) (β : DerivativeWord2 j) (g : Vec 2 → E) :
    orderedDerivative (Fin.cons k β : DerivativeWord2 (j + 1)) g =
      orderedDerivative β (fun x => fderiv ℝ g x (basisVec k)) := by
  simp [orderedDerivative, List.ofFn_succ]

theorem IsSlowSmooth.measurable_orderedDerivative_sq {m j : ℕ} {g : Vec 2 → Vec 2 → E}
    (hg : IsSlowSmooth m g) (hj : j ≤ m) (β : DerivativeWord2 j) (X : Vec 2) :
    Measurable (fun y => ‖orderedDerivative β (fun X' => g X' y) X‖ₑ ^ 2) := by
  have hc : Continuous (fun y => orderedDerivative β (fun X' => g X' y) X) :=
    (hg.continuous_orderedDerivative hj β).comp (Continuous.prodMk_right X)
  exact hc.enorm.measurable.pow_const 2

/-- Linearity of a word derivative on `-∑_k g_k`. -/
theorem orderedDerivative_neg_sum {j : ℕ} (β : DerivativeWord2 j) {g : Fin 2 → Vec 2 → E}
    (hg : ∀ k, ContDiff ℝ (j : ℕ∞) (g k)) (x : Vec 2) :
    orderedDerivative β (fun x' => -∑ k : Fin 2, g k x') x =
      -∑ k : Fin 2, orderedDerivative β (g k) x := by
  have hsum : ContDiff ℝ (j : ℕ∞) (fun x' => -∑ k : Fin 2, g k x') :=
    (ContDiff.sum fun k _ => hg k).neg
  rw [orderedDerivative_eq_iteratedFDeriv β hsum]
  simp only [orderedDerivative_eq_iteratedFDeriv β (hg _)]
  have h1 : (fun x' => -∑ k : Fin 2, g k x') = -(fun x' => ∑ k : Fin 2, g k x') := rfl
  rw [h1, iteratedFDeriv_neg_apply, iteratedFDeriv_sum fun k _ => hg k]
  simp

/-- One slow divergence costs one slow derivative: the jet of the next cleanup source. -/
theorem scalJet_cleanupSource_le {W : ℕ → Vec 2 → Vec 2 → Fin 2 → E} {j m : ℕ}
    (hW : IsSlowSmooth (m + 1) (W (j - 1))) (X : Vec 2) :
    scalJet (cleanupSource W j) m X ≤ 2 * vecJet (W (j - 1)) (m + 1) X := by
  have hcomp : ∀ k : Fin 2, IsSlowSmooth (m + 1) (fun X' y => W (j - 1) X' y k) :=
    fun k => hW.component k
  -- the source as a word derivative of the components
  have hword : ∀ (β : DerivativeWord2 m) (y : Vec 2),
      orderedDerivative β (fun X' => cleanupSource W j X' y) X =
        -∑ k : Fin 2, orderedDerivative (Fin.cons k β : DerivativeWord2 (m + 1))
          (fun X' => W (j - 1) X' y k) X := by
    intro β y
    have hd : ∀ k : Fin 2, ContDiff ℝ (m : ℕ∞)
        (fun X' => fderiv ℝ (fun X'' => W (j - 1) X'' y k) X' (basisVec k)) :=
      fun k => (((hcomp k).1 y).fderiv_right (by exact_mod_cast le_rfl)).clm_apply contDiff_const
    simp only [orderedDerivative_cons]
    exact orderedDerivative_neg_sum β
      (g := fun k X' => fderiv ℝ (fun X'' => W (j - 1) X'' y k) X' (basisVec k)) hd X
  unfold scalJet vecJet
  simp_rw [hword]
  -- pointwise: ‖-∑_k a_k‖² ≤ 2 ∑_k ‖a_k‖²
  have hpt : ∀ (β : DerivativeWord2 m) (y : Vec 2),
      ‖-∑ k : Fin 2, orderedDerivative (Fin.cons k β : DerivativeWord2 (m + 1))
          (fun X' => W (j - 1) X' y k) X‖ₑ ^ 2 ≤
        2 * ∑ k : Fin 2, ‖orderedDerivative (Fin.cons k β : DerivativeWord2 (m + 1))
          (fun X' => W (j - 1) X' y k) X‖ₑ ^ 2 := by
    intro β y
    rw [enorm_neg]
    calc _ ≤ (∑ k : Fin 2, ‖orderedDerivative (Fin.cons k β : DerivativeWord2 (m + 1))
          (fun X' => W (j - 1) X' y k) X‖ₑ) ^ 2 := by gcongr; exact enorm_sum_le _ _
      _ ≤ _ := by
        simpa using ennreal_sq_sum_le_card_mul_sum_sq (Finset.univ : Finset (Fin 2))
          (fun k => ‖orderedDerivative (Fin.cons k β : DerivativeWord2 (m + 1))
            (fun X' => W (j - 1) X' y k) X‖ₑ)
  calc ∑ β : DerivativeWord2 m, ∫⁻ y in AVenhance.unitCube,
        ‖-∑ k : Fin 2, orderedDerivative (Fin.cons k β : DerivativeWord2 (m + 1))
          (fun X' => W (j - 1) X' y k) X‖ₑ ^ 2
      ≤ ∑ β : DerivativeWord2 m, ∫⁻ y in AVenhance.unitCube, 2 * ∑ k : Fin 2,
          ∑ k' : Fin 2, ‖orderedDerivative (Fin.cons k β : DerivativeWord2 (m + 1))
            (fun X' => W (j - 1) X' y k') X‖ₑ ^ 2 := by
        gcongr with β _ y
        refine (hpt β y).trans ?_
        gcongr with k
        exact Finset.single_le_sum (f := fun k' => ‖orderedDerivative
          (Fin.cons k β : DerivativeWord2 (m + 1)) (fun X' => W (j - 1) X' y k') X‖ₑ ^ 2)
          (fun _ _ => bot_le) (Finset.mem_univ k)
    _ = 2 * ∑ β : DerivativeWord2 m, ∑ k : Fin 2, ∫⁻ y in AVenhance.unitCube,
          ∑ k' : Fin 2, ‖orderedDerivative (Fin.cons k β : DerivativeWord2 (m + 1))
            (fun X' => W (j - 1) X' y k') X‖ₑ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum]
        intro k _
        exact Finset.measurable_sum _ fun k' _ =>
          (hcomp k').measurable_orderedDerivative_sq le_rfl _ X
    _ = 2 * ∑ β' : DerivativeWord2 (m + 1), ∫⁻ y in AVenhance.unitCube,
          ∑ k' : Fin 2, ‖orderedDerivative β' (fun X' => W (j - 1) X' y k') X‖ₑ ^ 2 := by
        congr 1
        rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Fin 2).sum_comp, Fintype.sum_prod_type,
          Finset.sum_comm]
        rfl

end AVRegularity

namespace AVRegularity

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Antidivergence of the fibrewise jets. -/
theorem vecJet_le_of_isCellAntidivergence
    {sX sZ : ℕ} (hZ : 1 ≤ sZ) {f : Vec 2 → Vec 2 → E} {V : Vec 2 → Vec 2 → Fin 2 → E}
    (hV : IsCellAntidivergence sX sZ f V) {m : ℕ} (hm : m ≤ sX) (hf : IsSlowSmooth m f)
    (X : Vec 2) : vecJet V m X ≤ antidivConst * scalJet f m X := by
  unfold vecJet scalJet antidivConst
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun β _ =>
    cellAntidivergence_orderedDerivative_sq_le hZ hV hm hf β X

/-- Slow smoothness of a cleanup source. -/
theorem isSlowSmooth_cleanupSource {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W : ℕ → Vec 2 → Vec 2 → Fin 2 → F} {j m : ℕ} (hW : IsSlowSmooth (m + 1) (W (j - 1))) :
    IsSlowSmooth m (cleanupSource W j) := by
  have h := (IsSlowSmooth.sum Finset.univ fun k _ =>
    (hW.component k).slowPartial (k := k)).neg
  exact h

/-- Every member of a cleanup chain of a slow-smooth flux is slow smooth. -/
theorem IsCleanupChain.isSlowSmooth {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {sX sZ A : ℕ} {f₀ : Vec 2 → Vec 2 → F} {F₀ : Vec 2 → Vec 2 → Fin 2 → F}
    {V : ℕ → Vec 2 → Vec 2 → Fin 2 → F} (hF : IsSlowSmooth sX F₀)
    (hV : IsCleanupChain sX sZ A f₀ F₀ V) : ∀ j, j < A → IsSlowSmooth sX (V j) := by
  obtain ⟨⟨W₀, hW₀, hV0⟩, hVj⟩ := hV
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · rw [hV0]; exact hF.add hW₀.1.isSlowSmooth
  · exact (hVj j hjpos hj).1.isSlowSmooth

/-- Iterated cleanup: the `m`-th jet of `V_j` is controlled by the `(m+j)`-th jet of `V_0`. -/
theorem vecJet_cleanupChain_le {sX sZ A : ℕ} (hZ : 1 ≤ sZ) {f₀ : Vec 2 → Vec 2 → E}
    {F₀ : Vec 2 → Vec 2 → Fin 2 → E} {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E}
    (hF : IsSlowSmooth sX F₀) (hV : IsCleanupChain sX sZ A f₀ F₀ V) :
    ∀ j, j < A → ∀ m, m + j ≤ sX → ∀ X,
      vecJet (V j) m X ≤ (2 * antidivConst) ^ j * vecJet (V 0) (m + j) X := by
  have hbox := IsCleanupChain.isSlowSmooth hF hV
  intro j
  induction j with
  | zero => intro _ m _ X; simp
  | succ j ih =>
    intro hjA m hm X
    have hVj := hV.2 (j + 1) (by omega) hjA
    have hslow : IsSlowSmooth (m + 1) (V j) := (hbox j (by omega)).mono (by omega)
    have hsrc : IsSlowSmooth m (cleanupSource V (j + 1)) :=
      isSlowSmooth_cleanupSource (W := V) (j := j + 1) (by simpa using hslow)
    calc vecJet (V (j + 1)) m X ≤ antidivConst * scalJet (cleanupSource V (j + 1)) m X :=
          vecJet_le_of_isCellAntidivergence hZ hVj (by omega) hsrc X
      _ ≤ antidivConst * (2 * vecJet (V j) (m + 1) X) := by
          gcongr
          simpa using scalJet_cleanupSource_le (W := V) (j := j + 1) (m := m)
            (by simpa using hslow) X
      _ ≤ antidivConst * (2 * ((2 * antidivConst) ^ j * vecJet (V 0) (m + 1 + j) X)) := by
          gcongr
          exact ih (by omega) (m + 1) (by omega) X
      _ = (2 * antidivConst) ^ (j + 1) * vecJet (V 0) (m + (j + 1)) X := by
          rw [show m + 1 + j = m + (j + 1) by omega, pow_succ]
          ring

/-- The first member of the chain: `V_0 = F₀ + 𝒜_z f₀`. -/
theorem vecJet_cleanupChain_zero_le {sX sZ A : ℕ} (hZ : 1 ≤ sZ) {f₀ : Vec 2 → Vec 2 → E}
    {F₀ : Vec 2 → Vec 2 → Fin 2 → E} {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E}
    (hF : IsSlowSmooth sX F₀) (hV : IsCleanupChain sX sZ A f₀ F₀ V) {m : ℕ} (hm : m ≤ sX)
    (hf₀ : IsSlowSmooth m f₀) (X : Vec 2) :
    vecJet (V 0) m X ≤ 2 * vecJet F₀ m X + 2 * (antidivConst * scalJet f₀ m X) := by
  obtain ⟨⟨W₀, hW₀, hV0⟩, -⟩ := hV
  have hFs : IsSlowSmooth m F₀ := hF.mono hm
  have hWs : IsSlowSmooth m W₀ := hW₀.1.isSlowSmooth.mono hm
  have hW := vecJet_le_of_isCellAntidivergence hZ hW₀ hm hf₀ X
  have hsplit : vecJet (V 0) m X ≤ 2 * vecJet F₀ m X + 2 * vecJet W₀ m X := by
    unfold vecJet
    rw [hV0, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun β _ => ?_
    have hmeasF : ∀ k : Fin 2, Measurable fun y =>
        ‖orderedDerivative β (fun X' => F₀ X' y k) X‖ₑ ^ 2 :=
      fun k => (hFs.component k).measurable_orderedDerivative_sq le_rfl β X
    have hmeasW : ∀ k : Fin 2, Measurable fun y =>
        ‖orderedDerivative β (fun X' => W₀ X' y k) X‖ₑ ^ 2 :=
      fun k => (hWs.component k).measurable_orderedDerivative_sq le_rfl β X
    rw [← lintegral_const_mul _ (Finset.measurable_sum _ fun k _ => hmeasF k),
      ← lintegral_const_mul _ (Finset.measurable_sum _ fun k _ => hmeasW k),
      ← lintegral_add_left ((Finset.measurable_sum _ fun k _ => hmeasF k).const_mul _)]
    refine lintegral_mono fun y => ?_
    rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [orderedDerivative_add β ((hFs.component k).1 y) ((hWs.component k).1 y)]
    calc _ ≤ (‖orderedDerivative β (fun X' => F₀ X' y k) X‖ₑ +
          ‖orderedDerivative β (fun X' => W₀ X' y k) X‖ₑ) ^ 2 := by
          gcongr; exact enorm_add_le _ _
      _ ≤ _ := ennreal_add_sq_le _ _
  calc vecJet (V 0) m X ≤ 2 * vecJet F₀ m X + 2 * vecJet W₀ m X := hsplit
    _ ≤ _ := by gcongr

/-- The scalar remainder `f_A = -div_X V_{A-1}` of the chain. -/
theorem scalJet_cleanupChain_remainder_le {sX sZ A : ℕ} (hZ : 1 ≤ sZ) (hA : 1 ≤ A)
    {f₀ : Vec 2 → Vec 2 → E} {F₀ : Vec 2 → Vec 2 → Fin 2 → E}
    {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E}
    (hF : IsSlowSmooth sX F₀) (hV : IsCleanupChain sX sZ A f₀ F₀ V) {m : ℕ}
    (hm : m + A ≤ sX) (X : Vec 2) :
    scalJet (cleanupSource V A) m X ≤
      2 * ((2 * antidivConst) ^ (A - 1) * vecJet (V 0) (m + A) X) := by
  have hbox := IsCleanupChain.isSlowSmooth hF hV
  have hslow : IsSlowSmooth (m + 1) (V (A - 1)) := (hbox (A - 1) (by omega)).mono (by omega)
  calc scalJet (cleanupSource V A) m X ≤ 2 * vecJet (V (A - 1)) (m + 1) X :=
        scalJet_cleanupSource_le hslow X
    _ ≤ 2 * ((2 * antidivConst) ^ (A - 1) * vecJet (V 0) (m + 1 + (A - 1)) X) := by
        gcongr
        exact vecJet_cleanupChain_le hZ hF hV (A - 1) (by omega) (m + 1) (by omega) X
    _ = _ := by rw [show m + 1 + (A - 1) = m + A by omega]

end InnerProduct

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! Cleanup chains commute with continuous linear maps of the values; in particular a cleanup
chain of a field with values in a finite Hilbert family projects to a cleanup chain of each
component. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The vectorwise action of a continuous linear map. -/
def clmVec (L : E →L[ℝ] F) : (Fin 2 → E) →L[ℝ] (Fin 2 → F) :=
  ContinuousLinearMap.pi fun k => L.comp (ContinuousLinearMap.proj k)

@[simp] theorem clmVec_apply (L : E →L[ℝ] F) (w : Fin 2 → E) (k : Fin 2) :
    clmVec L w k = L (w k) := rfl

/-- The slow source commutes with a continuous linear map of the values. -/
theorem cleanupSource_clm_comp {sX : ℕ} (hX : 1 ≤ sX) {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E}
    {j : ℕ} (hV : IsSlowSmooth sX (V (j - 1))) (L : E →L[ℝ] F) :
    cleanupSource (fun i X z k => L (V i X z k)) j = fun X z => L (cleanupSource V j X z) := by
  funext X z
  have hsX : ((sX : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : sX ≠ 0)
  simp only [cleanupSource, slowPartial, map_neg, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have hd : DifferentiableAt ℝ (fun X' => V (j - 1) X' z k) X :=
    differentiableAt_pi.1 ((hV.1 z).differentiable hsX X) k
  have hc : (fun X' => L (V (j - 1) X' z k)) = L ∘ fun X' => V (j - 1) X' z k := rfl
  rw [hc, fderiv_comp X L.differentiableAt hd]
  simp

/-- A cleanup chain maps to a cleanup chain under a continuous linear map of the values. -/
theorem IsCleanupChain.clm_comp [CompleteSpace E] [CompleteSpace F] {sX sZ A : ℕ} (hX : 1 ≤ sX)
    (hZ : 1 ≤ sZ)
    {f₀ : Vec 2 → Vec 2 → E} {F₀ : Vec 2 → Vec 2 → Fin 2 → E} {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E}
    (hF : IsSlowSmooth sX F₀) (hV : IsCleanupChain sX sZ A f₀ F₀ V) (L : E →L[ℝ] F) :
    IsCleanupChain sX sZ A (fun X z => L (f₀ X z)) (fun X z k => L (F₀ X z k))
      (fun j X z k => L (V j X z k)) := by
  have hbox := IsCleanupChain.isSlowSmooth hF hV
  obtain ⟨⟨W₀, hW₀, hV0⟩, hVj⟩ := hV
  refine ⟨⟨fun X z k => L (W₀ X z k), hW₀.clm_comp hZ L, ?_⟩, fun j hj1 hjA => ?_⟩
  · funext X z k
    simp only
    rw [hV0, map_add]
  · rw [cleanupSource_clm_comp hX (hbox (j - 1) (by omega)) L]
    exact (hVj j hj1 hjA).clm_comp hZ L

end AVRegularity
end
end
