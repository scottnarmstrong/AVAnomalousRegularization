-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.LiftSetting.Main
import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets
public import AVRegularity.CycleJoint.Assembly.CycleJointOfIngredients
import AVRegularity.CycleComparison.Reconstruction.PiolaTested
import AVRegularity.Applications.Transfer.TubeK
import AVRegularity.Applications.TorusEnergy.StreamFacts
public import AVRegularity.CycleJoint.Assembly.CentreFlowWindow
public import AVRegularity.Weighted.WeightedMultiplicationTermTime
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! Positive prices for each original identity in the dimensional analytic envelope. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The complete original analytic price of one identity, before summing identities. -/
def blockIdentityAnalyticPriceENN (F : ChartedFamily ι h D P Ctx) (dom : F.Domain)
    (E : ℝ) (Ks Ls : ℕ) (v u : ι) (γ : F.Γ v u) : ℝ≥0∞ :=
  ENNReal.ofReal ‖(F.identity v u γ).map‖ *
    ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
      ∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (Ls + 1),
        ENNReal.ofReal (E ^ r) * jetSupFam (fun x : F.Index => dom x.1 x.2) r q
          (fun x => F.slowFlux E x.1 x.2 v u γ d I)

/-- The finite real price of one original identity. -/
def blockIdentityAnalyticPrice (F : ChartedFamily ι h D P Ctx) (dom : F.Domain)
    (E : ℝ) (Ks Ls : ℕ) (v u : ι) (γ : F.Γ v u) : ℝ :=
  (blockIdentityAnalyticPriceENN F dom E Ks Ls v u γ).toReal

/-- Analytic input data, retaining the original slow scale and both reserves. -/
structure BlockLetterAnalyticInputs (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ)
    (W : Set ℝ) (E Ca : ℝ) (Ks Ls : ℕ) (B : ι → ι → ℝ) : Prop where
  slow_pos : 0 < E
  mass_pos : ∀ v, 0 < π v
  nonneg : ∀ v u, 0 ≤ B v u
  envelope : IsAnalyticEnvelope F π (ChartedFamily.Domain.onWindow F W) E Ca Ks Ls B

variable {F : ChartedFamily ι h D P Ctx} {π : ι → ℝ} {W : Set ℝ}
  {E Ca : ℝ} {Ks Ls : ℕ} {B : ι → ι → ℝ}

/-- No original positive identity price is infinite. -/
theorem blockIdentityAnalyticPriceENN_ne_top
    (data : BlockLetterAnalyticInputs F π W E Ca Ks Ls B) (v u : ι) (γ : F.Γ v u) :
    blockIdentityAnalyticPriceENN F (ChartedFamily.Domain.onWindow F W) E Ks Ls v u γ ≠ ⊤ := by
  have hmass : ENNReal.ofReal (Real.sqrt (π u / π v)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (div_pos (data.mass_pos u) (data.mass_pos v)))).ne'
  have hh := data.envelope.2 v u
  have hs := (ENNReal.lt_top_of_mul_ne_top_right
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hh) hmass).ne
  exact ne_top_of_le_ne_top hs (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ γ))

/-- The weighted sum of identity prices costs only the supplied analytic constant. -/
theorem blockIdentityAnalyticPrice_sum_le
    (data : BlockLetterAnalyticInputs F π W E Ca Ks Ls B) (v u : ι) :
    Real.sqrt (π u / π v) * ∑ γ, blockIdentityAnalyticPrice F
      (ChartedFamily.Domain.onWindow F W) E Ks Ls v u γ ≤ |Ca| * B v u := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (data.envelope.2 v u)
  change (ENNReal.ofReal (Real.sqrt (π u / π v)) *
    ∑ γ, blockIdentityAnalyticPriceENN F (ChartedFamily.Domain.onWindow F W) E Ks Ls v u γ).toReal ≤ _ at hh
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_sum (fun γ _ => blockIdentityAnalyticPriceENN_ne_top data v u γ)] at hh
  apply hh.trans
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self Ca) (data.nonneg v u)))
  simpa only [ENNReal.toReal_ofReal (mul_nonneg (abs_nonneg Ca) (data.nonneg v u))] using hb

/-- One reserved term lies below the identity price without cancelling a map. -/
theorem blockIdentityAnalyticPriceENN_term_le (F : ChartedFamily ι h D P Ctx)
    (dom : F.Domain) (E : ℝ) (Ks Ls : ℕ) (v u : ι) (γ : F.Γ v u)
    (d : ℕ) (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (r q : ℕ) (hr : r ≤ Ks) (hq : q ≤ Ls) :
    ENNReal.ofReal ‖(F.identity v u γ).map‖ * (ENNReal.ofReal (E ^ r) *
      jetSupFam (fun x : F.Index => dom x.1 x.2) r q (fun x => F.slowFlux E x.1 x.2 v u γ d I)) ≤
    blockIdentityAnalyticPriceENN F dom E Ks Ls v u γ := by
  refine mul_le_mul' le_rfl ?_
  let term := fun (d : ℕ) (I : DerivativeWord2 (d - 1)) (r q : ℕ) =>
    ENNReal.ofReal (E ^ r) * jetSupFam (fun x : F.Index => dom x.1 x.2) r q
      (fun x => F.slowFlux E x.1 x.2 v u γ d I)
  have hq' : term d I r q ≤ ∑ q ∈ Finset.range (Ls + 1), term d I r q :=
    Finset.single_le_sum (f := term d I r) (fun _ _ => bot_le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))
  have hr' : (∑ q ∈ Finset.range (Ls + 1), term d I r q) ≤
      ∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (Ls + 1), term d I r q :=
    Finset.single_le_sum (f := fun r => ∑ q ∈ Finset.range (Ls + 1), term d I r q)
      (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  have hI' : (∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (Ls + 1), term d I r q) ≤
      ∑ I, ∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (Ls + 1), term d I r q :=
    Finset.single_le_sum (f := fun I => ∑ r ∈ Finset.range (Ks + 1),
      ∑ q ∈ Finset.range (Ls + 1), term d I r q) (fun _ _ => bot_le) (Finset.mem_univ I)
  exact hq'.trans (hr'.trans (hI'.trans
    (Finset.single_le_sum (f := fun d => ∑ I, ∑ r ∈ Finset.range (Ks + 1),
      ∑ q ∈ Finset.range (Ls + 1), term d I r q) (fun _ _ => bot_le) hd)))

/-- Nonzero original maps have finite reserved dimensional jets. -/
theorem blockAnalytic_reserved_jet_ne_top
    (data : BlockLetterAnalyticInputs F π W E Ca Ks Ls B) (v u : ι) (γ : F.Γ v u)
    (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder) (I : DerivativeWord2 (d - 1))
    (r q : ℕ) (hr : r ≤ Ks) (hq : q ≤ Ls) :
    jetSupFam (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2) r q
      (fun x => F.slowFlux E x.1 x.2 v u γ d I) ≠ ⊤ := by
  have hterm := blockIdentityAnalyticPriceENN_term_le F (ChartedFamily.Domain.onWindow F W)
    E Ks Ls v u γ d hd I r q hr hq
  have hf := ne_top_of_le_ne_top (blockIdentityAnalyticPriceENN_ne_top data v u γ) hterm
  rw [← mul_assoc] at hf
  have hc : ENNReal.ofReal ‖(F.identity v u γ).map‖ * ENNReal.ofReal (E ^ r) ≠ 0 := by
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hγ)).ne'
      (ENNReal.ofReal_pos.mpr (pow_pos data.slow_pos r)).ne'
  exact (ENNReal.lt_top_of_mul_ne_top_right hf hc).ne

/-- A reserved normalized jet is controlled almost everywhere by its identity price. -/
theorem blockAnalytic_flux_jet_ae_bound
    (data : BlockLetterAnalyticInputs F π W E Ca Ks Ls B) (v u : ι) (γ : F.Γ v u)
    (hγ : (F.identity v u γ).map ≠ 0) (p : P) (c : Ctx p) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder) (I : DerivativeWord2 (d - 1))
    (r q : ℕ) (hr : r ≤ Ks) (hq : q ≤ Ls) :
    ∀ᵐ t ∂volume, t ∈ (F.piece p).output ∩ W → ∀ X z,
      ‖(F.identity v u γ).map‖ *
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (F.flux p c v u γ d I t Y) z) X‖ ≤
      blockIdentityAnalyticPrice F (ChartedFamily.Domain.onWindow F W) E Ks Ls v u γ := by
  let jet := jetSupFam (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2) r q
    (fun x => F.slowFlux E x.1 x.2 v u γ d I)
  have hfin : jet ≠ ⊤ := blockAnalytic_reserved_jet_ne_top data v u γ hγ d hd I r q hr hq
  have hp : jetSupOn (ChartedFamily.Domain.onWindow F W p c) r q
      (F.slowFlux E p c v u γ d I) ≤ jet :=
    le_iSup (fun x : F.Index => jetSupOn (ChartedFamily.Domain.onWindow F W x.1 x.2) r q
      (F.slowFlux E x.1 x.2 v u γ d I)) ⟨p, c⟩
  have ha := Weighted.jetSupOn_ae_norm_bound _ r q _ (ne_top_of_le_ne_top hfin hp)
  have hprice := ENNReal.toReal_mono (blockIdentityAnalyticPriceENN_ne_top data v u γ)
    (blockIdentityAnalyticPriceENN_term_le F (ChartedFamily.Domain.onWindow F W)
      E Ks Ls v u γ d hd I r q hr hq)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_ofReal (pow_nonneg data.slow_pos.le _)] at hprice
  filter_upwards [ha] with t ht
  intro htime X z
  have hbox := CycleComparison.LiftSetting.isBoxSmooth_flux F W E data.slow_pos.ne'
    data.envelope.1 p c htime v u γ d I
  have heq := congrArg ENNReal.toReal
    (CycleComparison.LiftSetting.enorm_lift_jet_eq hbox hr hq (lam := 1) zero_le_one data.slow_pos X z)
  simp only [one_smul, one_pow, ENNReal.ofReal_one, one_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg data.slow_pos.le _), toReal_enorm] at heq
  have hn := (ht (E • X) ⟨htime, Set.mem_univ _⟩ z).trans (ENNReal.toReal_mono hfin hp)
  calc
    _ = ‖(F.identity v u γ).map‖ * (E ^ r *
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q
          (F.slowFlux E p c v u γ d I t Y) z) (E • X)‖) := by rw [heq]; rfl
    _ ≤ ‖(F.identity v u γ).map‖ * (E ^ r * jet.toReal) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn (pow_nonneg data.slow_pos.le _))
        (norm_nonneg _)
    _ ≤ _ := hprice
end

/-! Literal finite-sum readout of the analytic envelope of an edge family. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- A zero field has zero essential mixed jet envelope. -/
theorem block_jetSupOn_zero (dom : Set (ℝ × Vec 2)) (r q : ℕ) :
    jetSupOn dom r q (fun _ _ _ => (0 : Vec 2)) = 0 := by
  apply le_antisymm _ bot_le
  refine essSup_le_of_ae_le 0 ?_
  filter_upwards [] with t
  refine iSup_le fun Y => iSup_le fun hY => iSup_le fun z => ?_
  simp only [iteratedFDeriv_fun_zero, Pi.zero_apply]
  simp only [← ofReal_norm, norm_zero, ENNReal.ofReal_zero]
  exact le_rfl

/-- An almost-everywhere bound of all declared slow and fast points controls the essential jet. -/
theorem block_jetSupOn_le_of_ae_norm (dom : Set (ℝ × Vec 2)) (r q : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → Vec 2) (C : ℝ)
    (hb : ∀ᵐ t ∂volume, ∀ X, (t, X) ∈ dom → ∀ z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (f t Y) z) X‖ ≤ C) :
    jetSupOn dom r q f ≤ ENNReal.ofReal C := by
  refine essSup_le_of_ae_le _ ?_
  filter_upwards [hb] with t ht
  refine iSup_le fun X => iSup_le fun hX => iSup_le fun z => ?_
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (ht X hX z)

/-- A fixed nonnegative map weight can stay outside the essential time supremum. -/
theorem block_jetSupOn_weighted_le (dom : Set (ℝ × Vec 2)) (r q : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → Vec 2) (w C : ℝ) (hw : 0 ≤ w)
    (hb : ∀ᵐ t ∂volume, ∀ X, (t, X) ∈ dom → ∀ z,
      w * ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (f t Y) z) X‖ ≤ C) :
    ENNReal.ofReal w * jetSupOn dom r q f ≤ ENNReal.ofReal C := by
  by_cases hz : w = 0
  · simp only [hz, ENNReal.ofReal_zero, zero_mul, zero_le]
  have hp : 0 < w := lt_of_le_of_ne hw (Ne.symm hz)
  have hj := block_jetSupOn_le_of_ae_norm dom r q f (C / w) (by
    filter_upwards [hb] with t ht
    intro X hX z
    exact (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using ht X hX z))
  calc
    _ ≤ ENNReal.ofReal w * ENNReal.ofReal (C / w) := mul_le_mul' le_rfl hj
    _ = ENNReal.ofReal C := by
      rw [← ENNReal.ofReal_mul hw, mul_div_cancel₀ C hz]

/-- One constituent contributes only at its declared order. -/
theorem block_ofFiber_jetSupFam (edge : ConstituentEdges D h) (dom : Set (ℝ × Vec 2))
    (v u : ι) (γ : (ChartedFamily.ofFiber edge).Γ v u)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (r q : ℕ) :
    jetSupFam (fun _ : (ChartedFamily.ofFiber edge).Index => dom) r q
      (fun x => (ChartedFamily.ofFiber edge).slowFlux 1 x.1 x.2 v u γ d I) =
    if hd : d = γ.1.val then
      jetSupOn dom r q (((edge v u γ.1).get γ.2).coeff (by subst hd; exact I)) else 0 := by
  by_cases hd : d = γ.1.val
  · subst d
    unfold jetSupFam ChartedFamily.slowFlux
    simp only [ChartedFamily.ofFiber, dite_true, inv_one, one_smul, iSup_const]
  · unfold jetSupFam ChartedFamily.slowFlux
    simp only [ChartedFamily.ofFiber, hd, dite_false, block_jetSupOn_zero, iSup_const]

/-- The analytic budget of a constituent list of one fixed order. -/
def blockListAnalyticBudget {Hu Hv : Type*}
    [NormedAddCommGroup Hu] [NormedSpace ℝ Hu] [NormedAddCommGroup Hv] [NormedSpace ℝ Hv]
    {d : ℕ} (cs : List (Constituent d Hu Hv)) (dom : Set (ℝ × Vec 2)) (Ks J : ℕ) : ℝ≥0∞ :=
  ∑ k : Fin cs.length, ENNReal.ofReal ‖(cs.get k).map‖ *
    ∑ I : DerivativeWord2 (d - 1), ∑ r ∈ Finset.range (Ks + 1),
      ∑ q ∈ Finset.range (J + 1), jetSupOn dom r q ((cs.get k).coeff I)

/-- The finite analytic budget of an edge family, summed once per actual constituent. -/
def blockFiberAnalyticBudget (edge : ConstituentEdges D h) (dom : Set (ℝ × Vec 2))
    (Ks J : ℕ) (v u : ι) : ℝ≥0∞ :=
  ∑ o : Finset.Icc 2 D, blockListAnalyticBudget (edge v u o) dom Ks J

/-- The complete reserved budget of one constituent costs only its finite jet count. -/
theorem block_constituent_analyticBudget_le {Hu Hv : Type*}
    [NormedAddCommGroup Hu] [NormedSpace ℝ Hu] [NormedAddCommGroup Hv] [NormedSpace ℝ Hv]
    {d : ℕ} (c : Constituent d Hu Hv) (dom : Set (ℝ × Vec 2)) (Ks J : ℕ) (C : ℝ)
    (hb : ∀ I r q, r ≤ Ks → q ≤ J →
      ENNReal.ofReal ‖c.map‖ * jetSupOn dom r q (c.coeff I) ≤ ENNReal.ofReal C) :
    ENNReal.ofReal ‖c.map‖ * ∑ I : DerivativeWord2 (d - 1),
      ∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (J + 1), jetSupOn dom r q (c.coeff I) ≤
    ((Fintype.card (DerivativeWord2 (d - 1)) * (Ks + 1) * (J + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal C := by
  calc
    _ = ∑ I : DerivativeWord2 (d - 1), ∑ r ∈ Finset.range (Ks + 1),
        ∑ q ∈ Finset.range (J + 1), ENNReal.ofReal ‖c.map‖ * jetSupOn dom r q (c.coeff I) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ _I : DerivativeWord2 (d - 1), ∑ _r ∈ Finset.range (Ks + 1),
        ∑ _q ∈ Finset.range (J + 1), ENNReal.ofReal C := by
      apply Finset.sum_le_sum
      intro I hI
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro q hq
      exact hb I r q (by have := Finset.mem_range.mp hr; omega)
        (by have := Finset.mem_range.mp hq; omega)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Finset.card_range, nsmul_eq_mul, Nat.cast_mul]
      ring

/-- The ofFiber envelope contains no duplicated lower orders. -/
theorem block_ofFiber_analyticBudget_eq (edge : ConstituentEdges D h) (dom : Set (ℝ × Vec 2))
    (Ks J : ℕ) (v u : ι) :
    (∑ γ : (ChartedFamily.ofFiber edge).Γ v u,
      ENNReal.ofReal ‖((ChartedFamily.ofFiber edge).identity v u γ).map‖ *
        ∑ d ∈ Finset.Icc 2 ((ChartedFamily.ofFiber edge).identity v u γ).maxOrder,
          ∑ I : DerivativeWord2 (d - 1), ∑ r ∈ Finset.range (Ks + 1),
            ∑ q ∈ Finset.range (J + 1), ENNReal.ofReal ((1 : ℝ) ^ r) *
              jetSupFam (fun _ : (ChartedFamily.ofFiber edge).Index => dom) r q
                (fun x => (ChartedFamily.ofFiber edge).slowFlux 1 x.1 x.2 v u γ d I)) =
    blockFiberAnalyticBudget edge dom Ks J v u := by
  classical
  change (∑ γ : Σ o : Finset.Icc 2 D, Fin (edge v u o).length, _) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro o ho
  apply Finset.sum_congr rfl
  intro k hk
  change ENNReal.ofReal ‖((edge v u o).get k).map‖ * _ = _
  congr 1
  rw [Finset.sum_eq_single o.val]
  · apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro q hq
    rw [block_ofFiber_jetSupFam edge dom v u ⟨o, k⟩ o.val I r q]
    simp only [dite_true, one_pow, ENNReal.ofReal_one, one_mul]
  · intro d hd hne
    apply Finset.sum_eq_zero
    intro I hI
    apply Finset.sum_eq_zero
    intro r hr
    apply Finset.sum_eq_zero
    intro q hq
    rw [block_ofFiber_jetSupFam edge dom v u ⟨o, k⟩ d I r q]
    simp only [hne, dite_false, mul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp o.property).1, le_rfl⟩))

/-- Spatial smoothness of all actual coefficients supplies the qualitative envelope field. -/
theorem block_ofFiber_isSmoothOn (edge : ConstituentEdges D h) (dom : Set (ℝ × Vec 2))
    (n : ℕ)
    (hs : ∀ v u o, ∀ c ∈ edge v u o, ∀ I tX, tX ∈ dom → ∀ z,
      ContDiffAt ℝ (n : ℕ) (fun w : Vec 2 × Vec 2 => c.coeff I tX.1 w.1 w.2) (tX.2, z)) :
    (ChartedFamily.ofFiber edge).IsSmoothOn (fun _ _ => dom) 1 (fun _ => n) := by
  intro p ctx v u γ d I tX htX z
  by_cases hd : d = γ.1.val
  · subst d
    simpa only [ChartedFamily.ofFiber, dite_true, inv_one, one_smul] using
      hs v u γ.1 ((edge v u γ.1).get γ.2) (List.get_mem _ _) I tX htX z
  · simpa only [ChartedFamily.ofFiber, hd, dite_false, inv_one, one_smul] using
      (contDiffAt_const (𝕜 := ℝ) (n := (n : ℕ)) (c := (0 : Vec 2)) (x := (tX.2, z)))

/-- Supply the literal finite budget and spatial regularity to construct the analytic envelope. -/
theorem block_ofFiber_analyticEnvelope (edge : ConstituentEdges D h) (π : ι → ℝ)
    (dom : Set (ℝ × Vec 2)) (Ks J : ℕ) (B : ι → ι → ℝ)
    (hs : ∀ v u o, ∀ c ∈ edge v u o, ∀ I tX, tX ∈ dom → ∀ z,
      ContDiffAt ℝ (Ks + J : ℕ) (fun w : Vec 2 × Vec 2 => c.coeff I tX.1 w.1 w.2) (tX.2, z))
    (hb : ∀ v u, ENNReal.ofReal (Real.sqrt (π u / π v)) *
      blockFiberAnalyticBudget edge dom Ks J v u ≤ ENNReal.ofReal (B v u)) :
    IsAnalyticEnvelope (ChartedFamily.ofFiber edge) π (fun _ _ => dom) 1 1 Ks J B := by
  refine ⟨block_ofFiber_isSmoothOn edge dom (Ks + J) hs, ?_⟩
  intro v u
  rw [block_ofFiber_analyticBudget_eq, one_mul]
  exact hb v u
end

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs.Assembly

/-! Normalized slow-jet bounds for the centered metric coefficient. -/

/-- Polarization gives the entrywise deviation directly at the scale g. -/
theorem block_metric_entry_deviation (M : Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ)
    (hsym : M.IsSymm)
    (hnear : ∀ ξ : Vec 2, |∑ i, ∑ j, ξ i * (M - 1) i j * ξ j| ≤ g * ∑ i, ξ i ^ 2)
    (i j : Fin 2) : |M i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ g := by
  have hs : M 1 0 = M 0 1 := by
    change M.transpose = M at hsym
    exact congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hsym
  have h00 := hnear ![1, 0]
  have h11 := hnear ![0, 1]
  have hp := hnear ![1, 1]
  have hm := hnear ![1, -1]
  simp only [Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h00 h11 hp hm
  norm_num at h00 h11 hp hm
  rw [hs] at hp hm
  rw [abs_le] at h00 h11 hp hm ⊢
  fin_cases i <;> fin_cases j
  · change -g ≤ M 0 0 - 1 ∧ M 0 0 - 1 ≤ g
    exact h00
  · change -g ≤ M 0 1 - 0 ∧ M 0 1 - 0 ≤ g
    constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]
  · change -g ≤ M 1 0 - 0 ∧ M 1 0 - 0 ≤ g
    rw [hs]
    constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]
  · change -g ≤ M 1 1 - 1 ∧ M 1 1 - 1 ≤ g
    exact h11

/-- A finite price for the metric's zeroth and positive normalized slow jets. -/
def blockMetricJetPrice (Ks : ℕ) (CG : ℕ → ℝ) : ℝ :=
  2 + ∑ j ∈ Finset.range (Ks + 1), |CG j|

theorem blockMetricJetPrice_nonneg (Ks : ℕ) (CG : ℕ → ℝ) : 0 ≤ blockMetricJetPrice Ks CG := by
  unfold blockMetricJetPrice
  positivity

/-- Replacing cell coordinates by normalized slow coordinates cancels every delta factor. -/
theorem block_metric_normalized_entry_jet (Ks : ℕ) (CG : ℕ → ℝ)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (X₀ : Vec 2) (δ g : ℝ)
    (hδ : 0 < δ) (hg : 0 ≤ g)
    (hs : ∀ i j, ContDiff ℝ (Ks : ℕ) (fun x => G x i j))
    (hnear : ∀ x, (G x).IsSymm ∧ ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (G x - 1) i j * ξ j| ≤ g * ∑ i, ξ i ^ 2)
    (hj : ∀ x j, 1 ≤ j → j ≤ Ks → ∀ i k,
      ‖iteratedFDeriv ℝ j (fun y => G y i k) x‖ ≤ CG j * g * δ ^ j)
    (j : ℕ) (hjKs : j ≤ Ks) (i k : Fin 2) (X : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun Y => G (δ⁻¹ • (Y - X₀)) i k - G 0 i k) X‖ ≤
      blockMetricJetPrice Ks CG * g := by
  have hsum : 0 ≤ ∑ j ∈ Finset.range (Ks + 1), |CG j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have htwo : 2 ≤ blockMetricJetPrice Ks CG := by unfold blockMetricJetPrice; linarith
  by_cases hzero : j = 0
  · subst j
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    calc
      _ ≤ |G (δ⁻¹ • (X - X₀)) i k - (1 : Matrix (Fin 2) (Fin 2) ℝ) i k| +
          |(1 : Matrix (Fin 2) (Fin 2) ℝ) i k - G 0 i k| := abs_sub_le _ _ _
      _ ≤ g + g := add_le_add
        (block_metric_entry_deviation _ g (hnear _).1 (hnear _).2 i k)
        (by rw [abs_sub_comm]; exact block_metric_entry_deviation _ g (hnear 0).1 (hnear 0).2 i k)
      _ ≤ _ := by simpa only [two_mul] using mul_le_mul_of_nonneg_right htwo hg
  · have hf : ContDiff ℝ (j : ℕ) (fun x => G x i k) :=
      (hs i k).of_le (by exact_mod_cast hjKs)
    have hscale := hf.comp (contDiff_id.const_smul δ⁻¹)
    have hshift : (fun Y => G (δ⁻¹ • (Y - X₀)) i k) =
        (fun Y => G (δ⁻¹ • Y) i k) ∘ (fun Y => Y + -X₀) := by
      funext Y
      simp only [Function.comp_apply, sub_eq_add_neg]
    rw [Construction.Preservation.FullLift.norm_iteratedFDeriv_sub_const_of_ne j hzero _
      (by rw [hshift]; exact hscale.comp (contDiff_id.add contDiff_const))]
    rw [hshift]
    change ‖iteratedFDeriv ℝ j (fun Y : Vec 2 => G (δ⁻¹ • (Y + -X₀)) i k) X‖ ≤ _
    rw [iteratedFDeriv_comp_add_right (𝕜 := ℝ)
      (f := fun Y : Vec 2 => G (δ⁻¹ • Y) i k) j (-X₀) X]
    rw [congrFun (iteratedFDeriv_comp_const_smul δ⁻¹ hf) (X + -X₀), norm_smul,
      Real.norm_of_nonneg (pow_nonneg (inv_pos.mpr hδ).le j)]
    have hCG : CG j ≤ blockMetricJetPrice Ks CG := by
      have hh := Finset.single_le_sum (fun a _ => abs_nonneg (CG a))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hjKs))
      exact (le_abs_self _).trans (hh.trans (by unfold blockMetricJetPrice; linarith))
    calc
      _ ≤ δ⁻¹ ^ j * (CG j * g * δ ^ j) :=
        mul_le_mul_of_nonneg_left (hj _ j (by omega) hjKs i k) (pow_nonneg (inv_pos.mpr hδ).le j)
      _ = CG j * g := by
        have hc : δ⁻¹ ^ j * δ ^ j = 1 := by rw [← mul_pow, inv_mul_cancel₀ hδ.ne', one_pow]
        calc
          _ = (CG j * g) * (δ⁻¹ ^ j * δ ^ j) := by ring
          _ = _ := by rw [hc, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hCG hg

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CycleComparison.Reconstruction
namespace AVRegularity.CycleJointProofs.Assembly

/-! Conservation of the zero Fourier mode of the homogeneous coupled equation. -/

universe u v

section ConstantTest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Periodicity and incompressibility annihilate transport against a constant test. -/
theorem constant_test_transport {K : ℕ} (W : TorusHk (K + 1) E)
    (b : Vec 2 → Vec 2) (hb : ∀ k, ContDiff ℝ 1 (fun x => b x k))
    (hp : IsZ2Periodic b)
    (hd : ∀ x, ∑ k : Fin 2, fderiv ℝ (fun y => b y k) x (basisVec k) = 0) (c : E) :
    (∫ x in unitCube, ∑ k : Fin 2, b x k *
      inner ℝ (W.toFunction.jet
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ x) c) = 0 := by
  let V := truncateTorusHk (Nat.succ_le_succ (Nat.zero_le K)) W
  have hF : ∀ k, ContDiff ℝ 1 (fun x => b x k • c) :=
    fun k => (hb k).smul contDiff_const
  have hFp : ∀ k, IsZ2Periodic (fun x => b x k • c) := by
    intro k n x
    exact congrArg (fun z : Vec 2 => z k • c) (hp n x)
  have hdiv : ∀ x, (∑ k : Fin 2, fderiv ℝ (fun y => b y k • c) x (basisVec k)) = 0 := by
    intro x
    simp only [fderiv_smul_const ((hb _).differentiable (by decide) x),
      ContinuousLinearMap.smulRight_apply, ← Finset.sum_smul, hd x, zero_smul]
  have h := cell_ibp_div_H1 V hF hFp
  simp only [hdiv, inner_zero_left, integral_zero] at h
  have he : (fun x => ∑ k : Fin 2, inner ℝ (b x k • c)
      (V.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) =
      (fun x => ∑ k : Fin 2, b x k * inner ℝ (W.toFunction.jet
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ x) c) := by
    funext x
    apply Finset.sum_congr rfl
    intro k _
    rw [real_inner_smul_left, real_inner_comm]
    rfl
  rw [he] at h
  exact neg_eq_zero.mp h.symm

omit [FiniteDimensional ℝ E] in
/-- The constant-test weak identity reduces to equality of its endpoint pairings. -/
theorem constant_test_endpoint {ν a t : ℝ} {b : ℝ → Vec 2 → Vec 2}
    {U f : Vec 2 → E} {du : ℝ → Fin 2 → Vec 2 → E}
    {flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} {g : ℝ → Vec 2 → E}
    (c : E)
    (htransport : ∀ s, (∫ x in unitCube, ∑ k : Fin 2,
      b s x k * inner ℝ (du s k x) c) = 0)
    (hg : ∀ s, g s =ᵐ[volume.restrict unitCube] fun _ => 0)
    (hw : CoupledWeakIdentity (volume.restrict unitCube) ν a t b U f
      ((torusConstantCarrier 1 c).toFunction.jet (valueIndex2 1))
      (fun k => (torusConstantCarrier 1 c).toFunction.jet
        ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩) du flux F g) :
    (∫ x in unitCube, inner ℝ (U x) c) = ∫ x in unitCube, inner ℝ (f x) c := by
  have hc := torusConstantCarrier_raw_value_ae 1 c
  have hd : ∀ᵐ x ∂(volume.restrict unitCube), ∀ k : Fin 2,
      (torusConstantCarrier 1 c).toFunction.jet
        ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x = 0 := by
    rw [ae_all_iff]
    intro k
    exact torusConstantCarrier_raw_positive_ae 1 c _ Nat.zero_lt_one
  have hz : ∀ s, (∫ x in unitCube,
      -(∑ k : Fin 2, b s x k * inner ℝ (du s k x)
        ((torusConstantCarrier 1 c).toFunction.jet (valueIndex2 1) x)) -
      ν * ∑ k : Fin 2, inner ℝ (du s k x)
        ((torusConstantCarrier 1 c).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x) -
      (∑ k : Fin 2, inner ℝ (flux s x k + F s x k)
        ((torusConstantCarrier 1 c).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) +
      inner ℝ (g s x) ((torusConstantCarrier 1 c).toFunction.jet (valueIndex2 1) x)) = 0 := by
    intro s
    calc
      _ = ∫ x in unitCube, -(∑ k : Fin 2, b s x k * inner ℝ (du s k x) c) := by
        apply integral_congr_ae
        filter_upwards [hc, hd, hg s] with x hcx hdx hgx
        simp only [hcx, hdx, hgx, inner_zero_right, inner_zero_left,
          Finset.sum_const_zero, mul_zero, sub_zero, add_zero]
      _ = 0 := by rw [integral_neg, htransport s, neg_zero]
  have he := hw.2.2.2.2
  rw [show (∫ x in unitCube, inner ℝ (U x)
      ((torusConstantCarrier 1 c).toFunction.jet (valueIndex2 1) x)) =
      ∫ x in unitCube, inner ℝ (U x) c from
        integral_congr_ae (hc.mono fun x hx => congrArg (inner ℝ (U x)) hx),
    show (∫ x in unitCube, inner ℝ (f x)
      ((torusConstantCarrier 1 c).toFunction.jet (valueIndex2 1) x)) =
      ∫ x in unitCube, inner ℝ (f x) c from
        integral_congr_ae (hc.mono fun x hx => congrArg (inner ℝ (f x)) hx)] at he
  simpa only [hz, integral_zero, sub_eq_zero] using he

end ConstantTest

/-- Homogeneous coupled solutions conserve the cell mean of every component. -/
theorem meanConservation : MeanConservationStatement.{u, v} := by
  intro ι _ h _ _ _ _ _ _ φ hφ ν t₀ t₁ D K A f u w hu i t ht
  have hs : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (φ s) := fun s =>
    hφ.1.comp (contDiff_const.prodMk contDiff_id)
  have hp : ∀ s, IsZ2Periodic (φ s) := by
    intro s n x
    simpa only [Int.cast_zero, add_zero] using hφ.2 0 n s x
  apply ext_inner_left ℝ
  intro c
  have hc := constant_test_endpoint c
    (fun s => constant_test_transport (w i s) (streamVel φ s)
      (fun k => (Applications.streamVel_comp_smooth hs s k).of_le (by simp))
      (Applications.streamVel_periodic hp s)
      (fun x => by simpa only [Fin.sum_univ_two, Applications.pd] using
        Applications.streamVel_classical_div hs s x) c)
    (fun _ => (periodicJetRepresentative_ae (0 : TorusHk (K i) (h i)).val
      (valueIndex2 (K i))).trans (by exact Lp.coeFn_zero _ _ _))
    (hu.2.2.2.2 i t ht (torusConstantCarrier 1 c))
  have hi (z : TorusHk (K i) (h i)) :
      Integrable (z.toFunction.jet (valueIndex2 (K i))) (volume.restrict unitCube) :=
    (z.toFunction.hasPeriodicWeakJet.2.1 _).integrable (by norm_num)
  simp_rw [real_inner_comm] at hc
  simpa only [integral_inner (hi _) c, torusMean] using hc

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution AVRegularity.CycleJointProofs
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! Quadratic moments suffice for absolute local L² convergence of lattice images. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Finite factorial energy controls each actual weighted jet representative. -/
theorem finite_moment_component_memLp {K : ℕ} (f : PlaneHk Set.univ K E)
    (n : ℕ) (ϖ : ℝ) (z : Vec 2)
    (he : weightedFactorialNormSq n ϖ z 1 K f ≠ ⊤) (a : JetIndex2 K) :
    MemLp (fun x => planeMomentSquareRoot n ϖ z x • f.toFunction.jet a x) 2 volume := by
  rw [weightedFactorialNormSq_stored_readout] at he
  have hc := storedChartFactorialEnergy_component_ne_top 1 (by norm_num)
    (planeMomentPolynomial n ϖ z) f he a
  have hsq : (fun x => planeMomentSquareRoot n ϖ z x ^ 2) =
      planeMomentPolynomial n ϖ z := funext (planeMomentSquareRoot_sq n ϖ z)
  have hm := weighted_plane_memLp_of_chartEnergy_ne_top (planeMomentSquareRoot n ϖ z)
    (planeMomentSquareRoot_continuous n ϖ z) (planeJetReadoutOperator K a f)
    (by simpa only [hsq] using hc)
  apply hm.ae_eq
  filter_upwards [univToPlane_ae (f.val a)] with x hx
  exact congrArg (fun v : E => planeMomentSquareRoot n ϖ z x • v) hx

/-- Any moment of order at least two controls the quadratic radial moment. -/
theorem quadratic_radial_le_moment (n : ℕ) (hn : 2 ≤ n) (ϖ : ℝ) (hϖ : 0 < ϖ)
    (z x : Vec 2) :
    (1 + ‖x - z‖) ^ 2 ≤ (Real.sqrt (2 + 4 / ϖ ^ 2)) ^ 2 *
      planeMomentSquareRoot n ϖ z x := by
  have hh := plane_polynomial_moment_absorption ϖ hϖ 0 2 (x - z)
  have hbase : 1 ≤ 1 + ϖ ^ 2 * ((x 0 - z 0) ^ 2 + (x 1 - z 1) ^ 2) :=
    le_add_of_nonneg_right (by positivity)
  have hm : planeMomentSquareRoot 2 ϖ z x ≤ planeMomentSquareRoot n ϖ z x :=
    Real.sqrt_le_sqrt (pow_le_pow_right₀ hbase hn)
  apply le_trans _ (mul_le_mul_of_nonneg_left hm (sq_nonneg _))
  simpa only [planeMomentSquareRoot, planeMomentPolynomial, pow_zero, Real.sqrt_one,
    mul_one, zero_add, Pi.zero_apply, Pi.sub_apply, sub_zero] using hh

/-- The weighted energy supplies the moment used in the lattice convergence argument. -/
theorem finite_moment_quadratic_memLp {K : ℕ} (f : PlaneHk Set.univ K E)
    (n : ℕ) (hn : 2 ≤ n) (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2)
    (he : weightedFactorialNormSq n ϖ z 1 K f ≠ ⊤) (a : JetIndex2 K) :
    MemLp (fun x => (1 + ‖x - z‖) ^ 2 • f.toFunction.jet a x) 2 volume := by
  have hf : AEStronglyMeasurable (f.toFunction.jet a) volume := by
    simpa only [Measure.restrict_univ] using (f.toFunction.memL2 a).aestronglyMeasurable
  have hc : Continuous (fun x : Vec 2 => (1 + ‖x - z‖) ^ 2) := by fun_prop
  apply (finite_moment_component_memLp f n ϖ z he a).of_le_mul
    (c := (Real.sqrt (2 + 4 / ϖ ^ 2)) ^ 2) (hc.aestronglyMeasurable.smul hf)
  filter_upwards with x
  change ‖(1 + ‖x - z‖) ^ 2 • f.toFunction.jet a x‖ ≤
    (Real.sqrt (2 + 4 / ϖ ^ 2)) ^ 2 * ‖planeMomentSquareRoot n ϖ z x • f.toFunction.jet a x‖
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (1 + ‖x - z‖) ^ 2),
    abs_of_nonneg (show 0 ≤ planeMomentSquareRoot n ϖ z x from Real.sqrt_nonneg _)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (quadratic_radial_le_moment n hn ϖ hϖ z x) (norm_nonneg (f.toFunction.jet a x))

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- Norm squares of the localized lattice images sum to the plane square norm. -/
theorem translated_cell_norm_sq_summable (f : Vec 2 → E) (hf : MemLp f 2 volume) :
    Summable (fun k : Fin 2 → ℤ =>
      (eLpNorm (fun x => f (x + AVenhance.latticeShift k)) 2
        (volume.restrict Applications.cellI)).toReal ^ 2) := by
  have hi := hf.norm.integrable_sq
  have hfi : IntegrableOn (fun x => ‖f x‖ ^ 2)
      (⋃ k : Fin 2 → ℤ, Applications.cellAt k) volume := by
    simpa only [cellAt_iUnion, IntegrableOn, Measure.restrict_univ] using hi
  have hs := (hasSum_integral_iUnion Applications.measurableSet_cellAt
    (fun _ _ h => Applications.cellAt_disjoint h) hfi).summable
  apply hs.congr
  intro k
  rw [integral_cellAt_translate]
  have hm : MemLp (fun x => f (x + AVenhance.latticeShift k)) 2
      (volume.restrict Applications.cellI) := (hf.comp_measurePreserving (measurePreserving_add_right volume
    (AVenhance.latticeShift k))).mono_measure Measure.restrict_le_self
  rw [← Lp.norm_toLp _ hm, CoupledEnergyPlane.L2Indicator.norm_sq_eq_integral (𝕜 := ℝ)]
  apply integral_congr_ae
  filter_upwards [hm.coeFn_toLp] with x hx
  rw [hx]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- A quadratic radial moment yields an absolutely summable series of cell L² norms. -/
theorem quadratic_images_cell_summable (f : Vec 2 → E) (hf : MemLp f 2 volume)
    (z : Vec 2) (hm : MemLp (fun x => (1 + ‖x - z‖) ^ 2 • f x) 2 volume) :
    (∑' k : Fin 2 → ℤ, eLpNorm (fun x => f (x + AVenhance.latticeShift k)) 2
      (volume.restrict Applications.cellI)) < ⊤ := by
  let b := fun k : Fin 2 → ℤ =>
    (eLpNorm (fun x => (1 + ‖x + AVenhance.latticeShift k - z‖) ^ 2 •
      f (x + AVenhance.latticeShift k)) 2 (volume.restrict Applications.cellI)).toReal
  have hb : Summable (fun k => b k ^ (2 : ℝ)) := by
    simpa only [b, Real.rpow_two] using translated_cell_norm_sq_summable _ hm
  have ha : Summable (fun k : Fin 2 → ℤ =>
      (1 / spatialLatticeWeight k) ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two] using spatialLatticeReciprocal_square_summable
  have hp := Real.summable_mul_of_Lp_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 from
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (fun k => (one_div_pos.mpr (spatialLatticeWeight_pos k)).le)
    (fun k => ENNReal.toReal_nonneg) ha hb
  have hs := hp.mul_left ((2 + ‖z‖) ^ 2)
  have hn (k : Fin 2 → ℤ) :
      eLpNorm (fun x => f (x + AVenhance.latticeShift k)) 2
        (volume.restrict Applications.cellI) ≤
      ENNReal.ofReal (((2 + ‖z‖) ^ 2 / spatialLatticeWeight k) * b k) := by
    have hfk := hf.comp_measurePreserving (measurePreserving_add_right volume
      (AVenhance.latticeShift k))
    have hmk := hm.comp_measurePreserving (measurePreserving_add_right volume
      (AVenhance.latticeShift k))
    have hc : 0 ≤ (2 + ‖z‖) ^ 2 / spatialLatticeWeight k :=
      div_nonneg (sq_nonneg _) (spatialLatticeWeight_pos k).le
    have hl := weightedLocal_eLpNorm_le (fun x => f (x + AVenhance.latticeShift k))
      (fun x => (1 + ‖x + AVenhance.latticeShift k - z‖) ^ 2)
      (volume.restrict Applications.cellI) ((2 + ‖z‖) ^ 2 / spatialLatticeWeight k)
      hc (hfk.aestronglyMeasurable.restrict (s := Applications.cellI)) ?_
    · rw [ENNReal.ofReal_mul hc]
      dsimp only [b]
      have hfin : (eLpNorm (fun x => (1 + ‖x + AVenhance.latticeShift k - z‖) ^ 2 •
          f (x + AVenhance.latticeShift k)) 2 (volume.restrict Applications.cellI)) ≠ ⊤ :=
        (hmk.mono_measure (Measure.restrict_le_self (s := Applications.cellI))).eLpNorm_ne_top
      rw [ENNReal.ofReal_toReal hfin]
      exact hl
    · filter_upwards [ae_restrict_mem Applications.measurableSet_cellI] with x hx
      have hxnorm : ‖x‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun i => by
        have hi := hx i (Set.mem_univ i)
        rw [Real.norm_eq_abs, abs_of_nonneg hi.1]
        exact hi.2.le)
      have hw := spatialLatticeWeight_le_local_moment k x z 1 (by norm_num) hxnorm
      have hh := (div_le_div_iff_of_pos_right (spatialLatticeWeight_pos k)).mpr hw
      simpa only [div_self (spatialLatticeWeight_pos k).ne', show (1 : ℝ) + 1 = 2 by norm_num,
        mul_div_assoc, div_mul_eq_mul_div] using hh
  apply (ENNReal.tsum_le_tsum hn).trans_lt
  have he (k : Fin 2 → ℤ) : ((2 + ‖z‖) ^ 2 / spatialLatticeWeight k) * b k =
      (2 + ‖z‖) ^ 2 * ((1 / spatialLatticeWeight k) * b k) := by ring
  simpa only [he] using hs.tsum_ofReal_lt_top

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- A finite cell cover bounds the norm on any ball. -/
theorem ball_eLpNorm_le_cell_sum (f : Vec 2 → E) (_hf : MemLp f 2 volume)
    (A : ℝ) (M : ℕ) (hM : A + 1 ≤ M) :
    eLpNorm f 2 (volume.restrict (Metric.ball (0 : Vec 2) A)) ≤
      ∑ m ∈ Applications.latBox M, eLpNorm f 2 (volume.restrict (Applications.cellAt m)) := by
  classical
  let g : Vec 2 → E := ∑ m ∈ Applications.latBox M, (Applications.cellAt m).indicator f
  have he : f =ᵐ[volume.restrict (Metric.ball (0 : Vec 2) A)] g := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hxn : ‖x‖ ≤ A := by
      have hh : ‖x‖ < A := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      exact hh.le
    have hxc := Applications.supBall_subset_iUnion_cellAt hM hxn
    obtain ⟨m, hxm⟩ := Set.mem_iUnion.mp hxc
    obtain ⟨hm, hxm⟩ := Set.mem_iUnion.mp hxm
    dsimp only [g]
    simp only [Finset.sum_apply]
    symm
    rw [Finset.sum_eq_single m]
    · exact Set.indicator_of_mem hxm f
    · intro j _ hne
      apply Set.indicator_of_notMem
      intro hxj
      exact Set.disjoint_left.mp (Applications.cellAt_disjoint hne) hxj hxm
    · intro hnot
      exact (hnot hm).elim
  rw [eLpNorm_congr_ae he]
  apply (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
  have hn := eLpNorm_sum_le (μ := (volume : Measure (Vec 2))) (p := 2)
    (f := fun m => (Applications.cellAt m).indicator f)
    (s := Applications.latBox M) (by norm_num)
  simpa only [g, eLpNorm_indicator_eq_eLpNorm_restrict
    (Applications.measurableSet_cellAt _)] using hn

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- Reindexing an image norm on a translated cell returns the original cell norm. -/
theorem image_cellAt_eLpNorm (f : Vec 2 → E) (hf : MemLp f 2 volume)
    (k m : Fin 2 → ℤ) :
    eLpNorm (fun x => f (x + AVenhance.latticeShift k)) 2
      (volume.restrict (Applications.cellAt m)) =
    eLpNorm (fun x => f (x + AVenhance.latticeShift (k + m))) 2
      (volume.restrict Applications.cellI) := by
  have hm : MeasurePreserving (fun x : Vec 2 => x + AVenhance.latticeShift m)
      (volume.restrict Applications.cellI) (volume.restrict (Applications.cellAt m)) := by
    simpa only [cellAt_add_shift_preimage] using
      (measurePreserving_add_right volume (AVenhance.latticeShift m)).restrict_preimage
        (Applications.measurableSet_cellAt m)
  have hfk := hf.comp_measurePreserving (measurePreserving_add_right volume
    (AVenhance.latticeShift k))
  have he := eLpNorm_comp_measurePreserving (p := 2)
    (hfk.aestronglyMeasurable.restrict (s := Applications.cellAt m)) hm
  simpa only [Function.comp_def, latticeShift_add, add_assoc,
    add_comm (AVenhance.latticeShift m) (AVenhance.latticeShift k)] using he.symm

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- Cell convergence propagates to every bounded observation ball. -/
theorem images_ball_summable_of_cell (f : Vec 2 → E) (hf : MemLp f 2 volume)
    (hc : (∑' k : Fin 2 → ℤ, eLpNorm (fun x => f (x + AVenhance.latticeShift k)) 2
      (volume.restrict Applications.cellI)) < ⊤) (A : ℝ) :
    (∑' k : Fin 2 → ℤ, eLpNorm (fun x => f (x + AVenhance.latticeShift k)) 2
      (volume.restrict (Metric.ball (0 : Vec 2) A))) < ⊤ := by
  classical
  obtain ⟨M, hM⟩ := exists_nat_ge (A + 1)
  have hn (k : Fin 2 → ℤ) := ball_eLpNorm_le_cell_sum
    (fun x => f (x + AVenhance.latticeShift k))
    (hf.comp_measurePreserving (measurePreserving_add_right volume
      (AVenhance.latticeShift k))) A M hM
  apply (ENNReal.tsum_le_tsum hn).trans_lt
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply ENNReal.sum_lt_top.mpr
  intro m _
  simp_rw [image_cellAt_eLpNorm f hf]
  have he := (latticeDisplacementEquiv (-m)).tsum_eq
    (fun k : Fin 2 → ℤ => eLpNorm (fun x => f (x + AVenhance.latticeShift k)) 2
      (volume.restrict Applications.cellI))
  have he' : (∑' k : Fin 2 → ℤ, eLpNorm (fun x => f (x + AVenhance.latticeShift (k + m))) 2
      (volume.restrict Applications.cellI)) =
      ∑' k : Fin 2 → ℤ, eLpNorm (fun x => f (x + AVenhance.latticeShift k)) 2
        (volume.restrict Applications.cellI) := by
    change (∑' k : Fin 2 → ℤ, eLpNorm (fun x => f (x + AVenhance.latticeShift (k - -m))) 2
      (volume.restrict Applications.cellI)) = _ at he
    simpa only [sub_neg_eq_add] using he
  rw [he']
  exact hc

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleJointProofs
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! The quadratic moment periodization is a genuine linear torus Sobolev carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

/-- The componentwise cell convergence criterion for a plane carrier. -/
theorem quadratic_carrier_cell_sum (f : PlaneHk Set.univ K E) (z : Vec 2)
    (hm : ∀ a, MemLp (fun x => (1 + ‖x - z‖) ^ 2 • f.toFunction.jet a x) 2 volume)
    (a : JetIndex2 K) :
    (∑' k : Fin 2 → ℤ, eLpNorm (fun x => f.toFunction.jet a (x + AVenhance.latticeShift k)) 2
      (volume.restrict AVenhance.unitCube)) < ⊤ := by
  rw [← Measure.restrict_congr_set Applications.cellI_ae_eq_unitCube]
  exact quadratic_images_cell_summable _
    (by simpa only [Measure.restrict_univ] using f.toFunction.memL2 a) z (hm a)

/-- The cell series and its weak derivatives define an actual periodic jet. -/
theorem quadratic_carrier_periodic_jet (f : PlaneHk Set.univ K E) (z : Vec 2)
    (hm : ∀ a, MemLp (fun x => (1 + ‖x - z‖) ^ 2 • f.toFunction.jet a x) 2 volume) :
    HasPeriodicOrderedWeakJet (periodizeRawJet f.toFunction.jet) := by
  classical
  have hc := quadratic_carrier_cell_sum f z hm
  apply periodizeRawJet_hasPeriodicWeakJet _ f.toFunction.hasWeakJet
  · rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    exact ENNReal.sum_lt_top.mpr (fun a _ => hc a)
  · intro A _
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    apply ENNReal.sum_lt_top.mpr
    intro a _
    apply images_ball_summable_of_cell _
      (by simpa only [Measure.restrict_univ] using f.toFunction.memL2 a) _ A
    rw [Measure.restrict_congr_set Applications.cellI_ae_eq_unitCube]
    exact hc a

/-- Periodization with exactly the moments required by the periodized-sum statement. -/
def quadraticPeriodizedCarrier (f : PlaneHk Set.univ K E) (z : Vec 2)
    (hm : ∀ a, MemLp (fun x => (1 + ‖x - z‖) ^ 2 • f.toFunction.jet a x) 2 volume) :
    TorusHk K E :=
  (TorusHkFunction.mk (periodizeRawJet f.toFunction.jet)
    (quadratic_carrier_periodic_jet f z hm)).toHk

/-- The carrier reads the literal series on the cell. -/
theorem quadraticPeriodizedCarrier_ae (f : PlaneHk Set.univ K E) (z : Vec 2)
    (hm : ∀ a, MemLp (fun x => (1 + ‖x - z‖) ^ 2 • f.toFunction.jet a x) 2 volume)
    (a : JetIndex2 K) :
    (quadraticPeriodizedCarrier f z hm).val a =ᵐ[volume.restrict AVenhance.unitCube]
      periodizeRawJet f.toFunction.jet a :=
  torusJetToL2_ae _ (quadratic_carrier_periodic_jet f z hm).2.1 a

/-- The linear image classes form an absolutely convergent Hilbert space series. -/
theorem quadratic_carrier_image_enorm_sum (f : PlaneHk Set.univ K E) (z : Vec 2)
    (hm : ∀ a, MemLp (fun x => (1 + ‖x - z‖) ^ 2 • f.toFunction.jet a x) 2 volume)
    (a : JetIndex2 K) :
    (∑' k : Fin 2 → ℤ, ‖planeImageJetCLM AVenhance.unitCube (AVenhance.latticeShift k) a f‖ₑ) < ⊤ := by
  have he (k : Fin 2 → ℤ) := eLpNorm_congr_ae (p := 2)
    (planeImageJetCLM_ae AVenhance.unitCube (AVenhance.latticeShift k) a f)
  simpa only [← Lp.enorm_def, ← he] using quadratic_carrier_cell_sum f z hm a

/-- Each component is the sum of the actual linear image readouts. -/
theorem quadraticPeriodizedCarrier_eq_series (f : PlaneHk Set.univ K E) (z : Vec 2)
    (hm : ∀ a, MemLp (fun x => (1 + ‖x - z‖) ^ 2 • f.toFunction.jet a x) 2 volume)
    (a : JetIndex2 K) :
    (quadraticPeriodizedCarrier f z hm).val a =
      ∑' k : Fin 2 → ℤ, planeImageJetCLM AVenhance.unitCube (AVenhance.latticeShift k) a f := by
  apply Lp.ext
  exact (quadraticPeriodizedCarrier_ae f z hm a).trans
    (periodized_image_jet_series_ae _ a f (quadratic_carrier_image_enorm_sum f z hm a)).symm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A linear plane family with finite moments has a linear periodized family. -/
def weightedPeriodizeLinear (n : ℕ) (hn : 2 ≤ n) (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2)
    (G : V →ₗ[ℝ] PlaneHk Set.univ K E)
    (hG : ∀ v, weightedFactorialNormSq n ϖ z 1 K (G v) ≠ ⊤) : V →ₗ[ℝ] TorusHk K E where
  toFun v := quadraticPeriodizedCarrier (G v) z
    (finite_moment_quadratic_memLp (G v) n hn ϖ hϖ z (hG v))
  map_add' v w := by
    apply Subtype.ext
    apply PiLp.ext
    intro a
    rw [torusJetComponent_add, quadraticPeriodizedCarrier_eq_series,
      quadraticPeriodizedCarrier_eq_series, quadraticPeriodizedCarrier_eq_series]
    simp_rw [G.map_add, (planeImageJetCLM AVenhance.unitCube _ a).map_add]
    exact (Summable.of_enorm (quadratic_carrier_image_enorm_sum (G v) z
      (finite_moment_quadratic_memLp (G v) n hn ϖ hϖ z (hG v)) a).ne).tsum_add
      (Summable.of_enorm (quadratic_carrier_image_enorm_sum (G w) z
        (finite_moment_quadratic_memLp (G w) n hn ϖ hϖ z (hG w)) a).ne)
  map_smul' c v := by
    apply Subtype.ext
    apply PiLp.ext
    intro a
    rw [torusJetComponent_smul, quadraticPeriodizedCarrier_eq_series,
      quadraticPeriodizedCarrier_eq_series]
    simp_rw [G.map_smul, (planeImageJetCLM AVenhance.unitCube _ a).map_smul]
    exact (Summable.of_enorm (quadratic_carrier_image_enorm_sum (G v) z
      (finite_moment_quadratic_memLp (G v) n hn ϖ hϖ z (hG v)) a).ne).tsum_const_smul c

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleJointProofs AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! The exact counting constant bounds the squared norm of the actual periodized sum. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Weighted Cauchy--Schwarz followed by exact lattice tiling costs only the count bound. -/
theorem periodized_component_budget {J : Type*} [Fintype J]
    (D : J → Vec 2 → E) (hD : ∀ j, StronglyMeasurable (D j))
    (w : J → Vec 2 → ℝ) (hwm : ∀ j, Continuous (w j)) (hw : ∀ j x, 0 < w j x)
    (hi : ∀ j, Integrable (fun x => w j x * ‖D j x‖ ^ 2) volume)
    (Cc : ℝ)
    (hcount : ∀ z : Vec 2, Summable (fun p : J × (Fin 2 → ℤ) =>
        (w p.1 (z + AVenhance.latticeShift p.2))⁻¹) ∧
      ∑' p : J × (Fin 2 → ℤ), (w p.1 (z + AVenhance.latticeShift p.2))⁻¹ ≤ Cc)
    (Z : Lp E 2 (volume.restrict AVenhance.unitCube))
    (hZ : Z =ᵐ[volume.restrict AVenhance.unitCube]
      fun z => ∑ j, latticePeriodization (D j) z) :
    ENNReal.ofReal (‖Z‖ ^ 2) ≤ ENNReal.ofReal Cc *
      ∑ j, ∫⁻ x, ENNReal.ofReal (w j x * ‖D j x‖ ^ 2) := by
  classical
  let e := fun (p : J × (Fin 2 → ℤ)) (z : Vec 2) =>
    ENNReal.ofReal (w p.1 (z + AVenhance.latticeShift p.2) *
      ‖D p.1 (z + AVenhance.latticeShift p.2)‖ ^ 2)
  have he (p : J × (Fin 2 → ℤ)) : Measurable (e p) := by
    exact (((hwm p.1).measurable.comp (measurable_id.add measurable_const)).mul
      (((hD p.1).norm.measurable.comp (measurable_id.add measurable_const)).pow_const 2)).ennreal_ofReal
  have htiling : (∫⁻ z in AVenhance.unitCube, ∑' p, e p z) =
      ∑ j, ∫⁻ x, ENNReal.ofReal (w j x * ‖D j x‖ ^ 2) := by
    rw [lintegral_tsum (fun p => (he p).aemeasurable), ENNReal.tsum_prod', tsum_fintype]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Measure.restrict_congr_set Applications.cellI_ae_eq_unitCube]
    exact (lintegral_tiling_translate _
      (((hwm j).measurable.mul ((hD j).norm.measurable.pow_const 2)).ennreal_ofReal)).symm
  have hfinite : (∫⁻ z in AVenhance.unitCube, ∑' p, e p z) ≠ ⊤ := by
    rw [htiling]
    apply ENNReal.sum_ne_top.mpr
    intro j _
    rw [← ofReal_integral_eq_lintegral_ofReal (hi j)
      (Filter.Eventually.of_forall (fun x => mul_nonneg (hw j x).le (sq_nonneg _)))]
    exact ENNReal.ofReal_ne_top
  have henergy := ae_lt_top (Measurable.tsum he) hfinite
  have hCc : 0 ≤ Cc := (tsum_nonneg (fun p : J × (Fin 2 → ℤ) => (inv_pos.mpr (hw p.1 _)).le)).trans (hcount 0).2
  have hbound : ∀ᵐ z ∂volume.restrict AVenhance.unitCube,
      ENNReal.ofReal (‖Z z‖ ^ 2) ≤ ENNReal.ofReal Cc * ∑' p, e p z := by
    filter_upwards [hZ, henergy] with z hz hfin
    let f := fun p : J × (Fin 2 → ℤ) => D p.1 (z + AVenhance.latticeShift p.2)
    let W := fun p : J × (Fin 2 → ℤ) => w p.1 (z + AVenhance.latticeShift p.2)
    have hW (p : J × (Fin 2 → ℤ)) : 0 < W p := hw p.1 _
    have hs : Summable (fun p => W p * ‖f p‖ ^ 2) := by
      have hh := ENNReal.summable_toReal hfin.ne
      simpa only [e, W, f, ENNReal.toReal_ofReal (mul_nonneg (hW _).le (sq_nonneg _))] using hh
    have hsf := weighted_series_summable f W hW (hcount z).1 hs
    have hsum : (∑' p, f p) = ∑ j, latticePeriodization (D j) z := by
      rw [hsf.tsum_prod, tsum_fintype]
      rfl
    have hh := (weighted_series_norm_sq f W hW (hcount z).1 hs).trans
      (mul_le_mul_of_nonneg_right (hcount z).2 (tsum_nonneg (fun p => mul_nonneg (hW p).le (sq_nonneg _))))
    rw [hsum, ← hz] at hh
    apply (ENNReal.ofReal_le_ofReal hh).trans_eq
    rw [ENNReal.ofReal_mul hCc, ENNReal.ofReal_tsum_of_nonneg
      (fun p => mul_nonneg (hW p).le (sq_nonneg _)) hs]
  rw [CoupledEnergyPlane.L2Indicator.norm_sq_eq_integral (𝕜 := ℝ),
    ofReal_integral_eq_lintegral_ofReal (Lp.memLp Z).norm.integrable_sq
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
  calc
    _ ≤ ∫⁻ z in AVenhance.unitCube, ENNReal.ofReal Cc * ∑' p, e p z := lintegral_mono_ae hbound
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, htiling]

/-- The retained weighted norm is the sum of the energies of the retained original jets. -/
theorem weighted_factorial_retained_readout {K k : ℕ} (hk : k ≤ K) (n : ℕ)
    (ϖ : ℝ) (r : ℝ) (zc : Vec 2) (U : PlaneHk Set.univ K E) :
    weightedFactorialNormSq n ϖ zc r k U =
      ∑ a : JetIndex2 k, ENNReal.ofReal (factorialWeight r a.1.val) *
        ∫⁻ x, ENNReal.ofReal (planeMomentPolynomial n ϖ zc x *
          ‖U.toFunction.jet (truncateJetIndex hk a) x‖ ^ 2) := by
  rw [← weightedFactorialNormSq_truncate hk, weightedFactorialNormSq_stored_readout]
  unfold storedChartFactorialEnergy
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  unfold chartScalarEnergy
  rw [planeJetReadoutOperator_apply]
  apply lintegral_congr_ae
  filter_upwards [univToPlane_ae ((truncatePlaneHk hk U).val a)] with x hx
  rw [hx, truncatePlaneHk_apply]
  rfl

/-- Componentwise counting bounds retain their constant in every factorial truncation. -/
theorem periodized_factorial_budget {J : Type*} [Fintype J] {K : ℕ}
    (U : J → PlaneHk Set.univ K E) (n : ℕ) (ϖ : ℝ) (zc : J → Vec 2) (Cc : ℝ)
    (hU : ∀ j, weightedFactorialNormSq n ϖ (zc j) 1 K (U j) ≠ ⊤)
    (hcount : ∀ z : Vec 2, Summable (fun p : J × (Fin 2 → ℤ) =>
        (planeMomentPolynomial n ϖ (zc p.1) (z + AVenhance.latticeShift p.2))⁻¹) ∧
      ∑' p : J × (Fin 2 → ℤ),
        (planeMomentPolynomial n ϖ (zc p.1) (z + AVenhance.latticeShift p.2))⁻¹ ≤ Cc)
    (Y : TorusHk K E)
    (hY : ∀ a, Y.val a =ᵐ[volume.restrict AVenhance.unitCube]
      fun z => ∑ j, periodizeRawJet (U j).toFunction.jet a z)
    (k : ℕ) (hk : k ≤ K) (r : ℝ) :
    ENNReal.ofReal (factorialNormSq r (truncateTorusHk hk Y).val) ≤
      ENNReal.ofReal Cc * ∑ j, weightedFactorialNormSq n ϖ (zc j) r k (U j) := by
  classical
  let energy := fun (j : J) (a : JetIndex2 k) =>
    ∫⁻ x, ENNReal.ofReal (planeMomentPolynomial n ϖ (zc j) x *
      ‖(U j).toFunction.jet (truncateJetIndex hk a) x‖ ^ 2)
  have hb (a : JetIndex2 k) : ENNReal.ofReal (‖Y.val (truncateJetIndex hk a)‖ ^ 2) ≤
      ENNReal.ofReal Cc * ∑ j, energy j a := by
    apply periodized_component_budget (fun j => (U j).toFunction.jet (truncateJetIndex hk a))
      (fun j => Lp.stronglyMeasurable ((U j).val (truncateJetIndex hk a)))
      (fun j => planeMomentPolynomial n ϖ (zc j))
      (fun j => by unfold planeMomentPolynomial; fun_prop)
      (fun j x => by unfold planeMomentPolynomial; positivity) _ Cc hcount _ (hY _)
    intro j
    have hm := finite_moment_component_memLp (U j) n ϖ (zc j) (hU j) (truncateJetIndex hk a)
    simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, planeMomentSquareRoot_sq] using
      hm.norm.integrable_sq
  rw [factorialNormSq_eq_sum_indices, ENNReal.ofReal_sum_of_nonneg
    (fun a _ => mul_nonneg (factorialWeight_nonneg r a.1.val) (sq_nonneg _))]
  simp_rw [ENNReal.ofReal_mul (factorialWeight_nonneg r _), truncateTorusHk_apply]
  calc
    _ ≤ ∑ a : JetIndex2 k, ENNReal.ofReal (factorialWeight r a.1.val) *
        (ENNReal.ofReal Cc * ∑ j, energy j a) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul' le_rfl (hb a))
    _ = ENNReal.ofReal Cc * ∑ j, ∑ a : JetIndex2 k,
        ENNReal.ofReal (factorialWeight r a.1.val) * energy j a := by
      simp_rw [mul_left_comm (ENNReal.ofReal (factorialWeight r _)) (ENNReal.ofReal Cc),
        Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact (weighted_factorial_retained_readout hk n ϖ r (zc j) (U j)).symm

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! Ingredient CJ04: the finite linear family is periodized with the exact counting budget. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleJointProofs
open scoped ENNReal

universe v w

namespace AVRegularity.CycleJointProofs.Assembly

/-- Periodize finite linear plane families with the constant supplied by centre counting. -/
theorem periodizedSum : PeriodizedSumStatement.{v, w} := by
  intro E _ _ _ _ _ _ V _ _ J _ y R Cc n hR _ hn hcount K G hG
  classical
  let L := fun j => weightedPeriodizeLinear n hn R⁻¹ (inv_pos.mpr hR) (y j) (G j) (hG j)
  let Y : V →ₗ[ℝ] TorusHk K E := ∑ j, L j
  have hY (v : V) (a : JetIndex2 K) : (Y v).val a =
      ∑ j, (L j v).val a := by
    change torusJetComponentCLM a (Y v) = _
    simp only [Y, LinearMap.sum_apply, map_sum, torusJetComponentCLM_apply]
  have hYae (v : V) (a : JetIndex2 K) : (Y v).val a =ᵐ[volume.restrict AVenhance.unitCube]
      fun z => ∑ j, periodizeRawJet (G j v).toFunction.jet a z := by
    rw [hY]
    have ha := ae_all_iff.mpr (fun j => quadraticPeriodizedCarrier_ae (G j v) (y j)
      (finite_moment_quadratic_memLp (G j v) n hn R⁻¹ (inv_pos.mpr hR) (y j) (hG j v)) a)
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => (L j v).val a), ha]
      with z hz hj
    simp only [Finset.sum_apply] at hz
    exact hz.trans (Finset.sum_congr rfl (fun j _ => hj j))
  refine ⟨Y, ?_, hYae, ?_⟩
  · intro v j a
    have hm := finite_moment_quadratic_memLp (G j v) n hn R⁻¹ (inv_pos.mpr hR) (y j) (hG j v)
    have hs := (CycleEvolution.cellLpSeries_memLp_bound _ _
      (quadratic_carrier_cell_sum (G j v) (y j) hm a)).2.2
    filter_upwards [hs] with z hz
    exact Summable.of_norm hz
  · intro v k hk r
    apply periodized_factorial_budget (fun j => G j v) n R⁻¹ y Cc
      (fun j => hG j v) _ (Y v) (hYae v) k hk r
    intro z
    simpa only [planeMomentPolynomial, latticeCountWeight, Pi.add_apply,
      AVenhance.latticeShift] using hcount z

end AVRegularity.CycleJointProofs.Assembly
end
end
