-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.QuietDecay.Fast.Word
import AVRegularity.CycleComparison.Residual.QuietMean.CellMean
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.QuietDecay.Scalar.Weighted

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! The vector slow engine: a finite family of components, all solving the cell equation with the
same slow-point metric. The data are taken over the sum of the components before the supremum over
slow points and words, so the constants do not depend on the number of components. -/

variable {a b : ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {h Γ : ℝ} {P : ℕ}
variable {κ : Type*} [Fintype κ] {Φ : κ → CellFam}

/-- The summed initial data of the words of length at most `n`. -/
def initSupV (a : ℝ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : κ → CellFam) (h : ℝ) (n : ℕ) :
    ℝ≥0∞ :=
  ⨆ (l : {l : List (Fin 2) // l.length ≤ n}) (X : Vec 2),
    ∑ k, cellL2Norm (cellValue ((famWord G (Φ k) l.1 h).D X) a) ^ 2

/-- The summed sources of the words of length at most `n` at the time `σ`. -/
def srcSupV (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : κ → CellFam) (h : ℝ) (n : ℕ) (σ : ℝ) :
    ℝ≥0∞ :=
  ⨆ (l : {l : List (Fin 2) // l.length ≤ n}) (X : Vec 2),
    ∑ k, cellL2Norm ((famWord G (Φ k) l.1 h).src X σ) ^ 2

/-- The summed data bound. -/
def dataBdV (a : ℝ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : κ → CellFam) (h : ℝ) (n : ℕ)
    (τ : ℝ) : ℝ≥0∞ :=
  wt τ a * initSupV a G Φ h n + ∫⁻ σ in Icc a τ, wt τ σ * srcSupV G Φ h n σ

theorem dataBdV_mono (a : ℝ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : κ → CellFam) (h : ℝ)
    {m n : ℕ} (hmn : m ≤ n) (τ : ℝ) : dataBdV a G Φ h m τ ≤ dataBdV a G Φ h n τ := by
  unfold dataBdV initSupV srcSupV
  gcongr with σ
  · exact iSup_le fun l => iSup_le fun X =>
      le_iSup_of_le (⟨l.1, l.2.trans hmn⟩ : {l : List (Fin 2) // l.length ≤ n})
        (le_iSup (fun X => ∑ k, cellL2Norm (cellValue ((famWord G (Φ k) l.1 h).D X) a) ^ 2) X)
  · exact iSup_le fun l => iSup_le fun X =>
      le_iSup_of_le (⟨l.1, l.2.trans hmn⟩ : {l : List (Fin 2) // l.length ≤ n})
        (le_iSup (fun X => ∑ k, cellL2Norm ((famWord G (Φ k) l.1 h).src X σ) ^ 2) X)

section Comp

variable {Ψ : CellFam} (H : EngineHyp a b G Ψ h Γ P)
include H

/-- The flux part of the forcing integral of one component. -/
theorem flux_part_le (l : List (Fin 2)) (hl : l.length ≤ P) (X : Vec 2) {τ : ℝ}
    (hτ : τ ∈ Icc a b) :
    ∫⁻ σ in Icc a τ, wt τ σ *
        (8 * ∑ k : Fin 2, cellL2Norm (fun z => (famWord G Ψ l h).F X σ z k) ^ 2) ≤
      ENNReal.ofReal (32 * (terms h l).length * Γ ^ 2) *
        ((terms h l).map fun τ' => ∫⁻ σ in Icc a τ, wt τ σ *
          gradDen G Ψ h τ'.dw (X + τ'.ds) σ).sum := by
  have hsub : Icc a τ ⊆ Icc a b := Icc_subset_Icc le_rfl hτ.2
  have hmono : volume.restrict (Icc a τ) ≤ volume.restrict (Icc a b) :=
    Measure.restrict_mono hsub le_rfl
  have hT := mem_terms h l
  have hae : ∀ᵐ σ ∂volume.restrict (Icc a τ),
      wt τ σ * (8 * ∑ k : Fin 2, cellL2Norm (fun z => (famWord G Ψ l h).F X σ z k) ^ 2) ≤
        ENNReal.ofReal (32 * (terms h l).length * Γ ^ 2) *
          ((terms h l).map fun τ' => wt τ σ * gradDen G Ψ h τ'.dw (X + τ'.ds) σ).sum := by
    filter_upwards [ae_mono hmono (ae_flux_meas H l X), ae_mono hmono (ae_grad_meas H l X),
      ae_restrict_mem measurableSet_Icc] with σ hF hg hσ
    have hσ' : σ ∈ Icc a b := hsub hσ
    have hb := flux_sq_le G Ψ H.F0 h Γ H.Γ0 l X σ
      (fun τ' hτ' j k => H.Gd σ hσ' τ'.gw ((hT τ' hτ').2.trans hl) _ j k) hg hF
    calc wt τ σ * (8 * ∑ k : Fin 2, cellL2Norm (fun z => (famWord G Ψ l h).F X σ z k) ^ 2)
        ≤ wt τ σ * (8 * (ENNReal.ofReal (4 * (terms h l).length * Γ ^ 2) *
            ((terms h l).map fun τ' => gradDen G Ψ h τ'.dw (X + τ'.ds) σ).sum)) := by
          gcongr
          exact hb
      _ = ENNReal.ofReal (32 * (terms h l).length * Γ ^ 2) *
          ((terms h l).map fun τ' => wt τ σ * gradDen G Ψ h τ'.dw (X + τ'.ds) σ).sum := by
          rw [list_smul_sum_ennreal]
          have e : ENNReal.ofReal (32 * (terms h l).length * Γ ^ 2) =
              8 * ENNReal.ofReal (4 * (terms h l).length * Γ ^ 2) := by
            rw [show (32 : ℝ) * (terms h l).length * Γ ^ 2 =
              8 * (4 * (terms h l).length * Γ ^ 2) by ring, ENNReal.ofReal_mul (by norm_num)]
            norm_num
          rw [e]
          ring
  refine (lintegral_mono_ae hae).trans_eq ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  refine lintegral_list_sum _ _ fun τ' _ => ?_
  exact (wt_measurable τ).aemeasurable.mul
    ((gradDen_aemeasurable H τ'.dw (X + τ'.ds)).mono_measure hmono)

/-- The endpoint and weighted gradient bounds of one component, keeping its own data. -/
theorem comp_bounds (l : List (Fin 2)) (hl : l.length ≤ P) (X : Vec 2) {τ : ℝ}
    (hτ : τ ∈ Icc a b) :
    cellL2Norm (cellValue ((famWord G Ψ l h).D X) τ) ^ 2 ≤
        wt τ a * cellL2Norm (cellValue ((famWord G Ψ l h).D X) a) ^ 2 +
          ((∫⁻ σ in Icc a τ, wt τ σ * cellL2Norm ((famWord G Ψ l h).src X σ) ^ 2) +
            ENNReal.ofReal (32 * (terms h l).length * Γ ^ 2) *
              ((terms h l).map fun τ' => ∫⁻ σ in Icc a τ, wt τ σ *
                gradDen G Ψ h τ'.dw (X + τ'.ds) σ).sum) ∧
      ∫⁻ σ in Icc a τ, wt τ σ * gradDen G Ψ h l X σ ≤
        2 * (wt τ a * cellL2Norm (cellValue ((famWord G Ψ l h).D X) a) ^ 2 +
          ((∫⁻ σ in Icc a τ, wt τ σ * cellL2Norm ((famWord G Ψ l h).src X σ) ^ 2) +
            ENNReal.ofReal (32 * (terms h l).length * Γ ^ 2) *
              ((terms h l).map fun τ' => ∫⁻ σ in Icc a τ, wt τ σ *
                gradDen G Ψ h τ'.dw (X + τ'.ds) σ).sum)) := by
  have hsub : Icc a τ ⊆ Icc a b := Icc_subset_Icc le_rfl hτ.2
  have hmono : volume.restrict (Icc a τ) ≤ volume.restrict (Icc a b) :=
    Measure.restrict_mono hsub le_rfl
  have hsrcm : AEMeasurable (fun σ => wt τ σ * cellL2Norm ((famWord G Ψ l h).src X σ) ^ 2)
      (volume.restrict (Icc a τ)) :=
    (wt_measurable τ).aemeasurable.mul ((src_aemeasurable H l X).mono_measure hmono)
  have hforce : ∫⁻ σ in Icc a τ, wt τ σ * (cellL2Norm ((famWord G Ψ l h).src X σ) ^ 2 +
      8 * ∑ k : Fin 2, cellL2Norm (fun z => (famWord G Ψ l h).F X σ z k) ^ 2) ≤
      (∫⁻ σ in Icc a τ, wt τ σ * cellL2Norm ((famWord G Ψ l h).src X σ) ^ 2) +
        ENNReal.ofReal (32 * (terms h l).length * Γ ^ 2) *
          ((terms h l).map fun τ' => ∫⁻ σ in Icc a τ, wt τ σ *
            gradDen G Ψ h τ'.dw (X + τ'.ds) σ).sum := by
    simp_rw [mul_add]
    rw [lintegral_add_left' hsrcm]
    exact add_le_add le_rfl (flux_part_le H l hl X hτ)
  have hsol := member_sol H l X
  have hE := cell_endpoint_bound H.hab (fun t => G t X) (fun _ _ => 0) (fun i j => H.Gm X i j)
    (fun t ht i j => H.Gs t ht X i j) (fun t ht ξ => H.Ge t ht X ξ) (fun _ _ _ => rfl)
    ((famWord G Ψ l h).src X) ((famWord G Ψ l h).F X) (famWord_srcm G Ψ H.srcm h l X)
    (famWord_Fm H.fam H.F0 H.Gm h l X) ((famWord G Ψ l h).D X) hsol
    (fun t ht => member_mean H l X t ht) τ hτ
  have hW := cell_weighted_gradient_bound H.hab (fun t => G t X) (fun _ _ => 0)
    (fun i j => H.Gm X i j) (fun t ht i j => H.Gs t ht X i j) (fun t ht ξ => H.Ge t ht X ξ)
    (fun _ _ _ => rfl) ((famWord G Ψ l h).src X) ((famWord G Ψ l h).F X)
    (famWord_srcm G Ψ H.srcm h l X) (famWord_Fm H.fam H.F0 H.Gm h l X) ((famWord G Ψ l h).D X)
    hsol (fun t ht => member_mean H l X t ht) τ hτ
  refine ⟨hE.trans (add_le_add le_rfl hforce), hW.trans ?_⟩
  rw [show ENNReal.ofReal 2 = 2 by norm_num]
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hforce) zero_le

end Comp

theorem finset_sum_list_sum {α : Type*} (L : List α) (f : κ → α → ℝ≥0∞) :
    ∑ k, (L.map (f k)).sum = (L.map fun x => ∑ k, f k x).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

section Vec

variable (H : ∀ k, EngineHyp a b G (Φ k) h Γ P)
include H

theorem member_stepV (l : List (Fin 2)) (hl : l.length ≤ P) (X : Vec 2) {τ : ℝ}
    (hτ : τ ∈ Icc a b) (Kp : ℝ≥0∞)
    (hIH : ∀ τ' ∈ terms h l, ∫⁻ σ in Icc a τ, wt τ σ *
      ∑ k, gradDen G (Φ k) h τ'.dw (X + τ'.ds) σ ≤ Kp * dataBdV a G Φ h l.length τ) :
    ∑ k, cellL2Norm (cellValue ((famWord G (Φ k) l h).D X) τ) ^ 2 ≤
        (1 + ENNReal.ofReal (32 * (terms h l).length ^ 2 * Γ ^ 2) * Kp) *
          dataBdV a G Φ h l.length τ ∧
      ∫⁻ σ in Icc a τ, wt τ σ * ∑ k, gradDen G (Φ k) h l X σ ≤
        2 * ((1 + ENNReal.ofReal (32 * (terms h l).length ^ 2 * Γ ^ 2) * Kp) *
          dataBdV a G Φ h l.length τ) := by
  set T := (terms h l).length
  have hsub : Icc a τ ⊆ Icc a b := Icc_subset_Icc le_rfl hτ.2
  have hmono : volume.restrict (Icc a τ) ≤ volume.restrict (Icc a b) :=
    Measure.restrict_mono hsub le_rfl
  set g : κ → FluxTerm → ℝ≥0∞ := fun k τ' => ∫⁻ σ in Icc a τ, wt τ σ *
    gradDen G (Φ k) h τ'.dw (X + τ'.ds) σ
  -- the summed right side
  have hR : ∑ k, (wt τ a * cellL2Norm (cellValue ((famWord G (Φ k) l h).D X) a) ^ 2 +
      ((∫⁻ σ in Icc a τ, wt τ σ * cellL2Norm ((famWord G (Φ k) l h).src X σ) ^ 2) +
        ENNReal.ofReal (32 * T * Γ ^ 2) * ((terms h l).map (g k)).sum)) ≤
      (1 + ENNReal.ofReal (32 * T ^ 2 * Γ ^ 2) * Kp) * dataBdV a G Φ h l.length τ := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      finset_sum_list_sum]
    have hinit : ∑ k, cellL2Norm (cellValue ((famWord G (Φ k) l h).D X) a) ^ 2 ≤
        initSupV a G Φ h l.length :=
      le_iSup_of_le (⟨l, le_rfl⟩ : {l' : List (Fin 2) // l'.length ≤ l.length})
        (le_iSup (fun X' => ∑ k, cellL2Norm (cellValue ((famWord G (Φ k) l h).D X') a) ^ 2) X)
    have hsrc : ∑ k, ∫⁻ σ in Icc a τ, wt τ σ * cellL2Norm ((famWord G (Φ k) l h).src X σ) ^ 2 ≤
        ∫⁻ σ in Icc a τ, wt τ σ * srcSupV G Φ h l.length σ := by
      have hm : ∀ k, AEMeasurable (fun σ => wt τ σ *
          cellL2Norm ((famWord G (Φ k) l h).src X σ) ^ 2) (volume.restrict (Icc a τ)) := fun k =>
        (wt_measurable τ).aemeasurable.mul ((src_aemeasurable (H k) l X).mono_measure hmono)
      rw [← lintegral_finsetSum' _ fun k _ => hm k]
      refine lintegral_mono fun σ => ?_
      rw [← Finset.mul_sum]
      gcongr
      exact le_iSup_of_le (⟨l, le_rfl⟩ : {l' : List (Fin 2) // l'.length ≤ l.length})
        (le_iSup (fun X' => ∑ k, cellL2Norm ((famWord G (Φ k) l h).src X' σ) ^ 2) X)
    have hgr : ((terms h l).map fun τ' => ∑ k, g k τ').sum ≤ T * (Kp * dataBdV a G Φ h l.length τ) := by
      have : ∀ L : List FluxTerm, (∀ τ' ∈ L, τ' ∈ terms h l) →
          (L.map fun τ' => ∑ k, g k τ').sum ≤ L.length * (Kp * dataBdV a G Φ h l.length τ) := by
        intro L hL
        induction L with
        | nil => simp
        | cons τ' L ih =>
            simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
            rw [add_mul, one_mul, add_comm]
            refine add_le_add (ih fun x hx => hL x (by simp [hx])) ?_
            have hτ' := hIH τ' (hL τ' (by simp))
            simp only [g]
            have hm : ∀ k, AEMeasurable (fun σ => wt τ σ *
                gradDen G (Φ k) h τ'.dw (X + τ'.ds) σ) (volume.restrict (Icc a τ)) := fun k =>
              (wt_measurable τ).aemeasurable.mul
                ((gradDen_aemeasurable (H k) τ'.dw (X + τ'.ds)).mono_measure hmono)
            rw [← lintegral_finsetSum' _ fun k _ => hm k]
            simp_rw [← Finset.mul_sum]
            exact hτ'
      exact this _ fun x hx => hx
    have hcoef : ENNReal.ofReal (32 * T * Γ ^ 2) * (T * (Kp * dataBdV a G Φ h l.length τ)) =
        ENNReal.ofReal (32 * T ^ 2 * Γ ^ 2) * Kp * dataBdV a G Φ h l.length τ := by
      rw [show (32 : ℝ) * T ^ 2 * Γ ^ 2 = (32 * T * Γ ^ 2) * T by ring,
        ENNReal.ofReal_mul (p := 32 * (T : ℝ) * Γ ^ 2) (by positivity), ENNReal.ofReal_natCast]
      ring
    calc _ ≤ wt τ a * initSupV a G Φ h l.length + ((∫⁻ σ in Icc a τ, wt τ σ *
            srcSupV G Φ h l.length σ) + ENNReal.ofReal (32 * T * Γ ^ 2) *
              (T * (Kp * dataBdV a G Φ h l.length τ))) := by gcongr
      _ = dataBdV a G Φ h l.length τ +
            ENNReal.ofReal (32 * T ^ 2 * Γ ^ 2) * Kp * dataBdV a G Φ h l.length τ := by
          rw [hcoef, ← add_assoc]; rfl
      _ = _ := by ring
  have hc := fun k => comp_bounds (H k) l hl X hτ
  constructor
  · exact (Finset.sum_le_sum fun k _ => (hc k).1).trans hR
  · have hgm : ∀ k ∈ (Finset.univ : Finset κ), AEMeasurable (fun σ => wt τ σ *
        gradDen G (Φ k) h l X σ) (volume.restrict (Icc a τ)) := fun k _ =>
      (wt_measurable τ).aemeasurable.mul ((gradDen_aemeasurable (H k) l X).mono_measure hmono)
    have e : ∫⁻ σ in Icc a τ, wt τ σ * ∑ k, gradDen G (Φ k) h l X σ =
        ∑ k, ∫⁻ σ in Icc a τ, wt τ σ * gradDen G (Φ k) h l X σ := by
      rw [← lintegral_finsetSum' _ hgm]
      simp_rw [Finset.mul_sum]
    rw [e]
    refine (Finset.sum_le_sum fun k _ => (hc k).2).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hR zero_le

/-- **The vector slow engine.** -/
theorem engine_boundV : ∀ n, n ≤ P → ∀ l : List (Fin 2), l.length = n → ∀ X, ∀ τ ∈ Icc a b,
    ∑ k, cellL2Norm (cellValue ((famWord G (Φ k) l h).D X) τ) ^ 2 ≤
        engK Γ n * dataBdV a G Φ h n τ ∧
      ∫⁻ σ in Icc a τ, wt τ σ * ∑ k, gradDen G (Φ k) h l X σ ≤ engK Γ n * dataBdV a G Φ h n τ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnP l hl X τ hτ
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have hT : terms h l = [] := by
      have h0 : (terms h l).length + 1 ≤ 1 := by simpa [hl] using terms_length_le h l
      exact List.eq_nil_of_length_eq_zero (by omega)
    obtain ⟨h1, h2⟩ := member_stepV H l (by omega) X hτ 0 (by simp [hT])
    rw [hl] at h1 h2
    simp only [hT, List.length_nil, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, zero_mul, ENNReal.ofReal_zero, add_zero] at h1 h2
    refine ⟨h1.trans ?_, h2.trans ?_⟩
    · rw [one_mul]
      exact le_mul_of_one_le_left zero_le (by simp [engK])
    · simp [engK]
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hIH : ∀ τ' ∈ terms h l, ∫⁻ σ in Icc a τ, wt τ σ *
        ∑ k, gradDen G (Φ k) h τ'.dw (X + τ'.ds) σ ≤ engK Γ n' * dataBdV a G Φ h l.length τ := by
      intro τ' hτ'
      have hlen := (mem_terms h l τ' hτ').1
      rw [hl] at hlen
      have := (ih τ'.dw.length (by omega) (by omega) τ'.dw rfl (X + τ'.ds) τ hτ).2
      refine this.trans (mul_le_mul' (engK_mono Γ (by omega)) (dataBdV_mono a G Φ h ?_ τ))
      omega
    obtain ⟨h1, h2⟩ := member_stepV H l (by omega) X hτ (engK Γ n') hIH
    rw [hl] at h1 h2
    have hT2 := terms_sq_le (h := h) l
    rw [hl] at hT2
    have hc : ENNReal.ofReal (32 * (terms h l).length ^ 2 * Γ ^ 2) ≤
        ENNReal.ofReal (32 * 4 ^ (n' + 1) * Γ ^ 2) :=
      ENNReal.ofReal_le_ofReal (by gcongr)
    have hc1 : 1 + ENNReal.ofReal (32 * (terms h l).length ^ 2 * Γ ^ 2) * engK Γ n' ≤
        1 + ENNReal.ofReal (32 * 4 ^ (n' + 1) * Γ ^ 2) * engK Γ n' := by gcongr
    have hK1 : 1 + ENNReal.ofReal (32 * 4 ^ (n' + 1) * Γ ^ 2) * engK Γ n' ≤ engK Γ (n' + 1) := by
      simp only [engK]
      calc 1 + ENNReal.ofReal (32 * 4 ^ (n' + 1) * Γ ^ 2) * engK Γ n'
          ≤ 2 * (1 + ENNReal.ofReal (32 * 4 ^ (n' + 1) * Γ ^ 2) * engK Γ n') :=
            le_mul_of_one_le_left zero_le (by norm_num)
        _ ≤ _ := le_add_self
    have hK2 : 2 * (1 + ENNReal.ofReal (32 * (terms h l).length ^ 2 * Γ ^ 2) * engK Γ n') ≤
        engK Γ (n' + 1) := by
      simp only [engK]
      exact (mul_le_mul_of_nonneg_left hc1 zero_le).trans le_add_self
    refine ⟨h1.trans (mul_le_mul_of_nonneg_right (hc1.trans hK1) zero_le), h2.trans ?_⟩
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hK2 zero_le

end Vec

end AVRegularity.QuietDecay
end

section
open MeasureTheory Set Filter Topology Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! The slow engine in derivative form: the cell `L²` norms of the slow derivatives of a family of
cell solutions at the time `τ` are bounded by the slow derivatives of its initial values and of its
sources, with the exponential weights; the difference quotients are removed by Fatou's lemma. -/

section
/-- Fatou's lemma along `h → 0`. -/
theorem fatou_nhds_ne {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    (f : ℝ → α → E) (F : α → E) (hm : ∀ h, h ≠ 0 → AEMeasurable (fun z => ‖f h z‖ₑ ^ 2) μ)
    (hlim : ∀ z, Tendsto (fun h => f h z) (𝓝[≠] 0) (𝓝 (F z))) (B : ℝ≥0∞)
    (hB : ∀ h, h ≠ 0 → ∫⁻ z, ‖f h z‖ₑ ^ 2 ∂μ ≤ B) :
    ∫⁻ z, ‖F z‖ₑ ^ 2 ∂μ ≤ B := by
  set s : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hs0 : ∀ k, s k ≠ 0 := fun k => by simp only [s]; positivity
  have hs : Tendsto s atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Eventually.of_forall fun k => hs0 k
  have hpt : ∀ z, ‖F z‖ₑ ^ 2 = liminf (fun k => ‖f (s k) z‖ₑ ^ 2) atTop := by
    intro z
    have h1 : Tendsto (fun k => ‖f (s k) z‖ₑ ^ 2) atTop (𝓝 (‖F z‖ₑ ^ 2)) :=
      ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp
        ((hlim z).comp hs))
    exact h1.liminf_eq.symm
  calc ∫⁻ z, ‖F z‖ₑ ^ 2 ∂μ = ∫⁻ z, liminf (fun k => ‖f (s k) z‖ₑ ^ 2) atTop ∂μ :=
        lintegral_congr hpt
    _ ≤ liminf (fun k => ∫⁻ z, ‖f (s k) z‖ₑ ^ 2 ∂μ) atTop :=
        lintegral_liminf_le' fun k => hm (s k) (hs0 k)
    _ ≤ B := liminf_le_of_le (by isBoundedDefault) fun b hb => by
        obtain ⟨k, hk⟩ := hb.exists
        exact hk.trans (hB (s k) (hs0 k))

theorem famWord_src_eq (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam)
    (l : List (Fin 2)) (h : ℝ) (σ : ℝ) (X z : Vec 2) :
    (famWord G Φ l h).src X σ z = slowDiffs l h (fun X' z' => Φ.src X' σ z') X z := by
  induction l using List.reverseRecOn generalizing X with
  | nil => rfl
  | append_singleton l i ih =>
      rw [famWord_src_append, slowDiffs_append, ih, ih]
      simp [sdiff, Complex.real_smul]

theorem diffs_eq_slowDiffs (w : List (Fin 2)) (h : ℝ) (g : Vec 2 → ℝ) (Y z : Vec 2) :
    diffs w h g Y = slowDiffs w h (fun X (_ : Vec 2) => g X) Y z := by
  induction w using List.reverseRecOn generalizing Y with
  | nil => rfl
  | append_singleton w i ih =>
      rw [diffs_append, slowDiffs_append]
      simp only [sdiff, ih]

theorem isSlowSmooth_const_fast {n : ℕ} {g : Vec 2 → ℝ} (hg : ContDiff ℝ (n : ℕ∞) g) :
    IsSlowSmooth n (fun X (_ : Vec 2) => g X) :=
  ⟨fun _ => hg, fun a ha => (hg.continuous_iteratedFDeriv (by exact_mod_cast ha)).comp
    continuous_fst⟩

/-- Difference quotients of a slow-only function are bounded by its derivatives. -/
theorem abs_diffs_le {n : ℕ} {g : Vec 2 → ℝ} (hg : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) g) {Γ : ℝ}
    (hΓ : ∀ w : List (Fin 2), w.length ≤ n → ∀ Y,
      ‖slowDerivs w (fun X (_ : Vec 2) => g X) Y 0‖ ≤ Γ)
    (w : List (Fin 2)) (hw : w.length ≤ n) {h : ℝ} (hh : h ≠ 0) (Y : Vec 2) :
    |diffs w h g Y| ≤ Γ := by
  have hΓ0 : 0 ≤ Γ := (norm_nonneg _).trans (hΓ [] (by simp) Y)
  have hS : IsSlowSmooth (w.length + 1) (fun X (_ : Vec 2) => g X) :=
    isSlowSmooth_const_fast (hg.of_le (by exact_mod_cast (by omega : w.length + 1 ≤ n + 1)))
  have hb := lintegral_slowDiffs_le hh w (fun X (_ : Vec 2) => g X) hS Y
  have hconst : ∀ (c : Vec 2 → ℝ) (Y' : Vec 2), (∀ z z', c z = c z') →
      ∫⁻ z in AVenhance.unitCube, ‖c z‖ₑ ^ 2 = ‖c 0‖ₑ ^ 2 := by
    intro c Y' hc
    rw [show (fun z => ‖c z‖ₑ ^ 2) = fun _ => ‖c 0‖ₑ ^ 2 from funext fun z => by rw [hc z 0],
      lintegral_const, Measure.restrict_apply_univ, volume_unitCube_eq_one, mul_one]
  have hfast0 : ∀ (l : List (Fin 2)) (φ : Vec 2 → Vec 2 → ℝ), (∀ X z z', φ X z = φ X z') →
      ∀ Y' z z', slowDerivs l φ Y' z = slowDerivs l φ Y' z' := by
    intro l
    induction l with
    | nil => intro φ hφ Y' z z'; exact hφ Y' z z'
    | cons i l ih =>
        intro φ hφ Y' z z'
        rw [slowDerivs_cons]
        refine ih _ (fun X z z' => ?_) Y' z z'
        unfold AVRegularity.slowPartial
        rw [show (fun X' => φ X' z) = fun X' => φ X' z' from funext fun X' => hφ X' z z']
  have hfast : ∀ (l : List (Fin 2)) (Y' z z' : Vec 2),
      slowDerivs l (fun X (_ : Vec 2) => g X) Y' z = slowDerivs l (fun X (_ : Vec 2) => g X) Y' z' :=
    fun l => hfast0 l _ fun _ _ _ => rfl
  have hd : ∀ z z', slowDiffs w h (fun X (_ : Vec 2) => g X) Y z =
      slowDiffs w h (fun X (_ : Vec 2) => g X) Y z' := fun z z' => by
    rw [← diffs_eq_slowDiffs, ← diffs_eq_slowDiffs]
  rw [hconst _ Y hd] at hb
  have hsup : (⨆ X' : Vec 2, ∫⁻ z in AVenhance.unitCube,
      ‖slowDerivs w.reverse (fun X (_ : Vec 2) => g X) X' z‖ₑ ^ 2) ≤ ENNReal.ofReal (Γ ^ 2) := by
    refine iSup_le fun X' => ?_
    rw [hconst _ X' (hfast w.reverse X'), enorm_sq_ofReal]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _)
      (hΓ w.reverse (by simpa using hw) X') 2)
  have h2 := hb.trans hsup
  rw [enorm_sq_ofReal, ← diffs_eq_slowDiffs] at h2
  have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
  rw [Real.norm_eq_abs] at h3
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) hΓ0 (by norm_num)).1 h3

/-- The hypotheses of the slow engine in derivative form. -/
structure EngineData (a b : ℝ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam)
    (Γ : ℝ) (P : ℕ) : Prop where
  hab : a ≤ b
  Gm : ∀ X i j, Measurable fun t => G t X i j
  Gs : ∀ t ∈ Icc a b, ∀ X i j, G t X i j = G t X j i
  Ge : ∀ t ∈ Icc a b, ∀ X (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t X i j * ξ i * ξ j ∧
    ∑ i, ∑ j, G t X i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2
  fam : IsCellFam (Icc a b) G (fun _ _ => 0) Φ
  F0 : Φ.F = fun _ _ _ => 0
  mean : ∀ X, ∀ t ∈ Icc a b, cellMean (cellValue (Φ.D X) t) = 0
  srcm : ∀ X, AEStronglyMeasurable (Function.uncurry (Φ.src X)) (winMeasure (Icc a b))
  Γ0 : 0 ≤ Γ
  Gsmooth : ∀ t ∈ Icc a b, ∀ j k, ContDiff ℝ ((P + 1 : ℕ) : ℕ∞) fun Y => G t Y j k
  Gder : ∀ t ∈ Icc a b, ∀ w : List (Fin 2), w.length ≤ P → ∀ Y j k,
    ‖slowDerivs w (fun X (_ : Vec 2) => G t X j k) Y 0‖ ≤ Γ
  valS : ∀ t ∈ Icc a b, IsSlowSmooth (P + 1) fun X z => cellValue (Φ.D X) t z
  srcS : ∀ t ∈ Icc a b, IsSlowSmooth (P + 1) fun X z => Φ.src X t z

variable {a b : ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {Φ : CellFam} {Γ : ℝ} {P : ℕ}

theorem EngineData.hyp (H : EngineData a b G Φ Γ P) {h : ℝ} (hh : h ≠ 0) :
    EngineHyp a b G Φ h Γ P :=
  ⟨H.hab, H.Gm, H.Gs, H.Ge, H.fam, H.F0, H.mean, H.srcm, H.Γ0, fun t ht gw hgw Y j k =>
    abs_diffs_le (H.Gsmooth t ht j k) (fun w hw Y => H.Gder t ht w hw Y j k) gw hgw hh Y⟩
end

/-! The mixed engine: fast derivatives of slow derivatives of a family of cell solutions, through
the translated families (fast difference quotients) and Fatou's lemma in the fast step. -/

section
/-- Fast difference quotients of a two-scale field. -/
def fastF (m : List (Fin 2)) (h : ℝ) (φ : Vec 2 → Vec 2 → ℂ) : Vec 2 → Vec 2 → ℂ :=
  fun X z => fastDiffs m h (φ X) z

theorem fastWord_src_eq (m : List (Fin 2)) (h : ℝ) (Φ : CellFam) (X : Vec 2) (t : ℝ) :
    (fastWord m h Φ).src X t = fastDiffs m h (Φ.src X t) := by
  induction m using List.reverseRecOn with
  | nil => rfl
  | append_singleton m i ih =>
      rw [fastWord_append, fastDiffs_append, ← ih]
      funext z
      simp [fastStep, sdiff, Complex.real_smul]

theorem isSlowSmooth_zshift {n : ℕ} {φ : Vec 2 → Vec 2 → ℂ} (hφ : IsSlowSmooth n φ) (c : Vec 2) :
    IsSlowSmooth n (fun X z => φ X (z + c)) :=
  ⟨fun y => hφ.1 (y + c), fun a ha => (hφ.2 a ha).comp
    (continuous_fst.prodMk (continuous_snd.add continuous_const))⟩

theorem isSlowSmooth_fastF {n : ℕ} {φ : Vec 2 → Vec 2 → ℂ} (hφ : IsSlowSmooth n φ)
    (m : List (Fin 2)) (h : ℝ) : IsSlowSmooth n (fastF m h φ) := by
  induction m using List.reverseRecOn with
  | nil => exact hφ
  | append_singleton m i ih =>
      have e : fastF (m ++ [i]) h φ =
          fun X z => h⁻¹ • (fastF m h φ X (z + h • basisVec i) - fastF m h φ X z) := by
        funext X z; simp [fastF, fastDiffs_append, sdiff]
      rw [e]
      exact ((isSlowSmooth_zshift ih _).sub ih).const_smul h⁻¹

theorem slowPartial_fastF {n : ℕ} {φ : Vec 2 → Vec 2 → ℂ} (hφ : IsSlowSmooth (n + 1) φ)
    (m : List (Fin 2)) (h : ℝ) (i : Fin 2) :
    AVRegularity.slowPartial i (fastF m h φ) = fastF m h (AVRegularity.slowPartial i φ) := by
  induction m using List.reverseRecOn with
  | nil => rfl
  | append_singleton m j ih =>
      have e : ∀ ψ : Vec 2 → Vec 2 → ℂ, fastF (m ++ [j]) h ψ =
          fun X z => h⁻¹ • (fastF m h ψ X (z + h • basisVec j) - fastF m h ψ X z) := by
        intro ψ; funext X z; simp [fastF, fastDiffs_append, sdiff]
      rw [e, e]
      funext X z
      have hd : ∀ w, DifferentiableAt ℝ (fun X' => fastF m h φ X' w) X := fun w =>
        (((isSlowSmooth_fastF hφ m h).1 w).differentiable (by simp)) X
      have hH : HasFDerivAt (fun X' => h⁻¹ • (fastF m h φ X' (z + h • basisVec j) - fastF m h φ X' z))
          (h⁻¹ • (fderiv ℝ (fun X' => fastF m h φ X' (z + h • basisVec j)) X -
            fderiv ℝ (fun X' => fastF m h φ X' z) X)) X :=
        ((hd _).hasFDerivAt.sub (hd _).hasFDerivAt).const_smul h⁻¹
      unfold AVRegularity.slowPartial
      change fderiv ℝ (fun X' => h⁻¹ • (fastF m h φ X' (z + h • basisVec j) - fastF m h φ X' z)) X
        (basisVec i) = _
      rw [hH.fderiv]
      simp only [smul_apply, sub_apply]
      have h2 : ∀ w, fderiv ℝ (fun X' => fastF m h φ X' w) X (basisVec i) =
          fastF m h (fun X z => fderiv ℝ (fun X' => φ X' z) X (basisVec i)) X w := fun w => by
        exact congrFun (congrFun ih X) w
      rw [h2, h2]

theorem slowDerivs_fastF : ∀ (l : List (Fin 2)) {φ : Vec 2 → Vec 2 → ℂ},
    IsSlowSmooth (l.length + 1) φ → ∀ (m : List (Fin 2)) (h : ℝ),
      slowDerivs l (fastF m h φ) = fastF m h (slowDerivs l φ) := by
  intro l
  induction l with
  | nil => intro φ _ m h; rfl
  | cons i l ih =>
      intro φ hφ m h
      rw [slowDerivs_cons, slowDerivs_cons]
      have hφ' : IsSlowSmooth (l.length + 1 + 1) φ := by simpa using hφ
      rw [slowPartial_fastF hφ' m h i]
      exact ih (hφ'.slowPartial i) m h

variable {a b : ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {Φ : CellFam} {Γ : ℝ} {P : ℕ}

/-- The translated family satisfies the engine hypotheses. -/
theorem EngineData.fast (H : EngineData a b G Φ Γ P)
    (hsrcP : ∀ X, ∀ t ∈ Icc a b, AVenhance.IsZ2Periodic (Φ.src X t)) (m : List (Fin 2)) (h : ℝ) :
    EngineData a b G (fastWord m h Φ) Γ P := by
  have hFP : ∀ X, ∀ t ∈ Icc a b, AVenhance.IsZ2Periodic (Φ.F X t) := by
    intro X t _ n z; rw [H.F0]
  refine ⟨H.hab, H.Gm, H.Gs, H.Ge, isCellFam_fastWord H.fam hsrcP hFP m h, fastWord_F_zero H.F0 m h,
    fastWord_cellMean H.fam hsrcP hFP H.mean m h,
    fastWord_src_aestronglyMeasurable measurableSet_Icc hsrcP H.srcm m h, H.Γ0, H.Gsmooth, H.Gder,
    fun t ht => ?_, fun t ht => ?_⟩
  · have e : (fun X z => cellValue ((fastWord m h Φ).D X) t z) =
        fastF m h (fun X z => cellValue (Φ.D X) t z) := by
      funext X z; rw [cellValue_fastWord]; rfl
    rw [e]; exact isSlowSmooth_fastF (H.valS t ht) m h
  · have e : (fun X z => (fastWord m h Φ).src X t z) = fastF m h (fun X z => Φ.src X t z) := by
      funext X z; rw [fastWord_src_eq]; rfl
    rw [e]; exact isSlowSmooth_fastF (H.srcS t ht) m h
end

/-! The vector slow engine in derivative form (dimension-free): the data are the suprema over slow
points and words of the SUMS over components of the cell `L²` norms of the slow derivatives. -/

section
variable {a b : ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {Γ : ℝ} {P : ℕ}
variable {κ : Type*} [Fintype κ] {Φ : κ → CellFam}

/-- The value fields of the components at the time `t`. -/
def valF (Φ : κ → CellFam) (t : ℝ) : κ → Vec 2 → Vec 2 → ℂ :=
  fun k X z => cellValue ((Φ k).D X) t z

/-- The source fields of the components at the time `t`. -/
def srcF (Φ : κ → CellFam) (t : ℝ) : κ → Vec 2 → Vec 2 → ℂ :=
  fun k X z => (Φ k).src X t z

/-- The summed initial slow derivative data. -/
def initDV (a : ℝ) (Φ : κ → CellFam) (n : ℕ) : ℝ≥0∞ :=
  ⨆ (l : {l : List (Fin 2) // l.length ≤ n}) (X : Vec 2),
    ∑ k, ∫⁻ z in AVenhance.unitCube, ‖slowDerivs l.1 (valF Φ a k) X z‖ₑ ^ 2

/-- The summed source slow derivative data. -/
def srcDV (Φ : κ → CellFam) (n : ℕ) (σ : ℝ) : ℝ≥0∞ :=
  ⨆ (l : {l : List (Fin 2) // l.length ≤ n}) (X : Vec 2),
    ∑ k, ∫⁻ z in AVenhance.unitCube, ‖slowDerivs l.1 (srcF Φ σ k) X z‖ₑ ^ 2

theorem lintegral_vecF (φ : κ → Vec 2 → ℂ) (hφ : ∀ k, Continuous (φ k)) :
    ∫⁻ z in AVenhance.unitCube, ‖(WithLp.toLp 2 fun k => φ k z : PiLp 2 (fun _ : κ => ℂ))‖ₑ ^ 2 =
      ∑ k, ∫⁻ z in AVenhance.unitCube, ‖φ k z‖ₑ ^ 2 := by
  simp_rw [enorm_sq_toLp]
  exact lintegral_finsetSum' _ fun k _ => ((hφ k).enorm.measurable.pow_const 2).aemeasurable

theorem slowDerivs_eq_orderedDerivative (l : List (Fin 2)) (φ : Vec 2 → Vec 2 → ℂ) (X z : Vec 2) :
    slowDerivs l φ X z = orderedDerivative (m := l.length) l.get (fun X' => φ X' z) X := by
  unfold orderedDerivative
  rw [List.ofFn_get]
  induction l generalizing φ with
  | nil => rfl
  | cons i l ih =>
      rw [slowDerivs_cons, ih]
      rfl

theorem continuous_slowDerivs {n : ℕ} {φ : Vec 2 → Vec 2 → ℂ} (hφ : IsSlowSmooth n φ)
    (l : List (Fin 2)) (hl : l.length ≤ n) (X : Vec 2) : Continuous (slowDerivs l φ X) := by
  have h1 := hφ.continuous_orderedDerivative hl (l.get)
  have h2 : Continuous fun z => orderedDerivative (m := l.length) l.get (fun X' => φ X' z) X :=
    h1.comp (continuous_const.prodMk continuous_id)
  simpa only [← slowDerivs_eq_orderedDerivative] using h2

/-- The packaged difference-quotient bound with the sum inside the supremum. -/
theorem sum_lintegral_slowDiffs_le {n : ℕ} {φ : κ → Vec 2 → Vec 2 → ℂ}
    (hφ : ∀ k, IsSlowSmooth (n + 1) (φ k)) {h : ℝ} (hh : h ≠ 0) (l : List (Fin 2))
    (hl : l.length ≤ n) (X : Vec 2) :
    ∑ k, ∫⁻ z in AVenhance.unitCube, ‖slowDiffs l h (φ k) X z‖ₑ ^ 2 ≤
      ⨆ (l' : {l : List (Fin 2) // l.length ≤ n}) (X' : Vec 2),
        ∑ k, ∫⁻ z in AVenhance.unitCube, ‖slowDerivs l'.1 (φ k) X' z‖ₑ ^ 2 := by
  have hv : IsSlowSmooth (l.length + 1) (vecF φ) :=
    isSlowSmooth_vecF fun k => (hφ k).mono (by omega)
  have hd := lintegral_slowDiffs_le hh l (vecF φ) hv X
  have hr : ∀ k, IsSlowSmooth (l.reverse.length + 1) (φ k) := fun k =>
    (hφ k).mono (by simp; omega)
  have e1 : ∫⁻ z in AVenhance.unitCube, ‖slowDiffs l h (vecF φ) X z‖ₑ ^ 2 =
      ∑ k, ∫⁻ z in AVenhance.unitCube, ‖slowDiffs l h (φ k) X z‖ₑ ^ 2 := by
    simp_rw [slowDiffs_vecF]
    exact lintegral_vecF _ (fun k => (isSlowSmooth_slowDiffs (hφ k) l h).continuous_fast X)
  have e2 : ∀ X', ∫⁻ z in AVenhance.unitCube, ‖slowDerivs l.reverse (vecF φ) X' z‖ₑ ^ 2 =
      ∑ k, ∫⁻ z in AVenhance.unitCube, ‖slowDerivs l.reverse (φ k) X' z‖ₑ ^ 2 := by
    intro X'
    simp_rw [slowDerivs_vecF l.reverse hr X']
    exact lintegral_vecF _ (fun k => continuous_slowDerivs ((hφ k).mono (by simp; omega))
      l.reverse le_rfl X')
  rw [e1] at hd
  refine hd.trans (iSup_le fun X' => ?_)
  rw [e2 X']
  exact le_iSup_of_le (⟨l.reverse, by simpa using hl⟩ : {l : List (Fin 2) // l.length ≤ n})
    (le_iSup (fun X'' => ∑ k, ∫⁻ z in AVenhance.unitCube,
      ‖slowDerivs l.reverse (φ k) X'' z‖ₑ ^ 2) X')

theorem cellL2Norm_famWord_value (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Ψ : CellFam)
    {n : ℕ} {t : ℝ} (hS : IsSlowSmooth n fun X z => cellValue (Ψ.D X) t z) (l : List (Fin 2)) (h : ℝ)
    (X : Vec 2) :
    cellL2Norm (cellValue ((famWord G Ψ l h).D X) t) ^ 2 =
      ∫⁻ z in AVenhance.unitCube,
        ‖slowDiffs l h (fun X' z' => cellValue (Ψ.D X') t z') X z‖ₑ ^ 2 := by
  rw [show cellValue ((famWord G Ψ l h).D X) t =
      fun z => slowDiffs l h (fun X' z' => cellValue (Ψ.D X') t z') X z from
    funext fun z => cellValue_famWord G Ψ l h t X z]
  exact cellL2Norm_sq_eq_lintegral ((isSlowSmooth_slowDiffs hS l h).continuous_fast X).aestronglyMeasurable

theorem cellL2Norm_famWord_src (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Ψ : CellFam)
    {n : ℕ} {σ : ℝ} (hS : IsSlowSmooth n fun X z => Ψ.src X σ z) (l : List (Fin 2)) (h : ℝ)
    (X : Vec 2) :
    cellL2Norm ((famWord G Ψ l h).src X σ) ^ 2 =
      ∫⁻ z in AVenhance.unitCube, ‖slowDiffs l h (fun X' z' => Ψ.src X' σ z') X z‖ₑ ^ 2 := by
  rw [show (famWord G Ψ l h).src X σ = fun z => slowDiffs l h (fun X' z' => Ψ.src X' σ z') X z from
    funext fun z => famWord_src_eq G Ψ l h σ X z]
  exact cellL2Norm_sq_eq_lintegral ((isSlowSmooth_slowDiffs hS l h).continuous_fast X).aestronglyMeasurable

/-- **The vector slow engine in derivative form.** -/
theorem engine_derivV (hab : a ≤ b) (H : ∀ k, EngineData a b G (Φ k) Γ P) (l : List (Fin 2))
    (hl : l.length ≤ P) (X : Vec 2) {τ : ℝ} (hτ : τ ∈ Icc a b) :
    ∑ k, ∫⁻ z in AVenhance.unitCube, ‖slowDerivs l (valF Φ τ k) X z‖ₑ ^ 2 ≤
      engK Γ l.length * (wt τ a * initDV a Φ l.length +
        ∫⁻ σ in Icc a τ, wt τ σ * srcDV Φ l.length σ) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hvS : ∀ k, IsSlowSmooth (P + 1) (valF Φ τ k) := fun k => (H k).valS τ hτ
  have hvl : ∀ k, IsSlowSmooth (l.length + 1) (valF Φ τ k) := fun k => (hvS k).mono (by omega)
  have e0 : ∑ k, ∫⁻ z in AVenhance.unitCube, ‖slowDerivs l (valF Φ τ k) X z‖ₑ ^ 2 =
      ∫⁻ z in AVenhance.unitCube, ‖slowDerivs l (vecF (valF Φ τ)) X z‖ₑ ^ 2 := by
    simp_rw [slowDerivs_vecF l hvl X]
    exact (lintegral_vecF _ fun k => continuous_slowDerivs (hvl k) l (by omega) X).symm
  rw [e0]
  have hV : IsSlowSmooth (l.reverse.length + 1) (vecF (valF Φ τ)) :=
    isSlowSmooth_vecF fun k => (hvS k).mono (by simp; omega)
  refine fatou_nhds_ne (fun h z => slowDiffs l.reverse h (vecF (valF Φ τ)) X z) _
    (fun h _ => ?_) (fun z => ?_) _ (fun h hh => ?_)
  · exact (((isSlowSmooth_slowDiffs hV l.reverse h).continuous_fast X).enorm.measurable.pow_const
      2).aemeasurable
  · simpa using slowDiffs_tendsto l.reverse (vecF (valF Φ τ)) hV X z
  · have e1 : ∫⁻ z in AVenhance.unitCube, ‖slowDiffs l.reverse h (vecF (valF Φ τ)) X z‖ₑ ^ 2 =
        ∑ k, cellL2Norm (cellValue ((famWord G (Φ k) l.reverse h).D X) τ) ^ 2 := by
      simp_rw [slowDiffs_vecF]
      rw [lintegral_vecF _ fun k =>
        (isSlowSmooth_slowDiffs (hvS k) l.reverse h).continuous_fast X]
      exact Finset.sum_congr rfl fun k _ => (cellL2Norm_famWord_value G (Φ k) (hvS k) _ h X).symm
    rw [e1]
    refine (engine_boundV (fun k => (H k).hyp hh) l.length hl l.reverse (by simp) X τ hτ).1.trans
      (mul_le_mul_of_nonneg_left ?_ zero_le)
    unfold dataBdV
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le) (lintegral_mono_ae ?_)
    · refine iSup_le fun l' => iSup_le fun X' => ?_
      rw [Finset.sum_congr rfl fun k _ => cellL2Norm_famWord_value G (Φ k) ((H k).valS a ha) l'.1 h X']
      exact sum_lintegral_slowDiffs_le (n := l.length)
        (fun k => ((H k).valS a ha).mono (by omega)) hh l'.1 l'.2 X'
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
      have hσ' : σ ∈ Icc a b := ⟨hσ.1, hσ.2.trans hτ.2⟩
      refine mul_le_mul_of_nonneg_left (iSup_le fun l' => iSup_le fun X' => ?_) zero_le
      rw [Finset.sum_congr rfl fun k _ =>
        cellL2Norm_famWord_src G (Φ k) ((H k).srcS σ hσ') l'.1 h X']
      exact sum_lintegral_slowDiffs_le (n := l.length)
        (fun k => ((H k).srcS σ hσ').mono (by omega)) hh l'.1 l'.2 X'
end

/-! The vector mixed engine (dimension-free): fast derivatives of slow derivatives of all
components, summed over components, through the translated families and Fatou's lemma. -/

section
variable {a b : ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {Γ : ℝ} {P : ℕ}
variable {κ : Type*} [Fintype κ] {Φ : κ → CellFam}

/-- Fatou's lemma along `h → 0` for nonnegative extended functions. -/
theorem fatou_nhds_ne' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : ℝ → α → ℝ≥0∞) (F : α → ℝ≥0∞) (hm : ∀ h, h ≠ 0 → AEMeasurable (g h) μ)
    (hlim : ∀ z, Tendsto (fun h => g h z) (𝓝[≠] 0) (𝓝 (F z))) (B : ℝ≥0∞)
    (hB : ∀ h, h ≠ 0 → ∫⁻ z, g h z ∂μ ≤ B) :
    ∫⁻ z, F z ∂μ ≤ B := by
  set s : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hs0 : ∀ k, s k ≠ 0 := fun k => by simp only [s]; positivity
  have hs : Tendsto s atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Eventually.of_forall fun k => hs0 k
  have hpt : ∀ z, F z = liminf (fun k => g (s k) z) atTop := fun z =>
    (((hlim z).comp hs).liminf_eq).symm
  calc ∫⁻ z, F z ∂μ = ∫⁻ z, liminf (fun k => g (s k) z) atTop ∂μ := lintegral_congr hpt
    _ ≤ liminf (fun k => ∫⁻ z, g (s k) z ∂μ) atTop :=
        lintegral_liminf_le' fun k => hm (s k) (hs0 k)
    _ ≤ B := liminf_le_of_le (by isBoundedDefault) fun b hb => by
        obtain ⟨k, hk⟩ := hb.exists
        exact hk.trans (hB (s k) (hs0 k))

/-- The summed mixed initial data. -/
def initMDV (a : ℝ) (Φ : κ → CellFam) (n : ℕ) (m : List (Fin 2)) : ℝ≥0∞ :=
  ⨆ (l : {l : List (Fin 2) // l.length ≤ n}) (X : Vec 2),
    ∑ k, ∫⁻ z in AVenhance.unitCube, ‖fastDerivs m (slowDerivs l.1 (valF Φ a k) X) z‖ₑ ^ 2

/-- The summed mixed source data. -/
def srcMDV (Φ : κ → CellFam) (n : ℕ) (m : List (Fin 2)) (σ : ℝ) : ℝ≥0∞ :=
  ⨆ (l : {l : List (Fin 2) // l.length ≤ n}) (X : Vec 2),
    ∑ k, ∫⁻ z in AVenhance.unitCube, ‖fastDerivs m (slowDerivs l.1 (srcF Φ σ k) X) z‖ₑ ^ 2

theorem contDiff_fastDerivs {k : ℕ} : ∀ (m : List (Fin 2)) {g : Vec 2 → ℂ},
    ContDiff ℝ ((k + m.length : ℕ) : ℕ∞) g → ContDiff ℝ (k : ℕ∞) (fastDerivs m g) := by
  intro m
  induction m with
  | nil => intro g hg; simpa [fastDerivs] using hg
  | cons i m ih =>
      intro g hg
      rw [fastDerivs_cons]
      refine ih ?_
      have : ContDiff ℝ (((k + m.length : ℕ) : WithTop ℕ∞) + 1) g := by
        refine hg.of_le ?_
        simp only [List.length_cons]
        exact_mod_cast le_of_eq (by ring)
      exact contDiff_fderiv_apply this i

theorem tendsto_enorm_sq {f : ℝ → ℂ} {c : ℂ} (h : Tendsto f (𝓝[≠] 0) (𝓝 c)) :
    Tendsto (fun x => ‖f x‖ₑ ^ 2) (𝓝[≠] 0) (𝓝 (‖c‖ₑ ^ 2)) :=
  ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp h)
end

/-! The vector mixed engine with fast regularity `C^Q` for fast words of length `≤ Q` (no extra
fast derivative), through the sharp convergence of the fast difference quotients. -/

section
variable {a b : ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {Γ : ℝ} {P : ℕ}
variable {κ : Type*} [Fintype κ] {Φ : κ → CellFam}

/-- **The vector mixed engine**, with fast regularity of the order of the fast word only. -/
theorem engine_mixedV_sharp (hab : a ≤ b) (H : ∀ k, EngineData a b G (Φ k) Γ P)
    (hsrcP : ∀ k X, ∀ t ∈ Icc a b, AVenhance.IsZ2Periodic ((Φ k).src X t)) (Q : ℕ)
    (hvalF : ∀ k, ∀ t ∈ Icc a b, ∀ l : List (Fin 2), l.length ≤ P → ∀ X,
      ContDiff ℝ (Q : ℕ∞) (slowDerivs l (valF Φ t k) X) ∧
      AVenhance.IsZ2Periodic (slowDerivs l (valF Φ t k) X))
    (hsrcF : ∀ k, ∀ t ∈ Icc a b, ∀ l : List (Fin 2), l.length ≤ P → ∀ X,
      ContDiff ℝ (Q : ℕ∞) (slowDerivs l (srcF Φ t k) X) ∧
      AVenhance.IsZ2Periodic (slowDerivs l (srcF Φ t k) X))
    (l : List (Fin 2)) (hl : l.length ≤ P) (m : List (Fin 2)) (hm : m.length ≤ Q)
    (X : Vec 2) {τ : ℝ} (hτ : τ ∈ Icc a b) :
    ∑ k, ∫⁻ z in AVenhance.unitCube, ‖fastDerivs m (slowDerivs l (valF Φ τ k) X) z‖ₑ ^ 2 ≤
      engK Γ l.length * (wt τ a * initMDV a Φ l.length m +
        ∫⁻ σ in Icc a τ, wt τ σ * srcMDV Φ l.length m σ) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hcd : ∀ {g : Vec 2 → ℂ}, ContDiff ℝ (Q : ℕ∞) g →
      ContDiff ℝ (m.reverse.length : WithTop ℕ∞) g := fun hg => hg.of_le (by
        rw [List.length_reverse]; exact_mod_cast hm)
  have hcont : ∀ {g : Vec 2 → ℂ}, ContDiff ℝ (Q : ℕ∞) g → Continuous (fastDerivs m g) := fun hg =>
    (contDiff_fastDerivs (k := 0) m (hg.of_le (by exact_mod_cast (by omega : 0 + m.length ≤ Q)))).continuous
  set gF : κ → Vec 2 → ℂ := fun k => slowDerivs l (valF Φ τ k) X
  rw [← lintegral_finsetSum' _ fun k _ =>
    ((hcont (hvalF k τ hτ l hl X).1).enorm.measurable.pow_const 2).aemeasurable]
  refine fatou_nhds_ne' (fun h z => ∑ k, ‖fastDiffs m.reverse h (gF k) z‖ₑ ^ 2) _
    (fun h _ => ?_) (fun z => ?_) _ (fun h hh => ?_)
  · exact Finset.aemeasurable_fun_sum _ fun k _ =>
      (((contDiff_fastDiffs (hvalF k τ hτ l hl X).1 m.reverse h).continuous).enorm.measurable.pow_const
        2).aemeasurable
  · refine tendsto_finsetSum _ fun k _ => tendsto_enorm_sq ?_
    simpa using fastDiffs_tendsto_sharp m.reverse (gF k) (hcd (hvalF k τ hτ l hl X).1) z
  · set Φ' : κ → CellFam := fun k => fastWord m.reverse h (Φ k)
    have H' : ∀ k, EngineData a b G (Φ' k) Γ P := fun k => (H k).fast (hsrcP k) m.reverse h
    have hvalΦ' : ∀ t k, valF Φ' t k = fastF m.reverse h (valF Φ t k) := fun t k => by
      funext X' z'; simp only [valF, Φ']; rw [cellValue_fastWord]; rfl
    have hsrcΦ' : ∀ t k, srcF Φ' t k = fastF m.reverse h (srcF Φ t k) := fun t k => by
      funext X' z'; simp only [srcF, Φ']; rw [fastWord_src_eq]; rfl
    have hb := engine_derivV hab H' l hl X hτ
    have e1 : ∫⁻ z in AVenhance.unitCube, ∑ k, ‖fastDiffs m.reverse h (gF k) z‖ₑ ^ 2 =
        ∑ k, ∫⁻ z in AVenhance.unitCube, ‖slowDerivs l (valF Φ' τ k) X z‖ₑ ^ 2 := by
      rw [lintegral_finsetSum' _ fun k _ =>
        (((contDiff_fastDiffs (hvalF k τ hτ l hl X).1 m.reverse h).continuous).enorm.measurable.pow_const
          2).aemeasurable]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hvalΦ', slowDerivs_fastF l (φ := valF Φ τ k) (((H k).valS τ hτ).mono (by omega))]
      rfl
    rw [e1]
    refine hb.trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le)
      (lintegral_mono_ae ?_)) zero_le)
    · refine iSup_le fun l' => iSup_le fun X' => ?_
      refine le_iSup_of_le l' (le_iSup_of_le X' (Finset.sum_le_sum fun k _ => ?_))
      rw [hvalΦ', slowDerivs_fastF l'.1 (φ := valF Φ a k) (((H k).valS a ha).mono (by omega))]
      have h2 := hvalF k a ha l'.1 (l'.2.trans hl) X'
      have := lintegral_fastDiffs_le_sharp hh m.reverse _ h2.2 (hcd h2.1)
      rw [List.reverse_reverse] at this
      exact this
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
      have hσ' : σ ∈ Icc a b := ⟨hσ.1, hσ.2.trans hτ.2⟩
      refine mul_le_mul_of_nonneg_left (iSup_le fun l' => iSup_le fun X' => ?_) zero_le
      refine le_iSup_of_le l' (le_iSup_of_le X' (Finset.sum_le_sum fun k _ => ?_))
      rw [hsrcΦ', slowDerivs_fastF l'.1 (φ := srcF Φ σ k) (((H k).srcS σ hσ').mono (by omega))]
      have h2 := hsrcF k σ hσ' l'.1 (l'.2.trans hl) X'
      have := lintegral_fastDiffs_le_sharp hh m.reverse _ h2.2 (hcd h2.1)
      rw [List.reverse_reverse] at this
      exact this
end

end AVRegularity.QuietDecay
end
