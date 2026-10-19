-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.GluedTail
import AVRegularity.Proofs.Intermediate.CycleComparison.CycleLiftIdentity
import AVRegularity.Proofs.Intermediate.CycleComparison.OcFlowJets
import AVRegularity.CycleComparison.QuietDecay.Partition.Main
import AVRegularity.CycleComparison.Reconstruction.FiniteRankIdentity
public import AVRegularity.CycleComparison.Reconstruction.ApproxDefect
public import AVRegularity.CycleComparison.Reconstruction.ApproxMeasurableTail
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseResponses
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseWitness
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.CycleComparison.Reconstruction.PulseInstance
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

section
/-! **One transition of one charted lift**.

`transition_label_bound`: the quiet-gap bound of one transition
(`Providers.cycle_residual_partition_differentiated`) for the chart-frame field `a ∘ χ` of a
coarse field `a`, with the energy of `a ∘ χ` transported back to `a` by the exact chart
(`Providers.cycle_residual_chart_transport`, part 2). The lower integral over all times equals the
residual norm over the gap since the transition field vanishes outside the support of its time
weight. The constants depend only on the orders and on the setting constants.

`piece_zero`: a lift that starts at the beginning of its quiet gap (zero entrance trace,
`hasQuietEntranceTrace_start`) produces no transition source on that gap. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory Set AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open scoped ENNReal

universe u v

namespace AVRegularity.CycleComparison.Reconstruction

/-- The bound of one transition of one charted lift, label frame, with the energy of the coarse
field: the conclusion of `transition_label_bound` for the constants `C, c`. -/
def TransitionLabelBound (Acl N D H kl Ll r : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (Dχ C c : ℝ) : Prop :=
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, CompleteSpace (h i)]
    (Q : LiftOperatorData ι h D) (π : ι → ℝ) (t₀ t₁ e ν B ρ rs E ℓ dstar εc lam Rχ : ℝ)
    (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ) (bm : ι → ι → ℝ) (Θ : ℝ),
    0 < rs → rs ≤ e → e ≤ ρ → ρ ≤ Rχ →
    IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N
      (Acl + 2 + r + D * (H + 1) * N) (kl + r + D * (H + 1) * N)
      (Ll + r + D * (H + 1) * N) qs qf CG Cw Cj bm Θ →
    (∃ M : ℕ, e⁻¹ = (M : ℝ)) →
    ∀ Cc : ℕ → ℕ → LiftCoeff ι h,
    IsLiftSequence Q (Acl + 2 + r + D * (H + 1) * N + D + 2)
      (max (kl + r + D * (H + 1) * N + 1) (Ll + r + D * (H + 1) * N + 2)) t₀ t₁ N H Cc →
    ∀ χ χi : ℝ → Vec 2 → Vec 2, (∀ t, IsChart (χ t) (χi t)) →
    (∀ t, ContDiff ℝ (⊤ : ℕ∞) (χ t)) → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (χi t)) →
    ∀ g d : ℝ, 0 < d → ℓ ^ 2 * t₀ ≤ g → g + d ≤ ℓ ^ 2 * t₁ →
    (∀ t ∈ Set.Icc g (g + d),
      JetBound (χ t) (4 * (N + D) + 2 * Acl + 16 + r + 2) Dχ Rχ ∧
      JetBound (χi t) (4 * (N + D) + 2 * Acl + 16 + r + 2) Dχ Rχ) →
    IsQuietOn Q.edge (fun τ z => Real.sqrt Q.η • Q.v τ z)
      (Set.Icc (g / ℓ ^ 2) ((g + d) / ℓ ^ 2)) →
    ∀ I : ℕ → ℝ, HasQuietEntranceTrace π Cc (g / ℓ ^ 2) lam N H
      (Acl + 2 + r + D * (H + 1) * N) (max (kl + r) (Ll + r + 2) + D * (H + 1) * N) I →
    ∀ (ψ : ℝ → ℝ) (M δ : ℝ), 0 ≤ δ → δ ≤ d → (∀ t, |ψ t| ≤ M) →
    Function.support ψ ⊆ Set.Icc (g + δ) (g + d) →
    ∀ hh, hh ≤ H → ∀ a : ℝ → Vec 2 → ∀ i, h i, (∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) →
    (∀ t, IsZ2Periodic (a t)) → ∀ j, j ≤ r → ∀ w : DerivativeWord2 j,
      ∫⁻ t, scalInt π (fun y => rs ^ j • orderedDerivative w
          (transitionSourceField N hh ℓ ρ e εc ψ Cc (fun t' y' => a t' (χ t' y')) t) y) ^
          (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C * (∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b) * M * ℓ *
          Real.sqrt d * Real.exp (-(c * δ / ℓ ^ 2))) *
        classicalStrongEnergy ρ B π (Set.Icc g (g + d)) (4 * (N + D) + 2 * Acl + 16 + r) a

/-- **One transition of one charted lift, with the energy of the coarse field.** -/
theorem transition_label_bound (Acl N D H kl Ll r : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (Dχ : ℝ) (hAcl : 1 ≤ Acl) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      TransitionLabelBound.{u, v} Acl N D H kl Ll r CG Cw Cj Dχ C c := by
  obtain ⟨C₁, c₁, hC₁, hc₁, hP⟩ :=
    Providers.cycle_residual_partition_differentiated.{u, v} Acl N D H kl Ll CG Cw Cj hAcl r
  obtain ⟨C₂, hC₂, hT⟩ := Providers.cycle_residual_chart_transport.{u, v}
    (4 * (N + D) + 2 * Acl + 16) r (fun _ => Dχ)
  refine ⟨C₁ * C₂, c₁, mul_nonneg hC₁ hC₂, hc₁, ?_⟩
  unfold TransitionLabelBound
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ rs E ℓ dstar εc lam Rχ par V qs qf bm Θ hrs hrse heρ
    hρR hset hM Cc hseq χ χi hC hχ hχi g d hd hg hgd hJ hq I hI ψ M δ hδ0 hδd hψM hψs hh hhH a
    ha hap j hj w
  have hsm : ∀ t, ContDiff ℝ ((4 * (N + D) + 2 * Acl + 16 + r + 1 : ℕ) : ℕ∞)
      ((fun t' y' => a t' (χ t' y')) t) := fun t =>
    ((ha t).comp (hχ t)).of_le (natCast_le_top_order _)
  have hper : ∀ t, IsZ2Periodic ((fun t' y' => a t' (χ t' y')) t) := fun t n y => by
    show a t (χ t (y + latticeShift n)) = a t (χ t y)
    rw [(hC t).equiv n y, hap t n (χ t y)]
  have hprov := hP Q π t₀ t₁ e ν B ρ rs E ℓ dstar εc lam hrs hrse heρ par V qs qf bm Θ
    (4 * (N + D) + 2 * Acl + 16) (Acl + 2) rfl rfl hset hM Cc
    (IsLiftSequence.isLiftSequenceFrom hseq) g d hd hg hgd hq I hI ψ M δ hδ0 hδd hψM hψs hh hhH
    (fun t' y' => a t' (χ t' y')) hsm hper j hj w
  have hE := (hT π ν B ρ rs Rχ g (g + d) χ χi hrs (hrse.trans heρ) hρR
    (fun t y => (hC t).left y) (fun t x => (hC t).right x) (fun t n y => (hC t).equiv n y)
    (fun t y => (hC t).det y) (fun t => (hχ t).of_le (natCast_le_top_order _))
    (fun t => (hχi t).of_le (natCast_le_top_order _))
    (fun t ht p hp1 hp2 y => ⟨(hJ t ht).1 p hp1 hp2 y, (hJ t ht).2 p hp1 hp2 y⟩)).2.1 a
    (fun t => (ha t).of_le (natCast_le_top_order _)) hap
  have hsupp := support_transition_subset (S := Set.Icc g (g + d))
    (hψs.trans (Set.Icc_subset_Icc_left (by linarith))) N hh ℓ ρ e εc Cc
    (fun t' y' => a t' (χ t' y')) π rs w
  rw [← setLIntegral_eq_of_support_subset hsupp]
  have hres : ∫⁻ t in Set.Icc g (g + d), scalInt π (fun y => rs ^ j • orderedDerivative w
      (transitionSourceField N hh ℓ ρ e εc ψ Cc (fun t' y' => a t' (χ t' y')) t) y) ^
        (1 / 2 : ℝ) =
      residualNorm ν π (Set.Icc g (g + d)) (fun _ _ _ => 0) (fun t x => rs ^ j •
        orderedDerivative w (transitionSourceField N hh ℓ ρ e εc ψ Cc
          (fun t' y' => a t' (χ t' y')) t) x) := by
    rw [QuietDecay.Partition.residualNorm_zero_flux]
    rfl
  rw [hres]
  refine hprov.trans ?_
  calc _ ≤ ENNReal.ofReal (C₁ * (∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b) * M * ℓ *
          Real.sqrt d * Real.exp (-(c₁ * δ / ℓ ^ 2))) *
          (ENNReal.ofReal C₂ * classicalStrongEnergy ρ B π (Set.Icc g (g + d))
            (4 * (N + D) + 2 * Acl + 16 + r) a) := mul_le_mul_right hE _
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul' hC₂]
        congr 2
        ring

/-- **A lift entering its quiet gap at the start of its window produces no source there.** The
gap is `[ℓ² t₀, G]`; the entrance trace of the zero-start lift vanishes
(`hasQuietEntranceTrace_start`), so the bound of `transition_label_bound` is zero. -/
theorem piece_zero {Acl N D H kl Ll r : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {Dχ C c : ℝ}
    (hL1 : TransitionLabelBound.{u, v} Acl N D H kl Ll r CG Cw Cj Dχ C c)
    {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, CompleteSpace (h i)]
    {Q : LiftOperatorData ι h D} {π : ι → ℝ} {t₀ t₁ e ν B ρ rs E ℓ dstar εc lam Rχ : ℝ}
    {par : Fin 2} {V : ℝ → ℝ → ℝ} {qs qf : ℕ} {bm : ι → ι → ℝ} {Θ : ℝ}
    (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ) (hρR : ρ ≤ Rχ)
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N
      (Acl + 2 + r + D * (H + 1) * N) (kl + r + D * (H + 1) * N)
      (Ll + r + D * (H + 1) * N) qs qf CG Cw Cj bm Θ)
    (hM : ∃ M : ℕ, e⁻¹ = (M : ℝ)) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q (Acl + 2 + r + D * (H + 1) * N + D + 2)
      (max (kl + r + D * (H + 1) * N + 1) (Ll + r + D * (H + 1) * N + 2)) t₀ t₁ N H Cc)
    {χ χi : ℝ → Vec 2 → Vec 2} (hC : ∀ t, IsChart (χ t) (χi t))
    (hχ : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (χ t)) (hχi : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (χi t))
    (G : ℝ) (hG : G ≤ ℓ ^ 2 * t₁)
    (hJ : ∀ t ∈ Set.Icc (ℓ ^ 2 * t₀) G,
      JetBound (χ t) (4 * (N + D) + 2 * Acl + 16 + r + 2) Dχ Rχ ∧
      JetBound (χi t) (4 * (N + D) + 2 * Acl + 16 + r + 2) Dχ Rχ)
    (hq : ℓ ^ 2 * t₀ < G →
      IsQuietOn Q.edge (fun τ z => Real.sqrt Q.η • Q.v τ z) (Set.Icc t₀ (G / ℓ ^ 2)))
    (ψ : ℝ → ℝ) {M : ℝ} (hψM : ∀ t, |ψ t| ≤ M)
    (hψs : Function.support ψ ⊆ Set.Icc (ℓ ^ 2 * t₀) G) {hh : ℕ} (hhH : hh ≤ H)
    {a : ℝ → Vec 2 → ∀ i, h i} (ha : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t))
    (hap : ∀ t, IsZ2Periodic (a t)) {j : ℕ} (hj : j ≤ r) (w : DerivativeWord2 j) :
    ∫⁻ t, scalInt π (fun y => rs ^ j • orderedDerivative w
        (transitionSourceField N hh ℓ ρ e εc ψ Cc (fun t' y' => a t' (χ t' y')) t) y) ^
        (1 / 2 : ℝ) = 0 := by
  rcases le_or_gt G (ℓ ^ 2 * t₀) with hle | hlt
  · exact lintegral_eq_zero_of_support_Icc hle
      (support_transition_subset hψs N hh ℓ ρ e εc Cc _ π rs w)
  have hℓ : ℓ ≠ 0 := by
    rw [hset.ℓ_eq]
    exact div_ne_zero hset.e_pos.ne' (Real.sqrt_pos.2 hset.ν_pos).ne'
  have hc : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 hℓ
  have hg0 : ℓ ^ 2 * t₀ / ℓ ^ 2 = t₀ := mul_div_cancel_left₀ t₀ hc
  have hgd : ℓ ^ 2 * t₀ + (G - ℓ ^ 2 * t₀) = G := by ring
  have hq' : IsQuietOn Q.edge (fun τ z => Real.sqrt Q.η • Q.v τ z)
      (Set.Icc (ℓ ^ 2 * t₀ / ℓ ^ 2) ((ℓ ^ 2 * t₀ + (G - ℓ ^ 2 * t₀)) / ℓ ^ 2)) := by
    rw [hg0, hgd]
    exact hq hlt
  have hI' : HasQuietEntranceTrace π Cc (ℓ ^ 2 * t₀ / ℓ ^ 2) lam N H
      (Acl + 2 + r + D * (H + 1) * N) (max (kl + r) (Ll + r + 2) + D * (H + 1) * N)
      (fun _ => 0) := by
    rw [hg0]
    exact hasQuietEntranceTrace_start π hseq hset.window lam _ _
  have hJ' : ∀ t ∈ Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₀ + (G - ℓ ^ 2 * t₀)),
      JetBound (χ t) (4 * (N + D) + 2 * Acl + 16 + r + 2) Dχ Rχ ∧
      JetBound (χi t) (4 * (N + D) + 2 * Acl + 16 + r + 2) Dχ Rχ := by
    rw [hgd]
    exact hJ
  have hψs' : Function.support ψ ⊆
      Set.Icc (ℓ ^ 2 * t₀ + 0) (ℓ ^ 2 * t₀ + (G - ℓ ^ 2 * t₀)) := by
    rw [add_zero, hgd]
    exact hψs
  have hG' : ℓ ^ 2 * t₀ + (G - ℓ ^ 2 * t₀) ≤ ℓ ^ 2 * t₁ := by
    rw [hgd]
    exact hG
  have hb := hL1 Q π t₀ t₁ e ν B ρ rs E ℓ dstar εc lam Rχ par V qs qf bm Θ hrs hrse heρ hρR
    hset hM Cc hseq χ χi hC hχ hχi (ℓ ^ 2 * t₀) (G - ℓ ^ 2 * t₀) (by linarith) le_rfl hG'
    hJ' hq' (fun _ => 0) hI' ψ M 0 le_rfl (by linarith) hψM hψs' hh hhH a ha hap j hj w
  refine le_antisymm (hb.trans (le_of_eq ?_)) zero_le
  simp

end AVRegularity.CycleComparison.Reconstruction
end
end

section
/-! **The coarse energies in bill form**. From the coarse defect bound
(`Providers.cycle_coarse_defect_bound`), when its quantities `q₀ ≤ A E^{2δ}`, `q₁ ≤ Q`,
`ω ≤ W E^δ`, `k₀ ≤ K`, the strong energy of the retained field is at most `C Σ(A,Q) ‖f‖` and the
`B^{-1/2}`-weighted `L²` norm of the retained flux is at most
`C ‖f‖ C(A,Q,W,K) (E^{2δ(J+1)} + E^{δp})` (`coarse_energy_bill`, by `coarseSig_mono` and
`coarse_bracket_le`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

universe u v

namespace AVRegularity.CycleComparison.Reconstruction

/-- **The coarse energies in bill form.** -/
theorem coarse_energy_bill (D H p J k : ℕ) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧
      ∀ (B₀ Cstar Θ : ℝ), 1 ≤ B₀ → 0 ≤ Cstar → 0 ≤ Θ →
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (t₀ t₁ ρ B a lam : ℝ) (b : ℝ → Vec 2 → Vec 2) (L N : ℕ)
        (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
        (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
        (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
          (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
            (PiLp 2 (fun _ : Fin 2 => h v)))
        (π : ι → ℝ) (Aedge : Matrix ι ι ℝ),
        IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ →
        ∀ (f : ∀ v, TorusHk N (h v))
          (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
          (Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v))
          (G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
            (PiLp 2 (fun _ : Fin 2 => h v))),
          IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G →
          ∀ (W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v))
            (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))),
            IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc →
            ∀ (E δ A Q Wc Kc : ℝ), 0 < E → E ≤ 1 → 0 < δ → 0 ≤ A → 0 ≤ Wc →
              Cc * (a * B₀ * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B
                + (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
                  (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal) ≤ A * E ^ (2 * δ) →
              Cc * (∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r) ≤ Q →
              (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / ρ ^ 2 ≤ Wc * E ^ δ →
              (matrixSupNorm (fun t => Jm t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ))
                t₀ t₁).toReal / B ≤ Kc →
              strongEnergyUpTo ρ B π t₀ t₁ k W ≤ ENNReal.ofReal (Cc * coarseSig A Q J H *
                Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val))) ∧
              ENNReal.ofReal (Real.sqrt B)⁻¹ * (∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal
                  (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k) ρ
                    π (fun v => (Fc v s).val))) ^ (1 / 2 : ℝ) ≤
                ENNReal.ofReal (Cc * Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π
                    (fun v => (f v).val)) *
                  (coarseBracketConst A Q Wc Kc J p H *
                    (E ^ (2 * δ * ((J : ℝ) + 1)) + E ^ (δ * (p : ℝ))))) := by
  obtain ⟨C, hC, hb⟩ := Providers.cycle_coarse_defect_bound.{u, v} D H p J k
  refine ⟨C, hC, ?_⟩
  intro B₀ Cstar Θ hB₀ hCs hΘ ι _ _ h _ _ _ _ _ _ t₀ t₁ ρ B a lam b L N Jm AD CE π Aedge hcs f U
    Uw G hresp W Fc hwit E δ A Q Wc Kc hE hE1 hδ hA hWc hq₀ hq₁ hω hk₀
  obtain ⟨q₀, hq₀e⟩ : ∃ q₀ : ℝ, q₀ = C * (a * B₀ *
      (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B
      + (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
        (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal) := ⟨_, rfl⟩
  obtain ⟨q₁, hq₁e⟩ : ∃ q₁ : ℝ, q₁ = C * (∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r) := ⟨_, rfl⟩
  obtain ⟨ω, hωe⟩ : ∃ ω : ℝ,
      ω = (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / ρ ^ 2 := ⟨_, rfl⟩
  obtain ⟨k₀, hk₀e⟩ : ∃ k₀ : ℝ, k₀ = (matrixSupNorm
      (fun t => Jm t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t₀ t₁).toReal / B := ⟨_, rfl⟩
  obtain ⟨h1, h2⟩ := hb B₀ Cstar Θ hB₀ hCs hΘ t₀ t₁ ρ B a lam b L N Jm AD CE π Aedge hcs f U Uw
    G hresp W Fc hwit q₀ q₁ hq₀e hq₁e _ ω k₀ rfl hωe hk₀e
  have hBpos : 0 < B := hcs.B_pos
  have hρ : 0 < ρ := hcs.rho_pos
  have ha := hcs.a_nonneg
  have hB₀0 : 0 ≤ B₀ := by linarith
  have hq0 : 0 ≤ q₀ := by rw [hq₀e]; positivity
  have hq1 : 0 ≤ q₁ := by
    rw [hq₁e]
    exact mul_nonneg hC (Finset.sum_nonneg fun r _ => pow_nonneg (mul_nonneg hCs hΘ) _)
  have hω0 : 0 ≤ ω := by rw [hωe]; positivity
  have hk0 : 0 ≤ k₀ := by rw [hk₀e]; positivity
  rw [← hq₀e] at hq₀
  rw [← hq₁e] at hq₁
  rw [← hωe] at hω
  rw [← hk₀e] at hk₀
  have hEd : E ^ (2 * δ) ≤ 1 := Real.rpow_le_one hE.le hE1 (by linarith)
  have hqA : q₀ ≤ A := hq₀.trans (by simpa using mul_le_mul_of_nonneg_left hEd hA)
  have hsq := Real.sqrt_nonneg (massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val))
  refine ⟨h1.trans (ENNReal.ofReal_le_ofReal ?_), h2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (coarseSig_mono hq0 hq1 hqA hq₁ J H) hC) hsq
  · exact mul_le_mul_of_nonneg_left (coarse_bracket_le hE hE1 hδ hA hWc hq0 hq₀ hq1 hq₁ hω0 hω
      hk0 hk₀ J p H) (mul_nonneg hC hsq)

/-- **The coarse energies with the actual drift scales.** On a coarse setting whose drift has the
normalized jets `(a', B₀, lam')` with `a' B₀ ρ² ≤ min(B/8, C₁ B E^{2δ})`, whose covariance is at
most `C₂ ρ² E^δ`, whose flux matrix satisfies `‖𝖩 - B·1‖/B ≤ C₃` and whose diagonal letters
satisfy `∑_d 𝒜(A_d)/(Bρ^{d-2}) ≤ C₄ E^{2δ}`, the strong energy of `W` and the coarse flux are
bounded by the coarse bill of `coarse_energy_bill` at the constants
`A = C (C₁ + C₄⁺)`, `Q = C ∑_{r ≤ H} (|C_*| Θ⁺)^r`, `W = C₂`, `K = C₃` (the coarse setting is
rescaled to the drift scales, `IsCoarseSetting.rescale`). -/
theorem coarse_window_bill (D H p J k : ℕ) (C₁ C₂ C₃ C4 Cstar Θc B₀d : ℝ) (hB₀d : 1 ≤ B₀d)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (t₀ t₁ ρ B a B₀ lam a' lam' E δ : ℝ) (b : ℝ → Vec 2 → Vec 2) (L N : ℕ)
        (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
        (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
        (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
          (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
            (PiLp 2 (fun _ : Fin 2 => h v)))
        (π : ι → ℝ) (Aedge : Matrix ι ι ℝ),
        IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θc →
        0 ≤ a' → 0 < lam' →
        (∀ l : ℕ, 1 ≤ l → ∀ (t : ℝ) (x : Vec 2),
          ‖coefficientDerivativeArray (driftCoefficient (b t)) l x‖ ≤
            a' * B₀d ^ l * (l.factorial : ℝ) * lam' ^ ((1 : ℤ) - l)) →
        B₀d * ρ / lam' ≤ 1 / 2 → a' * B₀d * ρ ^ 2 ≤ B / 8 →
        a' * B₀d * ρ ^ 2 ≤ C₁ * B * E ^ (2 * δ) →
        matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁ ≤ ENNReal.ofReal (C₂ * ρ ^ 2 * E ^ δ) →
        (matrixSupNorm (fun t => Jm t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t₀ t₁).toReal / B ≤
          C₃ →
        (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
            (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹) ≤ ENNReal.ofReal (C4 * E ^ (2 * δ)) →
        0 < E → E ≤ 1 → 0 < δ →
        ∀ (f : ∀ v, TorusHk N (h v))
          (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
          (Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v))
          (G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
            (PiLp 2 (fun _ : Fin 2 => h v))),
          IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G →
          ∀ (W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v))
            (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))),
            IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc →
            strongEnergyUpTo ρ B π t₀ t₁ k W ≤ ENNReal.ofReal (Cc *
              coarseSig (Cc * (C₁ + max C4 0))
                (Cc * ∑ r ∈ Finset.Icc 1 H, (|Cstar| * max Θc 0) ^ r) J H *
              Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val))) ∧
            ENNReal.ofReal (Real.sqrt B)⁻¹ * (∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal
                (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k) ρ
                  π (fun v => (Fc v s).val))) ^ (1 / 2 : ℝ) ≤
              ENNReal.ofReal (Cc * Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π
                  (fun v => (f v).val)) *
                (coarseBracketConst (Cc * (C₁ + max C4 0))
                  (Cc * ∑ r ∈ Finset.Icc 1 H, (|Cstar| * max Θc 0) ^ r) C₂ C₃ J p H *
                  (E ^ (2 * δ * ((J : ℝ) + 1)) + E ^ (δ * (p : ℝ))))) := by
  choose Cc hCc hb using coarse_energy_bill.{u, v} D H p J k
  refine ⟨Cc, hCc, ?_⟩
  intro ι _ _ h _ _ _ _ _ _ t₀ t₁ ρ B a B₀ lam a' lam' E δ b L N Jm AD CE π Aedge hcs ha' hlam'
    hjets hscale hsmall hsmallE hcovE hk₀ hAD hE hE1 hδ f U Uw G hresp W Fc hwit
  have hcs' := IsCoarseSetting.rescale hcs ha' hB₀d hlam' (fun l hl1 _ t _ x => hjets l hl1 t x)
    hscale hsmall
  have hBpos : 0 < B := hcs.B_pos
  have hρ : 0 < ρ := hcs.rho_pos
  have hcov : (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal ≤ ρ ^ 2 :=
    ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hcs.cov_small
  have hE2 : 0 ≤ E ^ (2 * δ) := Real.rpow_nonneg hE.le _
  have hA0 : 0 ≤ Cc * (C₁ + max C4 0) := mul_nonneg hCc (add_nonneg hC₁ (le_max_right _ _))
  have hq₀ : Cc * (a' * B₀d * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B +
      (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
        (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal) ≤
      Cc * (C₁ + max C4 0) * E ^ (2 * δ) := by
    have h1 : a' * B₀d * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B ≤
        C₁ * E ^ (2 * δ) := by
      rw [div_le_iff₀ hBpos]
      have hab' : 0 ≤ a' * B₀d := mul_nonneg ha' (by linarith)
      calc a' * B₀d * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal
          ≤ a' * B₀d * ρ ^ 2 := mul_le_mul_of_nonneg_left hcov hab'
        _ ≤ C₁ * B * E ^ (2 * δ) := hsmallE
        _ = C₁ * E ^ (2 * δ) * B := by ring
    have h2 := ENNReal.toReal_le_of_le_ofReal (mul_nonneg (le_max_right C4 0) hE2)
      (hAD.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left C4 0) hE2)))
    calc Cc * (a' * B₀d * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B +
          (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
            (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal)
        ≤ Cc * (C₁ * E ^ (2 * δ) + max C4 0 * E ^ (2 * δ)) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) hCc
      _ = Cc * (C₁ + max C4 0) * E ^ (2 * δ) := by ring
  have hω : (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / ρ ^ 2 ≤ C₂ * E ^ δ := by
    have hρ2 : 0 < ρ ^ 2 := pow_pos hρ 2
    rw [div_le_iff₀ hρ2]
    have := ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg hC₂ hρ2.le)
      (Real.rpow_nonneg hE.le _)) hcovE
    linarith
  exact hb B₀d |Cstar| (max Θc 0) hB₀d (abs_nonneg _) (le_max_right _ _) t₀ t₁ ρ B a' lam' b L N
    Jm AD CE π Aedge hcs' f U Uw G hresp W Fc hwit E δ (Cc * (C₁ + max C4 0))
    (Cc * ∑ r ∈ Finset.Icc 1 H, (|Cstar| * max Θc 0) ^ r) C₂ C₃ hE hE1 hδ hA0 hC₂ hq₀ le_rfl hω
    hk₀

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The weak identity of the glued lift of a finite-rank coarse field, closed form**.
`glued_finiteRank_identity` with its
auxiliary hypotheses discharged from the hypotheses of the comparison window: the slow periodicity
of the pulse edges (torus compatibility, `pulse_edge_slow_invariant`), the agreement of the
weighted pulse means (`obs_pulse_means_agree`: quiet means are physical), the smoothness of the
glued mean of a smooth field (it is the mean of one weighted pulse, `setting_liftMeanPoly_contDiff`)
and the coverage of the window by the pieces (`exists_output_of_partition`). What remains are the
data of the window, the lift settings and lift sequences of the observed pulses, the finite-rank
field, and cleanup chains of its tails. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- **The weak identity of the glued lift of a finite-rank coarse field**, with the mean, edge
periodicity and coverage hypotheses discharged. -/
theorem glued_finiteRank_identity_closed {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
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
    (hppinj : Set.InjOn pp ↑(ocObsPulses α q Λ m tA tZ)) {Cpart : ℝ}
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k))
      (ocPulseWindow α q Λ m) (ocQuietTimes α q Λ ζ m) (Icc tA tZ) (ocTau α q Λ m) Cpart)
    (hquiet : F.IsFastIndependentOn (ocTrimmedQuietTimes α q Λ ζ m ∩ Icc tA tZ))
    {π : ι → ℝ} {e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : ℤ → Fin 2}
    {V : ℤ → ℝ → ℝ → ℝ} {H N K₀ k₀ L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSetting (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k)
        (actual (pp k)))) π
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)
        e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ (par k) (V k) H N K₀ k₀ L qs qf CG Cw Cj edgeM Θ)
    (hDsZ : D ≤ max (k₀ + 1) (L + 2)) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k)
        (actual (pp k)))) (K₀ + D + 2) (max (k₀ + 1) (L + 2))
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    (sXc sZc Acl : ℕ) (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (hX : sXc ≤ K₀ + D + 2) (hZ : sZc ≤ max (k₀ + 1) (L + 2))
    {κ : Type*} [Fintype κ] (cf dcf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (φ j)) (hφp : ∀ j, IsZ2Periodic (φ j)) (A₀ B₀ : ℝ)
    (hA : A₀ ≤ tA) (hB₀ : tZ ≤ B₀) (hcf : ∀ j, IsPrimOn A₀ B₀ (cf j) (dcf j))
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
  have hlam : ρ / E * ρ⁻¹ = E⁻¹ := by
    rw [div_mul_eq_mul_div, mul_inv_cancel₀ hρ.ne', one_div]
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have hsX : 2 ≤ K₀ + D + 2 := Nat.le_add_left 2 (K₀ + D)
  have hsZ : 2 ≤ max (k₀ + 1) (L + 2) := (Nat.le_add_left 2 L).trans (le_max_right _ _)
  have ha : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (fun x' => ∑ j', cf j' t • φ j' x') := fun t =>
    ContDiff.sum fun j _ => (hφ j).const_smul (cf j t)
  have hagree : ∀ t ∈ Icc tA tZ, ∀ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t ≠ 0 →
      ∀ j ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp j) t ≠ 0 → ∀ r ∈ Finset.range (H + 1), ∀ x,
        pulseMeanField (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r (pulseLiftData α q Λ m ζ
          (Φ (m - 1)) hφs ν B ρ (ρ / E) j (F.fiber (pp j) (actual (pp j)))) (Cc j) (ocChart α q Λ m
          (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m j)) (ocChartInv α q Λ m (Φ (m - 1)) hφs
          (ocPulseChartIndex α q Λ m j)) (fun t' x' => ∑ j', cf j' t' • φ j' x') t x =
          pulseMeanField (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r (pulseLiftData α q Λ m ζ
            (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual (pp k)))) (Cc k) (ocChart α q Λ
            m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocChartInv α q Λ m (Φ (m - 1)) hφs
            (ocPulseChartIndex α q Λ m k)) (fun t' x' => ∑ j', cf j' t' • φ j' x') t x :=
    fun t ht k hk hwk j hj hwj r hr x =>
      obs_pulse_means_agree hΛ hζ hφs hν hB hρ hlam F actual K hdesc hquiet T hTcons hTcov hTq
        hTact pp hpp hppinj hpart P hDsZ Cc hseq (fun t' x' => ∑ j', cf j' t' • φ j' x') ht (ha t)
        hk hwk hj hwj hr x
  have hMr : ∀ t ∈ Icc tA tZ, ∀ r ∈ Finset.range (H + 1), ContDiff ℝ (N : ℕ∞) (fun x =>
      gluedMean (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k)) (ocEll q Λ m ν ^ 2) ρ
        (ocDStar q Λ m ν B / ρ) N r (fun k => pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E)
        k (F.fiber (pp k) (actual (pp k)))) Cc (fun k => ocChart α q Λ m (Φ (m - 1)) hφs
        (ocPulseChartIndex α q Λ m k)) (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs
        (ocPulseChartIndex α q Λ m k)) (fun t'' x'' => ∑ j', cf j' t'' • φ j' x'') t x) := by
    intro t ht r hr
    have hsum : ∑ j ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp j) t = 1 := hpart.2.2.1 t ht
    obtain ⟨k, hk, hwk⟩ : ∃ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t ≠ 0 := by
      by_contra hne
      push Not at hne
      rw [Finset.sum_eq_zero hne] at hsum
      exact zero_ne_one hsum
    have htk : t ∈ ocPulseWindow α q Λ m k := hpart.2.2.2.1 k hk t hwk
    have hs := cellTime_mem_pulseLiftWindow (α := α) (q := q) (Λ := Λ) (m := m) (k := k) hc0 htk ht
    have hχt : ContDiff ℝ (⊤ : ℕ∞) (ocChart α q Λ m (Φ (m - 1)) hφs
        (ocPulseChartIndex α q Λ m k) t) :=
      (Charts.contDiff_ocChart_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)).comp
        (contDiff_const.prodMk contDiff_id)
    have hψt : ContDiff ℝ (⊤ : ℕ∞) (ocChartInv α q Λ m (Φ (m - 1)) hφs
        (ocPulseChartIndex α q Λ m k) t) :=
      (Charts.contDiff_ocChartInv_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)).comp
        (contDiff_const.prodMk contDiff_id)
    have hg : ContDiff ℝ (⊤ : ℕ∞) (fun X : Vec 2 => ∑ j', cf j' t • φ j' (ocChart α q Λ m
        (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) t (ρ • X))) :=
      ContDiff.sum fun j _ => ((hφ j).comp (hχt.comp (contDiff_const_smul ρ))).const_smul (cf j t)
    have hlab : ContDiff ℝ (N : ℕ∞) (fun x : Vec 2 => ρ⁻¹ • ocChartInv α q Λ m (Φ (m - 1)) hφs
        (ocPulseChartIndex α q Λ m k) t x) :=
      (hψt.const_smul ρ⁻¹).of_le (by exact_mod_cast le_top)
    have hL := setting_liftMeanPoly_contDiff (P k hk) hsX hsZ (hseq k hk)
      (ocDStar q Λ m ν B / ρ) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)) _ hg hs
    refine (congrArg (ContDiff ℝ (N : ℕ∞)) (funext fun x => ?_)).mpr
      ((hL.comp hlab).const_smul (ocEll q Λ m ν ^ 2)⁻¹)
    rw [pulseMeanField_eq_gluedMean _ _ _ _ _ _ _ _ _ _ _ _ hsum
      (fun j hj hwj x' => hagree t ht k hk hwk j hj hwj r hr x') x,
      pulseMeanField_eq_frame _ _ _ _ _ _ _ _ _ _ hc0.ne' x]
    rfl
  exact glued_finiteRank_identity hseqΦ hm hΛ hζ hφs hν hB hρ F actual K hdesc htorus T htAZ hTcons
    hTcov hTq hTact pp hpp hppinj hpart (fun t ht => exists_output_of_partition F pp hpart ht) P
    _ _ hsX hsZ Cc hseq sXc sZc Acl hAcl hXc hZc hX hZ cf dcf φ hφ hφp A₀ B₀ hA hB₀ hcf
    (fun k _ => pulse_edge_slow_invariant α q Λ m ζ hφs ν B hρ.ne' k htorus (pp k)) Vc hV hagree
    hMr v φt hφt hφtp

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The weak identity of the glued lift of a Galerkin approximant with its residual
presentation**. The
finite-rank identity of the glued lift (`glued_finiteRank_identity_closed`) of the approximant
`a_n = ∑_r c_r e_r` of the coarse field, with the coarse defect field split into the commutator
remainder and the divergence of the flux approximant (`coarse_defect_split`), the glued lift of
that divergence in cleanup form (`glued_liftFlux`) and one periodic integration by parts
(`cell_ibp_div`), is the weak identity of the coupled system with edge flux `edgeFluxOf` and the
residual presentation
* flux `R_n = (glued tail flux) + S_n F_coarse + (glued lifted coarse flux)`,
* forcing `q_n = (glued tail force) + (glued lifted coarse force) + 𝒯 e_n + ∑_k ϖ_k' (lift of
  pulse k)`
(`approx_weak_identity`). -/

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The glued physical tail flux of the observed pulses. -/
def gluedTailFlux (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (ψs : ℤ → ℝ → Vec 2 → Vec 2)
    (H N Acl : ℕ) (ε c ρs es : ℝ) (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ)
    (x : Vec 2) (a₀ : Fin 2) : E :=
  ∑ k ∈ kset, ϖ k t • tailFluxPhys (ψs k t) H N Acl ε c ρs es (Vc k) t x a₀

/-- The glued physical tail force of the observed pulses. -/
def gluedTailForce (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (ψs : ℤ → ℝ → Vec 2 → Vec 2)
    (H N Acl : ℕ) (ε c ρs es : ℝ) (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ)
    (x : Vec 2) : E :=
  ∑ k ∈ kset, ϖ k t • tailForcePhys (ψs k t) H N Acl ε c ρs es (Vc k) t x

/-- The glued physical lifted coarse flux of the observed pulses. -/
def gluedLiftFlux (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (ψs : ℤ → ℝ → Vec 2 → Vec 2)
    (H N Acl : ℕ) (ε c ρs es : ℝ) (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E)
    (t : ℝ) (x : Vec 2) (a₀ : Fin 2) : E :=
  ∑ k ∈ kset, ϖ k t • liftFluxPhys (ψs k t) H N Acl ε c ρs es (Vn k) t x a₀

/-- The glued physical lifted coarse force of the observed pulses. -/
def gluedLiftForce (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (ψs : ℤ → ℝ → Vec 2 → Vec 2)
    (H N Acl : ℕ) (ε c ρs es : ℝ) (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E)
    (t : ℝ) (x : Vec 2) : E :=
  ∑ k ∈ kset, ϖ k t • liftForcePhys (ψs k t) H N Acl ε c ρs es (Vn k) t x

end Defs

section Lift

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

/-- **The glued lift of a sum of two fields of class `C^N` at the time `t`.** -/
theorem gluedLift_add_input (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) {c : ℝ} (hc : c ≠ 0)
    (ρ e εc : ℝ) (N H : ℕ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) {t : ℝ}
    (hχ : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (chart k t))
    (a b : ℝ → Vec 2 → ∀ i, h i) (ha : ContDiff ℝ (N : ℕ∞) (a t))
    (hb : ContDiff ℝ (N : ℕ∞) (b t)) (x : Vec 2) :
    gluedLift kset ϖ c ρ e εc N H Cc chart label (fun s y => a s y + b s y) t x =
      gluedLift kset ϖ c ρ e εc N H Cc chart label a t x +
        gluedLift kset ϖ c ρ e εc N H Cc chart label b t x := by
  have hct : c * (c⁻¹ * t) = t := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  simp only [gluedLift]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← smul_add]
  congr 1
  have hA : ContDiff ℝ (N : ℕ∞)
      ((fun s X => a (c * s) (chart k (c * s) (ρ • X))) (c⁻¹ * t)) := by
    show ContDiff ℝ (N : ℕ∞) (fun X => a (c * (c⁻¹ * t)) (chart k (c * (c⁻¹ * t)) (ρ • X)))
    rw [hct]
    exact ha.comp (((hχ k hk).of_le (by exact_mod_cast le_top)).comp (contDiff_const_smul ρ))
  have hB : ContDiff ℝ (N : ℕ∞)
      ((fun s X => b (c * s) (chart k (c * s) (ρ • X))) (c⁻¹ * t)) := by
    show ContDiff ℝ (N : ℕ∞) (fun X => b (c * (c⁻¹ * t)) (chart k (c * (c⁻¹ * t)) (ρ • X)))
    rw [hct]
    exact hb.comp (((hχ k hk).of_le (by exact_mod_cast le_top)).comp (contDiff_const_smul ρ))
  exact labelLift_add_input (Cc k) N H εc (fun s X => a (c * s) (chart k (c * s) (ρ • X)))
    (fun s X => b (c * s) (chart k (c * s) (ρ • X))) ρ e c t hA hB (label k t x)

/-- The glued lift only sees the field at the physical time. -/
theorem gluedLift_congr_time (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) {c : ℝ} (hc : c ≠ 0)
    (ρ e εc : ℝ) (N H : ℕ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) {a b : ℝ → Vec 2 → ∀ i, h i} {t : ℝ}
    (hab : a t = b t) (x : Vec 2) :
    gluedLift kset ϖ c ρ e εc N H Cc chart label a t x =
      gluedLift kset ϖ c ρ e εc N H Cc chart label b t x := by
  simp only [gluedLift]
  exact Finset.sum_congr rfl fun k _ => by
    rw [pulsePhysicalLift_congr_time c ρ e εc N H (Cc k) (chart k) (label k) hc hab x]

end Lift

section Window

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The glued lift over the observed pulses of a window, in the renewal charts. -/
def obsGlued (α q : ℝ) (Λ m : ℕ) (φs : ℝ → Vec 2 → ℝ) (hφs : IsAdmissibleStream φs)
    (ν B ρ tA tZ : ℝ) (ϖ : ℤ → ℝ → ℝ) (N H : ℕ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (x : Vec 2) : ∀ i, h i :=
  gluedLift (ocObsPulses α q Λ m tA tZ) ϖ (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m)
    (ocDStar q Λ m ν B / ρ) N H Cc (fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
    (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) a t x

/-- The flux residual of the glued lift of the Galerkin approximant. -/
def approxFlux (α q : ℝ) (Λ m : ℕ) (φs : ℝ → Vec 2 → ℝ) (hφs : IsAdmissibleStream φs)
    (ν B ρ tA tZ : ℝ) (ϖ : ℤ → ℝ → ℝ) (H N Acl : ℕ)
    (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) (n : ℕ) {k : ℕ}
    (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (v : ι) (s : ℝ) (x : Vec 2) :
    PiLp 2 (fun _ : Fin 2 => h v) :=
  WithLp.toLp 2 fun a₀ =>
    gluedTailFlux (ocObsPulses α q Λ m tA tZ) ϖ
        (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) H N Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vc s x a₀ v
      + fluxApprox n (fun v => Fc v s) x a₀ v
      + gluedLiftFlux (ocObsPulses α q Λ m tA tZ) ϖ
        (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) H N Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vn s x a₀ v

/-- The forcing residual of the glued lift of the Galerkin approximant. -/
def approxForce (α q : ℝ) (Λ m : ℕ) (φs : ℝ → Vec 2 → ℝ) (hφs : IsAdmissibleStream φs)
    (ν B ρ tA tZ : ℝ) (ϖ : ℤ → ℝ → ℝ) (H N Acl : ℕ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) (n : ℕ)
    (b : ℝ → Vec 2 → Vec 2) (Dl : ℕ)
    (AD : ∀ d : Finset.Icc 2 Dl, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 Dl), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (aRep : ℝ → Vec 2 → ∀ i, h i) (v : ι) (s : ℝ) (x : Vec 2) : h v :=
  gluedTailForce (ocObsPulses α q Λ m tA tZ) ϖ
      (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) H N Acl
      (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vc s x v
    + gluedLiftForce (ocObsPulses α q Λ m tA tZ) ϖ
      (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) H N Acl
      (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vn s x v
    + obsGlued α q Λ m φs hφs ν B ρ tA tZ ϖ N H Cc
      (defectRemainder n b Dl H AD CE Jm W aRep) s x v
    + (∑ k ∈ ocObsPulses α q Λ m tA tZ, deriv (ϖ k) s •
      pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H
        (Cc k) (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
        (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) (coarseTraj n W) s x) v

end Window

end AVRegularity.CycleComparison.Reconstruction
end
end
