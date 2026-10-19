-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.PulseInstance
import AVRegularity.Proofs.Intermediate.CycleComparison.CycleLiftIdentity
import AVRegularity.Proofs.Intermediate.CycleComparison.OcFlowJets
import AVRegularity.CycleComparison.QuietDecay.Partition.Main
import AVRegularity.CycleComparison.Reconstruction.PulseIdentity
public import AVRegularity.Proofs.WeakGen.Residual.LiftedComparison
import AVRegularity.CycleReference.TestDriftIntegrability
public import AVRegularity.CycleComparison.Reconstruction.GluedTail
import AVRegularity.CycleComparison.Reconstruction.Orders
import Mathlib.Algebra.Ring.IsFormallyReal

section
section
section
/-! **Finite-reserve transition of one charted lift**.

`weak_gluing_transition_label_bound`: the quiet-gap bound of one transition
(`Providers.cycle_residual_partition_differentiated`) for the chart-frame field `a ∘ χ` of a
coarse field `a`, with the energy of `a ∘ χ` transported back to `a` by the exact chart
(`Providers.cycle_residual_chart_transport`, part 2). The lower integral over all times equals the
residual norm over the gap since the transition field vanishes outside the support of its time
weight. The constants depend only on the orders and on the setting constants.

The existing proof uses only the displayed finite reserve of its input. This adapter retains
that reserve rather than requiring an infinitely smooth coarse representative.
-/

@[expose] public noncomputable section

open Homogenization MeasureTheory Set AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open scoped ENNReal Classical

universe u v

namespace AVRegularity.Providers.WeakGen.Residual
open CycleComparison.Reconstruction

/-- The bound of one transition of one charted lift, label frame, with the energy of the coarse
field: the conclusion of `weak_gluing_transition_label_bound` for the constants `C, c`. -/
def WeakGluingTransitionLabelBound (Acl N D H kl Ll r : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
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
    ∀ hh, hh ≤ H → ∀ a : ℝ → Vec 2 → ∀ i, h i, (∀ t, ContDiff ℝ ((4 * (N + D) + 2 * Acl + 16 + r + 1 : ℕ) : ℕ∞) (a t)) →
    (∀ t, IsZ2Periodic (a t)) → ∀ j, j ≤ r → ∀ w : DerivativeWord2 j,
      ∫⁻ t, scalInt π (fun y => rs ^ j • orderedDerivative w
          (transitionSourceField N hh ℓ ρ e εc ψ Cc (fun t' y' => a t' (χ t' y')) t) y) ^
          (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C * (∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b) * M * ℓ *
          Real.sqrt d * Real.exp (-(c * δ / ℓ ^ 2))) *
        classicalStrongEnergy ρ B π (Set.Icc g (g + d)) (4 * (N + D) + 2 * Acl + 16 + r) a

/-- **One transition of one charted lift, with the energy of the coarse field.** -/
theorem weak_gluing_transition_label_bound (Acl N D H kl Ll r : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (Dχ : ℝ) (hAcl : 1 ≤ Acl) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      WeakGluingTransitionLabelBound.{u, v} Acl N D H kl Ll r CG Cw Cj Dχ C c := by
  obtain ⟨C₁, c₁, hC₁, hc₁, hP⟩ :=
    Providers.cycle_residual_partition_differentiated.{u, v} Acl N D H kl Ll CG Cw Cj hAcl r
  obtain ⟨C₂, hC₂, hT⟩ := Providers.cycle_residual_chart_transport.{u, v}
    (4 * (N + D) + 2 * Acl + 16) r (fun _ => Dχ)
  refine ⟨C₁ * C₂, c₁, mul_nonneg hC₁ hC₂, hc₁, ?_⟩
  unfold WeakGluingTransitionLabelBound
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ rs E ℓ dstar εc lam Rχ par V qs qf bm Θ hrs hrse heρ
    hρR hset hM Cc hseq χ χi hC hχ hχi g d hd hg hgd hJ hq I hI ψ M δ hδ0 hδd hψM hψs hh hhH a
    ha hap j hj w
  have hsm : ∀ t, ContDiff ℝ ((4 * (N + D) + 2 * Acl + 16 + r + 1 : ℕ) : ℕ∞)
      ((fun t' y' => a t' (χ t' y')) t) := fun t =>
    (ha t).comp ((hχ t).of_le (natCast_le_top_order _))
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
    ha hap
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

/-- Zero extension of the coarse representative controls the energy on an original quiet gap
by its energy on the comparison window. Thus clipping the input does not restart the lift. -/
theorem weak_gluing_zero_extension_energy_le
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ v, NormedAddCommGroup (h v)] [∀ v, NormedSpace ℝ (h v)]
    (ρ B : ℝ) (π : ι → ℝ) (I S : Set ℝ) (hS : MeasurableSet S) (m : ℕ)
    (a : ℝ → Vec 2 → ∀ v, h v) :
    classicalStrongEnergy ρ B π I m (fun t => if t ∈ S then a t else 0) ≤
      classicalStrongEnergy ρ B π S m a := by
  classical
  have hz (v : ι) : classicalFactorialSq ρ m (fun _ : Vec 2 => (0 : h v)) = 0 := by
    simp [classicalFactorialSq, orderedDerivative_zero_fun]
  have hzg (v : ι) : classicalGradFactorialSq ρ m (fun _ : Vec 2 => (0 : h v)) = 0 := by
    simp [classicalGradFactorialSq, orderedDerivative_zero_fun]
  unfold classicalStrongEnergy
  refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun v _ => mul_le_mul_right ?_ _) (by norm_num)
  apply add_le_add
  · refine iSup_le fun t => iSup_le fun _ht => ?_
    by_cases ht : t ∈ S
    · simp only [ht, ite_true]
      exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)
    · simpa only [ht, ite_false, Pi.zero_apply, hz] using
        (zero_le : (0 : ℝ≥0∞) ≤ ⨆ t ∈ S, classicalFactorialSq ρ m (fun x => a t x v))
  · apply mul_le_mul_right
    calc
      (∫⁻ t in I, classicalGradFactorialSq ρ m
          (fun x => (if t ∈ S then a t else 0) x v)) ≤
          ∫⁻ t, classicalGradFactorialSq ρ m (fun x => (if t ∈ S then a t else 0) x v) :=
        setLIntegral_le_lintegral _ _
      _ = ∫⁻ t in S, classicalGradFactorialSq ρ m (fun x => a t x v) := by
        rw [← lintegral_indicator hS]
        apply lintegral_congr
        intro t
        by_cases ht : t ∈ S
        · simp only [ht, ite_true, Set.indicator_of_mem ht]
        · simp only [ht, ite_false, Pi.zero_apply, hzg, Set.indicator_of_notMem ht]

/-- A transition source only reads the input at the physical time of the source. -/
theorem weak_gluing_transition_input_congr
    {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ v, NormedAddCommGroup (h v)]
    [∀ v, NormedSpace ℝ (h v)] (N hh : ℕ) (ℓ ρ e εc : ℝ) (hℓ : ℓ ≠ 0)
    (ψ : ℝ → ℝ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    {a b : ℝ → Vec 2 → ∀ v, h v} {t : ℝ} (hab : a t = b t) :
    transitionSourceField N hh ℓ ρ e εc ψ Cc a t =
      transitionSourceField N hh ℓ ρ e εc ψ Cc b t := by
  have hct : ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hℓ), one_mul]
  funext y
  rw [transitionSourceField_eq_smul, transitionSourceField_eq_smul]
  apply congrArg (fun z : ∀ v, h v => ψ t • z)
  unfold labelSrc diagSample
  apply Finset.sum_congr rfl
  intro n _hn
  apply congrArg (fun z : ∀ v, h v => εc ^ n • z)
  exact congrFun (congrFun (liftApply_congr_time
    (c₁ := Cc hh n) (c₂ := Cc hh n) (fun _ _ _ _ => rfl)
    (by funext X; rw [hct, hab])) _) _

/-- Apply the transition bound `weak_gluing_transition_label_bound` when the coarse field is
supplied only on
its comparison window. The input is extended by zero; the lift and its memory are retained. -/
theorem weak_gluing_transition_label_on_window
    {Acl N D H kl Ll r : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {Dχ C c : ℝ}
    (hL1 : WeakGluingTransitionLabelBound.{u, v} Acl N D H kl Ll r CG Cw Cj Dχ C c) :
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
    ∀ (S : Set ℝ), MeasurableSet S → Function.support ψ ⊆ S →
    ∀ hh, hh ≤ H → ∀ a : ℝ → Vec 2 → ∀ i, h i, (∀ t ∈ S, ContDiff ℝ ((4 * (N + D) + 2 * Acl + 16 + r + 1 : ℕ) : ℕ∞) (a t)) →
    (∀ t ∈ S, IsZ2Periodic (a t)) → ∀ j, j ≤ r → ∀ w : DerivativeWord2 j,
      ∫⁻ t, scalInt π (fun y => rs ^ j • orderedDerivative w
          (transitionSourceField N hh ℓ ρ e εc ψ Cc (fun t' y' => a t' (χ t' y')) t) y) ^
          (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C * (∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b) * M * ℓ *
          Real.sqrt d * Real.exp (-(c * δ / ℓ ^ 2))) *
        classicalStrongEnergy ρ B π S (4 * (N + D) + 2 * Acl + 16 + r) a := by
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ rs E ℓ dstar εc lam Rχ par V qs qf bm Θ
    hrs hrse heρ hρR hset he Cc hseq χ χi hC hχ hχi g d hd hg hgd hJ hquiet
    I hI ψ M δ hδ hδd hψ hsupport S hS hsuppS hh hhh a ha haper j hj w
  let a₀ : ℝ → Vec 2 → ∀ v, h v := fun t => if t ∈ S then a t else 0
  have ha₀ : ∀ t, ContDiff ℝ ((4 * (N + D) + 2 * Acl + 16 + r + 1 : ℕ) : ℕ∞) (a₀ t) := by
    intro t
    by_cases ht : t ∈ S
    · simpa only [a₀, ht, ite_true] using ha t ht
    · simp only [a₀, ht, ite_false]
      change ContDiff ℝ _ (fun _ : Vec 2 => (0 : ∀ v, h v))
      exact contDiff_const
  have hp₀ : ∀ t, IsZ2Periodic (a₀ t) := by
    intro t
    by_cases ht : t ∈ S
    · simpa only [a₀, ht, ite_true] using haper t ht
    · intro k x
      simp only [a₀, ht, ite_false, Pi.zero_apply]
  have hℓ : ℓ ≠ 0 := by
    rw [hset.ℓ_eq]
    exact (div_pos hset.e_pos (Real.sqrt_pos.mpr hset.ν_pos)).ne'
  have hfields : transitionSourceField N hh ℓ ρ e εc ψ Cc (fun t y => a₀ t (χ t y)) =
      transitionSourceField N hh ℓ ρ e εc ψ Cc (fun t y => a t (χ t y)) := by
    funext t
    by_cases ht : t ∈ S
    · exact weak_gluing_transition_input_congr N hh ℓ ρ e εc hℓ ψ Cc
        (by funext y; simp only [a₀, ht, ite_true])
    · have hz : ψ t = 0 := by
        by_contra hne
        exact ht (hsuppS (Function.mem_support.mpr hne))
      rw [transitionSourceField_of_eq_zero hz, transitionSourceField_of_eq_zero hz]
  have hb := hL1 Q π t₀ t₁ e ν B ρ rs E ℓ dstar εc lam Rχ par V qs qf bm Θ
    hrs hrse heρ hρR hset he Cc hseq χ χi hC hχ hχi g d hd hg hgd hJ hquiet I hI
    ψ M δ hδ hδd hψ hsupport hh hhh a₀ ha₀ hp₀ j hj w
  rw [hfields] at hb
  exact hb.trans (mul_le_mul_right
    (weak_gluing_zero_extension_energy_le ρ B π (Set.Icc g (g + d)) S hS
      (4 * (N + D) + 2 * Acl + 16 + r) a) _)

/-- Sum finitely many charted transition grades after their individual label-frame bounds.
The bound uses the number of observed pieces, rather than the component count or ambient
cap. The labels may come from different effective caps. -/
theorem weak_gluing_transition_sum_bound
    {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (P : Finset (ℤ × Bool)) (H r : ℕ)
    {Dχ Rχ rs : ℝ} (hDχ : 1 ≤ Dχ) (hrs : 0 < rs) (hsR : rs ≤ Rχ)
    (π : ι → ℝ) (I : Set ℝ) (hI : MeasurableSet I)
    (ψ : ℤ × Bool → ℝ → ℝ)
    (χ χi : ℤ × Bool → ℝ → Vec 2 → Vec 2)
    (L : ℤ × Bool → ℕ → ℝ → Vec 2 → ∀ v, h v)
    (hC : ∀ p ∈ P, ∀ t ∈ I, ψ p t ≠ 0 → IsChart (χ p t) (χi p t))
    (hχi : ∀ p ∈ P, ∀ t ∈ I, ψ p t ≠ 0 → ContDiff ℝ (r : ℕ∞) (χi p t))
    (hJ : ∀ p ∈ P, ∀ t ∈ I, ψ p t ≠ 0 → JetBound (χi p t) r Dχ Rχ)
    (hL : ∀ p ∈ P, ∀ t ∈ I, ψ p t ≠ 0 → ∀ hh ∈ Finset.range (H + 1),
      ContDiff ℝ (r : ℕ∞) (L p hh t))
    (hLp : ∀ p ∈ P, ∀ t ∈ I, ψ p t ≠ 0 → ∀ hh ∈ Finset.range (H + 1),
      IsZ2Periodic (L p hh t))
    (hcard : ∀ t ∈ I, (P.filter fun p => ψ p t ≠ 0).card ≤ 2)
    (hm : ∀ p ∈ P, ∀ j ∈ Finset.range (r + 1), ∀ w : DerivativeWord2 j,
      ∀ hh ∈ Finset.range (H + 1), AEMeasurable (fun t => scalInt π
        (fun y => rs ^ j • orderedDerivative w (fun y' => ψ p t • L p hh t y') y) ^
          (1 / 2 : ℝ)) (volume.restrict I))
    (X : ℝ≥0∞)
    (hb : ∀ p ∈ P, ∀ j ∈ Finset.range (r + 1), ∀ w : DerivativeWord2 j,
      ∀ hh ∈ Finset.range (H + 1),
      ∫⁻ t in I, scalInt π (fun y => rs ^ j • orderedDerivative w
        (fun y' => ψ p t • L p hh t y') y) ^ (1 / 2 : ℝ) ≤ X) :
    ∫⁻ t in I, (∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j,
      scalInt π (fun x => rs ^ j • orderedDerivative w (fun x' =>
        ∑ p ∈ P, ψ p t • ∑ hh ∈ Finset.range (H + 1), L p hh t (χi p t x')) x)) ^
        (1 / 2 : ℝ) ≤
      ENNReal.ofReal (sliceConst H r Dχ ^ (1 / 2 : ℝ)) *
        ((P.card * ∑ j ∈ Finset.range (r + 1), 2 ^ j * (H + 1) : ℕ) : ℝ≥0∞) * X := by
  have hpt : ∀ t ∈ I,
      (∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j,
        scalInt π (fun x => rs ^ j • orderedDerivative w (fun x' =>
          ∑ p ∈ P, ψ p t • ∑ hh ∈ Finset.range (H + 1), L p hh t (χi p t x')) x)) ^
            (1 / 2 : ℝ) ≤
      ENNReal.ofReal (sliceConst H r Dχ ^ (1 / 2 : ℝ)) *
        ∑ p ∈ P, ∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j,
          ∑ hh ∈ Finset.range (H + 1), scalInt π (fun y => rs ^ j •
            orderedDerivative w (fun y' => ψ p t • L p hh t y') y) ^ (1 / 2 : ℝ) := by
    intro t ht
    have hs := slice_bound (P := P) (H := H) (r := r) hDχ hrs hsR π (fun p => ψ p t)
      (fun p => χ p t) (fun p => χi p t) (fun p hh => L p hh t)
      (fun p x => ∑ hh ∈ Finset.range (H + 1), L p hh t (χi p t x)) (fun _ _ => rfl)
      (fun p hp => hC p hp t ht) (fun p hp => hχi p hp t ht)
      (fun p hp => hJ p hp t ht) (fun p hp => hL p hp t ht)
      (fun p hp => hLp p hp t ht) (hcard t ht)
    refine (ENNReal.rpow_le_rpow hs (by norm_num)).trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 1 / 2 by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (sliceConst_nonneg H r Dχ)
        (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
    exact mul_le_mul_right (rpow_half_nested_le P r H _) _
  refine (setLIntegral_mono' hI hpt).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_nested_sum P r H _ hm]
  have hsum :
      (∑ p ∈ P, ∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j,
        ∑ hh ∈ Finset.range (H + 1), ∫⁻ t in I, scalInt π (fun y => rs ^ j •
          orderedDerivative w (fun y' => ψ p t • L p hh t y') y) ^ (1 / 2 : ℝ)) ≤
      ∑ _p ∈ P, ∑ j ∈ Finset.range (r + 1), ∑ _w : DerivativeWord2 j,
        ∑ _hh ∈ Finset.range (H + 1), X :=
    Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun j hj =>
      Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun hh hhh => hb p hp j hj w hh hhh
  exact (mul_le_mul_right hsum _).trans_eq (by rw [nested_sum_const]; rw [mul_assoc])

end AVRegularity.Providers.WeakGen.Residual
end
end

section
/-! The transition bound uses the parent radius `E`, whereas the coarse energy is supplied
at `cE`. This finite change of radius costs only a power of the requested scalar radius,
chosen before the construction and its ambient degree cap. -/

@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

private theorem weakGluingRadiusWeight_le {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (ρ : ℝ) {j m : ℕ} (hj : j ≤ m) :
    ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2 ≤
      c⁻¹ ^ (2 * m) * ((c * ρ) ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) := by
  have hcinv : 1 ≤ c⁻¹ := (one_le_inv₀ hc).mpr hc1
  have hpow := pow_le_pow_right₀ hcinv (Nat.mul_le_mul_left 2 hj)
  have he : ρ ^ (2 * j) = c⁻¹ ^ (2 * j) * (c * ρ) ^ (2 * j) := by
    rw [← mul_pow, inv_mul_cancel_left₀ hc.ne']
  rw [he, mul_div_assoc]
  have hnum : 0 ≤ (c * ρ) ^ (2 * j) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  exact mul_le_mul_of_nonneg_right hpow (div_nonneg hnum (sq_nonneg _))

private theorem weakGluingRadiusSum_le {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (ρ : ℝ) {m K : ℕ} (hmK : m ≤ K) (Z : ℕ → ℝ≥0∞) :
    (∑ j ∈ Finset.range (m + 1),
      ENNReal.ofReal (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) * Z j) ≤
    ENNReal.ofReal (c⁻¹ ^ (2 * m)) *
      ∑ j ∈ Finset.range (K + 1),
        ENNReal.ofReal ((c * ρ) ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) * Z j := by
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum fun j hj => ?_).trans
    (Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hmK)))
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ c⁻¹ ^ (2 * m))]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal
    (weakGluingRadiusWeight_le hc hc1 ρ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))) le_rfl

/-- Both classical factorial densities obey the same finite change of radius. No spatial
regularity is needed for this comparison of their literal nonnegative sums. -/
theorem weak_gluing_classical_density_radius_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (ρ : ℝ) {m K : ℕ} (hmK : m ≤ K)
    (a : Vec 2 → E) :
    classicalFactorialSq ρ m a ≤
      ENNReal.ofReal (c⁻¹ ^ (2 * m)) * classicalFactorialSq (c * ρ) K a ∧
    classicalGradFactorialSq ρ m a ≤
      ENNReal.ofReal (c⁻¹ ^ (2 * m)) * classicalGradFactorialSq (c * ρ) K a := by
  constructor <;> exact weakGluingRadiusSum_le hc hc1 ρ hmK _

/-- A finite higher coarse energy at `cE` controls the energy of the transition bound at `E`. The
factor depends only on c and the requested order, and is uniform in all stage data. -/
theorem weak_gluing_classical_energy_radius_le
    {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ v, NormedAddCommGroup (h v)]
    [∀ v, NormedSpace ℝ (h v)] {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (ρ B : ℝ) (π : ι → ℝ) (I : Set ℝ) {m K : ℕ} (hmK : m ≤ K)
    (a : ℝ → Vec 2 → ∀ v, h v) :
    classicalStrongEnergy ρ B π I m a ≤
      ENNReal.ofReal ((c⁻¹ ^ (2 * m)) ^ (1 / 2 : ℝ)) *
        classicalStrongEnergy (c * ρ) B π I K a := by
  let A := ENNReal.ofReal (c⁻¹ ^ (2 * m))
  have hFS (v : ι) (t : ℝ) := (weak_gluing_classical_density_radius_le hc hc1 ρ hmK
    (fun x => a t x v)).1
  have hGS (v : ι) (t : ℝ) := (weak_gluing_classical_density_radius_le hc hc1 ρ hmK
    (fun x => a t x v)).2
  have hs (v : ι) : (⨆ t ∈ I, classicalFactorialSq ρ m (fun x => a t x v)) ≤
      A * ⨆ t ∈ I, classicalFactorialSq (c * ρ) K (fun x => a t x v) := by
    refine iSup₂_le fun t ht => (hFS v t).trans ?_
    exact mul_le_mul_right (le_iSup₂
      (f := fun t (_ : t ∈ I) => classicalFactorialSq (c * ρ) K (fun x => a t x v)) t ht) A
  have hi (v : ι) : (∫⁻ t in I, classicalGradFactorialSq ρ m (fun x => a t x v)) ≤
      A * ∫⁻ t in I, classicalGradFactorialSq (c * ρ) K (fun x => a t x v) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun t => hGS v t
  unfold classicalStrongEnergy
  have hsum : (∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
      ((⨆ t ∈ I, classicalFactorialSq ρ m (fun x => a t x v)) +
        ENNReal.ofReal B * ∫⁻ t in I, classicalGradFactorialSq ρ m (fun x => a t x v))) ≤
      A * ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
        ((⨆ t ∈ I, classicalFactorialSq (c * ρ) K (fun x => a t x v)) +
          ENNReal.ofReal B * ∫⁻ t in I, classicalGradFactorialSq (c * ρ) K (fun x => a t x v)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    refine (mul_le_mul_right (add_le_add (hs v) (mul_le_mul_right (hi v) _)) _).trans_eq ?_
    ring
  refine (ENNReal.rpow_le_rpow hsum (by norm_num)).trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  change ENNReal.ofReal (c⁻¹ ^ (2 * m)) ^ (1 / 2 : ℝ) * _ = _
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]

end AVRegularity.Providers.WeakGen.Residual
end
end

section
/-! Entrance traces of a selected weak slot, uniformly in its effective cap. The necessary
partition reserves are explicit numerical inequalities; this module does not infer them from
the weaker reserves presently stored by `WeakPositiveParameters`. -/

@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual
open Finite.WeakLift

/-- Extra numerical reserves needed for `cycle_residual_partition_differentiated` at
`(kl,Ll)=(2,0)`. They are uniform over the selected cap, and the slot-lift supplier must retain
them. -/
def WeakGluingPartitionReserves {N H U : ℕ} (P : WeakPositiveParameters N H U)
    (Acl r : ℕ) : Prop :=
  Acl + 2 + r + P.capMax * (H + 1) * N ≤ P.slowOrder ∧
    2 + r + P.capMax * (H + 1) * N ≤ P.fastOrder

/-- Reserves at the maximal cap supply the setting, sequence, and trace orders at each
selected cap. The fast trace order is within the available energy jets, not merely the
larger fast box order of the sequence. -/
theorem weak_gluing_partition_orders {N H U : ℕ} {P : WeakPositiveParameters N H U}
    {Acl r cap : ℕ} (hreserve : WeakGluingPartitionReserves P Acl r) (hcap : cap ≤ P.capMax) :
    Acl + 2 + r + cap * (H + 1) * N ≤ P.slowOrder ∧
    2 + r + cap * (H + 1) * N ≤ P.fastOrder ∧
    Acl + 2 + r + cap * (H + 1) * N + cap + 2 ≤ P.slowOrder + cap + 2 ∧
    max (2 + r + cap * (H + 1) * N + 1) (r + cap * (H + 1) * N + 2) ≤
      max (P.fastOrder + 1) (P.fastOrder + 2) ∧
    max (2 + r) (r + 2) + cap * (H + 1) * N ≤ P.fastOrder + 1 := by
  have hmul := Nat.mul_le_mul_right N (Nat.mul_le_mul_right (H + 1) hcap)
  obtain ⟨hslow, hfast⟩ := hreserve
  omega

/-- One entrance-trace constant works for every slot, stage, and cap bounded by `P.capMax`.
The full available trace orders are returned, independently of quietness of the slot lift. -/
theorem weak_gluing_slot_lift_entrance_traces {N H U : ℕ} (P : WeakPositiveParameters N H U) :
    ∃ CI : ℝ, 0 ≤ CI ∧
    ∀ {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (i : ℕ)
      (G : GenStage D ScalarH Dm bw j₀) (π : CompIn G.comps → ℝ) (slot : OddSlot)
      (W : WeakPositiveSlot P i G π slot) (s : ℝ),
      s ∈ Set.Icc (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) →
      ∀ K L : ℕ, K ≤ P.slowOrder → L ≤ P.fastOrder + 1 →
        HasQuietEntranceTrace π W.coeff s 1 N H K L (fun hh => CI * P.S ^ hh) := by
  classical
  choose C hC htrace using fun cap : ℕ =>
    CycleComparison.Reconstruction.setting_quietEntranceTrace N P.slowOrder
      P.fastOrder P.fastOrder cap H P.CG P.Cw P.Cj
  refine ⟨∑ cap ∈ Finset.range (P.capMax + 1), C cap,
    Finset.sum_nonneg (fun cap _ => hC cap), ?_⟩
  intro D Dm bw j₀ i G π slot W s hs K L hK hL
  have htr := htrace W.cap W.Q π _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    W.setting P.S_nonneg W.coeff W.sequence s hs K L hK (by omega)
  have hlam : D.eps (i - 1) / D.eps (i - 1) = (1 : ℝ) := by
    exact div_self (ne_of_gt W.setting.E_pos)
  rw [hlam] at htr
  have hcap : W.cap ∈ Finset.range (P.capMax + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le W.cap_le)
  have hle : C W.cap ≤ ∑ cap ∈ Finset.range (P.capMax + 1), C cap :=
    Finset.single_le_sum (fun cap _ => hC cap) hcap
  refine ⟨fun hh _ => mul_nonneg (Finset.sum_nonneg (fun cap _ => hC cap))
    (pow_nonneg P.S_nonneg hh), ?_⟩
  intro hh hhH n hn hnN m hm p hp q hq
  exact (htr.2 hh hhH n hn hnN m hm p hp q hq).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hle (pow_nonneg P.S_nonneg hh)) (pow_nonneg zero_le_one p)))

end AVRegularity.Providers.WeakGen.Residual
end
end
end

section
section
/-! Conditional assemblies for the two gluing terms. Quietness of the slot lift is an input on
the selected slot lift, discharged by `weak_gluing_slot_lift_quiet_of_native` from native
quietness and `edge_fast`; it is not inferred from equality of sources.
The other leaves separate classical regularity, the transition estimate, and the numerical
price. The presentation step is discharged by the classical presentation theorem. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen.Residual

open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift

/-- Quietness of a selected slot lift on a physical transition interval. The interval must be
inside the slot-lift window and inside the trimmed quiet set. No untrimmed assertion is made. -/
def WeakSlotLiftQuiet {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ) {U : ℕ}
    {P : WeakPositiveParameters A.Nw (A.Jw * A.Rw) U}
    (slotLifts : ∀ slot : OddSlot, WeakPositiveSlot P i (c.stage i)
      (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) slot) : Prop :=
  ∀ (slot : OddSlot) (g d : ℝ), 0 < d →
    c.D.cellScaleSq i * weakSlotLeft c.D i slot.1 ≤ g →
    g + d ≤ c.D.cellScaleSq i * weakSlotRight c.D i slot.1 →
    Set.Icc g (g + d) ⊆ ocTrimmedQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ i →
    IsQuietOn (slotLifts slot).Q.edge
      (fun t z => Real.sqrt (slotLifts slot).Q.η • (slotLifts slot).Q.v t z)
      (Set.Icc (g / c.D.cellScaleSq i) ((g + d) / c.D.cellScaleSq i))

/-- Additional input: the slot lifts can be selected jointly with their quietness.
This does not assert quietness for every source-equivalent slot lift. All constants precede data
and the ambient cap, exactly as in `WeakSlotLiftStatement`. -/
def WeakSlotLiftQuietStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (Lr : ℕ), A.Jw * A.Nw ≤ Lr →
    ∃ SX SZ : ℕ, ∀ R : WeakPassageRequest A, SX ≤ R.sX → SZ ≤ R.sZ →
    ∃ (P : WeakPositiveParameters A.Nw (A.Jw * A.Rw) (Lr + 3)) (CH Υ : ℝ)
      (M₀ : ℕ → ℕ),
      ∀ c : WeakPassageInstance plan R,
        IsCarrierStart B.α B.q A.Λ A.bw CH Υ c.j₀ → M₀ c.j₀ ≤ c.M →
        ∀ i, c.M < i → i ≤ c.M + A.Jw →
          WeakPositiveGeometry P i (c.stage i) ∧
          ∃ slotLifts : ∀ slot : OddSlot, WeakPositiveSlot P i (c.stage i)
            (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) slot,
            WeakSlotLiftQuiet c i slotLifts

/-- The energy order and the coefficient multiplying the coarse energy after summing transition
estimates. Both are fixed before the construction, the ambient cap, and the solution. -/
structure WeakGluingPrices where
  order : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ
  meanOrder : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
    WeakPassageRequest A → ℕ
  meanFactor : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
    WeakPassageRequest A → ℝ≥0∞
  factor : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
    WeakPassageRequest A → ℕ → ℝ≥0∞

/-- Classical regularity needed for the already proved presentation theorem; `p` is 2 or 3 in
the applications. This is spatial regularity and joint measurability, not a PDE assertion. -/
def WeakGluingRegularityStatement (plan : WeakPassagePlan) (p : Fin 4)
    (prices : WeakGluingPrices) : Prop :=
  WeakSlotLiftStatement plan → WeakSlotLiftQuietStatement plan →
  WeakCoarseReadoutEnergyStatement plan prices.order →
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A},
    A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1) →
    A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 <
      2 * weakAStar B.α B.q * (A.Rw + 1) →
  ∀ (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → ∀ h : WeakComparisonInput r i,
    (∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), ∀ v,
      ContDiff ℝ ((plan.forcingOrder R + 1 : ℕ) : ℕ∞)
        (fun x => weakComparisonPiece h p t x v) ∧
      IsZ2Periodic (fun x => weakComparisonPiece h p t x v)) ∧
    (∀ v n, n ≤ plan.forcingOrder R + 1 → ∀ w : DerivativeWord2 n,
      ContinuousOn (fun z : ℝ × Vec 2 =>
        orderedDerivative w (fun x => weakComparisonPiece h p z.1 x v) z.2)
        (Set.Icc (r.tq i) (r.a + A.T₀) ×ˢ Set.univ))

/-- The price condition: floors and scalar constants only, chosen before instances and `Dm`.
`Cen` is an explicit coarse readout energy constant, fixed before the level floor. -/
def WeakGluingPricePlanOK (plan : WeakPassagePlan) (prices : WeakGluingPrices)
    (Cen : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℝ) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
    0 ≤ Cen R ∧ 0 < plan.forceC R ∧
    ∀ j₀ M : ℕ, plan.baseFloor B ≤ A.Λ → plan.levelFloor R j₀ ≤ M →
      prices.factor R M * ENNReal.ofReal (Cen R) ≤
        ENNReal.ofReal (plan.forceC R / 8 *
          ocEpsilon B.q A.Λ M ^ (A.Pw + 2 * B.q ^ A.Jw + 1))

/-- The analytic price leaf, for the actual chosen factors. The eventual threshold
precedes instances, carrier starts and Dm, and pays any positive scalar budget. -/
def WeakGluingAbsorptionStatement (prices : WeakGluingPrices) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
    A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1) →
    A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 <
      2 * weakAStar B.α B.q * (A.Rw + 1) →
    128 ≤ A.Λ →
    ∀ C c₀ : ℝ, 0 ≤ C → 0 < c₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      prices.factor R M * ENNReal.ofReal C ≤
        ENNReal.ofReal (c₀ * ocEpsilon B.q A.Λ M ^ (A.Pw + 2 * B.q ^ A.Jw + 1))

end AVRegularity.Providers.WeakGen.Residual
end
end

section
/-! The scalar absorption used by both weak gluing estimates. The level floor is chosen
after the finite polynomial loss, decay coefficient, coarse energy constant and target price,
and before data or the ambient cap. This is the scalar part of the two price leaves. -/

@[expose] public noncomputable section
open Filter Topology
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-- Every fixed polynomial loss times the quiet exponential is eventually smaller than an
arbitrary positive multiple of the requested wavelength power. No Dm occurs in the floor. -/
theorem weak_gluing_quiet_price_eventually {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    {K A c p P δ : ℝ} (hc : 0 < c) (hp : 0 < p) (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ m ≥ M,
      K * ocEpsilon q Λ m ^ (-A) *
          Real.exp (-(c * ocEpsilon q Λ m ^ (-p))) ≤ δ * ocEpsilon q Λ m ^ P := by
  have he : ∀ m, 0 < ocEpsilon q Λ m := fun m => (Scales.epsilon_basic (m := m) hq hΛ).1
  have h := CycleReference.exponential_small_scale_eventually he
    (EntryWeakProofs.weak_epsilon_tendsto_zero hq hΛ) A P (K / δ) c p hc hp
  obtain ⟨M, hM⟩ := eventually_atTop.mp h
  refine ⟨M, fun m hm => ?_⟩
  have hmul := mul_le_mul_of_nonneg_left (hM m hm) hδ.le
  calc K * ocEpsilon q Λ m ^ (-A) * Real.exp (-(c * ocEpsilon q Λ m ^ (-p)))
      = δ * (K / δ * ocEpsilon q Λ m ^ (-A) *
          Real.exp (-c * ocEpsilon q Λ m ^ (-p))) := by
        rw [neg_mul]
        field_simp
    _ ≤ δ * ocEpsilon q Λ m ^ P := hmul

open WeakEntryProofs.Assembly

/-- Choose the coarse-energy constant before the data; menus outside the analytical hypotheses
are irrelevant and receive zero. The choice is made from the coarse-energy input. -/
def weakGluingCoarseConstant (plan : WeakPassagePlan) (seed : WeakGluingPrices)
    (henergy : WeakCoarseReadoutEnergyStatement plan seed.order)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) : ℝ :=
  if h : (A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1)) ∧
      (A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 <
        2 * weakAStar B.α B.q * (A.Rw + 1)) then
    (henergy R h.1 h.2).choose else 0

/-- Sum the scalar transition prices over the finitely many parent levels of a passage.
The choice reads only the menu and request, and hence remains uniform in the ambient cap. -/
def weakGluingParentPrices (seed : WeakGluingPrices)
    (K Aexp c p : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℝ) : WeakGluingPrices :=
  { seed with factor := fun {B} {A} R M =>
      ∑ l ∈ Finset.range A.Jw, ENNReal.ofReal (K R * ocEpsilon B.q A.Λ (M + l) ^ (-Aexp R) *
          Real.exp (-(c R * ocEpsilon B.q A.Λ (M + l) ^ (-p R)))) }

/-- The finite parent-level sum is absorbed at the terminal wavelength. Each parent is
smaller than that wavelength; no comparison constant depending on the chain depth is used. -/
theorem weak_gluing_parent_absorption (seed : WeakGluingPrices)
    (K Aexp c p : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℝ)
    (hc : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      0 < c R)
    (hp : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      0 < p R) : WeakGluingAbsorptionStatement (weakGluingParentPrices seed K Aexp c p) := by
  intro B A R _ _ hΛ C c₀ hC hc₀
  have hJ : (0 : ℝ) < A.Jw := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one A.Jw_pos)
  have hP : 0 ≤ A.Pw + 2 * B.q ^ A.Jw + 1 := by
    have hPw := A.Pw_pos
    have hq : 0 ≤ B.q := (zero_lt_one.trans B.hq.1).le
    positivity
  obtain ⟨M₀, hM₀⟩ := weak_gluing_quiet_price_eventually B.hq.1 hΛ
    (K := K R * C) (A := Aexp R) (P := A.Pw + 2 * B.q ^ A.Jw + 1)
    (hc R) (hp R) (div_pos hc₀ hJ)
  refine ⟨M₀, fun M hM => ?_⟩
  change (∑ l ∈ Finset.range A.Jw, ENNReal.ofReal _) * ENNReal.ofReal C ≤ _
  rw [Finset.sum_mul]
  have hterm : ∀ l ∈ Finset.range A.Jw,
      ENNReal.ofReal (K R * ocEpsilon B.q A.Λ (M + l) ^ (-Aexp R) *
        Real.exp (-(c R * ocEpsilon B.q A.Λ (M + l) ^ (-p R)))) * ENNReal.ofReal C ≤
      ENNReal.ofReal (c₀ / A.Jw * ocEpsilon B.q A.Λ M ^
        (A.Pw + 2 * B.q ^ A.Jw + 1)) := by
    intro l _
    rw [← ENNReal.ofReal_mul' hC]
    apply ENNReal.ofReal_le_ofReal
    have h := hM₀ (M + l) (by omega)
    have he := EntryScales.epsilon_antitone B.hq.1 hΛ (show M ≤ M + l by omega)
    have hpw := Real.rpow_le_rpow
      (Scales.epsilon_basic (m := M + l) B.hq.1 hΛ).1.le he hP
    calc K R * ocEpsilon B.q A.Λ (M + l) ^ (-Aexp R) *
        Real.exp (-(c R * ocEpsilon B.q A.Λ (M + l) ^ (-p R))) * C
        = K R * C * ocEpsilon B.q A.Λ (M + l) ^ (-Aexp R) *
          Real.exp (-(c R * ocEpsilon B.q A.Λ (M + l) ^ (-p R))) := by ring
      _ ≤ c₀ / A.Jw * ocEpsilon B.q A.Λ (M + l) ^
          (A.Pw + 2 * B.q ^ A.Jw + 1) := h
      _ ≤ _ := mul_le_mul_of_nonneg_left hpw (div_nonneg hc₀.le hJ.le)
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg A.Jw)]
  congr 1
  field_simp

/-- The selected coarse constant is nonnegative for every menu, including menus outside
its analytical hypotheses. -/
theorem weak_gluing_coarse_constant_nonneg (plan : WeakPassagePlan)
    (prices : WeakGluingPrices) (henergy : WeakCoarseReadoutEnergyStatement plan prices.order)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) :
    0 ≤ weakGluingCoarseConstant plan prices henergy R := by
  unfold weakGluingCoarseConstant
  split
  next hm => exact (henergy R hm.1 hm.2).choose_spec.1
  next _ => exact le_rfl

/-- A numerical threshold paying the actual coarse constant exists before data, the
carrier start and Dm. Invalid menus have zero coarse constant and need no threshold. -/
theorem weak_gluing_price_floor_exists (plan : WeakPassagePlan) (prices : WeakGluingPrices)
    (henergy : WeakCoarseReadoutEnergyStatement plan prices.order)
    (habs : WeakGluingAbsorptionStatement prices)
    (hforce : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
      (R : WeakPassageRequest A), 0 < plan.forceC R)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (hΛ : 128 ≤ A.Λ) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀,
      prices.factor R M * ENNReal.ofReal (weakGluingCoarseConstant plan prices henergy R) ≤
        ENNReal.ofReal (plan.forceC R / 8 *
          ocEpsilon B.q A.Λ M ^ (A.Pw + 2 * B.q ^ A.Jw + 1)) := by
  by_cases hm : (A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1)) ∧
      (A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 <
        2 * weakAStar B.α B.q * (A.Rw + 1))
  · exact habs R hm.1 hm.2 hΛ _ _
      (weak_gluing_coarse_constant_nonneg plan prices henergy R)
      (div_pos (hforce R) (by norm_num))
  · refine ⟨0, fun M _ => ?_⟩
    simp only [weakGluingCoarseConstant, dite_eq_right hm, ENNReal.ofReal_zero, mul_zero]
    exact bot_le

/-- The scalar price floor is a function of the menu and request only. -/
def weakGluingPriceFloor (plan : WeakPassagePlan) (prices : WeakGluingPrices)
    (henergy : WeakCoarseReadoutEnergyStatement plan prices.order)
    (habs : WeakGluingAbsorptionStatement prices)
    (hforce : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
      (R : WeakPassageRequest A), 0 < plan.forceC R)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) : ℕ :=
  if hΛ : 128 ≤ A.Λ then
    (weak_gluing_price_floor_exists plan prices henergy habs hforce R hΛ).choose else 0

end AVRegularity.Providers.WeakGen.Residual
end
end

section
/-! Scalar prices of the gluing terms. A finite pulse count times the
quiet exponential has a fixed power loss at the parent wavelength. The degenerate cases are
included: an empty sum has zero cost; a zero prefactor has zero cost; at one passage the parent
sum has one term. These estimates contain neither component spaces nor the ambient degree cap. -/

@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual
open WeakEntryProofs.Assembly CycleComparison.Assembly

/-- The positive exponent in the weak quiet-gap ledger, with the formulas of `ocGamma` and
`ocDelta`. -/
theorem weak_gluing_quiet_exponent_pos {α q : ℝ} (hα : 0 < α) (hq : 1 < q) :
    0 < 2 * (q - 1) + ocGamma α q - 4 * ocDelta α q := by
  have hid : 2 * (q - 1) + ocGamma α q - 4 * ocDelta α q =
      (q - 1) * (4 * q + 5 + (2 * q + 3) * α) / (2 * (q + 1)) := by
    unfold ocGamma ocDelta
    field_simp
    ring
  rw [hid]
  have hq0 : 0 < q := zero_lt_one.trans hq
  exact div_pos (mul_pos (sub_pos.mpr hq) (by positivity)) (by positivity)

/-- A quiet-scale lower bound controls both the heat prefactor and its exponential. -/
theorem weak_gluing_heat_price {E C c p ℓ τ : ℝ} (hE : 0 < E) (hE1 : E ≤ 1)
    (hC : 0 < C) (hc : 0 ≤ c) (hp : 0 ≤ p) (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (hquiet : C⁻¹ * E ^ (-p) ≤ τ / ℓ ^ 2) :
    ℓ * Real.sqrt (1 / τ) * Real.exp (-(c * τ / ℓ ^ 2)) ≤
      (1 + C) * Real.exp (-(c / C * E ^ (-p))) := by
  have hpow : 1 ≤ E ^ (-p) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hE hE1 (neg_nonpos.mpr hp)
  have hbase : C⁻¹ ≤ τ / ℓ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hC.le)
    exact (by simpa only [mul_one] using hh : C⁻¹ ≤ C⁻¹ * E ^ (-p)).trans hquiet
  have hmul : ℓ ^ 2 ≤ C * τ := by
    have hh := (le_div_iff₀ (sq_pos_of_pos hℓ)).mp hbase
    have hh' := mul_le_mul_of_nonneg_left hh hC.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] using hh'
  have hratio : ℓ ^ 2 / τ ≤ C := (div_le_iff₀ hτ).mpr hmul
  have hpre : ℓ * Real.sqrt (1 / τ) ≤ 1 + C := by
    simpa only [mul_one] using bill_prefactor_le hℓ (show (0 : ℝ) ≤ 1 by norm_num)
      hC.le hratio
  have hexp : Real.exp (-(c * τ / ℓ ^ 2)) ≤ Real.exp (-(c / C * E ^ (-p))) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    calc c / C * E ^ (-p) = c * (C⁻¹ * E ^ (-p)) := by ring
      _ ≤ c * (τ / ℓ ^ 2) := mul_le_mul_of_nonneg_left hquiet hc
      _ = c * τ / ℓ ^ 2 := (mul_div_assoc c τ (ℓ ^ 2)).symm
  exact mul_le_mul hpre hexp (Real.exp_pos _).le (by positivity)

/-- The weak scale ledger supplies the quiet lower bound uniformly for every diffusivity
in the terminal band. The inverse pulse length has only a fixed polynomial parent loss. -/
theorem weak_gluing_parent_scale_prices (B : WeakCoefficientBase) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Λ : ℕ, 128 ≤ Λ → ∀ M : ℕ, ∀ ν ∈ ocBand B.α B.q Λ M,
      ∀ i : ℕ, M < i →
      C⁻¹ * ocEpsilon B.q Λ (i - 1) ^
        (-(2 * (B.q - 1) + ocGamma B.α B.q - 4 * ocDelta B.α B.q)) ≤
          ocTau B.α B.q Λ i / (ocEpsilon B.q Λ i / Real.sqrt ν) ^ 2 ∧
      (ocTau B.α B.q Λ i)⁻¹ ≤ (2 ^ (26 : ℕ) * 81) *
        ocEpsilon B.q Λ (i - 1) ^ (-(2 - (1 + B.α) + 4 * ocDelta B.α B.q)) := by
  obtain ⟨C, hC, hs⟩ := EntryScales.weak_scales_core B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq
  refine ⟨C, hC, fun Λ hΛ M ν hν i hi => ?_⟩
  have hE := (Scales.epsilon_basic (m := i - 1) B.hq.1 hΛ).1
  have hν0 : 0 < ν := lt_of_lt_of_le
    (div_pos (Real.rpow_pos_of_pos (Scales.epsilon_basic (m := M) B.hq.1 hΛ).1 _) (by norm_num)) hν.1
  have heq : ocTau B.α B.q Λ i / (ocEpsilon B.q Λ i / Real.sqrt ν) ^ 2 =
      ν * ocTau B.α B.q Λ i / ocEpsilon B.q Λ i ^ 2 := by
    rw [div_pow, Real.sq_sqrt hν0.le]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact (hs Λ hΛ M ν hν i hi).2.2.2.1
  · exact inv_le_powerLaw hE (by norm_num)
      (CycleReference.ocTau_asymp B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq hΛ (m := i)).1

end AVRegularity.Providers.WeakGen.Residual
end
end
end
end

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-! The exposed factory orders, and `cycle_residual_partition_differentiated` at a weak
slot. The fixed-carrier factory supplies the three equalities; no extra reserve is
assumed. All numerical choices and its constants precede the data and the ambient cap. -/

open Finite.WeakLift CycleComparison.Reconstruction WeakEntryProofs.Assembly EntryWeakProofs

/-- The factory choices. -/
structure WeakGluingFactoryOrders {N H : ℕ} (J Lr : ℕ)
    (P : WeakPositiveParameters N H (Lr + 3)) : Prop where
  capMax_eq : P.capMax = max 2 (1 + J * N)
  slowOrder_eq : P.slowOrder = Lr + 3 + (N + P.capMax)
  fastOrder_eq : P.fastOrder = Lr + 3

/-- The consumer's order, also covering the menu lower bound of the slot-lift supplier. -/
def weakGluingReadoutOrder (J N H Acl r : ℕ) : ℕ :=
  max (J * N) (Acl + r + max 2 (1 + J * N) * (H + 1) * N + 2)

/-- The explicit factory choices pay the partition reserves at `(kl,Ll)=(2,0)`. -/
theorem weak_gluing_factory_reserves {N H J Lr Acl r : ℕ}
    {P : WeakPositiveParameters N H (Lr + 3)} (hP : WeakGluingFactoryOrders J Lr P)
    (hL : weakGluingReadoutOrder J N H Acl r ≤ Lr) :
    J * N ≤ Lr ∧ WeakGluingPartitionReserves P Acl r := by
  have hmax := max_le_iff.mp hL
  rw [← hP.capMax_eq] at hmax
  unfold WeakGluingPartitionReserves
  rw [hP.slowOrder_eq, hP.fastOrder_eq]
  omega

/-- The shared, plan-free slot-lift parameters have precisely the differentiated partition
orders. This reads the factory's choice once, without choosing new slot-lift data. -/
theorem weak_gluing_slot_lift_factory_orders {B : WeakCoefficientBase}
    (A : WeakCoefficientPhysical B) (Lr : ℕ) (hLr : A.Jw * A.Nw ≤ Lr) (sX sZ : ℕ) :
    WeakGluingFactoryOrders A.Jw Lr (weakSlotLiftParams A Lr sX sZ) := by
  rw [weakSlotLiftParams, dite_eq_left hLr]
  obtain ⟨hcap, hslow, hfast, _⟩ :=
    Classical.choose_spec (weakSlotLiftEx A Lr sX sZ hLr)
  exact ⟨hcap, hslow, hfast⟩

/-- Quietness of the slot lift on a trimmed physical interval follows from native quietness and
`edge_fast`. The original slot-lift window and its original lift start are retained. -/
theorem weak_gluing_slot_lift_quiet_of_native {plan : WeakPassagePlan}
    (hquiet : WeakSlotNativeQuietStatement plan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) {i : ℕ} (hi : c.M < i) (hiJ : i ≤ c.M + A.Jw)
    {U : ℕ} {P : WeakPositiveParameters A.Nw (A.Jw * A.Rw) U}
    (slotLifts : ∀ slot : OddSlot, WeakPositiveSlot P i (c.stage i)
      (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) slot) :
    WeakSlotLiftQuiet c i slotLifts := by
  intro slot g d hd hg hgd htrim
  let cs := c.D.cellScaleSq i
  have hΛ : 1 ≤ c.D.Λ := by
    rw [c.base_eq]
    have := (plan.base_ge B).trans c.base_ge
    omega
  have hζ : IsFastProfile c.D.ζ := c.profile_eq.symm ▸ B.hζ
  have hcs : 0 < cs := by
    change 0 < c.D.cellScaleSq i
    exact weakData_cellScaleSq_pos c.D hΛ hζ
      (by rw [c.alpha, c.q_eq, c.base_eq, c.profile_eq, c.terminal]; exact c.band) i
  let S := Set.Icc (g / cs) ((g + d) / cs)
  have hS : S ⊆ Set.Icc (weakSlotLeft c.D i slot.1) (weakSlotRight c.D i slot.1) := by
    intro t ht
    exact ⟨((le_div_iff₀ hcs).mpr (by simpa only [cs, mul_comm] using hg)).trans ht.1,
      ht.2.trans ((div_le_iff₀ hcs).mpr (by simpa only [cs, mul_comm] using hgd))⟩
  have hphys : ∀ t ∈ S, c.D.cellScaleSq i * t ∈
      ocTrimmedQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ i := by
    intro t ht
    apply htrim
    exact ⟨(div_le_iff₀ hcs).mp ht.1 |>.trans_eq (mul_comm _ _),
      (le_div_iff₀ hcs).mp ht.2 |>.trans' (le_of_eq (mul_comm _ _))⟩
  have hn := hquiet c i hi hiJ slot S hS hphys
  refine ⟨?_, (slotLifts slot).edge_fast S hS hn.2⟩
  intro t ht z
  rw [(slotLifts slot).drift_eq]
  change Real.sqrt (slotLifts slot).Q.η •
    ocPulseCellDrift c.D.α c.D.q c.D.Λ c.D.ζ i (c.D.kap i) slot.1 t z = 0
  rw [weakNativeQuietDrift hΛ hζ (slotLifts slot).setting.ν_pos slot.2
    (QuietAtlas.ocTrimmedQuietTimes_subset hΛ c.D.ζ i (hphys t ht)) z, smul_zero]

end AVRegularity.Providers.WeakGen.Residual
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-! The original-window partition estimate at a weak slot, with constants uniform over
the factory's finite set of effective caps. The coarse input is required only on its
comparison window; it is extended by zero without restarting the stored lift. -/

open Finite.WeakLift CycleComparison.Reconstruction

private theorem weakGluingFiniteDecayConstants (Dmax : ℕ) (C c : ℕ → ℝ)
    (hC : ∀ d, 0 ≤ C d) (hc : ∀ d, 0 < c d) :
    ∃ C₀ c₀ : ℝ, 0 ≤ C₀ ∧ 0 < c₀ ∧
      ∀ d ≤ Dmax, C d ≤ C₀ ∧ c₀ ≤ c d := by
  obtain ⟨d₀, _, hmin⟩ := (Finset.range (Dmax + 1)).exists_min_image c
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  refine ⟨∑ d ∈ Finset.range (Dmax + 1), C d, c d₀,
    Finset.sum_nonneg (fun d _ => hC d), hc d₀, fun d hd => ?_⟩
  have hm : d ∈ Finset.range (Dmax + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hd)
  exact ⟨Finset.single_le_sum (fun d _ => hC d) hm, hmin d hm⟩

private theorem weakGluingDecayFactor_le {C C₀ c c₀ J M ℓ d δ : ℝ}
    (hCpos : 0 ≤ C) (hC : C ≤ C₀) (hc : c₀ ≤ c) (hJ : 0 ≤ J) (hM : 0 ≤ M)
    (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) :
    C * J * M * ℓ * Real.sqrt d * Real.exp (-(c * δ / ℓ ^ 2)) ≤
      C₀ * J * M * ℓ * Real.sqrt d * Real.exp (-(c₀ * δ / ℓ ^ 2)) := by
  have hcoeff : C * J * M * ℓ * Real.sqrt d ≤ C₀ * J * M * ℓ * Real.sqrt d :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC hJ) hM) hℓ.le) (Real.sqrt_nonneg _)
  have hexp : Real.exp (-(c * δ / ℓ ^ 2)) ≤ Real.exp (-(c₀ * δ / ℓ ^ 2)) :=
    Real.exp_le_exp.mpr (neg_le_neg (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc hδ) (sq_nonneg _)))
  exact mul_le_mul hcoeff hexp (Real.exp_pos _).le
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hCpos.trans hC) hJ) hM) hℓ.le)
      (Real.sqrt_nonneg _))

/-- The label-frame transition of any selected slot lift, after transport of the energy of
the charted input. Its constants, trace price and coarse energy order do not depend on
the selected cap, the stage, the component family, the data or the ambient cap. -/
theorem weak_gluing_slot_lift_transition_on_window {N H J Lr Acl r : ℕ}
    (P : WeakPositiveParameters N H (Lr + 3)) (hP : WeakGluingFactoryOrders J Lr P)
    (hL : weakGluingReadoutOrder J N H Acl r ≤ Lr) (hAcl : 1 ≤ Acl) (Dχ : ℝ) :
    ∃ C c CI : ℝ, 0 ≤ C ∧ 0 < c ∧ 0 ≤ CI ∧
    ∀ {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (i : ℕ)
      (G : GenStage D ScalarH Dm bw j₀) (π : CompIn G.comps → ℝ) (slot : OddSlot)
      (W : WeakPositiveSlot P i G π slot) (rs : ℝ),
      0 < rs → rs ≤ D.eps i → D.eps i ≤ D.eps (i - 1) →
      D.kap (i - 1) = D.kap i → (∃ M : ℕ, (D.eps i)⁻¹ = (M : ℝ)) →
    ∀ χ χi : ℝ → Vec 2 → Vec 2, (∀ t, IsChart (χ t) (χi t)) →
      (∀ t, ContDiff ℝ (⊤ : ℕ∞) (χ t)) → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (χi t)) →
    ∀ g d : ℝ, 0 < d →
      (D.eps i / Real.sqrt (D.kap i)) ^ 2 * weakSlotLeft D i slot.1 ≤ g →
      g + d ≤ (D.eps i / Real.sqrt (D.kap i)) ^ 2 * weakSlotRight D i slot.1 →
      (∀ t ∈ Set.Icc g (g + d),
        JetBound (χ t) (4 * (N + P.capMax) + 2 * Acl + 16 + r + 2) Dχ (D.eps (i - 1)) ∧
        JetBound (χi t) (4 * (N + P.capMax) + 2 * Acl + 16 + r + 2) Dχ (D.eps (i - 1))) →
      IsQuietOn W.Q.edge (fun t z => Real.sqrt W.Q.η • W.Q.v t z)
        (Set.Icc (g / (D.eps i / Real.sqrt (D.kap i)) ^ 2)
          ((g + d) / (D.eps i / Real.sqrt (D.kap i)) ^ 2)) →
    ∀ (ψ : ℝ → ℝ) (M δ : ℝ), 0 ≤ δ → δ ≤ d →
      (∀ t, |ψ t| ≤ M) → Function.support ψ ⊆ Set.Icc (g + δ) (g + d) →
    ∀ S : Set ℝ, MeasurableSet S → Function.support ψ ⊆ S →
    ∀ hh, hh ≤ H → ∀ a : ℝ → Vec 2 → CompIn G.comps → ℝ,
      (∀ t ∈ S, ContDiff ℝ ((4 * (N + P.capMax) + 2 * Acl + 16 + r + 1 : ℕ) : ℕ∞) (a t)) →
      (∀ t ∈ S, IsZ2Periodic (a t)) → ∀ j, j ≤ r → ∀ w : DerivativeWord2 j,
      ∫⁻ t, scalInt π (fun y => rs ^ j • orderedDerivative w
          (transitionSourceField N hh (D.eps i / Real.sqrt (D.kap i))
            (D.eps (i - 1)) (D.eps i) (D.eps i / D.eps (i - 1)) ψ W.coeff
            (fun t' y' => a t' (χ t' y')) t) y) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C *
          (∑ b ∈ Finset.range (hh + 1), P.S ^ (hh - b) * (CI * P.S ^ b)) *
          M * (D.eps i / Real.sqrt (D.kap i)) * Real.sqrt d *
          Real.exp (-(c * δ / (D.eps i / Real.sqrt (D.kap i)) ^ 2))) *
        classicalStrongEnergy (D.eps (i - 1)) (D.kap (i - 1)) π S
          (4 * (N + P.capMax) + 2 * Acl + 16 + r) a := by
  classical
  choose C c hC hc hgate using fun cap =>
    weak_gluing_transition_label_bound Acl N cap H 2 0 r P.CG P.Cw P.Cj Dχ hAcl
  obtain ⟨C₀, c₀, hC₀, hc₀, hbound⟩ := weakGluingFiniteDecayConstants P.capMax C c hC hc
  obtain ⟨CI, hCI, htrace⟩ := weak_gluing_slot_lift_entrance_traces P
  refine ⟨C₀, c₀, CI, hC₀, hc₀, hCI, ?_⟩
  intro D Dm bw j₀ i G π slot W rs hrs hrse heρ hplateau he χ χi hchart hχ hχi
    g d hd hg hgd hJ hquiet ψ M δ hδ hδd hψ hsupp S hS hsuppS hh hhh a ha haper j hj w
  have horders := weak_gluing_partition_orders (weak_gluing_factory_reserves hP hL).2 W.cap_le
  have hsetting := weakIsLiftSetting_mono W.setting horders.1 horders.2.1
    (show r + W.cap * (H + 1) * N ≤ P.fastOrder by omega) rfl rfl
  have hεc : ocDStar D.q D.Λ i (D.kap i) (D.kap (i - 1)) / D.eps (i - 1) =
      D.eps i / D.eps (i - 1) := by
    simp only [ocDStar, hplateau, div_self W.setting.ν_pos.ne', Real.sqrt_one, mul_one, OCData.eps]
  rw [hεc] at hsetting
  have hseq := isLiftSequence_mono W.sequence horders.2.2.1 horders.2.2.2.1
  have hℓ : 0 < D.eps i / Real.sqrt (D.kap i) :=
    div_pos W.setting.e_pos (Real.sqrt_pos.mpr W.setting.ν_pos)
  have hℓ2 : 0 < (D.eps i / Real.sqrt (D.kap i)) ^ 2 := sq_pos_of_pos hℓ
  have ht : g / (D.eps i / Real.sqrt (D.kap i)) ^ 2 ∈
      Set.Icc (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) := by
    constructor
    · exact (le_div_iff₀ hℓ2).mpr (by simpa only [mul_comm] using hg)
    · exact (div_le_iff₀ hℓ2).mpr ((by linarith only [hd] : g ≤ g + d).trans
        (by simpa only [mul_comm] using hgd))
  have hI := htrace i G π slot W _ ht _ _ horders.1 horders.2.2.2.2
  have hlam : D.eps (i - 1) / D.eps (i - 1) = (1 : ℝ) := div_self W.setting.E_pos.ne'
  rw [← hlam] at hI
  have hK : 4 * (N + W.cap) + 2 * Acl + 16 + r ≤
      4 * (N + P.capMax) + 2 * Acl + 16 + r := by have := W.cap_le; omega
  have hb := weak_gluing_transition_label_on_window (hgate W.cap) W.Q π
    (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1)
    (D.eps i) (D.kap i) (D.kap (i - 1)) (D.eps (i - 1)) rs (D.eps (i - 1))
    (D.eps i / Real.sqrt (D.kap i)) (ocDStar D.q D.Λ i (D.kap i) (D.kap (i - 1)))
    (D.eps i / D.eps (i - 1)) (D.eps (i - 1) / D.eps (i - 1)) (D.eps (i - 1))
    (EntryWeakProofs.pulseParallel slot.1)
    (EntryWeakProofs.pulseShearProfile D.α D.q D.Λ i D.ζ (D.kap i) slot.1)
    _ _ W.price P.S hrs hrse heρ le_rfl
    (by simpa only [Nat.zero_add] using hsetting) he W.coeff
    (by simpa only [Nat.zero_add] using hseq) χ χi hchart hχ hχi g d hd hg hgd
    (fun t ht => ⟨fun p hp1 hp2 y => (hJ t ht).1 p hp1 (by omega) y,
      fun p hp1 hp2 y => (hJ t ht).2 p hp1 (by omega) y⟩) hquiet (fun b => CI * P.S ^ b)
    (by simpa only [Nat.zero_add] using hI) ψ M δ hδ hδd hψ hsupp S hS hsuppS hh hhh a
    (fun t ht => (ha t ht).of_le (natCast_le_natCast_order (by omega))) haper j hj w
  have henergy := weak_gluing_classical_energy_radius_le (c := 1) zero_lt_one le_rfl
    (D.eps (i - 1)) (D.kap (i - 1)) π S hK a
  simp only [inv_one, one_pow, Real.one_rpow, ENNReal.ofReal_one, one_mul] at henergy
  have hfactor := weakGluingDecayFactor_le
    (J := ∑ b ∈ Finset.range (hh + 1), P.S ^ (hh - b) * (CI * P.S ^ b))
    (d := d) (hC W.cap) (hbound W.cap W.cap_le).1
    (hbound W.cap W.cap_le).2
    (Finset.sum_nonneg fun b _ => mul_nonneg (pow_nonneg P.S_nonneg _)
      (mul_nonneg hCI (pow_nonneg P.S_nonneg _)))
    ((abs_nonneg (ψ 0)).trans (hψ 0)) hℓ hδ
  exact hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hfactor) henergy)

end AVRegularity.Providers.WeakGen.Residual
end

section
open Homogenization MeasureTheory
namespace AVRegularity.Providers.WeakGen.Residual

/-! Each clipped cutoff derivative is estimated on its original quiet gap. Both gaps
have a positive delay before the derivative can be nonzero, even when the observation
window starts inside the falling overlap. -/

open CycleComparison.Reconstruction

/-- Original quiet entrance of a falling or rising transition. -/
def weakGluingGapLeft (τ : ℝ) (k : ℤ) : Bool → ℝ
  | true => ((k : ℝ) + 17 / 24) * τ
  | false => ((k : ℝ) - 61 / 48) * τ

/-- Original right endpoint of a falling or rising transition. -/
def weakGluingGapRight (τ : ℝ) (k : ℤ) : Bool → ℝ
  | true => ((k : ℝ) + 61 / 48) * τ
  | false => ((k : ℝ) - 35 / 48) * τ

/-- The two original gaps have length at most one slow period and lie strictly within
the original slot window. The uniform delay `τ/48` is smaller than each gap. -/
theorem weak_gluing_original_gap_geometry {τ : ℝ} (hτ : 0 < τ) (k : ℤ) (σ : Bool) :
    0 < weakGluingGapRight τ k σ - weakGluingGapLeft τ k σ ∧
    weakGluingGapRight τ k σ - weakGluingGapLeft τ k σ ≤ τ ∧
    τ / 48 ≤ weakGluingGapRight τ k σ - weakGluingGapLeft τ k σ ∧
    ((k : ℝ) - 61 / 48) * τ ≤ weakGluingGapLeft τ k σ ∧
    weakGluingGapRight τ k σ ≤ ((k : ℝ) + 61 / 48) * τ := by
  cases σ <;> dsimp only [weakGluingGapRight, weakGluingGapLeft] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ring_nf <;> linarith only [hτ]

/-- Original gaps are trimmed quiet sets. This asserts no quietness outside the trimmed
set and does not clip the entrance to the supplied comparison window. -/
theorem weak_gluing_original_gap_trimmed {D : OCData} (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (i : ℕ) {k : ℤ} (hk : Odd k) (σ : Bool) :
    Set.Icc (weakGluingGapLeft (ocTau D.α D.q D.Λ i) k σ)
      (weakGluingGapRight (ocTau D.α D.q D.Λ i) k σ) ⊆
      ocTrimmedQuietTimes D.α D.q D.Λ D.ζ i := by
  intro t ht
  have hτ : 0 < ocTau D.α D.q D.Λ i := Construction.Stream.ocTau_pos hΛ
  cases σ
  · exact CycleComparison.odd_trimmed_gap_left hΛ hζ hk
      (by dsimp only [weakGluingGapLeft] at ht; linarith only [ht.1, hτ])
      (by dsimp only [weakGluingGapRight] at ht; linarith only [ht.2, hτ])
  · exact CycleComparison.odd_trimmed_gap hΛ hζ hk ht.1
      (by dsimp only [weakGluingGapRight] at ht; linarith only [ht.2, hτ])

/-- The actual clipped derivative weight is supported after the positive delay from
its original entrance, and is supported inside the comparison window. -/
theorem weak_gluing_transition_weight_support {D : OCData} (hΛ : 1 ≤ D.Λ)
    (i : ℕ) (a b : ℝ) (k : ℤ) (σ : Bool) :
    Function.support (trWeight (ocCutoff D.α D.q D.Λ i)
      (ocTau D.α D.q D.Λ i) a b k σ) ⊆
        Set.Icc (weakGluingGapLeft (ocTau D.α D.q D.Λ i) k σ + ocTau D.α D.q D.Λ i / 48)
          (weakGluingGapRight (ocTau D.α D.q D.Λ i) k σ) ∧
    Function.support (trWeight (ocCutoff D.α D.q D.Λ i)
      (ocTau D.α D.q D.Λ i) a b k σ) ⊆ Set.Icc a b := by
  have hτ : 0 < ocTau D.α D.q D.Λ i := Construction.Stream.ocTau_pos hΛ
  constructor
  · intro t ht
    obtain ⟨htI, hderiv⟩ := trWeight_ne_zero (Function.mem_support.mp ht)
    have hw := (mem_window_of_trIcc hτ htI).1
    have hdist := (CycleReference.cutoff_derivative_nonzero_distance hΛ k t hderiv).2
    cases σ
    · change max _ a ≤ t ∧ t ≤ min _ b at htI
      have hhi := htI.2.trans (min_le_left _ _)
      have hneg : t - (k : ℝ) * ocTau D.α D.q D.Λ i ≤ 0 := by linarith only [hhi, hτ]
      rw [abs_of_nonpos hneg] at hdist
      constructor
      · dsimp only [weakGluingGapLeft]
        linarith only [hdist]
      · exact hhi
    · change max _ a ≤ t ∧ t ≤ min _ b at htI
      constructor
      · have hlo := (le_max_left _ _).trans htI.1
        dsimp only [weakGluingGapLeft]
        linarith only [hlo]
      · exact hw.2
  · intro t ht
    exact (mem_window_of_trIcc hτ (trWeight_ne_zero (Function.mem_support.mp ht)).1).2

/-- The two clipped transition weights split the literal derivative on the closed
comparison window. This uses the actual cutoff support, including at both endpoints,
rather than a partition theorem that restarts lifts at those endpoints. -/
theorem weak_gluing_transition_weight_add {D : OCData} (hΛ : 1 ≤ D.Λ)
    (i : ℕ) (a b : ℝ) (k : ℤ) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    deriv (ocCutoff D.α D.q D.Λ i k) t =
      trWeight (ocCutoff D.α D.q D.Λ i) (ocTau D.α D.q D.Λ i) a b k true t +
      trWeight (ocCutoff D.α D.q D.Λ i) (ocTau D.α D.q D.Λ i) a b k false t := by
  have hτ : 0 < ocTau D.α D.q D.Λ i := Construction.Stream.ocTau_pos hΛ
  by_cases hd : deriv (ocCutoff D.α D.q D.Λ i k) t = 0
  · simp only [trWeight, Set.indicator_apply, hd]
    split_ifs <;> simp
  obtain ⟨hlo, hhi⟩ := CycleReference.cutoff_derivative_nonzero_distance hΛ k t hd
  rcases le_or_gt t ((k : ℝ) * ocTau D.α D.q D.Λ i) with hside | hside
  · rw [abs_of_nonpos (sub_nonpos.mpr hside)] at hlo hhi
    have hmem : t ∈ Set.Icc (trLo (ocTau D.α D.q D.Λ i) a k false)
        (trHi (ocTau D.α D.q D.Λ i) b k false) := by
      constructor
      · exact max_le (by linarith only [hhi, hτ]) ht.1
      · exact le_min (by linarith only [hlo, hτ]) ht.2
    have hnot : t ∉ Set.Icc (trLo (ocTau D.α D.q D.Λ i) a k true)
        (trHi (ocTau D.α D.q D.Λ i) b k true) := by
      intro hm
      have hh := (le_max_left _ _).trans hm.1
      change ((k : ℝ) + 35 / 48) * ocTau D.α D.q D.Λ i ≤ t at hh
      linarith only [hh, hside, hτ]
    simp only [trWeight, Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot, zero_add]
  · rw [abs_of_nonneg (sub_nonneg.mpr hside.le)] at hlo hhi
    have hmem : t ∈ Set.Icc (trLo (ocTau D.α D.q D.Λ i) a k true)
        (trHi (ocTau D.α D.q D.Λ i) b k true) := by
      constructor
      · exact max_le (by linarith only [hlo, hτ]) ht.1
      · exact le_min (by linarith only [hhi, hτ]) ht.2
    have hnot : t ∉ Set.Icc (trLo (ocTau D.α D.q D.Λ i) a k false)
        (trHi (ocTau D.α D.q D.Λ i) b k false) := by
      intro hm
      have hh := hm.2.trans (min_le_left _ _)
      change t ≤ ((k : ℝ) - 35 / 48) * ocTau D.α D.q D.Λ i at hh
      linarith only [hh, hside, hτ]
    simp only [trWeight, Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot, add_zero]

end AVRegularity.Providers.WeakGen.Residual
end
end
end
