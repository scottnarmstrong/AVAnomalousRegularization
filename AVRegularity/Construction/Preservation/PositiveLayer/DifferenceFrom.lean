-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.Intermediate.CycleComparison.CycleResidualDifferentiated
import AVRegularity.Proofs.Results.Construction.SuccessorFluxUnique
import AVRegularity.CycleComparison.Reconstruction.Orders
public import AVRegularity.Construction.Preservation.PositiveLayer.CellFourierBounds
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.Construction.InitialLayer.Comparison
import AVRegularity.CycleComparison.Residual.CoarseFlux
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
import AVRegularity.CycleEvolution.FibreCoefficientWeightedForcing

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.PositiveLayer

/-! Promotion of an actual Hilbert-fibre lift to the existence theorem's stored orders.
Uniqueness is applied at the minimum of the two pairs of orders. Thus no positive lower
bound on the original stored orders is needed.

The degenerate cases are included: zero stored orders, `H = 0`, `Theta = 0`, empty and singleton
fibres, identity metric, `D = 2`, and edgeless data use the same uniqueness argument. No time
interval is lengthened, and no entrance trace is changed; intervals shorter than one are allowed. -/

open CycleComparison.Reconstruction CycleComparison.Lift

variable {ι : Type} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {bb : ι → ι → ℝ} {Θ : ℝ}

/-- Raise the stored regularity of the given sequence itself, without replacing its values. -/
theorem positive_layer_lift_sequence_promote
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bb Θ)
    {sX sZ : ℕ} (hX : sX ≤ qs) (hZ : sZ ≤ qf)
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hC : IsLiftSequence Q sX sZ a b N H Cc) :
    IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc := by
  obtain ⟨Cc', hC'⟩ := Providers.cycle_lift_exists N K k L D H CG Cw Cj Q π a b
    e ν B ρ E ℓ dstar εc lam par V qs qf bb Θ P
  have he := Providers.lift_sequence_unique Q π a b e ν B ρ E ℓ dstar εc lam par V
    H N K k L qs qf CG Cw Cj bb Θ P
    (min sX (K + D + 2)) (min sZ (max (k + 1) (L + 2)))
    ((min_le_left _ _).trans hX) ((min_le_left _ _).trans hZ) Cc Cc'
    (isLiftSequence_mono hC (min_le_left _ _) (min_le_left _ _))
    (isLiftSequence_mono hC' (min_le_right _ _) (min_le_right _ _))
  refine ⟨hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2.1, ?_, ?_⟩
  · intro hh hhH n m α v u t ht
    have hf : (fun X z => Cc hh n m α t X z v u) =
        (fun X z => Cc' hh n m α t X z v u) :=
      funext fun X => funext fun z => he hh hhH n m α t ht X z v u
    refine ⟨?_, (hC.2.2.2.2.2.1 hh hhH n m α v u t ht).2⟩
    rw [hf]
    exact (hC'.2.2.2.2.2.1 hh hhH n m α v u t ht).1
  · intro hh hhH n hn hnN f hf X
    refine ⟨?_, (hC.2.2.2.2.2.2 hh hhH n hn hnN f hf X).2⟩
    intro t ht
    have ha := liftApply_congr_at_time n (Cc hh n) (Cc' hh n) (fun _ => f) t
      (fun m α Y z v u => he hh hhH n m α t ht Y z v u)
    change ContDiff ℝ (max (k + 1) (L + 2) : ℕ∞) (liftApply n (Cc hh n) (fun _ => f) t X)
    rw [ha]
    exact (hC'.2.2.2.2.2.2 hh hhH n hn hnN f hf X).1 t ht

private theorem time_sup_le {I J : Set ℝ} (hJI : J ⊆ I) (f : ℝ → ℝ≥0∞) :
    (⨆ t ∈ J, f t) ≤ ⨆ t ∈ I, f t :=
  iSup₂_le fun t ht => le_iSup₂_of_le t (hJI ht) le_rfl

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
/-- Restrict the setting to a later entrance, retaining all constants and reserves. -/
theorem positive_layer_setting_restrict
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bb Θ)
    {a' : ℝ} (haa : a ≤ a') (hab : a' ≤ b) :
    IsLiftSetting Q π a' b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bb Θ := by
  have hI : Set.Icc a' b ⊆ Set.Icc a b := Set.Icc_subset_Icc haa le_rfl
  refine { P with
    window := hab
    G_smooth := fun t ht => P.G_smooth t (hI ht)
    G_ellip := fun t ht => P.G_ellip t (hI ht)
    G_jets := fun r hr => (time_sup_le hI _).trans (P.G_jets r hr)
    V_smooth := fun t ht => P.V_smooth t (hI ht)
    V_per := fun t ht => P.V_per t (hI ht)
    V_mean := fun t ht => P.V_mean t (hI ht)
    w_jets := fun r hr => (time_sup_le hI _).trans (P.w_jets r hr)
    transverse := fun v u d γ hγ α t ht => P.transverse v u d γ hγ α t (hI ht)
    coeff_smooth := fun v u d γ hγ α t ht => P.coeff_smooth v u d γ hγ α t (hI ht)
    envelope := { P.envelope with jets := ?_ } }
  intro v u r hr q hq
  refine le_trans ?_ (P.envelope.jets v u r hr q hq)
  gcongr
  generalize Q.edge v u d = xs
  induction xs with
  | nil => exact le_rfl
  | cons γ xs ih =>
    simp only [List.map_cons, List.sum_cons]
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le) ih
    exact Finset.sum_le_sum fun α _ => time_sup_le hI _

end AVRegularity.Construction.Preservation.PositiveLayer
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.PositiveLayer

/-! The promoted sequences have the classical quiet facts needed by the existing mean
and source identities. The degree-one mean is treated explicitly; the mean formula
starts at degree two. -/

section
open QuietDecay CycleComparison.Lift
variable {ι : Type} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {o : Orders} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}

/-- Both original sequences have the promoted stored orders on their original windows. -/
theorem positive_layer_promoted_sequences (P : Input (ι := ι) (h := h) o CG Cw Cj) :
    IsLiftSequence P.Q (o.entranceSlow + o.D + 2)
      (max (o.k + 1) (o.settingFast + 2)) P.sOld P.s₁ o.N o.H P.Cc ∧
    IsLiftSequence P.Q (o.entranceSlow + o.D + 2)
      (max (o.k + 1) (o.settingFast + 2)) P.sNew P.s₁ o.N o.H P.Cc' := by
  exact ⟨positive_layer_lift_sequence_promote P.setting P.slow_le P.fast_le P.sequence,
    positive_layer_lift_sequence_promote
      (positive_layer_setting_restrict P.setting P.starts (P.new_le.trans (P.interval.trans P.end_le)))
      P.slow_le P.fast_le P.sequence'⟩

/-- The source order is covered by the promoted fast reserve even at the smallest orders. -/
theorem positive_layer_source_order (o : Orders) :
    o.D ≤ max (o.k + 1) (o.settingFast + 2) := by
  have h1 := Nat.le_mul_of_pos_right o.D (by omega : 0 < o.H + 1)
  have h2 := Nat.le_mul_of_pos_right (o.D * (o.H + 1)) o.degree_pos
  dsimp only [Orders.settingFast, Orders.reserve]
  omega

/-- Pointwise classical facts on the quiet interval, for either promoted sequence. -/
theorem positive_layer_quiet_facts (P : Input (ι := ι) (h := h) o CG Cw Cj)
    {Cc : ℕ → ℕ → LiftCoeff ι h} {a : ℝ} (ha : a ≤ P.a)
    (hc : IsLiftSequence P.Q (o.entranceSlow + o.D + 2)
      (max (o.k + 1) (o.settingFast + 2)) a P.s₁ o.N o.H Cc)
    {f : Vec 2 → ∀ i, h i} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {t : ℝ} (ht : t ∈ Set.Icc P.a P.b) :
    QuietFacts P.Q Cc f t o.H := by
  have htI : t ∈ Set.Icc a P.s₁ := ⟨ha.trans ht.1, ht.2.trans P.end_le⟩
  have hc' := hc.isLiftSequenceFrom
  have hqs : 1 ≤ o.slowReserve := by
    dsimp only [Orders.slowReserve, Orders.entranceSlow, Orders.reserve]
    have hsum : 0 < o.N + o.D := by have := o.degree_pos; omega
    have : 0 < 4 * (o.H + 1) * (o.N + o.D) ^ 2 := by positivity
    omega
  refine {
    D_ge := o.source_order
    G_smooth := fun i j => (P.setting.G_smooth t
      ⟨P.starts.trans (P.new_le.trans ht.1), ht.2.trans P.end_le⟩ i j).of_le (by exact_mod_cast hqs)
    drift := fun z k => by rw [P.drift_zero t ht z]; simp
    edge_quiet := fun v u d γ hγ α X z z' => P.independent v u d γ hγ α t ht X z z'
    edge_smooth := fun v u d γ hγ α z =>
      ((P.setting.coeff_smooth v u d γ hγ α t
        ⟨P.starts.trans (P.new_le.trans ht.1), ht.2.trans P.end_le⟩).contDiff_slow z).of_le
        (by exact_mod_cast hqs)
    good := fun hh hhH n => liftApply_goodField_of_seqFrom P.Q hc'
      (by omega) (by have := positive_layer_source_order o; have := o.source_order; omega) hhH n hf htI
    cent := fun hh hhH n hn => liftApply_centField_of_seqFrom P.Q hc'
      (by omega) (positive_layer_source_order o) hhH hn hf htI
    fast0 := ?_ }
  intro hh hhH
  by_cases h0 : hh = 0
  · subst hh
    have he : liftApply 0 (Cc 0 0) (fun _ => f) t = fun X _ => f X :=
      funext fun X => funext fun z => hc.1 f hf t htI X z
    rw [he]
    exact fun _ _ _ => rfl
  · rw [liftApply_eq_zero _ _ 0 t (fun m α X z v u => hc.2.1 hh (by omega) hhH m α t X z v u)]
    exact FastIndep.zero

/-- The quiet mean at degree one, where `quiet_mean_from` is intentionally not stated. -/
theorem positive_layer_quiet_mean_one (P : Input (ι := ι) (h := h) o CG Cw Cj)
    {Cc : ℕ → ℕ → LiftCoeff ι h} {a : ℝ} (ha : a ≤ P.a)
    (hc : IsLiftSequence P.Q (o.entranceSlow + o.D + 2)
      (max (o.k + 1) (o.settingFast + 2)) a P.s₁ o.N o.H Cc)
    {f : Vec 2 → ∀ i, h i} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {t : ℝ} (ht : t ∈ Set.Icc P.a P.b)
    {hh : ℕ} (hhH : hh ≤ o.H) :
    liftMean P.Q Cc (fun _ => f) hh 1 t = quietMean P.Q (fun _ => f) hh 1 t := by
  have facts := positive_layer_quiet_facts P ha hc hf ht
  have htI : t ∈ Set.Icc a P.s₁ := ⟨ha.trans ht.1, ht.2.trans P.end_le⟩
  have hbase : liftApply 0 (Cc 0 0) (fun _ => f) t = fun X _ => f X :=
    funext fun X => funext fun z => hc.1 f hf t htI X z
  have hzero (g : ℕ) (hg : g ≠ 0) (hgH : g ≤ o.H) :
      liftApply 0 (Cc g 0) (fun _ => f) t = 0 :=
    liftApply_eq_zero _ _ 0 t (fun m α X z v u => hc.2.1 g (by omega) hgH m α t X z v u)
  have hB := cellB1_eq_zero_of_fastIndep P.Q.η P.Q.G P.Q.v t facts.drift (facts.fast0 hh hhH)
  funext X
  rw [facts.liftMean_eq hhH (by omega)]
  unfold quietFast quietMean
  simp only [show (1 : ℕ) ≠ 2 by omega, ↓reduceIte, Nat.sub_self, hB]
  by_cases h0 : hh = 0
  · simp [h0]
  · by_cases h1 : hh = 1
    · simp [h1, hbase, show 1 ≤ o.D by have := o.source_order; omega]
    · have hz := hzero (hh - 1) (by omega) (by omega)
      simp [h0, h1, hz, sourceCoeff_zero_input]
end

/-! Subtract the actual quiet sources after identifying their means. All differentiation
is justified at the promoted orders. The degenerate cases are included: degree one and grade zero
retain the homogeneous equation; empty and singleton fibres, identity metric, `D = 2`, zero input,
edgeless data, zero majorant and short windows require no exceptional division. -/

section
open QuietDecay CycleComparison.Lift
variable {ι : Type} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {o : Orders} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}

private theorem good_cellB1_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => G t X i j))
    {F F' : Vec 2 → Vec 2 → E} (hF : GoodField 2 F) (hF' : GoodField 2 F') (X z : Vec 2) :
    cellB1 η G v t (fun X z => F X z - F' X z) X z =
      cellB1 η G v t F X z - cellB1 η G v t F' X z := by
  let Fs : Fin 2 → Vec 2 → Vec 2 → E := fun i => if i = 0 then F else F'
  have hs (i : Fin 2) (_ : i ∈ (Finset.univ : Finset (Fin 2))) : GoodField 2 (Fs i) := by
    dsimp only [Fs]; split <;> assumption
  simpa [Fs, Fin.sum_univ_two, sub_eq_add_neg] using
    cellB1_fsum η G v t hG Finset.univ (fun i : Fin 2 => if i = 0 then 1 else -1) hs X z

private theorem good_cellB2_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => G t X i j))
    {F F' : Vec 2 → Vec 2 → E} (hF : GoodField 2 F) (hF' : GoodField 2 F') (X z : Vec 2) :
    cellB2 η G t (fun X z => F X z - F' X z) X z =
      cellB2 η G t F X z - cellB2 η G t F' X z := by
  let Fs : Fin 2 → Vec 2 → Vec 2 → E := fun i => if i = 0 then F else F'
  have hs (i : Fin 2) (_ : i ∈ (Finset.univ : Finset (Fin 2))) : GoodField 2 (Fs i) := by
    dsimp only [Fs]; split <;> assumption
  simpa [Fs, Fin.sum_univ_two, sub_eq_add_neg] using
    cellB2_fsum η G t hG Finset.univ (fun i : Fin 2 => if i = 0 then 1 else -1) hs X z

private theorem good_sourceCoeff_sub (P : Input (ι := ι) (h := h) o CG Cw Cj)
    {t : ℝ} (ht : t ∈ Set.Icc P.a P.b)
    {F F' : Vec 2 → Vec 2 → ∀ i, h i} (hF : GoodField o.D F) (hF' : GoodField o.D F')
    (n : ℕ) (X z : Vec 2) :
    sourceCoeff P.Q.edge P.Q.η n t (fun X z => F X z - F' X z) X z =
      sourceCoeff P.Q.edge P.Q.η n t F X z - sourceCoeff P.Q.edge P.Q.η n t F' X z := by
  let Fs : Fin 2 → Vec 2 → Vec 2 → ∀ i, h i := fun i => if i = 0 then F else F'
  have hs (i : Fin 2) (_ : i ∈ (Finset.univ : Finset (Fin 2))) : GoodField o.D (Fs i) := by
    dsimp only [Fs]; split <;> assumption
  have hqs : 1 ≤ o.slowReserve := by
    have := P.setting.qs_eq
    have hd := o.source_order
    have hn := o.degree_pos
    have hp : 0 < 4 * (o.H + 1) * (o.N + o.D) ^ 2 := by positivity
    omega
  have hsm : ∀ v u d, ∀ γ ∈ P.Q.edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z) := fun v u d γ hγ α z =>
    ((P.setting.coeff_smooth v u d γ hγ α t
      ⟨P.starts.trans (P.new_le.trans ht.1), ht.2.trans P.end_le⟩).contDiff_slow z).of_le
      (by exact_mod_cast hqs)
  simpa [Fs, Fin.sum_univ_two, sub_eq_add_neg] using
    sourceCoeff_fsum P.Q.edge (by have := o.source_order; omega) P.Q.η t
      (fun v u d γ hγ α X z z' => P.independent v u d γ hγ α t ht X z z') hsm
      Finset.univ (fun i : Fin 2 => if i = 0 then 1 else -1) hs n X z

/-- The uncentered recursion source is linear in the coefficient difference at a quiet time. -/
theorem positive_layer_liftA_sub (P : Input (ι := ι) (h := h) o CG Cw Cj)
    {f : Vec 2 → ∀ i, h i} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {t : ℝ} (ht : t ∈ Set.Icc P.a P.b) {hh : ℕ} (hhH : hh ≤ o.H) (n : ℕ) (X z : Vec 2) :
    liftA P.Q (liftDiff P.Cc P.Cc') (fun _ => f) hh n t X z =
      liftA P.Q P.Cc (fun _ => f) hh n t X z - liftA P.Q P.Cc' (fun _ => f) hh n t X z := by
  obtain ⟨hC, hC'⟩ := positive_layer_promoted_sequences P
  have htOld : t ∈ Set.Icc P.sOld P.s₁ :=
    ⟨P.starts.trans (P.new_le.trans ht.1), ht.2.trans P.end_le⟩
  have htNew : t ∈ Set.Icc P.sNew P.s₁ := ⟨P.new_le.trans ht.1, ht.2.trans P.end_le⟩
  have hg (p : ℕ) (hp : p ≤ o.H) (j : ℕ) :
      GoodField o.D (liftApply j (P.Cc p j) (fun _ => f) t) :=
    liftApply_goodField_of_seqFrom P.Q hC.isLiftSequenceFrom (by omega)
      (positive_layer_source_order o) hp j hf htOld
  have hg' (p : ℕ) (hp : p ≤ o.H) (j : ℕ) :
      GoodField o.D (liftApply j (P.Cc' p j) (fun _ => f) t) :=
    liftApply_goodField_of_seqFrom P.Q hC'.isLiftSequenceFrom (by omega)
      (positive_layer_source_order o) hp j hf htNew
  have facts := positive_layer_quiet_facts P (P.starts.trans P.new_le) hC hf ht
  have he (p j : ℕ) : liftApply j (liftDiff P.Cc P.Cc' p j) (fun _ => f) t =
      fun X z => liftApply j (P.Cc p j) (fun _ => f) t X z -
        liftApply j (P.Cc' p j) (fun _ => f) t X z :=
    congrFun (liftApply_coefficient_sub j (P.Cc p j) (P.Cc' p j) (fun _ => f)) t
  unfold liftA
  simp only [he]
  rw [good_cellB1_sub _ _ _ _ facts.G_smooth
    ((hg hh hhH (n - 1)).mono o.source_order) ((hg' hh hhH (n - 1)).mono o.source_order)]
  have hb := good_cellB2_sub P.Q.η P.Q.G t facts.G_smooth
    ((hg hh hhH (n - 2)).mono o.source_order) ((hg' hh hhH (n - 2)).mono o.source_order) X z
  by_cases h0 : hh = 0
  · simp only [h0, ↓reduceIte, sub_zero] at hb ⊢
    by_cases hn : 2 ≤ n
    · simp only [hn, ↓reduceIte, hb]; abel
    · simp only [hn, ↓reduceIte]; abel
  · simp only [h0, ↓reduceIte]
    have hs := fun j => good_sourceCoeff_sub P ht
      (hg (hh - 1) (by omega) (n - j)) (hg' (hh - 1) (by omega) (n - j)) j X z
    simp only [hs, Finset.sum_sub_distrib]
    by_cases hn : 2 ≤ n
    · simp only [hn, ↓reduceIte, hb]; abel
    · simp only [hn, ↓reduceIte]; abel

/-- Common quiet means remove the forcing from the difference of the centered sources. -/
theorem positive_layer_source_sub_of_means (P : Input (ι := ι) (h := h) o CG Cw Cj)
    {f : Vec 2 → ∀ i, h i} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {t : ℝ} (ht : t ∈ Set.Icc P.a P.b) {hh n : ℕ} (hhH : hh ≤ o.H)
    (hn : 1 ≤ n) (hnN : n ≤ o.N)
    (hm : ∀ p ≤ o.H, ∀ j, 1 ≤ j → j ≤ o.N + o.D →
      liftMean P.Q P.Cc (fun _ => f) p j t = quietMean P.Q (fun _ => f) p j t ∧
      liftMean P.Q P.Cc' (fun _ => f) p j t = quietMean P.Q (fun _ => f) p j t)
    (X z : Vec 2) :
    liftCellSource P.Q P.Cc (fun _ => f) hh n t X z -
      liftCellSource P.Q P.Cc' (fun _ => f) hh n t X z =
        quietDifferenceSource P.Q (liftDiff P.Cc P.Cc') (fun _ => f) hh n t X z := by
  have htop := hm hh hhH n hn (by omega)
  have hsum : (∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (P.Cc p.1 j) (liftMean P.Q P.Cc (fun _ => f) p.2 (n - j)) t X z) -
    (∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (P.Cc' p.1 j) (liftMean P.Q P.Cc' (fun _ => f) p.2 (n - j)) t X z) =
    ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (liftDiff P.Cc P.Cc' p.1 j) (quietMean P.Q (fun _ => f) p.2 (n - j)) t X z := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hj' := Finset.mem_Icc.mp hj
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hm' := hm p.2 (by omega) (n - j) (by omega) (by omega)
    rw [show liftApply j (P.Cc p.1 j) (liftMean P.Q P.Cc (fun _ => f) p.2 (n - j)) t =
        liftApply j (P.Cc p.1 j) (quietMean P.Q (fun _ => f) p.2 (n - j)) t from
      liftApply_input_congr_at_time _ _ _ _ _ hm'.1,
      show liftApply j (P.Cc' p.1 j) (liftMean P.Q P.Cc' (fun _ => f) p.2 (n - j)) t =
        liftApply j (P.Cc' p.1 j) (quietMean P.Q (fun _ => f) p.2 (n - j)) t from
      liftApply_input_congr_at_time _ _ _ _ _ hm'.2]
    exact (congrFun (congrFun (congrFun (liftApply_coefficient_sub j (P.Cc p.1 j)
      (P.Cc' p.1 j) (quietMean P.Q (fun _ => f) p.2 (n - j))) t) X) z).symm
  have hA := positive_layer_liftA_sub P hf ht hhH n X z
  change -(liftA P.Q P.Cc (fun _ => f) hh n t X z - liftMean P.Q P.Cc (fun _ => f) hh n t X) + _ -
      (-(liftA P.Q P.Cc' (fun _ => f) hh n t X z - liftMean P.Q P.Cc' (fun _ => f) hh n t X) + _) =
    -liftA P.Q (liftDiff P.Cc P.Cc') (fun _ => f) hh n t X z + _
  rw [htop.1, htop.2, hA, ← hsum]
  abel
end

/-! The quiet triangular difference source, using the existing quiet mean theorem and
finite-synthesis linearity. Promotion is internal, so original stored orders may be zero.
For `H = 0` this recovers the homogeneous initial layer, and for `Theta = 0` the source
coupling is removed. No decay estimate is assumed. -/

section
open QuietDecay
variable {ι : Type} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {o : Orders} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}

/-- The quiet mean formula, with degree one supplied by the explicit base algebra. -/
theorem positive_layer_quiet_means (P : Input (ι := ι) (h := h) o CG Cw Cj)
    {Cc : ℕ → ℕ → LiftCoeff ι h} {a : ℝ} (ha : a ≤ P.a)
    (hset : IsLiftSetting P.Q P.π a P.s₁ P.e P.ν P.B P.ρ P.E P.ℓ P.dstar P.εc P.lam
      P.par P.V o.H o.N o.entranceSlow o.k o.settingFast o.slowReserve o.fastReserve
      CG Cw Cj P.bb P.Θ)
    (hc : IsLiftSequence P.Q (o.entranceSlow + o.D + 2)
      (max (o.k + 1) (o.settingFast + 2)) a P.s₁ o.N o.H Cc)
    {f : Vec 2 → ∀ i, h i} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {t : ℝ} (ht : t ∈ Set.Icc P.a P.b)
    {hh n : ℕ} (hhH : hh ≤ o.H) (hn : 1 ≤ n) (hnN : n ≤ o.N + o.D) :
    liftMean P.Q Cc (fun _ => f) hh n t = quietMean P.Q (fun _ => f) hh n t := by
  by_cases hn1 : n = 1
  · subst n
    exact positive_layer_quiet_mean_one P ha hc hf ht hhH
  · funext X
    simpa only [quietMean, ite_apply, Pi.zero_apply] using quiet_mean_from o.N o.entranceSlow o.k o.settingFast o.D o.H CG Cw Cj
      (positive_layer_source_order o) P.Q P.π a P.s₁ P.e P.ν P.B P.ρ P.E P.ℓ P.dstar
      P.εc P.lam P.par P.V o.slowReserve o.fastReserve P.bb P.Θ hset Cc hc.isLiftSequenceFrom
      (Set.Icc P.a P.b) (Set.Icc_subset_Icc ha P.end_le)
      ⟨fun t ht z => by simp only [P.drift_zero t ht z, smul_zero], P.independent⟩
      f hf hh hhH n (by omega) hnN t ht X

/-- No external forcing remains in the quiet difference at any retained grade and degree. -/
theorem quiet_triangular_source (o : Orders) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    QuietTriangularSourceStatement o CG Cw Cj := by
  intro ι _ h _ _ _ _ P
  obtain ⟨hc, hc'⟩ := positive_layer_promoted_sequences P
  have hs := positive_layer_setting_restrict P.setting P.starts
    (P.new_le.trans (P.interval.trans P.end_le))
  intro hh hhH n hn hnN f hf t ht
  have hm (p : ℕ) (hp : p ≤ o.H) (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ o.N + o.D) :
      liftMean P.Q P.Cc (fun _ => f) p j t = quietMean P.Q (fun _ => f) p j t ∧
      liftMean P.Q P.Cc' (fun _ => f) p j t = quietMean P.Q (fun _ => f) p j t :=
    ⟨positive_layer_quiet_means P (P.starts.trans P.new_le) P.setting hc hf ht hp hj hjN,
      positive_layer_quiet_means P P.new_le hs hc' hf ht hp hj hjN⟩
  exact ⟨hm hh hhH n hn (by omega), positive_layer_source_sub_of_means P hf ht hhH hn hnN hm⟩
end

end AVRegularity.Construction.Preservation.PositiveLayer
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.PositiveLayer

/-! Normalize the slow scale for the quiet decay corollary, without a loss at entrance.
The proof does not divide by any coefficient bound.
-/

private theorem ofReal_mul_pow_le {x lam : ℝ} (hlam : 0 ≤ lam) (h1 : lam ≤ 1) (r : ℕ) :
    ENNReal.ofReal (x * lam ^ r) ≤ ENNReal.ofReal x := by
  by_cases hx : 0 ≤ x
  · exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hx (pow_le_one₀ hlam h1))
  · have hxp : x * lam ^ r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hx)
      (pow_nonneg hlam r)
    simp only [ENNReal.ofReal_eq_zero.mpr hxp, zero_le]

variable {ι : Type} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {o : Orders} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}

/-- Auxiliary reserve, with k0=0 and L0=L+2 in the theorem. -/
def Orders.cellFastReserve (o : Orders) : ℕ :=
  max o.reserve o.entranceFast + o.H * o.D + 2 * o.N + 2 * o.D

omit [∀ i, CompleteSpace (h i)] in
/-- The given setting supplies the quiet-decay setting at E=rho and lambda=1.
Only reserved orders are lowered; data and all envelope constants stay the same. -/
theorem positive_layer_auxiliary_setting (P : Input (ι := ι) (h := h) o CG Cw Cj) :
    IsLiftSetting P.Q P.π P.a P.b P.e P.ν P.B P.ρ P.ρ P.ℓ P.dstar P.εc 1
      P.par P.V o.H o.N o.entranceSlow o.reserve o.settingFast
      o.slowReserve o.cellFastReserve CG Cw Cj P.bb P.Θ := by
  have hI : Set.Icc P.a P.b ⊆ Set.Icc P.sOld P.s₁ :=
    Set.Icc_subset_Icc (P.starts.trans P.new_le) P.end_le
  have hset := positive_layer_setting_restrict P.setting (P.starts.trans P.new_le)
    (P.interval.trans P.end_le)
  have hlam : 0 ≤ P.lam := by
    rw [P.setting.lam_eq]
    exact (div_pos P.setting.ρ_pos P.setting.E_pos).le
  have hfast : o.cellFastReserve ≤ o.fastReserve := by
    dsimp only [Orders.cellFastReserve, Orders.fastReserve, Orders.entranceFast]
    omega
  refine { hset with
    window := P.interval
    E_pos := P.setting.ρ_pos
    lam_eq := (div_self P.setting.ρ_pos.ne').symm
    lam_le := le_rfl
    qf_eq := by
      simp only [Orders.cellFastReserve, Orders.settingFast, Orders.entranceFast, Nat.add_assoc]
    G_smooth := fun t ht => P.setting.G_smooth t (hI ht)
    G_ellip := fun t ht => P.setting.G_ellip t (hI ht)
    G_jets := ?_
    V_smooth := fun t ht => (P.setting.V_smooth t (hI ht)).of_le (by exact_mod_cast hfast)
    V_per := fun t ht => P.setting.V_per t (hI ht)
    V_mean := fun t ht => P.setting.V_mean t (hI ht)
    w_jets := ?_
    transverse := fun v u d γ hγ α t ht => P.setting.transverse v u d γ hγ α t (hI ht)
    coeff_smooth := fun v u d γ hγ α t ht =>
      (P.setting.coeff_smooth v u d γ hγ α t (hI ht)).mono le_rfl hfast
    envelope := { P.setting.envelope with jets := ?_ } }
  · intro r hr
    have htime : (⨆ t ∈ Set.Icc P.a P.b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun X' => P.Q.G t X') X‖ₑ) ≤
        ⨆ t ∈ Set.Icc P.sOld P.s₁, ⨆ X : Vec 2,
          ‖iteratedFDeriv ℝ r (fun X' => P.Q.G t X') X‖ₑ :=
      iSup₂_le fun t ht => le_iSup₂_of_le t (hI ht) le_rfl
    simpa only [one_pow, mul_one] using
      htime.trans ((P.setting.G_jets r hr).trans (ofReal_mul_pow_le hlam P.setting.lam_le r))
  · intro r hr
    refine le_trans ?_ (P.setting.w_jets r (hr.trans hfast))
    exact iSup₂_le fun t ht => le_iSup₂_of_le t (hI ht) le_rfl
  · intro v u r hr q hq
    have hsub := P.setting.envelope.jets v u r hr q (hq.trans hfast)
    have hm : ENNReal.ofReal (Cj r q * P.lam ^ r * P.bb v u) ≤
        ENNReal.ofReal (Cj r q * 1 ^ r * P.bb v u) := by
      simpa only [one_pow, mul_one, mul_assoc, mul_left_comm, mul_comm] using
        ofReal_mul_pow_le (x := Cj r q * P.bb v u) hlam P.setting.lam_le r
    refine le_trans ?_ (hsub.trans hm)
    gcongr
    generalize P.Q.edge v u d = xs
    induction xs with
    | nil => exact le_rfl
    | cons γ xs ih =>
      simp only [List.map_cons, List.sum_cons]
      refine add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le) ih
      exact Finset.sum_le_sum fun α _ =>
        iSup₂_le fun t ht => le_iSup₂_of_le t (hI ht) le_rfl

end AVRegularity.Construction.Preservation.PositiveLayer
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.PositiveLayer

/-! Same-order conversion of the actual quiet entrance trace to its Fourier norm.
Positive-degree zero-order constituents vanish, and centeredness discards the
zero Fourier mode. Constants involve only finite word counts and the prescribed orders;
infinite entrance norms need no exception. The entrance is evaluated at the original time a. -/

open CycleComparison.Lift QuietDecay AVenhance.Infra.Torus

private theorem coefficient_weighted_slow_regular
    {ι : Type} [Fintype ι] [DecidableEq ι] {h : ι → Type}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
    {sX sZ : ℕ} (hsZ : 1 ≤ sZ) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    {hh n m p : ℕ} (hhH : hh ≤ H) (hnN : n ≤ N) (hm : m ≤ n) (hp : p ≤ K)
    (α : DerivativeWord2 m) (v u : ι) {t : ℝ} (ht : t ∈ Icc a b)
    (w : Vec 2 → ℝ) (hw : Continuous w) (hwn : ∀ z, ‖w z‖ ≤ 1) :
    ContDiff ℝ (p : ℕ∞) (fun X => ∫ z in AVenhance.unitCube, w z • Cc hh n m α t X z v u) := by
  have data := (setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
    K (by simpa only [Nat.add_assoc] using setting_ambient_output_supported P) hh hhH n (by omega)).coefficient
  have hp' : p ≤ ambientDegreeSlowReserve K (N + D) n := by
    unfold ambientDegreeSlowReserve; omega
  let f := fun X z => Cc hh n m α t X z v u
  have hf := data.box m hm α v u t ht
  apply weighted_cell_coefficient_contDiff p f (fun X => (hf.1 X).continuous)
    (fun z => (boxSmooth_slow_contDiff hf z).of_le (by exact_mod_cast hp'))
    (fun r => (ambientCoefficientScalarBudget K (max k (L + 2)) D H (N + D) N hh n CG Cw Cj *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) * lam ^ (n - m + r)) ?_ w hw hwn
  intro r hr X z
  have hb := data.bound m hm α v u r (hr.trans hp') 0 (Nat.zero_le _) t ht X z
  simpa only [norm_mixed_jet_fast_zero, f] using hb

private theorem coefficient_entrance_term_le
    {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] [∀ i, CompleteSpace (h i)]
    (C : ℕ → ℕ → LiftCoeff ι h) (hh N K L n m p : ℕ)
    (hn : n ∈ Finset.Icc 1 N) (hm : m ∈ Finset.Icc 1 n) (hp : p ≤ K)
    (α : DerivativeWord2 m) (a : ℝ) (v u : ι) :
    (∑' ξ : NZMode, ENNReal.ofReal ((1 + modeLen ξ.1) ^ L) *
        ⨆ X, modeJet (fun Y z => C hh n m α a Y z v u) ξ.1 p X) ≤
      ENNReal.ofReal (K.factorial : ℝ) * layerEntry C hh N K L {a} (some a) v u := by
  classical
  let S := ∑' ξ : NZMode, ENNReal.ofReal ((1 + modeLen ξ.1) ^ L) *
    ⨆ X, modeJet (fun Y z => C hh n m α a Y z v u) ξ.1 p X
  let T := fun (n d : ℕ) (β : DerivativeWord2 d) (j : ℕ) =>
    ENNReal.ofReal ((j.factorial : ℝ)⁻¹) * ∑' ξ : NZMode,
      ENNReal.ofReal ((1 + modeLen ξ.1) ^ L) *
        ⨆ X, modeJet (fun Y z => C hh n d β a Y z v u) ξ.1 j X
  have hterm : ENNReal.ofReal ((p.factorial : ℝ)⁻¹) * S ≤
      layerEntry C hh N K L {a} (some a) v u := by
    have hj : T n m α p ≤ ∑ j ∈ Finset.range (K + 1), T n m α j :=
      Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_range.mpr (by omega))
    have hα : (∑ j ∈ Finset.range (K + 1), T n m α j) ≤
        ∑ β : DerivativeWord2 m, ∑ j ∈ Finset.range (K + 1), T n m β j :=
      Finset.single_le_sum (f := fun β : DerivativeWord2 m =>
        ∑ j ∈ Finset.range (K + 1), T n m β j) (fun _ _ => zero_le) (Finset.mem_univ α)
    have hd : (∑ β : DerivativeWord2 m, ∑ j ∈ Finset.range (K + 1), T n m β j) ≤
        ∑ d ∈ Finset.Icc 1 n, ∑ β : DerivativeWord2 d,
          ∑ j ∈ Finset.range (K + 1), T n d β j :=
      Finset.single_le_sum (f := fun d => ∑ β : DerivativeWord2 d,
        ∑ j ∈ Finset.range (K + 1), T n d β j) (fun _ _ => zero_le) hm
    have hlayer : (∑ d ∈ Finset.Icc 1 n, ∑ β : DerivativeWord2 d,
        ∑ j ∈ Finset.range (K + 1), T n d β j) ≤
        ∑ nn ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 nn, ∑ β : DerivativeWord2 d,
          ∑ j ∈ Finset.range (K + 1), T nn d β j :=
      Finset.single_le_sum (f := fun nn => ∑ d ∈ Finset.Icc 1 nn,
        ∑ β : DerivativeWord2 d, ∑ j ∈ Finset.range (K + 1), T nn d β j) (fun _ _ => zero_le) hn
    exact hj.trans (hα.trans (hd.trans hlayer))
  have hfac : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (K.factorial : ℝ) *
      ENNReal.ofReal ((p.factorial : ℝ)⁻¹) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have hpos : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
    have hle : (p.factorial : ℝ) ≤ K.factorial := by exact_mod_cast Nat.factorial_le hp
    have hnum : 1 ≤ (K.factorial : ℝ) * (p.factorial : ℝ)⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ hpos).mpr (by simpa only [one_mul] using hle)
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hnum
  calc
    S ≤ (ENNReal.ofReal (K.factorial : ℝ) * ENNReal.ofReal ((p.factorial : ℝ)⁻¹)) * S :=
      le_mul_of_one_le_left zero_le hfac
    _ = ENNReal.ofReal (K.factorial : ℝ) * (ENNReal.ofReal ((p.factorial : ℝ)⁻¹) * S) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hterm zero_le

variable {ι : Type} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {o : Orders} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}

/-- The actual Fourier entrance term bounds any mixed cell trace of a retained constituent. -/
theorem positive_layer_coefficient_entrance_bound
    (P : Input (ι := ι) (h := h) o CG Cw Cj) {hh n m p q : ℕ}
    (hhH : hh ≤ o.H) (hn1 : 1 ≤ n) (hnN : n ≤ o.N) (hm : m ≤ n)
    (hp : p ≤ o.entranceSlow) (hq : q ≤ o.entranceFast)
    (α : DerivativeWord2 m) (v u : ι) :
    mixedCellL2Jet {P.a} p q (fun t X z => quietLiftDiff P.Cc P.Cc' hh n m α t X z v u) ≤
      ENNReal.ofReal (((1 + 2 * Real.pi) ^ o.entranceFast) * (o.entranceSlow.factorial : ℝ)) *
        layerEntry (liftDiff P.Cc P.Cc') hh o.N o.entranceSlow o.entranceFast {P.a} (some P.a) v u := by
  classical
  let : ∀ i, MeasurableSpace (h i) := fun _ => borel _
  let : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
  obtain ⟨hc, hc'⟩ := positive_layer_promoted_sequences P
  have ha : P.a ∈ Icc P.sOld P.s₁ :=
    ⟨P.starts.trans P.new_le, P.interval.trans P.end_le⟩
  have ha' : P.a ∈ Icc P.sNew P.s₁ := ⟨P.new_le, P.interval.trans P.end_le⟩
  have Ps := positive_layer_setting_restrict P.setting P.starts
    (P.new_le.trans (P.interval.trans P.end_le))
  let f := fun X z => liftDiff P.Cc P.Cc' hh n m α P.a X z v u
  have hreg := (hc.2.2.2.2.2.1 hh hhH n m α v u P.a ha).1
  have hreg' := (hc'.2.2.2.2.2.1 hh hhH n m α v u P.a ha').1
  have hbox : IsBoxSmooth p q f := (hreg.sub hreg').mono (by omega)
    (by
      have hmax := le_max_right (o.k + 1) (o.settingFast + 2)
      dsimp only [Orders.settingFast, Orders.entranceFast] at hmax hq ⊢
      omega)
  have hper : ∀ X, AVenhance.IsZ2Periodic (f X) := by
    intro X a z
    exact congrArg₂ (fun A B => A - B)
      ((hc.2.2.2.2.2.1 hh hhH n m α v u P.a ha).2 X a z)
      ((hc'.2.2.2.2.2.1 hh hhH n m α v u P.a ha').2 X a z)
  have htime : mixedCellL2Jet {P.a} p q
      (fun t X z => quietLiftDiff P.Cc P.Cc' hh n m α t X z v u) =
      mixedCellL2Jet {P.a} p q (fun _ => f) := by
    unfold mixedCellL2Jet
    apply iSup_congr fun t => iSup_congr fun ht => ?_
    have he : t = P.a := Set.mem_singleton_iff.mp ht
    subst t
    simp only [quietLiftDiff, show n ≠ 0 by omega, ↓reduceIte]
    rfl
  rw [htime]
  by_cases hm0 : m = 0
  · subst m
    have hf0 : f = fun _ _ => 0 := by
      funext X z
      dsimp only [f, liftDiff]
      rw [liftSequence_zero_order_coefficient_zero P.setting _ _ P.Cc hc hh hhH n hn1 α
        P.a ha X z v u,
        liftSequence_zero_order_coefficient_zero Ps _ _ P.Cc' hc' hh hhH n hn1 α
        P.a ha' X z v u, sub_self]
    rw [hf0]
    simp only [mixedCellL2Jet, orderedDerivative_const_zero]
    simp
  have hmean (X : Vec 2) : fieldCellMean (f X) = 0 := by
    dsimp only [f, liftDiff]
    rw [fieldCellMean_sub (hreg.1 X).continuous (hreg'.1 X).continuous]
    have hmeanC (C : ℕ → ℕ → LiftCoeff ι h) (s : ℝ)
        (hseq : IsLiftSequence P.Q (o.entranceSlow + o.D + 2)
          (max (o.k + 1) (o.settingFast + 2)) s P.s₁ o.N o.H C)
        (ht : P.a ∈ Icc s P.s₁) :
        fieldCellMean (fun z => C hh n m α P.a X z v u) = 0 := by
      apply ContinuousLinearMap.ext
      intro η
      have he := fieldCellMean_clm (ContinuousLinearMap.apply ℝ (h v) η)
        ((hseq.2.2.2.2.2.1 hh hhH n m α v u P.a ht).1.1 X).continuous
      change fieldCellMean (fun z => C hh n m α P.a X z v u η) =
        (fieldCellMean (fun z => C hh n m α P.a X z v u)) η at he
      rw [← he]
      exact liftSequence_coefficient_applied_mean_zero P.Q _ _ s P.s₁ o.N o.H C hseq
        hh n m hhH hn1 hnN hm α P.a ht X v u η
    rw [hmeanC P.Cc P.sOld hc ha, hmeanC P.Cc' P.sNew hc' ha', sub_self]
  have hw (w : Vec 2 → ℝ) (hw : Continuous w) (hwn : ∀ z, ‖w z‖ ≤ 1) :
      ContDiff ℝ (p : ℕ∞) (fun X => ∫ z in AVenhance.unitCube, w z • f X z) := by
    have h0 := coefficient_weighted_slow_regular P.setting (by omega) hc hhH hnN hm hp α v u ha w hw hwn
    have h1 := coefficient_weighted_slow_regular Ps (by omega) hc' hhH hnN hm hp α v u ha' w hw hwn
    have he : (fun X => ∫ z in AVenhance.unitCube, w z • f X z) =
        fun X => (∫ z in AVenhance.unitCube, w z • P.Cc hh n m α P.a X z v u) -
          ∫ z in AVenhance.unitCube, w z • P.Cc' hh n m α P.a X z v u := by
      funext X
      dsimp only [f, liftDiff]
      simp_rw [smul_sub]
      exact integral_sub
        ((Calculus.continuous_integrableOn_unitCell (hw.smul (hreg.1 X).continuous)).congr_set_ae unitCell_ae_eq_unitCube.symm)
        ((Calculus.continuous_integrableOn_unitCell (hw.smul (hreg'.1 X).continuous)).congr_set_ae unitCell_ae_eq_unitCube.symm)
    rw [he]
    exact h0.sub h1
  have hcFourier ξ := hw (fun z => Real.cos (modePhase ξ z)) (by unfold modePhase; fun_prop)
    (fun z => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (modePhase ξ z))
  have hsFourier ξ := hw (fun z => Real.sin (modePhase ξ z)) (by unfold modePhase; fun_prop)
    (fun z => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (modePhase ξ z))
  refine (positive_layer_entrance_mixed_bound hq hbox hper hmean hcFourier hsFourier P.a).trans ?_
  rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ zero_le
  exact coefficient_entrance_term_le (liftDiff P.Cc P.Cc') hh o.N o.entranceSlow
    o.entranceFast n m p (Finset.mem_Icc.mpr ⟨hn1, hnN⟩)
    (Finset.mem_Icc.mpr ⟨by omega, hm⟩) hp α P.a v u

/-- A finite count of the mixed entrance words, fixed before the component spaces. -/
def Orders.entranceTraceCount (o : Orders) : ℝ :=
  ∑ m ∈ Finset.range (o.N + 1), ∑ _p ∈ Finset.range (o.entranceSlow + 1),
    ∑ _q ∈ Finset.range (o.entranceFast + 1), ∑ _α : DerivativeWord2 m, (1 : ℝ)

/-- The final Fourier entrance conversion, including every mixed trace used by the
proved quiet-decay recursion. No stored regularity floor is introduced. -/
theorem positive_layer_cell_entrance_comparison (o : Orders) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) : CellEntranceComparisonStatement o CG Cw Cj := by
  classical
  let C₀ : ℝ := (1 + 2 * Real.pi) ^ o.entranceFast * (o.entranceSlow.factorial : ℝ)
  let Ct : ℝ := o.entranceTraceCount * C₀ + 1
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hcount : 0 ≤ o.entranceTraceCount := by unfold Orders.entranceTraceCount; positivity
  have hCt : 1 ≤ Ct := by dsimp only [Ct]; linarith only [mul_nonneg hcount hC₀]
  have hecount : ENNReal.ofReal o.entranceTraceCount =
      ∑ m ∈ Finset.range (o.N + 1), ∑ _p ∈ Finset.range (o.entranceSlow + 1),
        ∑ _q ∈ Finset.range (o.entranceFast + 1), ∑ _α : DerivativeWord2 m, (1 : ℝ≥0∞) := by
    unfold Orders.entranceTraceCount
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ENNReal.ofReal_natCast]
  refine ⟨Ct, hCt, ?_⟩
  intro ι _ h _ _ _ _ P hh hhH n
  have hentry (v u : ι) : cellTrace P hh n v u ≤ ENNReal.ofReal Ct *
      layerEntry (liftDiff P.Cc P.Cc') hh o.N o.entranceSlow o.entranceFast {P.a} (some P.a) v u := by
    unfold cellTrace traceQ
    split_ifs with hn
    · let B := ENNReal.ofReal C₀ *
        layerEntry (liftDiff P.Cc P.Cc') hh o.N o.entranceSlow o.entranceFast {P.a} (some P.a) v u
      have hbound : traceT (quietLiftDiff P.Cc P.Cc') P.a o.entranceSlow o.entranceFast hh n v u ≤
          ∑ m ∈ Finset.range (n + 1), ∑ _p ∈ Finset.range (o.entranceSlow + 1),
            ∑ _q ∈ Finset.range (o.entranceFast + 1), ∑ _α : DerivativeWord2 m, B := by
        unfold traceT
        refine Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun p hp =>
          Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun α _ => ?_
        exact positive_layer_coefficient_entrance_bound P hhH hn.1 hn.2
          (by have := Finset.mem_range.mp hm; omega)
          (by have := Finset.mem_range.mp hp; omega)
          (by have := Finset.mem_range.mp hq; omega) α v u
      refine hbound.trans ((Finset.sum_le_sum_of_subset
        (Finset.range_mono (Nat.add_le_add_right hn.2 1))).trans ?_)
      calc
        _ = ENNReal.ofReal o.entranceTraceCount * B := by
          rw [hecount]
          simp_rw [Finset.sum_mul, one_mul]
        _ = (ENNReal.ofReal o.entranceTraceCount * ENNReal.ofReal C₀) *
            layerEntry (liftDiff P.Cc P.Cc') hh o.N o.entranceSlow o.entranceFast {P.a} (some P.a) v u :=
          (mul_assoc _ _ _).symm
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ zero_le
          rw [← ENNReal.ofReal_mul hcount]
          apply ENNReal.ofReal_le_ofReal
          exact le_add_of_nonneg_right zero_le_one
    · exact zero_le
  exact (schurSums_mono' P.π hentry).trans (schurSums_const_mul P.π _ _)

end AVRegularity.Construction.Preservation.PositiveLayer
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.PositiveLayer

/-! The homogeneous quiet difference retains identity at degree zero and its actual
positive-degree entrance traces. The difference is formed by
linear subtraction. No old entrance is reset to zero.
-/

open QuietDecay CycleComparison.Lift
variable {ι : Type} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {o : Orders} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}

omit [∀ i, CompleteSpace (h i)] in
private theorem diff_apply (P : Input (ι := ι) (h := h) o CG Cw Cj)
    (hh n : ℕ) (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (hn : n ≠ 0) :
    liftApply n (quietLiftDiff P.Cc P.Cc' hh n) f t =
      fun X z => liftApply n (P.Cc hh n) f t X z - liftApply n (P.Cc' hh n) f t X z := by
  simp only [quietLiftDiff, hn, ↓reduceIte]
  exact congrFun (liftApply_coefficient_sub n (P.Cc hh n) (P.Cc' hh n) f) t

/-- Classical centering and regularity of the homogeneous difference at a quiet time. -/
theorem quiet_lift_diff_facts (P : Input (ι := ι) (h := h) o CG Cw Cj)
    {f : Vec 2 → ∀ i, h i} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {t : ℝ} (ht : t ∈ Set.Icc P.a P.b) :
    QuietFacts P.Q (quietLiftDiff P.Cc P.Cc') f t o.H := by
  obtain ⟨hc, hc'⟩ := positive_layer_promoted_sequences P
  have h1 := positive_layer_quiet_facts P (P.starts.trans P.new_le) hc hf ht
  have h2 := positive_layer_quiet_facts P P.new_le hc' hf ht
  refine { h1 with good := ?_, cent := ?_, fast0 := ?_ }
  · intro hh hhH n
    by_cases hn : n = 0
    · simpa only [quietLiftDiff, hn, ↓reduceIte] using h1.good hh hhH 0
    · rw [diff_apply P hh n (fun _ => f) t hn]
      simpa only [sub_eq_add_neg] using (h1.good hh hhH n).add (h2.good hh hhH n).neg
  · intro hh hhH n hn
    by_cases hn0 : n = 0
    · simpa only [quietLiftDiff, hn0, ↓reduceIte] using h1.cent hh hhH 0 (by omega)
    · rw [diff_apply P hh n (fun _ => f) t hn0]
      simpa only [sub_eq_add_neg] using
        (h1.cent hh hhH n (Or.inl (by omega))).add (h2.cent hh hhH n (Or.inl (by omega))).neg
  · intro hh hhH
    simpa only [quietLiftDiff, ↓reduceIte] using h1.fast0 hh hhH

/-- The hybrid difference has the same explicit quiet means as each original lift.
This statement uses only centering and the identity, not the difference PDE. -/
theorem quiet_lift_diff_mean (P : Input (ι := ι) (h := h) o CG Cw Cj)
    {f : Vec 2 → ∀ i, h i} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {t : ℝ} (ht : t ∈ Set.Icc P.a P.b) {hh n : ℕ} (hhH : hh ≤ o.H) (hn : 1 ≤ n) :
    liftMean P.Q (quietLiftDiff P.Cc P.Cc') (fun _ => f) hh n t =
      quietMean P.Q (fun _ => f) hh n t := by
  have facts := quiet_lift_diff_facts P hf ht
  have hbase : liftApply 0 (quietLiftDiff P.Cc P.Cc' 0 0) (fun _ => f) t = fun X _ => f X :=
    funext fun X => funext fun z => P.sequence.1 f hf t
      ⟨P.starts.trans (P.new_le.trans ht.1), ht.2.trans P.end_le⟩ X z
  have hzero (g : ℕ) (hg : g ≠ 0) (hgH : g ≤ o.H) :
      liftApply 0 (quietLiftDiff P.Cc P.Cc' g 0) (fun _ => f) t = 0 := by
    simp only [quietLiftDiff, ↓reduceIte]
    exact liftApply_eq_zero _ _ 0 t
      (fun m α X z v u => P.sequence.2.1 g (by omega) hgH m α t X z v u)
  have hB1 : ∀ X z, (if n = 1 then
      cellB1 P.Q.η P.Q.G P.Q.v t
        (liftApply (n - 1) (quietLiftDiff P.Cc P.Cc' hh (n - 1)) (fun _ => f) t) X z
      else 0) = 0 := by
    intro X z
    split_ifs with hn1
    · subst n
      exact congrFun (congrFun (cellB1_eq_zero_of_fastIndep P.Q.η P.Q.G P.Q.v t
        facts.drift (facts.fast0 hh hhH)) X) z
    · rfl
  have hB2 : ∀ X z, (if n = 2 then
      cellB2 P.Q.η P.Q.G t
        (liftApply (n - 2) (quietLiftDiff P.Cc P.Cc' hh (n - 2)) (fun _ => f) t) X z
      else 0) = (if hh = 0 ∧ n = 2 then cellB2 P.Q.η P.Q.G t (fun X _ => f X) X z else 0) := by
    intro X z
    by_cases hn2 : n = 2
    · subst n
      simp only [Nat.sub_self, ↓reduceIte, and_true]
      by_cases hh0 : hh = 0
      · subst hh
        simp only [hbase, ↓reduceIte]
      · rw [hzero hh hh0 hhH]
        simp only [hh0, ↓reduceIte]
        exact congrFun (congrFun (cellB2_const P.Q.η P.Q.G t (0 : ∀ i, h i)) X) z
    · simp only [hn2, ↓reduceIte, and_false]
  have hS : ∀ X z, (if hh ≠ 0 ∧ n ≤ o.D then sourceCoeff P.Q.edge P.Q.η n t
      (liftApply (n - n) (quietLiftDiff P.Cc P.Cc' (hh - 1) (n - n)) (fun _ => f) t) X z else 0) =
      (if hh = 1 then sourceCoeff P.Q.edge P.Q.η n t (fun X _ => f X) X z else 0) := by
    intro X z
    simp only [Nat.sub_self]
    by_cases hh1 : hh = 1
    · subst hh
      simp only [Nat.sub_self, hbase, ↓reduceIte, ne_eq, one_ne_zero, not_false_eq_true, true_and]
      by_cases hnD : n ≤ o.D
      · simp only [hnD, ↓reduceIte]
      · simp only [hnD, ↓reduceIte]
        exact (sourceCoeff_eq_zero_of_gt P.Q.edge (by have := o.source_order; omega)
          P.Q.η t facts.edge_quiet facts.edge_smooth hf (by omega) X z).symm
    · simp only [hh1, ↓reduceIte]
      split_ifs with hh0
      · rw [hzero (hh - 1) (by omega) (by omega)]
        exact congrFun (congrFun (sourceCoeff_zero_input P.Q.edge P.Q.η n t) X) z
      · rfl
  funext X
  rw [facts.liftMean_eq hhH hn]
  change (if n = 1 then _ else 0) + (if n = 2 then _ else 0) -
    (if hh ≠ 0 ∧ n ≤ o.D then _ else 0) = _
  rw [hB1, hB2, hS, zero_add]
  simp only [quietMean, ite_apply, Pi.zero_apply]
  by_cases hh0 : hh = 0
  · simp [hh0]
  · by_cases hh1 : hh = 1
    · simp [hh1]
    · simp only [hh0, hh1, ↓reduceIte, false_and, sub_zero]


/-- Keeping identity at degree zero does not change the homogeneous quiet source. -/
theorem quiet_lift_diff_source (P : Input (ι := ι) (h := h) o CG Cw Cj)
    {f : Vec 2 → ∀ i, h i} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {t : ℝ} (ht : t ∈ Set.Icc P.a P.b) {hh n : ℕ}
    (hhH : hh ≤ o.H) (hn : 1 ≤ n) :
    liftCellSource P.Q (quietLiftDiff P.Cc P.Cc') (fun _ => f) hh n t =
      quietDifferenceSource P.Q (liftDiff P.Cc P.Cc') (fun _ => f) hh n t := by
  have facts := quiet_lift_diff_facts P hf ht
  have hmean (p j : ℕ) (hp : p ≤ o.H) (hj : 1 ≤ j) :
      liftMean P.Q (quietLiftDiff P.Cc P.Cc') (fun _ => f) p j t =
        fun X => quietMeanOp P.Q f p j t X := by
    rw [quiet_lift_diff_mean P hf ht hp hj]
    funext X
    simp only [quietMean, quietMeanOp]
    split_ifs <;> rfl
  have hzero (p : ℕ) (hp : p ≤ o.H) :
      liftApply 0 (liftDiff P.Cc P.Cc' p 0) (fun _ => f) t = 0 := by
    change liftApply 0 (fun m α t X z v u =>
      P.Cc p 0 m α t X z v u - P.Cc' p 0 m α t X z v u) (fun _ => f) t = 0
    rw [liftApply_coefficient_sub]
    funext X z
    change liftApply 0 (P.Cc p 0) (fun _ => f) t X z -
      liftApply 0 (P.Cc' p 0) (fun _ => f) t X z = 0
    by_cases hp0 : p = 0
    · subst p
      rw [P.sequence.1 f hf t ⟨P.starts.trans (P.new_le.trans ht.1), ht.2.trans P.end_le⟩,
        P.sequence'.1 f hf t ⟨P.new_le.trans ht.1, ht.2.trans P.end_le⟩]
      exact sub_self _
    · rw [liftApply_eq_zero _ _ 0 t
        (fun m α X z v u => P.sequence.2.1 p (by omega) hp m α t X z v u),
        liftApply_eq_zero _ _ 0 t
        (fun m α X z v u => P.sequence'.2.1 p (by omega) hp m α t X z v u)]
      exact sub_self _
  have he (p j : ℕ) (hj : j ≠ 0) :
      quietLiftDiff P.Cc P.Cc' p j = liftDiff P.Cc P.Cc' p j := by
    simp only [quietLiftDiff, hj, ↓reduceIte]
  funext X z
  rw [facts.liftCellSource_eq hhH hn (fun j hj p hp X' => by
    have hj' := Finset.mem_Icc.mp hj
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact congrFun (hmean p.2 (n - j) (by omega) (by omega)) X')]
  have h1 : (if 2 ≤ n then cellB1 P.Q.η P.Q.G P.Q.v t
      (liftApply (n - 1) (quietLiftDiff P.Cc P.Cc' hh (n - 1)) (fun _ => f) t) X z else 0) =
      cellB1 P.Q.η P.Q.G P.Q.v t
        (liftApply (n - 1) (liftDiff P.Cc P.Cc' hh (n - 1)) (fun _ => f) t) X z := by
    by_cases hn2 : 2 ≤ n
    · simp only [hn2, ↓reduceIte, he hh (n - 1) (by omega)]
    · have hn1 : n = 1 := by omega
      subst n
      simp only [Nat.sub_self, hzero hh hhH, hn2, ↓reduceIte]
      exact (congrFun (congrFun (cellB1_eq_zero_of_fastIndep P.Q.η P.Q.G P.Q.v t
        facts.drift (FastIndep.zero (E := ∀ i, h i))) X) z).symm
  have h2 : (if 3 ≤ n then cellB2 P.Q.η P.Q.G t
      (liftApply (n - 2) (quietLiftDiff P.Cc P.Cc' hh (n - 2)) (fun _ => f) t) X z else 0) =
      (if 2 ≤ n then cellB2 P.Q.η P.Q.G t
        (liftApply (n - 2) (liftDiff P.Cc P.Cc' hh (n - 2)) (fun _ => f) t) X z else 0) := by
    by_cases hn3 : 3 ≤ n
    · simp only [hn3, show 2 ≤ n by omega, ↓reduceIte, he hh (n - 2) (by omega)]
    · by_cases hn2 : 2 ≤ n
      · have hn' : n = 2 := by omega
        subst n
        simp only [Nat.sub_self, hzero hh hhH, hn3, hn2, ↓reduceIte]
        exact (congrFun (congrFun (cellB2_const P.Q.η P.Q.G t (0 : ∀ i, h i)) X) z).symm
      · simp only [hn3, hn2, ↓reduceIte]
  have hs : (if hh = 0 then 0 else ∑ j ∈ (Finset.range (min o.D n + 1)).filter (· < n),
      sourceCoeff P.Q.edge P.Q.η j t
        (liftApply (n - j) (quietLiftDiff P.Cc P.Cc' (hh - 1) (n - j)) (fun _ => f) t) X z) =
      (if hh = 0 then 0 else ∑ j ∈ Finset.range (min o.D n + 1),
        sourceCoeff P.Q.edge P.Q.η j t
          (liftApply (n - j) (liftDiff P.Cc P.Cc' (hh - 1) (n - j)) (fun _ => f) t) X z) := by
    by_cases hh0 : hh = 0
    · simp only [hh0, ↓reduceIte]
    · simp only [hh0, ↓reduceIte, sum_range_min_split]
      have hz : sourceCoeff P.Q.edge P.Q.η n t
          (liftApply (n - n) (liftDiff P.Cc P.Cc' (hh - 1) (n - n)) (fun _ => f) t) X z = 0 := by
        rw [Nat.sub_self, hzero (hh - 1) (by omega)]
        exact congrFun (congrFun (sourceCoeff_zero_input P.Q.edge P.Q.η n t) X) z
      simp only [hz, ite_self, add_zero]
      exact Finset.sum_congr rfl (fun j hj => by rw [he (hh - 1) (n - j)
        (by have := (Finset.mem_filter.mp hj).2; omega)])
  have hc : (∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (quietLiftDiff P.Cc P.Cc' p.1 j)
        (fun s X' => quietMeanOp P.Q f p.2 (n - j) s X') t X z) =
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
        liftApply j (liftDiff P.Cc P.Cc' p.1 j) (quietMean P.Q (fun _ => f) p.2 (n - j)) t X z := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro p _
    rw [he p.1 j (by have := (Finset.mem_Icc.mp hj).1; omega)]
    congr 4
    funext s X'
    simp only [quietMean, quietMeanOp]
    split_ifs <;> rfl
  change -_ - _ + _ + _ = -(_ + _ - _) + _
  rw [h1, h2, hs, hc]
  abel


/-- The quiet homogeneous difference is a genuine lift sequence from its own entrance.
Identity at degree zero is retained for the quiet-source calculus. -/
theorem quiet_lift_diff_sequence_from (P : Input (ι := ι) (h := h) o CG Cw Cj) :
    IsLiftSequenceFrom P.Q (o.entranceSlow + o.D + 2) o.entranceFast P.a P.b o.N o.H
      (quietLiftDiff P.Cc P.Cc') := by
  obtain ⟨hCo, hCn⟩ := positive_layer_promoted_sequences P
  have hF : o.settingFast + 2 = o.entranceFast := by
    simp only [Orders.settingFast, Orders.entranceFast, Nat.add_assoc]
  have hC := CycleComparison.Reconstruction.isLiftSequence_mono hCo le_rfl (le_max_right _ _)
  have hC' := CycleComparison.Reconstruction.isLiftSequence_mono hCn le_rfl (le_max_right _ _)
  rw [hF] at hC hC'
  have hold : Set.Icc P.a P.b ⊆ Set.Icc P.sOld P.s₁ :=
    Set.Icc_subset_Icc (P.starts.trans P.new_le) P.end_le
  have hnew : Set.Icc P.a P.b ⊆ Set.Icc P.sNew P.s₁ :=
    Set.Icc_subset_Icc P.new_le P.end_le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf t ht X z
    exact hC.1 f hf t (hold ht) X z
  · intro hh hh1 hhH m α t X z v u
    exact hC.2.1 hh hh1 hhH m α t X z v u
  · intro hh hhH n hn m α t X z v u
    have hn0 : n ≠ 0 := by omega
    simp only [quietLiftDiff, hn0, ↓reduceIte, liftDiff,
      hC.2.2.1 hh hhH n hn, hC'.2.2.1 hh hhH n hn, sub_self]
  · intro hh hhH n m hnm α t X z v u
    by_cases hn0 : n = 0
    · subst n
      exact hC.2.2.2.1 hh hhH 0 m hnm α t X z v u
    · simp only [quietLiftDiff, hn0, ↓reduceIte, liftDiff,
        hC.2.2.2.1 hh hhH n m hnm, hC'.2.2.2.1 hh hhH n m hnm, sub_self]
  · intro hh hhH n m α σ
    have h1 := hC.2.2.2.2.1 hh hhH n m α σ
    have h2 := hC'.2.2.2.2.1 hh hhH n m α σ
    by_cases hn0 : n = 0
    · simpa only [quietLiftDiff, hn0, ↓reduceIte] using h1
    · simp only [quietLiftDiff, hn0, ↓reduceIte]
      funext t X z v u
      change P.Cc hh n m (α ∘ σ) t X z v u - P.Cc' hh n m (α ∘ σ) t X z v u =
        P.Cc hh n m α t X z v u - P.Cc' hh n m α t X z v u
      rw [h1, h2]
  · intro hh hhH n m α v u t ht
    have h1 := hC.2.2.2.2.2.1 hh hhH n m α v u t (hold ht)
    have h2 := hC'.2.2.2.2.2.1 hh hhH n m α v u t (hnew ht)
    by_cases hn0 : n = 0
    · simpa only [quietLiftDiff, hn0, ↓reduceIte] using h1
    · simp only [quietLiftDiff, hn0, ↓reduceIte, liftDiff]
      refine ⟨h1.1.sub h2.1, ?_⟩
      intro X k z
      exact congrArg₂ (fun a b => a - b) (h1.2 X k z) (h2.2 X k z)
  · intro hh hhH n hn hnN f hf X
    have hn0 : n ≠ 0 := by omega
    let c : ℝ → Vec 2 → ∀ i, h i := fun t z => liftApply n (P.Cc hh n) (fun _ => f) t X z
    let c' : ℝ → Vec 2 → ∀ i, h i := fun t z => liftApply n (P.Cc' hh n) (fun _ => f) t X z
    have h1 := hC.2.2.2.2.2.2 hh hhH n hn hnN f hf X
    have h2 := hC'.2.2.2.2.2.2 hh hhH n hn hnN f hf X
    have hv : (fun t z => liftApply n (quietLiftDiff P.Cc P.Cc' hh n) (fun _ => f) t X z) =
        fun t z => c t z - c' t z := by
      funext t z
      exact congrFun (congrFun (diff_apply P hh n (fun _ => f) t hn0) X) z
    rw [hv]
    have hfast : ((o.entranceFast : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
      exact_mod_cast (show o.entranceFast ≠ 0 by dsimp [Orders.entranceFast]; omega)
    have hj (ℓ : (∀ i, h i) →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc P.a P.b) :
        (cellJetOfField ℓ c + (-1 : ℝ) • cellJetOfField ℓ c') t =
          cellJetOfField ℓ (fun t z => c t z - c' t z) t :=
      InitialLayer.cellJetOfField_sub ℓ c c' t ((h1.1 t (hold ht)).differentiable hfast)
        ((h2.1 t (hnew ht)).differentiable hfast)
    refine ⟨fun t ht => (h1.1 t (hold ht)).sub (h2.1 t (hnew ht)), fun ℓ => ?_⟩
    have hraw := quiet_difference_equation P hh hhH n hn hnN f hf X ℓ
    have hsol := InitialLayer.cellSolution_congr_jet measurableSet_Icc (hj ℓ) hraw.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply CycleEvolution.cellSolution_source_congr_sections _ _ _ _ _ _ _ ?_ ?_ hsol
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        refine Filter.Eventually.of_forall fun z => ?_
        dsimp only
        rw [(quiet_triangular_source o CG Cw Cj P hh hhH n hn hnN f hf t ht).2 X z]
        rw [congrFun (congrFun (quiet_lift_diff_source P hf ht hhH hn) X) z]
      · exact Filter.Eventually.of_forall fun _ => Filter.Eventually.of_forall fun _ => rfl
    · intro t ht
      unfold cellValue
      rw [← hj ℓ t ht]
      exact hraw.2 t ht
    · refine Filter.Eventually.of_forall fun z => ?_
      rw [AVRegularity.cellValue_cellJetOfField]
      dsimp only
      rw [congrFun (congrFun (diff_apply P hh n (fun _ => f) P.a hn0) X) z]
    · obtain ⟨S1, -, -, E1⟩ := h1.2 ℓ
      obtain ⟨S2, -, -, E2⟩ := h2.2 ℓ
      have S1' := CycleEvolution.cellSolution_restrict hold Set.ordConnected_Icc S1
      have S2' := CycleEvolution.cellSolution_restrict hnew Set.ordConnected_Icc S2
      have hm1 := CycleEvolution.cellRawGradient_aestronglyMeasurable _ _ S1'.2.2.2.1
      have hm2 := CycleEvolution.cellRawGradient_aestronglyMeasurable _ _ S2'.2.2.2.1
      rw [← InitialLayer.cellEnergyNorm_congr_jet measurableSet_Icc (hj ℓ)]
      refine (CycleEvolution.cellEnergyNorm_add _ (cellJetOfField ℓ c)
        ((-1 : ℝ) • cellJetOfField ℓ c') hm1 (hm2.const_smul (-1 : ℝ))).trans_lt ?_
      refine ENNReal.add_lt_top.2 ⟨(InitialLayer.cellEnergyNorm_mono hold _).trans_lt E1, ?_⟩
      refine (CycleEvolution.cellEnergyNorm_smul _ _ _ hm2).trans_lt ?_
      exact ENNReal.mul_lt_top (by simp) ((InitialLayer.cellEnergyNorm_mono hnew _).trans_lt E2)

end AVRegularity.Construction.Preservation.PositiveLayer
end
