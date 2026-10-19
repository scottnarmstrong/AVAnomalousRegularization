-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.CycleJoint.IsPointwiseMolecularEnvelope
import AVRegularity.Proofs.Results.Finite.TraceClosure
import AVRegularity.Proofs.QuietAtlas.QuietPulse
public import AVRegularity.Proofs.ComplexChain.Family
import AVRegularity.Construction.ChildInert.Center
import AVRegularity.Construction.Stream.NextAdmissible

section
/-! Field-group assembly of the natural preparation chart schedule. All constants are chosen
before the construction data, levels, window and family. -/

@[expose] public noncomputable section

universe u v z

open Homogenization AVenhance Set

namespace AVRegularity.CycleJointProofs.ChartSchedule

structure Parameters where
  α : ℝ
  s : ℝ
  q : ℝ
  Λ : ℕ
  CH : ℝ
  alpha_pos : 0 < α
  alpha_lt : α < 1 / 3
  s_pos : 0 < s
  s_lt : s < (1 - α) / 2
  admissible : IsAdmissibleQ α s q
  large : 128 ≤ Λ
  duration_pos : 0 < CH

structure Constants where
  Cpad : ℝ
  Cage : ℝ
  Npad : ℕ
  mStar : ℕ
  pad_nonneg : 0 ≤ Cpad
  age_pos : 0 < Cage

structure Window (B : Parameters) (K : Constants) where
  data : OCData
  alpha_eq : data.α = B.α
  q_eq : data.q = B.q
  lambda_eq : data.Λ = B.Λ
  Mnat : ℕ
  m : ℕ
  level_two : 2 ≤ m
  level_floor : K.mStar ≤ m
  level_top : m ≤ Mnat
  tS : ℝ
  l₀ : ℤ
  P : ℕ
  blocks_pos : 1 ≤ P
  start_lower : ((l₀ : ℝ) - 1 / 2) * ocTauPP B.α B.q B.Λ m ≤ tS
  start_upper : tS < ((l₀ : ℝ) + 1 / 2) * ocTauPP B.α B.q B.Λ m
  end_upper : tS + B.CH * ocTauPP B.α B.q B.Λ m ≤
    ((l₀ : ℝ) + P - 1 / 2) * ocTauPP B.α B.q B.Λ m

def Window.period {B : Parameters} {K : Constants} (w : Window B K) : ℝ :=
  ocTauPP B.α B.q B.Λ w.m

def Window.finish {B : Parameters} {K : Constants} (w : Window B K) : ℝ :=
  w.tS + B.CH * w.period

def Window.padded {B : Parameters} {K : Constants} (w : Window B K) : Set ℝ :=
  preparationPaddedWindow w.tS w.finish K.Cpad w.period

variable {B : Parameters} {K : Constants} (w : Window B K)
  {ι : Type u} {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {Ctx : OddSlot → Type z} (F : ChartedFamily ι h D OddSlot Ctx)

def Natural : Prop := ∀ p, IsNaturalPiece w.data w.Mnat w.m p.val (F.piece p)

def Meets (p : OddSlot) : Prop := ((F.piece p).output ∩ Icc w.tS w.finish).Nonempty

def FiniteReferenceFields : Prop :=
  {p | Meets w F p}.Finite ∧ (w.l₀ : ℝ) * w.period ∈ w.padded

def AvailabilityFields : Prop :=
  (∀ p, Meets w F p → OrdConnected (F.piece p).geometry) ∧
  (∀ p, Meets w F p → (F.piece p).anchor = ((F.piece p).label : ℝ) * w.period) ∧
  (∀ p, Meets w F p → ∀ r ∈ (F.piece p).geometry, ∀ y,
    (F.piece p).material r y = ocChart B.α B.q B.Λ w.m
      (w.data.Φ (w.m - 1)) (w.data.hΦ (w.m - 1)) (F.piece p).label r y)

def PaddedGeometryFields : Prop :=
  ∀ p, Meets w F p → (F.piece p).geometry ⊆ w.padded

def AgeFields : Prop :=
  (∀ p, Meets w F p → ∀ r ∈ (F.piece p).geometry,
    |r - (F.piece p).anchor| ≤ K.Cage * w.period) ∧
  (∀ p, Meets w F p → ∀ r ∈ (F.piece p).geometry,
    |r - (w.l₀ : ℝ) * w.period| ≤ K.Cage * w.period)

def SegmentFields : Prop :=
  (∀ p, Meets w F p → ∀ r ∈ (F.piece p).geometry,
    uIcc (F.piece p).anchor r ⊆ (F.piece p).geometry) ∧
  (∀ p, Meets w F p → ∀ r ∈ (F.piece p).geometry,
    uIcc ((w.l₀ : ℝ) * w.period) r ⊆ w.padded)

def CoverLabelFields : Prop :=
  ∀ p, Meets w F p → (F.piece p).label ∈
    Icc (w.l₀ - (K.Npad : ℤ)) (w.l₀ + (w.P : ℤ) - 1 + (K.Npad : ℤ))

def CoreLabelFields : Prop :=
  ∀ p, ∀ t ∈ (F.piece p).output ∩ Icc w.tS w.finish, ∀ j : ℤ,
    t ∈ Ioo (((j : ℝ) - 1 / 2) * w.period +
        (ocTauP B.α B.q B.Λ w.m - ocTau B.α B.q B.Λ w.m / 24))
      (((j : ℝ) + 1 / 2) * w.period -
        (ocTauP B.α B.q B.Λ w.m - ocTau B.α B.q B.Λ w.m / 24)) →
    (F.piece p).label = j

def FiniteReferenceStatement (B : Parameters) (K : Constants) : Prop :=
  ∀ (w : Window B K) {ι : Type u} {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {Ctx : OddSlot → Type z} (F : ChartedFamily ι h D OddSlot Ctx),
    Natural w F → FiniteReferenceFields w F

def AvailabilityStatement (B : Parameters) (K : Constants) : Prop :=
  ∀ (w : Window B K) {ι : Type u} {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {Ctx : OddSlot → Type z} (F : ChartedFamily ι h D OddSlot Ctx),
    Natural w F → AvailabilityFields w F

def PaddedGeometryStatement (B : Parameters) (K : Constants) : Prop :=
  ∀ (w : Window B K) {ι : Type u} {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {Ctx : OddSlot → Type z} (F : ChartedFamily ι h D OddSlot Ctx),
    Natural w F → PaddedGeometryFields w F

def AgeStatement (B : Parameters) (K : Constants) : Prop :=
  ∀ (w : Window B K) {ι : Type u} {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {Ctx : OddSlot → Type z} (F : ChartedFamily ι h D OddSlot Ctx),
    Natural w F → AgeFields w F

def SegmentStatement (B : Parameters) (K : Constants) : Prop :=
  ∀ (w : Window B K) {ι : Type u} {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {Ctx : OddSlot → Type z} (F : ChartedFamily ι h D OddSlot Ctx),
    Natural w F → SegmentFields w F

def CoverLabelStatement (B : Parameters) (K : Constants) : Prop :=
  ∀ (w : Window B K) {ι : Type u} {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {Ctx : OddSlot → Type z} (F : ChartedFamily ι h D OddSlot Ctx),
    Natural w F → CoverLabelFields w F

def CoreLabelStatement (B : Parameters) (K : Constants) : Prop :=
  ∀ (w : Window B K) {ι : Type u} {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {Ctx : OddSlot → Type z} (F : ChartedFamily ι h D OddSlot Ctx),
    Natural w F → CoreLabelFields w F

def Conclusion (B : Parameters) : Prop :=
    ∃ (Cpad Cage : ℝ) (Npad mStar : ℕ), 0 ≤ Cpad ∧ 0 < Cage ∧
      ∀ (data : OCData), data.α = B.α → data.q = B.q → data.Λ = B.Λ →
      ∀ (Mnat m : ℕ), 2 ≤ m → mStar ≤ m → m ≤ Mnat →
      ∀ (tS : ℝ) (l₀ : ℤ) (P : ℕ), 1 ≤ P →
        ((l₀ : ℝ) - 1 / 2) * ocTauPP B.α B.q B.Λ m ≤ tS →
        tS < ((l₀ : ℝ) + 1 / 2) * ocTauPP B.α B.q B.Λ m →
        tS + B.CH * ocTauPP B.α B.q B.Λ m ≤ ((l₀ : ℝ) + P - 1 / 2) * ocTauPP B.α B.q B.Λ m →
      ∀ {ι : Type u} {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
        {D : ℕ} {Ctx : OddSlot → Type z} (F : ChartedFamily ι h D OddSlot Ctx),
        (∀ p, IsNaturalPiece data Mnat m p.val (F.piece p)) →
        IsPreparationChartSchedule B.α B.q B.Λ m (data.Φ (m - 1)) (data.hΦ (m - 1))
          tS (tS + B.CH * ocTauPP B.α B.q B.Λ m) Cpad Cage Npad l₀ P F

theorem preparation_chart_schedule_of_ingredients (B : Parameters) (K : Constants)
    (hfinite : FiniteReferenceStatement.{u, v, z} B K)
    (havail : AvailabilityStatement.{u, v, z} B K)
    (hgeom : PaddedGeometryStatement.{u, v, z} B K)
    (hages : AgeStatement.{u, v, z} B K)
    (hsegments : SegmentStatement.{u, v, z} B K)
    (hlabels : CoverLabelStatement.{u, v, z} B K)
    (hcore : CoreLabelStatement.{u, v, z} B K) : Conclusion.{u, v, z} B := by
  refine ⟨K.Cpad, K.Cage, K.Npad, K.mStar, K.pad_nonneg, K.age_pos, ?_⟩
  intro data hα hq hΛ Mnat m hm hfloor htop tS l₀ P hP hlo hhi hend ι h _ _ D Ctx F hnat
  let w : Window B K := ⟨data, hα, hq, hΛ, Mnat, m, hm, hfloor, htop,
    tS, l₀, P, hP, hlo, hhi, hend⟩
  obtain ⟨hfin, href⟩ := hfinite w F hnat
  obtain ⟨hinterval, hanchor, hnatural⟩ := havail w F hnat
  obtain ⟨hage, hrefage⟩ := hages w F hnat
  obtain ⟨haseg, hrseg⟩ := hsegments w F hnat
  exact ⟨K.pad_nonneg, K.age_pos, hfin, href, hinterval, hanchor, hnatural,
    hgeom w F hnat, hage, hrefage, haseg, hrseg, hlabels w F hnat, hcore w F hnat⟩

end AVRegularity.CycleJointProofs.ChartSchedule
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance Set
namespace AVRegularity.CycleJointProofs.ChartSchedule

/-! Uniform choices of preparation padding, ages and the history-separation floor. -/

section
theorem chart_schedule_start_exists (B : Parameters) :
    ∃ j : ℕ, IsCarrierStart B.α B.q B.Λ 1 1 1 j :=
  Providers.carrier_start_exists B.α B.s B.alpha_pos B.alpha_lt B.s_pos B.s_lt
    B.q B.admissible B.Λ B.large 1 1 1 (by norm_num)

def constants (B : Parameters) : Constants where
  Cpad := 2
  Cage := B.CH + 4
  Npad := 2
  mStar := Classical.choose (chart_schedule_start_exists B)
  pad_nonneg := by norm_num
  age_pos := by linarith only [B.duration_pos]

theorem constants_history_start (B : Parameters) :
    IsCarrierStart B.α B.q B.Λ 1 1 1 (constants B).mStar :=
  Classical.choose_spec (chart_schedule_start_exists B)

variable {B : Parameters} (w : Window B (constants B))

theorem Window.period_pos : 0 < w.period :=
  Construction.Stream.ocTauPP_pos (α := B.α) (q := B.q) (by have := B.large; omega)

theorem Window.data_period : ocTauPP w.data.α w.data.q w.data.Λ w.m = w.period := by
  rw [w.alpha_eq, w.q_eq, w.lambda_eq]
  rfl

theorem Window.availability_subset (p : ℤ) :
    availInterval w.data w.Mnat w.m p ⊆ Providers.ComplexFlow.slotWin w.data w.m p := by
  have hs : IsCarrierStart w.data.α w.data.q w.data.Λ 1 1 1 (constants B).mStar := by
    rw [w.alpha_eq, w.q_eq, w.lambda_eq]
    exact constants_history_start B
  apply Providers.QuietAtlas.availInterval_subset_slotWin
    (by rw [w.lambda_eq]; have := B.large; omega) le_rfl hs w.Mnat w.m w.level_floor p
end

/-! Finiteness, the reference anchor, and the exact natural-chart identities. -/

section
universe u v z

theorem finite_reference (B : Parameters) :
    FiniteReferenceStatement.{u, v, z} B (constants B) := by
  intro w ι h _ _ D Ctx F _
  refine ⟨F.locally_finite w.tS w.finish, ?_⟩
  have hT := w.period_pos
  have hCHT : 0 < B.CH * w.period := mul_pos B.duration_pos hT
  have hlo := w.start_lower
  have hhi := w.start_upper
  change ((w.l₀ : ℝ) - 1 / 2) * w.period ≤ w.tS at hlo
  change w.tS < ((w.l₀ : ℝ) + 1 / 2) * w.period at hhi
  change w.tS - 2 * w.period ≤ (w.l₀ : ℝ) * w.period ∧
    (w.l₀ : ℝ) * w.period ≤ w.tS + B.CH * w.period + 2 * w.period
  constructor <;> linarith only [hlo, hhi, hT, hCHT]

theorem availability (B : Parameters) :
    AvailabilityStatement.{u, v, z} B (constants B) := by
  intro w ι h _ _ D Ctx F hnat
  refine ⟨?_, ?_, ?_⟩
  · intro p _
    rw [(hnat p).2.2.1]
    apply ordConnected_iff_uIcc_subset.mpr
    intro a ha b hb
    exact Providers.QuietAtlas.uIcc_subset_availInterval w.data w.Mnat w.m p.val ha hb
  · intro p _
    obtain ⟨hl, _, _, ha, _⟩ := hnat p
    rw [ha, hl]
    change (ocLabel w.data.α w.data.q w.data.Λ w.m p.val : ℝ) *
      ocTauPP w.data.α w.data.q w.data.Λ w.m = _
    rw [w.data_period]
  · intro p _ r _ y
    obtain ⟨hl, _, _, _, hf⟩ := hnat p
    have hr := congrFun (hf r) y
    simpa only [OCData.flowOf, OCData.slotAnchor, ocChart, hl,
      w.alpha_eq, w.q_eq, w.lambda_eq, Window.period] using hr
end

/-! Quantitative availability geometry and retained segments of natural chart pieces. -/

section
universe u v z

variable {B : Parameters} (w : Window B (constants B))
  {ι : Type u} {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {Ctx : OddSlot → Type z} (F : ChartedFamily ι h D OddSlot Ctx)

theorem natural_geometry_anchor_bound (hnat : Natural w F) (p : OddSlot) {r : ℝ}
    (hr : r ∈ (F.piece p).geometry) :
    |r - (F.piece p).anchor| ≤ 3 / 5 * w.period := by
  rw [(hnat p).2.2.1] at hr
  have hwin := w.availability_subset p.val hr
  change w.data.slotAnchor w.m p.val - 3 / 5 * ocTauPP w.data.α w.data.q w.data.Λ w.m ≤ r ∧
    r ≤ w.data.slotAnchor w.m p.val + 3 / 5 * ocTauPP w.data.α w.data.q w.data.Λ w.m at hwin
  rw [w.data_period, ← (hnat p).2.2.2.1] at hwin
  rw [abs_le]
  constructor <;> linarith only [hwin.1, hwin.2]

/-- Entire descendant histories fit in padding2, independently of their depth. -/
theorem padded_geometry (B : Parameters) :
    PaddedGeometryStatement.{u, v, z} B (constants B) := by
  intro w ι h _ _ D Ctx F hnat p hp r hr
  obtain ⟨t, ht, hW⟩ := hp
  have htgeom := (F.piece p).output_subset ht
  obtain ⟨hrlo, hrhi⟩ := abs_le.mp (natural_geometry_anchor_bound w F hnat p hr)
  obtain ⟨htlo, hthi⟩ := abs_le.mp (natural_geometry_anchor_bound w F hnat p htgeom)
  change w.tS - 2 * w.period ≤ r ∧ r ≤ w.finish + 2 * w.period
  constructor <;> linarith only [hrlo, hrhi, htlo, hthi, hW.1, hW.2, w.period_pos]

theorem ages (B : Parameters) : AgeStatement.{u, v, z} B (constants B) := by
  intro w ι h _ _ D Ctx F hnat
  refine ⟨?_, ?_⟩
  · intro p _ r hr
    have hb := natural_geometry_anchor_bound w F hnat p hr
    have hCT : 0 < B.CH * w.period := mul_pos B.duration_pos w.period_pos
    change |r - (F.piece p).anchor| ≤ (B.CH + 4) * w.period
    linarith only [hb, hCT, w.period_pos]
  · intro p hp r hr
    have hg := padded_geometry B w F hnat p hp hr
    change w.tS - 2 * w.period ≤ r ∧
      r ≤ w.tS + B.CH * w.period + 2 * w.period at hg
    have hlo := w.start_lower
    have hhi := w.start_upper
    change ((w.l₀ : ℝ) - 1 / 2) * w.period ≤ w.tS at hlo
    change w.tS < ((w.l₀ : ℝ) + 1 / 2) * w.period at hhi
    change |r - (w.l₀ : ℝ) * w.period| ≤ (B.CH + 4) * w.period
    have hCT : 0 < B.CH * w.period := mul_pos B.duration_pos w.period_pos
    rw [abs_le]
    constructor <;> linarith only [hg.1, hg.2, hlo, hhi, hCT, w.period_pos]

theorem segments (B : Parameters) : SegmentStatement.{u, v, z} B (constants B) := by
  intro w ι h _ _ D Ctx F hnat
  refine ⟨?_, ?_⟩
  · intro p hp r hr
    exact (availability B w F hnat).1 p hp |>.uIcc_subset (F.piece p).anchor_mem hr
  · intro p hp r hr
    have href := (finite_reference B w F hnat).2
    have hg := padded_geometry B w F hnat p hp hr
    exact ordConnected_Icc.uIcc_subset href hg
end

/-! Finite padding of renewal labels and alignment inside block cores. -/

section
universe u v z

theorem cover_labels (B : Parameters) :
    CoverLabelStatement.{u, v, z} B (constants B) := by
  intro w ι h _ _ D Ctx F hnat p hp
  obtain ⟨t, ht, hW⟩ := hp
  have hb := natural_geometry_anchor_bound w F hnat p ((F.piece p).output_subset ht)
  have ha := (availability B w F hnat).2.1 p ⟨t, ht, hW⟩
  rw [ha] at hb
  obtain ⟨hblo, hbhi⟩ := abs_le.mp hb
  have hlo := w.start_lower
  have hend := w.end_upper
  change ((w.l₀ : ℝ) - 1 / 2) * w.period ≤ w.tS at hlo
  change w.finish ≤ ((w.l₀ : ℝ) + w.P - 1 / 2) * w.period at hend
  change w.l₀ - 2 ≤ (F.piece p).label ∧
    (F.piece p).label ≤ w.l₀ + (w.P : ℤ) - 1 + 2
  constructor
  · by_contra hbad
    have hbadr : ((F.piece p).label : ℝ) < (w.l₀ : ℝ) - 2 := by
      exact_mod_cast (lt_of_not_ge hbad)
    have hm := mul_lt_mul_of_pos_right hbadr w.period_pos
    linarith only [hm, hbhi, hW.1, hlo, w.period_pos]
  · by_contra hbad
    have hbadr : (w.l₀ : ℝ) + w.P - 1 + 2 < ((F.piece p).label : ℝ) := by
      exact_mod_cast (lt_of_not_ge hbad)
    have hm := mul_lt_mul_of_pos_right hbadr w.period_pos
    linarith only [hm, hblo, hW.2, hend, w.period_pos]

private theorem five_tau_le_tauP (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) :
    5 * ocTau α q Λ m ≤ ocTauP α q Λ m := by
  have hL := ChildInert.ocL_ge_five α q hΛ m
  have hT := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ
  have hLpos : 0 < (ocL α q Λ m : ℝ) := by linarith only [hL]
  have heq : ocTauP α q Λ m = (ocL α q Λ m : ℝ) * ocTau α q Λ m := by
    unfold ocTauP ocTau
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_right hL
    (Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ).le

theorem core_label (B : Parameters) :
    CoreLabelStatement.{u, v, z} B (constants B) := by
  intro w ι h _ _ D Ctx F hnat p t ht j hj
  have hΛ : 1 ≤ w.data.Λ := by rw [w.lambda_eq]; have := B.large; omega
  have htwin : t ∈ ocPulseWindow w.data.α w.data.q w.data.Λ w.m p.val := by
    rw [← (hnat p).2.1]
    exact ht.1
  have hb := Providers.ComplexFlow.abs_sub_anchor_le_of_mem_window w.data hΛ htwin
  have h5 := five_tau_le_tauP w.data.α w.data.q hΛ w.m
  have hτ := Construction.Stream.ocTau_pos (α := w.data.α) (q := w.data.q) (m := w.m) hΛ
  rw [OCData.slotAnchor, ← (hnat p).1, w.alpha_eq, w.q_eq, w.lambda_eq] at hb
  rw [w.alpha_eq, w.q_eq, w.lambda_eq] at h5 hτ
  change |t - ((F.piece p).label : ℝ) * w.period| ≤
    w.period / 2 + 85 / 48 * ocTau B.α B.q B.Λ w.m at hb
  obtain ⟨hblo, hbhi⟩ := abs_le.mp hb
  rcases lt_trichotomy (F.piece p).label j with hlt | heq | hgt
  · have hr : ((F.piece p).label : ℝ) ≤ (j : ℝ) - 1 := by
      exact_mod_cast (show (F.piece p).label ≤ j - 1 by omega)
    have hm := mul_le_mul_of_nonneg_right hr w.period_pos.le
    exfalso
    linarith only [hm, hbhi, hj.1, h5, hτ]
  · exact heq
  · have hr : (j : ℝ) + 1 ≤ ((F.piece p).label : ℝ) := by
      exact_mod_cast (show j + 1 ≤ (F.piece p).label by omega)
    have hm := mul_le_mul_of_nonneg_right hr w.period_pos.le
    exfalso
    linarith only [hm, hblo, hj.2, h5, hτ]
end

end AVRegularity.CycleJointProofs.ChartSchedule
end
end
