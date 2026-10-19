-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Definitions.Construction.Gen.Majorant
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.Families.IsPointwiseAnalyticEnvelope
import AVRegularity.Construction.Stream.NextAdmissible
public import AVRegularity.Statements.Intermediate.Families.IsPointwiseMolecularEnvelope

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.StageEnvelopes

/-! One envelope interface for weak entry, terminal entry and a retained cascade stage.
The inner carrier is explicit; no smoothness outside it is asserted. The molecular radius
is a parameter, instantiated by rhoStar rather than silently identified with ocRhoMol.
Constants precede the ambient order cap, stage, component spaces, masses and time window. -/

section
/-- Fixed reserves for a context-to-envelope estimate. The actual component reserve is at
least certReserve, and the actual inner reserve is at most innerReserve. -/
structure ContextEnvelopeParameters where
  α : ℝ
  s : ℝ
  q : ℝ
  Λ : ℕ
  ζ : ℝ → ℝ
  alpha_pos : 0 < α
  alpha_lt : α < 1 / 3
  s_pos : 0 < s
  s_lt : s < (1 - α) / 2
  admissible_q : IsAdmissibleQ α s q
  base_large : 128 ≤ Λ
  profile : IsFastProfile ζ
  bw : ℝ
  bw_pos : 0 < bw
  bw_small : bw ≤ 1 / 10000
  certReserve : ℝ
  innerReserve : ℝ
  inner_nonneg : 0 ≤ innerReserve
  gap : innerReserve < certReserve
  cert_le_two : certReserve ≤ 2
  Ks : ℕ
  Kan : ℕ
  Lan : ℕ
  Jm : ℕ
  Dstar : ℕ

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm j₀ : ℕ} {b : ℝ}

/-- Geometric, carrier-environment and certificate inputs. Higher original lengths fit inside the *actual*
molecular radius. This is not automatic for an arbitrary seed. -/
structure ContextEnvelopeInput (p : ContextEnvelopeParameters)
    (G : GenStage D hr Dm b j₀) (k : InvConsts) (mres ρ : ℝ) : Prop where
  bw_eq : b = p.bw
  alpha_eq : D.α = p.α
  q_eq : D.q = p.q
  base_eq : D.Λ = p.Λ
  profile_eq : D.ζ = p.ζ
  stream : IsOCStreamSeq p.α p.q p.Λ p.ζ D.Φ
  natural : ∃ M, G.IsNatural M
  certified : G.IsContextCertified k
  level_pos : 1 ≤ G.level
  carrier_start : j₀ ≤ G.level
  carrier_environment : ∃ CH Υ : ℝ, CarrierOK 100 CH Υ ∧
    IsCarrierStart D.α D.q D.Λ b CH Υ j₀
  q_pos : 1 < D.q
  large : 128 ≤ D.Λ
  kap_pos : 0 < D.kap G.level
  radius_pos : 0 < ρ
  radius_le : ρ ≤ D.eps G.level
  wavelength_le : D.eps G.level ≤ D.eps (G.level - 1)
  inner_nonneg : 0 ≤ mres
  inner_le : mres ≤ p.innerReserve
  reserve_le : ∀ v : CompIn G.comps, p.certReserve ≤ compReserve k v.1
  reserve_upper : ∀ v : CompIn G.comps, compReserve k v.1 ≤ 2
  slot_order : k.Ks ≤ p.Ks
  slow_order : k.Kan ≤ p.Kan
  fast_order : k.Lan ≤ p.Lan
  molecular_order : k.Jm ≤ p.Jm
  source_order : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).maxOrder ≤ p.Dstar
  higher_length : ∀ v u (γ : G.fam.Γ v u), 3 ≤ (G.fam.identity v u γ).maxOrder →
    (G.fam.identity v u γ).record.length ≤ ρ

/-- Both essential and pointwise envelopes, at every reserved slot, in any positive constant
component weight. In particular this includes the ordinary and marked families. -/
def StageContextEnvelopes (G : GenStage D hr Dm b j₀) (law : BirthLaw) (k : InvConsts)
    (W : Set ℝ) (mres ρ : ℝ) : Prop :=
  ∀ w : CompIn G.comps → ℝ, (∀ v, 0 < w v) →
  ∀ K : CompIn G.comps → ℕ, (∀ v, K v ≤ k.Ks) →
  let F := markerConj w G.fam
  let dom := G.innerDomain W mres
  let B := fun v u => w v / w u * recordMajorant (G.mass law) G.fam v u
  IsAnalyticEnvelope F (G.mass law) dom (D.eps (G.level - 1)) k.Ca k.Kan k.Lan B ∧
    IsMolecularEnvelope F (G.mass law) K dom (D.kap G.level) (D.eps G.level)
      (D.eps (G.level - 1)) ρ k.Cm k.Jm B ∧
    IsPointwiseAnalyticEnvelope F (G.mass law) dom (D.eps (G.level - 1)) k.Ca k.Kan k.Lan B ∧
    IsPointwiseMolecularEnvelope F (G.mass law) K dom (D.kap G.level) (D.eps G.level)
      (D.eps (G.level - 1)) ρ k.Cm k.Jm B

/-- One fixed-reserve estimate, with constants preceding the actual stage and all data. -/
structure ContextEnvelopeEstimate (p : ContextEnvelopeParameters) where
  levelFloor : ℕ
  Ca : ℝ
  Cm : ℕ → ℝ
  analytic_nonneg : 0 ≤ Ca
  molecular_nonneg : ∀ j, 0 ≤ Cm j
  bound : ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    (D : OCData) (Dm j₀ : ℕ) (b : ℝ) (G : GenStage D hr Dm b j₀) (k : InvConsts) (mres ρ : ℝ),
    ContextEnvelopeInput p G k mres ρ → levelFloor ≤ G.level → Ca ≤ k.Ca → (∀ j, Cm j ≤ k.Cm j) →
    ∀ (law : BirthLaw) (W : Set ℝ), StageContextEnvelopes G law k W mres ρ

/-- The common producer of context envelope estimates, shared by the entry
constructions. The constants are uniform in Dm; Dstar bounds the actual source orders, independently of that ambient cap. -/
def ContextStageEnvelopesStatement : Prop :=
  ∀ p : ContextEnvelopeParameters, Nonempty (ContextEnvelopeEstimate p)
end

/-! The single analytic leaf of the shared producer: uniform Cauchy estimates on every
recentered inner carrier, before incidence sums or mass conjugation. -/

section
/-- Select the genuine time supremum or its essential version, without changing the domain. -/
def envelopeJetSup {ι : Type*} (pointwise : Bool) (dom : ι → Set (ℝ × Vec 2)) (r q : ℕ)
    (f : ι → ℝ → Vec 2 → Vec 2 → Vec 2) : ℝ≥0∞ :=
  if pointwise then pointwiseJetSupFam dom r q f else jetSupFam dom r q f

variable {ι : Type*} {h : ι → Type*} [∀ v, NormedAddCommGroup (h v)]
  [∀ v, NormedSpace ℝ (h v)] {Dm : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The unweighted analytic jet sum of one identity, with its original order range. -/
def analyticConstituentPrice (F : ChartedFamily ι h Dm P Ctx) (dom : F.Domain)
    (E : ℝ) (Ks Ls : ℕ) (pointwise : Bool) (v u : ι) (γ : F.Γ v u) : ℝ≥0∞ :=
  ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
    ∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (Ls + 1),
      ENNReal.ofReal (E ^ r) * envelopeJetSup pointwise (fun x : F.Index => dom x.1 x.2) r q
        (fun x => F.slowFlux E x.1 x.2 v u γ d I)

/-- The unweighted normalized molecular jet sum of one identity, including the exact
factorial ratio of the envelope (no replacement by the kernel Schur price). -/
def molecularConstituentPrice (F : ChartedFamily ι h Dm P Ctx) (dom : F.Domain)
    (ν e E ρ : ℝ) (k j : ℕ) (pointwise : Bool) (v u : ι) (γ : F.Γ v u) : ℝ≥0∞ :=
  ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
    (if pointwise then pointwiseMolecularJet ρ e k j (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)
      else molecularJet ρ e k j (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) *
      (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
      ENNReal.ofReal (((k + d - 2).factorial : ℝ) / (k.factorial : ℝ))

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {j₀ : ℕ} {b : ℝ}

/-- A constituentwise Cauchy budget, before multiplication by the constant component map
or mass factors. Scaling by a positive component weight scales the same original witness. -/
structure ContextConstituentBounds (G : GenStage D hr Dm b j₀) (k : InvConsts)
    (W : Set ℝ) (mres ρ : ℝ) (w : CompIn G.comps → ℝ) : Prop where
  smooth : (markerConj w G.fam).IsSmoothOn (G.innerDomain W mres) (D.eps (G.level - 1))
    (fun _ => max (k.Kan + k.Lan) (k.Ks + k.Jm))
  analytic : ∀ pointwise v u (γ : G.fam.Γ v u),
    analyticConstituentPrice (markerConj w G.fam) (G.innerDomain W mres)
      (D.eps (G.level - 1)) k.Kan k.Lan pointwise v u γ ≤
        ENNReal.ofReal (k.Ca * (w v / w u * (G.fam.identity v u γ).record.size))
  molecular : ∀ K : CompIn G.comps → ℕ, (∀ v, K v ≤ k.Ks) →
    ∀ pointwise v u (γ : G.fam.Γ v u) j, j ≤ k.Jm →
      molecularConstituentPrice (markerConj w G.fam) (G.innerDomain W mres)
        (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) ρ (K v) j pointwise v u γ ≤
          ENNReal.ofReal ((k.Cm j * ((D.eps (G.level - 1)) ^ j)⁻¹) *
            (w v / w u * (G.fam.identity v u γ).record.size))

/-- Open analytic leaf. It is uniform in all contexts and all output times, not only the
native chain. The same constants control essential and pointwise jet sums. -/
def ContextCertifiedConstituentCauchyStatement : Prop :=
  ∀ p : ContextEnvelopeParameters,
  ∃ (Ca : ℝ) (Cm : ℕ → ℝ) (mStar : ℕ), 0 ≤ Ca ∧ (∀ j, 0 ≤ Cm j) ∧
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    (D : OCData) (Dm j₀ : ℕ) (b : ℝ) (G : GenStage D hr Dm b j₀) (k : InvConsts) (mres ρ : ℝ),
    ContextEnvelopeInput p G k mres ρ → mStar ≤ G.level → Ca ≤ k.Ca → (∀ j, Cm j ≤ k.Cm j) →
    ∀ (W : Set ℝ) (w : CompIn G.comps → ℝ), (∀ v, 0 < w v) →
      ContextConstituentBounds G k W mres ρ w
end

/-! Shared context-envelope assembly. The only analytic input is the named constituent
Cauchy estimate; all identity sums, mass factors and component markers are discharged here. -/

section
private theorem incidence_sum {α : Type*} [Fintype α]
    (s C : ℝ) (w size : α → ℝ) (x : α → ℝ≥0∞)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hw : ∀ a, 0 ≤ w a) (hsize : ∀ a, 0 ≤ size a)
    (hx : ∀ a, x a ≤ ENNReal.ofReal (C * size a)) :
    ENNReal.ofReal s * ∑ a, ENNReal.ofReal (w a) * x a ≤
      ENNReal.ofReal (C * (s * ∑ a, w a * size a)) := by
  calc
    _ ≤ ENNReal.ofReal s * ∑ a, ENNReal.ofReal (w a) * ENNReal.ofReal (C * size a) :=
      mul_le_mul_right (Finset.sum_le_sum fun a _ => mul_le_mul_right (hx a) _) _
    _ = ENNReal.ofReal (s * ∑ a, w a * (C * size a)) := by
      simp_rw [← ENNReal.ofReal_mul (hw _)]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (hw a) (mul_nonneg hC (hsize a))),
        ← ENNReal.ofReal_mul hs]
    _ = _ := by
      congr 1
      simp_rw [mul_left_comm (w _) C]
      rw [← Finset.mul_sum, mul_left_comm]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm j₀ : ℕ} {b : ℝ}

private theorem weighted_record_sum (G : GenStage D hr Dm b j₀) (law : BirthLaw)
    (w : CompIn G.comps → ℝ) (v u : CompIn G.comps) :
    Real.sqrt (G.mass law u / G.mass law v) *
      (∑ γ, ‖(G.fam.identity v u γ).map‖ *
        (w v / w u * (G.fam.identity v u γ).record.size)) =
      w v / w u * recordMajorant (G.mass law) G.fam v u := by
  unfold recordMajorant
  simp_rw [mul_left_comm _ (w v / w u)]
  rw [← Finset.mul_sum, mul_left_comm]

/-- Incidence summation and constant diagonal conjugation lose no component-count factor. -/
theorem stage_envelopes_of_constituent_bounds
    (G : GenStage D hr Dm b j₀) (law : BirthLaw) (k : InvConsts) (W : Set ℝ) (mres ρ : ℝ)
    (hCa : 0 ≤ k.Ca) (hCm : ∀ j, 0 ≤ k.Cm j) (hE : 0 < D.eps (G.level - 1))
    (hb : ∀ w : CompIn G.comps → ℝ, (∀ v, 0 < w v) → ContextConstituentBounds G k W mres ρ w) :
    StageContextEnvelopes G law k W mres ρ := by
  intro w hw K hK
  have hc := hb w hw
  have hweight (v u : CompIn G.comps) : 0 ≤ w v / w u := (div_pos (hw v) (hw u)).le
  have hsize (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
      0 ≤ w v / w u * (G.fam.identity v u γ).record.size :=
    mul_nonneg (hweight v u) (G.fam.identity v u γ).record.size_nonneg
  have ha (pointwise : Bool) (v u : CompIn G.comps) :
      ENNReal.ofReal (Real.sqrt (G.mass law u / G.mass law v)) *
        ∑ γ, ENNReal.ofReal ‖(G.fam.identity v u γ).map‖ *
          analyticConstituentPrice (markerConj w G.fam) (G.innerDomain W mres)
            (D.eps (G.level - 1)) k.Kan k.Lan pointwise v u γ ≤
      ENNReal.ofReal (k.Ca * (w v / w u * recordMajorant (G.mass law) G.fam v u)) := by
    have hh := incidence_sum (Real.sqrt (G.mass law u / G.mass law v)) k.Ca
      (fun γ => ‖(G.fam.identity v u γ).map‖)
      (fun γ => w v / w u * (G.fam.identity v u γ).record.size) _
      (Real.sqrt_nonneg _) hCa (fun _ => norm_nonneg _) (hsize v u) (hc.analytic pointwise v u)
    rwa [weighted_record_sum] at hh
  have hm (pointwise : Bool) (v u : CompIn G.comps) (j : ℕ) (hj : j ≤ k.Jm) :
      ENNReal.ofReal (Real.sqrt (G.mass law u / G.mass law v)) *
        ∑ γ, ENNReal.ofReal ‖(G.fam.identity v u γ).map‖ *
          molecularConstituentPrice (markerConj w G.fam) (G.innerDomain W mres)
            (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) ρ (K v) j pointwise v u γ ≤
      ENNReal.ofReal (k.Cm j * ((D.eps (G.level - 1)) ^ j)⁻¹ *
        (w v / w u * recordMajorant (G.mass law) G.fam v u)) := by
    have hh := incidence_sum (Real.sqrt (G.mass law u / G.mass law v))
      (k.Cm j * ((D.eps (G.level - 1)) ^ j)⁻¹)
      (fun γ => ‖(G.fam.identity v u γ).map‖)
      (fun γ => w v / w u * (G.fam.identity v u γ).record.size) _
      (Real.sqrt_nonneg _) (mul_nonneg (hCm j) (inv_nonneg.mpr (pow_nonneg hE.le _)))
      (fun _ => norm_nonneg _) (hsize v u)
      (fun γ => hc.molecular K hK pointwise v u γ j hj)
    rwa [weighted_record_sum] at hh
  have hsa : (markerConj w G.fam).IsSmoothOn (G.innerDomain W mres) (D.eps (G.level - 1))
      (fun _ => k.Kan + k.Lan) := by
    intro p ctx v u γ d I tY htY z
    exact (hc.smooth p ctx v u γ d I tY htY z).of_le (by exact_mod_cast Nat.le_max_left _ _)
  have hsm : (markerConj w G.fam).IsSmoothOn (G.innerDomain W mres) (D.eps (G.level - 1))
      (fun v => K v + k.Jm) := by
    intro p ctx v u γ d I tY htY z
    exact (hc.smooth p ctx v u γ d I tY htY z).of_le (by
      exact_mod_cast (Nat.add_le_add_right (hK v) k.Jm).trans (Nat.le_max_right _ _))
  exact ⟨⟨hsa, ha false⟩, ⟨hsm, hm false⟩, ⟨hsa, ha true⟩, ⟨hsm, hm true⟩⟩

/-- Exact shared envelope statement, conditional on the single all-context Cauchy leaf. -/
theorem context_stage_envelopes_of_cauchy
    (hcauchy : ContextCertifiedConstituentCauchyStatement) : ContextStageEnvelopesStatement := by
  intro p
  obtain ⟨Ca, Cm, mStar, hCa, hCm, hc⟩ := hcauchy p
  refine ⟨⟨mStar, Ca, Cm, hCa, hCm, ?_⟩⟩
  intro hr _ _ D Dm j₀ b G k mres ρ hinput hlevel hCa' hCm' law W
  exact stage_envelopes_of_constituent_bounds G law k W mres ρ (hCa.trans hCa')
    (fun j => (hCm j).trans (hCm' j))
    (Construction.Stream.ocEpsilon_pos (by have := hinput.large; omega))
    (hc hr D Dm j₀ b G k mres ρ hinput hlevel hCa' hCm' W)
end

end AVRegularity.Construction.StageEnvelopes
end
