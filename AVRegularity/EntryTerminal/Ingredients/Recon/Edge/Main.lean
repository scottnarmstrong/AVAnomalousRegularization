-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryTerminal.Ingredients.PrepChart.Chart
public import AVRegularity.EntryTerminal.Ingredients.Recon.Coarse
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.CycleJoint.PlaneHkWindowChartH1
public import AVRegularity.EntryTerminal.Ingredients.Recon.Coeff.Main
import AVRegularity.EntryTerminal.Ingredients.Recon.Scale.Scale
import AVRegularity.Definitions.Finite.FiniteLiftBridge
import AVRegularity.Proofs.Results.CycleJoint.PreparationChartSchedule
import Mathlib.Algebra.Order.Star.Real

section
section
/-! **Edge clauses, step 2: the uniform bound of a sampled envelope.** The edge
coefficients on the window of a sampled envelope are bounded by `edgeBoundConst`, a constant that
does not depend on the window (`edgeCoefficient_bound_of_sampled` only gives an existential bound,
which cannot be shared by several windows).

Degenerate cases:
- `C b = 0`: the constant is `0`.
- Two windows with the same data: the same bound. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The bound of the sampled envelope, without the window. -/
def edgeBoundConst (π : ι → ℝ) (K : ι → ℕ) (ν ρ C : ℝ) (b : ι → ι → ℝ) (D : ℕ) : ℝ :=
  ∑ v, ∑ u, ∑ d ∈ admissibleOrders K D v u,
    C * b v u * (ν * ρ ^ (d - 2)) /
      (Real.sqrt (π u / π v) * (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ)))

/-- **The uniform bound.** -/
theorem edgeBound_of_sampled_uniform (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ)
    (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (actual : ∀ p, Ctx p) {t₀ t₁ ν e E ρ C : ℝ}
    {b : ι → ι → ℝ} (hν : 0 < ν) (hρ : 0 < ρ)
    (hfwd : IsSampledEnvelope F π K actual t₀ t₁ ν e E ρ C b) (hCb : ∀ v u, 0 ≤ C * b v u) :
    0 ≤ edgeBoundConst π K ν ρ C b D ∧
      ∀ t ∈ Set.Icc t₀ t₁, ∀ v u (d : admissibleOrders K D v u) x,
        ‖edgeCoefficient F ν e E actual K v u d t x‖ ≤ edgeBoundConst π K ν ρ C b D := by
  obtain ⟨T, hT⟩ : ∃ T : ι → ι → ℕ → ℝ, ∀ v u d, T v u d = C * b v u * (ν * ρ ^ (d - 2)) /
      (Real.sqrt (π u / π v) * (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hT0 : ∀ v u d, 0 ≤ T v u d := fun v u d => by
    rw [hT]
    have := hCb v u
    positivity
  have hsum : edgeBoundConst π K ν ρ C b D = ∑ v, ∑ u, ∑ d ∈ admissibleOrders K D v u, T v u d := by
    unfold edgeBoundConst
    simp only [hT]
  rw [hsum]
  refine ⟨Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun d _ =>
      hT0 v u d, fun t ht v u d x => ?_⟩
  have hd : d.1 ∈ Finset.Icc 2 D := (Finset.mem_filter.1 d.2).1
  have hb := CycleJointProofs.sampledEnvelope_physicalCoefficient_normalized_bound (P := P) F π K
    actual t₀ t₁ ν e E ρ C b hν hρ hfwd v u (hCb v u) d.1 hd t ht x
  have hpos1 : 0 < Real.sqrt (π u / π v) := Real.sqrt_pos.2 (div_pos (hπ u) (hπ v))
  have hpos2 : 0 < ν * ρ ^ (d.1 - 2) := mul_pos hν (pow_pos hρ _)
  have hpos3 : 0 < ((K v + d.1 - 2).factorial : ℝ) / ((K v).factorial : ℝ) := by positivity
  have h1 := CycleComparison.Reconstruction.le_of_mul_div_mul_le hpos1 hpos2 hpos3 hb
  have h2 : ‖edgeCoefficient F ν e E actual K v u d t x‖ ≤ T v u d.1 := by
    rw [hT]
    exact h1
  refine h2.trans ?_
  refine (Finset.single_le_sum (f := fun d => T v u d) (fun d _ => hT0 v u d) d.2).trans ?_
  refine (Finset.single_le_sum (f := fun u => ∑ d ∈ admissibleOrders K D v u, T v u d)
    (fun u _ => Finset.sum_nonneg fun d _ => hT0 v u d) (Finset.mem_univ u)).trans ?_
  exact Finset.single_le_sum (f := fun v => ∑ u, ∑ d ∈ admissibleOrders K D v u, T v u d)
    (fun v _ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun d _ => hT0 v u d)
    (Finset.mem_univ v)

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **Edge clauses, step 1: the chart certificate of a block.** The preparation chart
certificate of the weak family on a window `[t_S, t_S + 2τ''_M]` at any start `t_S` (the lemmas
`preparation_chart_schedule` and `prep_flow_jets` are generic in the start), with the renewal block
`l₀ = prepBlock τ'' t_S` and `P = 3` core charts. The constants do not depend on the start, the
level or the family.

Degenerate cases:
- `t_S = a_M`: the certificate of `PrepChartAtM` with `P = 3`.
- An empty weak family: the schedule is about no pieces. -/

@[expose] public section

open Homogenization AVenhance

namespace AVRegularity.EntryTerminal.Ingredients.Recon

open AVRegularity.EntryTerminal.Route AVRegularity.EntryTerminal.Ingredients

/-- **The chart certificate on a block.** -/
theorem reconEdge_chart (X : TermConstruction) {Λ : ℕ} (hΛ : 128 ≤ Λ) (Jchart : ℕ) :
    ∃ (Cpad Cage : ℝ) (Npad : ℕ) (Cchart : ℕ → ℝ) (M₀ : ℕ), ∀ M : ℕ, M₀ ≤ M →
      ∀ (D : OCData), IsTermData X Λ M D → ∀ {ι : Type} {h : ι → Type}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}
        {Ctx : OddSlot → Type} (F : ChartedFamily ι h Dm OddSlot Ctx) (Jw : ℕ)
        (_hnat : ∀ p, IsNaturalPiece D (M + Jw) M p.1 (F.piece p))
        (hφ : IsAdmissibleStream (D.Φ (M - 1))) (tS : ℝ),
        IsPreparationChartCertificate X.α X.q Λ M (D.Φ (M - 1)) hφ tS
          (tS + 2 * ocTauPP X.α X.q Λ M) Cpad Cage Npad Jchart Cchart
          (prepBlock (ocTauPP X.α X.q Λ M) tS) 3 F := by
  obtain ⟨C, -, hflow⟩ := prep_flow_jets X.α X.s X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq X.ζ X.hζ
  obtain ⟨Cpad, Cage, Npad, mStar, -, hage, hsch⟩ :=
    AVRegularity.Providers.preparation_chart_schedule X.α X.s X.q X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq Λ
      hΛ 2 two_pos
  obtain ⟨M₁, hM₁, hfl⟩ := hflow Λ hΛ Cage hage
  refine ⟨Cpad, Cage, Npad, prepChartConst C, max mStar M₁, fun M hM D hD ι h _ _ Dm Ctx F Jw hnat hφ tS => ?_⟩
  obtain ⟨hDα, hDq, hDΛ, -, hstream, -, -⟩ := hD
  have hh : 0 < ocTauPP X.α X.q Λ M := Construction.Stream.ocTauPP_pos (le_trans (by norm_num) hΛ)
  obtain ⟨hb1, hb2⟩ := prepBlock_spec (aM := tS) hh
  have hM2 : 2 ≤ M := le_trans hM₁ (le_trans (le_max_right _ _) hM)
  have hwin : tS + 2 * ocTauPP X.α X.q Λ M ≤
      (((prepBlock (ocTauPP X.α X.q Λ M) tS : ℤ) : ℝ) + ((3 : ℕ) : ℝ) - 1 / 2) *
        ocTauPP X.α X.q Λ M := by
    have := mul_lt_mul_of_pos_right hb2 hh
    nlinarith
  exact ⟨hsch D hDα hDq hDΛ (M + Jw) M hM2 (le_trans (le_max_left _ _) hM)
      (Nat.le_add_right _ _) tS _ 3 (by norm_num) hb1 hb2 hwin F hnat,
    hfl D.Φ hstream M (le_trans (le_max_right _ _) hM) hφ tS _ Cpad Jchart⟩

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end

section
section
/-! **Edge clauses, step 3: the sampled envelope of a block, at a context.** For a
window `[t_S, t_S + 2τ''_M] ⊆ [a_M, a + T₀]`, the pointwise molecular envelope of the actual family
(from the weak stage, `IsSeedPointwiseMolecular`, rescaled to the radius `min{c_K, 1} x`, as in
`prepFamilyPart`) and the chart certificate of the block give the sampled envelope
(`preparation_sampled_envelope_of_pointwise_certificate`). The constant `C_prep` and the bound
are the same for all blocks.

Degenerate cases:
- `c_K ≤ 1`: the radius is `c_K x`, the rescaling factor is `1`.
- An edge-free weak family: `recordMajorant = 0`, the bound is `0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.EntryTerminal.Ingredients

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **The edge coefficients on every block**: a uniform bound for all points of the plane and
continuity in space, at every time of every window `[t_S, t_S + 2τ''_M] ⊆ [a_M, a + T₀]`. -/
theorem reconEdge_block
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (ℓ : ℕ) (hcK : 0 < cK) (hc₀ : kW.c₀ = cK) (h128 : 128 ≤ A.Λ) (hjM : j₀ ≤ M)
    (hM1 : 1 ≤ M)
    (hKs : ∀ v, rK c ℓ v ≤ kW.Ks) (hJm : rKmax A ℓ + A.Dt + 2 ≤ kW.Jm)
    (hcap : ocEpsilon c.D.q c.D.Λ M ≤ Real.sqrt (c.D.κ M / ocA c.D.α c.D.q c.D.Λ M))
    (hεε : ocEpsilon c.D.q c.D.Λ M ≤ ocEpsilon c.D.q c.D.Λ (M - 1))
    (Cpad Cage : ℝ) (Npad : ℕ) (Cchart : ℕ → ℝ)
    (hchart : ∀ tS : ℝ, IsPreparationChartCertificate c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1))
      (c.D.hΦ (M - 1)) tS (tS + 2 * ocTauPP c.D.α c.D.q c.D.Λ M) Cpad Cage Npad
      (rKmax A ℓ + A.Dt + 2) Cchart (prepBlock (ocTauPP c.D.α c.D.q c.D.Λ M) tS) 3 c.Gw.actualFamily) :
    ∃ CA : ℝ, 0 ≤ CA ∧ ∀ tS : ℝ, c.aM ≤ tS → tS + 2 * ocTauPP c.D.α c.D.q c.D.Λ M ≤ c.a + A.T₀ →
      ∀ t ∈ Set.Icc tS (tS + 2 * ocTauPP c.D.α c.D.q c.D.Λ M), ∀ v u
        (d : admissibleOrders (rK c ℓ) A.Dt v u),
        Continuous ((edgeCoefficient c.Gw.actualFamily (c.D.κ M) (ocEpsilon c.D.q c.D.Λ M)
          (ocEpsilon c.D.q c.D.Λ (M - 1)) (fun _ => ()) (rK c ℓ)) v u d t) ∧
        ∀ y, ‖(edgeCoefficient c.Gw.actualFamily (c.D.κ M) (ocEpsilon c.D.q c.D.Λ M)
          (ocEpsilon c.D.q c.D.Λ (M - 1)) (fun _ => ()) (rK c ℓ)) v u d t y‖ ≤ CA := by
  obtain ⟨hα, hq, hΛD, hζ, -, hchain, hterm⟩ := c.data
  have hΛ : 128 ≤ c.D.Λ := hΛD ▸ h128
  have hqq : 1 < c.D.q := hq ▸ X.hq.1
  have hε := Scales.epsilon_basic (m := M) hqq hΛ
  have hν : 0 < c.D.κ M := by
    have hch : IsOCBandChain X.α X.q A.Λ X.ζ M c.D.κ := hchain
    exact CycleReference.bandChain_pos (by omega) X.hζ hch le_rfl
  have hπ : ∀ v, 0 < c.Gw.mass c.lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hqq hΛ c.lawW v.1
  have hW := c.weak
  have hlev : c.Gw.level = M := hW.2.2.1
  have hpw : IsSeedPointwiseMolecular c.lawW kW c.Gw c.aM (c.a + A.T₀) := hW.2.2.2.2.2.1.2.2
  have hnat := hW.2.2.2.2.2.2.2.2.2.1
  have hact : ∀ p, (c.Gw.actual p).1 = nativeChain c.Gw.level p.1 := hnat.2.2.1
  have hi : 1 ≤ c.Gw.level := by omega
  have hjl : j₀ ≤ c.Gw.level := by omega
  have hkap : c.D.kap c.Gw.level = c.D.κ M := by
    rw [hlev]
    unfold OCData.kap
    rw [hterm, min_self]
  have hrho : rhoStar c.D kW.c₀ c.Gw.level = cK * c.D.eps M := by
    rw [hlev, hc₀]
    have hcap' : c.D.eps M ≤ Real.sqrt (c.D.κ M / ocA c.D.α c.D.q c.D.Λ M) := hcap
    unfold rhoStar
    rw [min_eq_left hcap']
  have hmin0 : 0 < min cK 1 := lt_min hcK one_pos
  have hρ' : 0 < min cK 1 * ocEpsilon c.D.q c.D.Λ M := mul_pos hmin0 hε.1
  have hρ'ρ : min cK 1 * ocEpsilon c.D.q c.D.Λ M ≤ cK * ocEpsilon c.D.q c.D.Λ M :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hε.1.le
  have hlam1 : 1 ≤ cK / min cK 1 := by
    rw [le_div_iff₀ hmin0, one_mul]
    exact min_le_left _ _
  have hρlam : cK * ocEpsilon c.D.q c.D.Λ M ≤
      (cK / min cK 1) * (min cK 1 * ocEpsilon c.D.q c.D.Λ M) := by
    rw [← mul_assoc, div_mul_cancel₀ _ hmin0.ne']
  have hE0 : 0 ≤ ocEpsilon c.D.q c.D.Λ (M - 1) := (Scales.epsilon_basic (m := M - 1) hqq hΛ).1.le
  have hmaxF : ∀ v u (γ : c.Gw.actualFamily.Γ v u),
      (c.Gw.actualFamily.identity v u γ).maxOrder ≤ A.DW := fun v u γ =>
    (hW.2.2.2.2.2.2.1 v u γ).1
  have hb0 : ∀ v u, 0 ≤ recordMajorant (c.Gw.mass c.lawW) c.Gw.fam v u := fun v u =>
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun γ _ =>
      mul_nonneg (norm_nonneg _) (c.Gw.fam.identity v u γ).record.size_nonneg)
  obtain ⟨Cprep, hCprep, hsamp⟩ := CycleJointProofs.preparation_sampled_envelope_of_pointwise_certificate A.Dt (rKmax A ℓ)
    (rKmax A ℓ + A.Dt + 2) (rKmax A ℓ + A.Dt + 2) le_rfl le_rfl
    (fun j => (cK / min cK 1) ^ (A.DW - 2) * kW.Cm j) Cchart
  have hKmax : ∀ v, rK c ℓ v ≤ rKmax A ℓ := fun v => by
    have := descSlots_le c.Gw.actualFamily A.dW A.Dt v
    show A.k₀ + ℓ + descSlots c.Gw.actualFamily A.dW A.Dt v ≤ A.k₀ + ℓ + A.Dt * A.dW
    omega
  have hCb : ∀ v u, 0 ≤ Cprep * recordMajorant (c.Gw.mass c.lawW) c.Gw.fam v u := fun v u =>
    mul_nonneg (zero_le_one.trans hCprep) (hb0 v u)
  have hpt : ∀ tS : ℝ, c.aM ≤ tS → tS + 2 * ocTauPP c.D.α c.D.q c.D.Λ M ≤ c.a + A.T₀ →
      IsSampledEnvelope c.Gw.actualFamily (c.Gw.mass c.lawW) (rK c ℓ) (fun _ => ()) tS
        (tS + 2 * ocTauPP c.D.α c.D.q c.D.Λ M) (c.D.κ M) (ocEpsilon c.D.q c.D.Λ M)
        (ocEpsilon c.D.q c.D.Λ (M - 1)) (min cK 1 * ocEpsilon c.D.q c.D.Λ M) Cprep
        (recordMajorant (c.Gw.mass c.lawW) c.Gw.fam) := fun tS h1 h2 => by
    have hWsub : Set.Icc tS (tS + 2 * ocTauPP c.D.α c.D.q c.D.Λ M) ⊆
        Set.Icc c.aM (c.a + A.T₀) := fun t ht => ⟨h1.trans ht.1, ht.2.trans h2⟩
    have hP := hpw (rK c ℓ) hKs
    rw [hkap, hrho] at hP
    simp only [hlev] at hP
    have hP' := c.Gw.isPointwiseMolecularEnvelope_actualFamily hWsub kW.mEnv hact hi hjl hP
    have hP'' := pointwiseMolecularEnvelope_rescale _ _ _ _ hν hε.1 hρ' hρ'ρ hρlam hlam1
      hmaxF (pointwiseMolecularEnvelope_mono _ _ _ _ _ _ _ _ hE0 hJm (fun _ => le_rfl) hb0 hP')
    exact hsamp c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1)) tS _ Cpad Cage Npad _ 3 _ _ _
      hν hρ' (mul_le_of_le_one_left hε.1.le (min_le_right cK 1)) hεε c.Gw.actualFamily _ hπ
      (rK c ℓ) hKmax (fun _ => ()) _ hb0 (hchart tS) hP''
  have hCA : 0 ≤ edgeBoundConst (c.Gw.mass c.lawW) (rK c ℓ) (c.D.κ M)
      (min cK 1 * ocEpsilon c.D.q c.D.Λ M) Cprep (recordMajorant (c.Gw.mass c.lawW) c.Gw.fam)
      A.Dt :=
    Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun d _ => by
      have := hCb v u
      have h2 := hπ u
      have h3 := hπ v
      positivity
  refine ⟨_, hCA, ?_⟩
  intro tS h1 h2 t ht v u d
  obtain ⟨-, hb⟩ := edgeBound_of_sampled_uniform c.Gw.actualFamily (c.Gw.mass c.lawW) hπ (rK c ℓ)
    (fun _ => ()) hν hρ' (hpt tS h1 h2) hCb
  exact ⟨CycleComparison.Reconstruction.edgeCoefficient_continuous_of_sampled c.Gw.actualFamily (c.Gw.mass c.lawW) (rK c ℓ)
    (fun _ => ()) (hpt tS h1 h2) v u d ht, fun y => hb t ht v u d y⟩

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **Edge clauses, step 4: the assembly.** Every time `s` of the window lies in a block
`[t_S, t_S + 2τ''_M] ⊆ [a_M, a + T₀]` (`t_S = max a_M (min (s - τ'') (a + T₀ - 2τ''))`), so the
bound and the continuity on a block hold at `s`; continuity gives a.e. strong
measurability. The prefix is discharged with the order floor `K_max + D_t + 2`.

Degenerate cases:
- `s = t_p`: the first block, `t_S = max a_M (min (t_p - τ'') ...)`.
- `s = a + T₀`: the last block, `t_S = a + T₀ - 2τ''`. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.EntryTerminal.Ingredients

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The block of a time of the window. -/
theorem reconEdge_blockOf {aM tp T s h : ℝ} (hh : 0 < h) (hw : aM + 2 * h ≤ T) (hap : aM ≤ tp)
    (hs : s ∈ Set.Icc tp T) :
    aM ≤ max aM (min (s - h) (T - 2 * h)) ∧ max aM (min (s - h) (T - 2 * h)) + 2 * h ≤ T ∧
      s ∈ Set.Icc (max aM (min (s - h) (T - 2 * h))) (max aM (min (s - h) (T - 2 * h)) + 2 * h) := by
  obtain ⟨hs1, hs2⟩ := hs
  refine ⟨le_max_left _ _, ?_, ?_, ?_⟩
  · have := max_le (a := aM) (b := min (s - h) (T - 2 * h)) (c := T - 2 * h) (by linarith)
      (min_le_right _ _)
    linarith
  · refine max_le_iff.2 ⟨hap.trans hs1, ?_⟩
    linarith [min_le_left (s - h) (T - 2 * h)]
  · rcases le_total (s - h) (T - 2 * h) with h1 | h1
    · rw [min_eq_left h1]
      linarith [le_max_right aM (s - h)]
    · rw [min_eq_right h1]
      linarith [le_max_right aM (T - 2 * h)]

/-- **The edge clauses at a context.** -/
theorem reconEdge_at
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (ℓ : ℕ) (hcK : 0 < cK) (hc₀ : kW.c₀ = cK) (h128 : 128 ≤ A.Λ) (hjM : j₀ ≤ M)
    (hM1 : 1 ≤ M) (hcP : 0 < cP)
    (hKs : ∀ v, rK c ℓ v ≤ kW.Ks) (hJm : rKmax A ℓ + A.Dt + 2 ≤ kW.Jm)
    (hcapX : ∀ κ : ℕ → ℝ, IsOCBandChain X.α X.q A.Λ X.ζ M κ →
      ocEpsilon X.q A.Λ M ≤ Real.sqrt (κ M / ocA X.α X.q A.Λ M))
    (hwaitX : (|(1 : ℝ)| + 1) * ocTauPP X.α X.q A.Λ M + 6 * A.Jw * ocTauPP X.α X.q A.Λ (M + 1) ≤
      A.T₀)
    (hεε : ocEpsilon c.D.q c.D.Λ M ≤ ocEpsilon c.D.q c.D.Λ (M - 1))
    (Cpad Cage : ℝ) (Npad : ℕ) (Cchart : ℕ → ℝ)
    (hch : ∀ tS : ℝ, IsPreparationChartCertificate X.α X.q A.Λ M (c.D.Φ (M - 1))
      (c.D.hΦ (M - 1)) tS (tS + 2 * ocTauPP X.α X.q A.Λ M) Cpad Cage Npad
      (rKmax A ℓ + A.Dt + 2) Cchart (prepBlock (ocTauPP X.α X.q A.Λ M) tS) 3
      c.Gw.actualFamily) :
    Coeff.ReconEdgeAt c ℓ := by
  have hdata := c.data
  obtain ⟨hα, hq, hΛD, hζ, -, hchain, hterm⟩ := hdata
  have hchart : ∀ tS : ℝ, IsPreparationChartCertificate c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1))
      (c.D.hΦ (M - 1)) tS (tS + 2 * ocTauPP c.D.α c.D.q c.D.Λ M) Cpad Cage Npad
      (rKmax A ℓ + A.Dt + 2) Cchart (prepBlock (ocTauPP c.D.α c.D.q c.D.Λ M) tS) 3
      c.Gw.actualFamily := fun tS => by
    rw [hα, hq, hΛD]
    exact hch tS
  have hcap : ocEpsilon c.D.q c.D.Λ M ≤ Real.sqrt (c.D.κ M / ocA c.D.α c.D.q c.D.Λ M) := by
    rw [hα, hq, hΛD]
    exact hcapX c.D.κ hchain
  have hhX : 0 < ocTauPP X.α X.q A.Λ M :=
    Construction.Stream.ocTauPP_pos (le_trans (by norm_num) h128)
  have hhD : 0 < ocTauPP c.D.α c.D.q c.D.Λ M := by
    rw [hα, hq, hΛD]; exact hhX
  have hW := c.weak
  have haM : c.aM ≤ c.a + 6 * A.Jw * ocTauPP c.D.α c.D.q c.D.Λ (M + 1) := hW.2.1
  have hwait : c.aM + 2 * ocTauPP c.D.α c.D.q c.D.Λ M ≤ c.a + A.T₀ := by
    rw [hα, hq, hΛD] at haM ⊢
    rw [abs_one] at hwaitX
    linarith
  have hap : c.aM ≤ c.tp := by
    have h1 := c.prep.2.1
    have h2 : 0 < c.D.termH M := hhD
    nlinarith
  obtain ⟨CA, hCA, hblock⟩ := reconEdge_block c ℓ hcK hc₀ h128 hjM hM1 hKs hJm hcap hεε Cpad Cage
    Npad Cchart hchart
  refine ⟨CA, hCA, ?_, ?_⟩
  · intro s hs v u d y
    obtain ⟨h1, h2, h3⟩ := reconEdge_blockOf (T := c.a + A.T₀) hhD hwait hap
      (by simpa [rTobs] using hs)
    exact (hblock _ h1 h2 s h3 v u d).2 y
  · intro s hs v u d
    obtain ⟨h1, h2, h3⟩ := reconEdge_blockOf (T := c.a + A.T₀) hhD hwait hap
      (by simpa [rTobs] using hs)
    exact ((hblock _ h1 h2 s h3 v u d).1).aestronglyMeasurable

/-- **The coefficient bounds** with the prefix: the drift and the edge clauses. -/
theorem termReconCoeff : TermReconCoeffStatement := by
  intro ℓ X
  obtain ⟨Λ₁, hΛ₁, hlev⟩ := reconScale_levels X
  refine ⟨Λ₁, hΛ₁, fun A hΛ hV => ?_⟩
  have h128 : 128 ≤ A.Λ := le_trans hΛ₁ hΛ
  have hT0 : 0 < A.T₀ := hV.2.2.2.1.2.1.trans hV.2.2.2.1.2.2.1
  obtain ⟨M₁, -, hM₁⟩ := hlev A.Λ hΛ
  obtain ⟨Cpad, Cage, Npad, Cchart, Mc, hMc⟩ :=
    reconEdge_chart X h128 (rKmax A ℓ + A.Dt + 2)
  obtain ⟨Mp, hMp⟩ := exists_peclet_cap X h128
  obtain ⟨Mw, hMw⟩ := exists_entry_wait X.hα₀ X.hα₁ X.hq (by omega : 2 ≤ A.Λ) 1 A.Jw A.T₀ hT0
  refine ⟨0, fun kc _ => ⟨0, 0, 0, fun sXT sZT _ _ Kout _ => ⟨rKmax A ℓ + A.Dt + 2, ?_⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ hKsS _ _ hJmS cK CK CL Cχ Cread Cid kW hcK hc₀
    hal cP CP cHP Cw Ce cker hcP
  refine ⟨(), 1, 1, le_rfl, one_pos, fun j₀ _ =>
    ⟨max (max M₁ j₀) (max (max Mc Mp) (max Mw 1)), fun M hM c x => ?_⟩⟩
  simp only [max_le_iff] at hM
  obtain ⟨⟨hMM₁, hMj⟩, ⟨hMMc, hMMp⟩, hMMw, hM1⟩ := hM
  have hlv := hM₁ M hMM₁ c.D c.data
  have hW := c.weak
  have hlevM : c.Gw.level = M := hW.2.2.1
  have hnat : ∀ p, IsNaturalPiece c.D (M + A.Jw) M p.1 (c.Gw.actualFamily.piece p) := fun p =>
    (congrArg (fun i => IsNaturalPiece c.D (M + A.Jw) i p.1 (c.Gw.fam.piece p)) hlevM).mp
      (hW.2.2.2.2.2.2.2.2.2.1.1 p)
  have hKmax : ∀ v, rK c ℓ v ≤ rKmax A ℓ := fun v => by
    have := descSlots_le c.Gw.actualFamily A.dW A.Dt v
    show A.k₀ + ℓ + descSlots c.Gw.actualFamily A.dW A.Dt v ≤ A.k₀ + ℓ + A.Dt * A.dW
    omega
  have he := reconEdge_at c ℓ hcK hc₀ h128 hMj hM1 hcP
    (fun v => (hKmax v).trans ((by omega : rKmax A ℓ ≤ rKmax A ℓ + A.Dt + 2).trans
      (hKsS.trans hal.1)))
    (hJmS.trans hal.2.2.2.1) (hMp M hMMp) (hMw M hMMw) (hlv.2.2.1.trans hlv.2.2.2)
    Cpad Cage Npad Cchart (fun tS => hMc M hMMc c.D c.data c.Gw.actualFamily A.Jw hnat
      (c.D.hΦ (M - 1)) tS)
  exact Coeff.reconCoeffAt_of_edge c h128 ℓ he

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end
