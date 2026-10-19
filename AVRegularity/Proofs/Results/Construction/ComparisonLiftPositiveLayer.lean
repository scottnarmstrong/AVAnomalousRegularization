-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.ChildInert.Center
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
import AVRegularity.Construction.FreshAxes.RefFluxContinuous
import AVRegularity.CycleReference.FluxFastDiscrepancy
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
import AVRegularity.Construction.InitialLayer.Comparison
public import AVRegularity.Definitions.Construction.Gen.Majorant
import AVRegularity.Proofs.ComplexContext.Assemble
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal
import AVRegularity.Construction.Preservation.PositiveLayer.Assembly
public import AVRegularity.Definitions.CycleComparison.IsLiftTailPresentation
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.Proofs.ComplexContext.Leaf
import Mathlib.Algebra.Order.Star.Real

section
section
/-! Proof of `appended_child_center`: the appended child's center
trajectory passes at the output time through the family center, from the inverse laws of the
offset flow and of the relative displacement. -/

@[expose] public section

open Homogenization

namespace AVRegularity.Providers

/-- **The appended child's center trajectory passes through the family center**. -/
theorem appended_child_center (D : OCData) (b : ℝ) (j₀ : ℕ) (ch : RealChain)
    (hch : IsAdmissibleChain D b j₀ ch.ctxLevel ch.slot ch) (p' : ℤ) (_hp' : Odd p')
    (_hsch : IsScheduledIn D ch.ctxLevel p' ch.slot)
    (t : ℝ) (_ht : t ∈ ocPulseWindow D.α D.q D.Λ ch.ctxLevel ch.slot) (ζf : Vec 2) :
    ((ch.appendChild D p' t ζf).geom D).1 t ((ch.appendChild D p' t ζf).geom D).2.1
        ((ch.appendChild D p' t ζf).geom D).2.2 =
      (ch.geom D).1 t (ch.geom D).2.1 (ch.geom D).2.2 := by
  obtain ⟨-, -, hlen, -⟩ := hch
  set g := ch.geom D with hg
  have happ : (ch.appendChild D p' t ζf).geom D =
      D.childGeom ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) p')
        ⟨D.eps ch.ctxLevel • D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) p') t ζf,
          ζf + D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) p') t ζf⟩ g := by
    simp only [RealChain.geom, RealChain.appendChild]
    rw [ChainGeometry.geomAux_append D _ _ ch.children _ ch.slots _ hlen]
    have hhead : (ch.slots ++ [p']).headD 0 = ch.slots.headD 0 := by
      cases h : ch.slots with
      | nil => rw [h] at hlen; simp at hlen
      | cons a l => rfl
    have hL : ch.ctxLevel = ch.baseLevel + 1 + ch.children.length := by
      simp only [RealChain.ctxLevel, RealChain.lastLevel]; omega
    rw [hhead, hL]
    rfl
  have hinv : ChainGeometry.InvLaw g :=
    ChainGeometry.invLaw_geomAux D _ _ _ (ChainGeometry.invLaw_base D _ _ _)
  rw [happ]
  set L := ch.ctxLevel
  set s' := D.slotAnchor (L + 1) p'
  set δ := D.relDisp L ch.slot s' t ζf
  simp only [OCData.childGeom]
  rw [hinv]
  by_cases he : D.eps L = 0
  · have h0 : ∀ u r θ, D.relDisp L ch.slot u r θ = 0 := by
      intro u r θ; simp [OCData.relDisp, he]
    simp [h0, he]
  · have harg : (D.eps L)⁻¹ • (g.2.1 + D.eps L • δ) +
        ((ζf + δ) - (D.eps L)⁻¹ • (g.2.1 + D.eps L • δ)) = ζf + δ := by abel
    rw [harg, ChainGeometry.relDisp_inverse, smul_neg, add_neg_cancel_right]

end AVRegularity.Providers
end
end

section
/-! Proof of `appended_child_inert`. -/

@[expose] public section

open Homogenization

namespace AVRegularity.Providers

/-- **The appended child of an admissible context is admissible where its weight is nonzero**. -/
theorem appended_child_inert (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∃ CH Υ : ℝ, 1 ≤ CH ∧ 0 < Υ ∧
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ (m : ℕ), j₀ + 1 ≤ m → ∀ (pc : ℤ) (ch : RealChain), IsAdmissibleChain D bw j₀ (m - 1) pc ch →
    ∀ k : ℤ, Odd k → IsScheduledIn D (m - 1) k pc →
    ∀ t : ℝ, ocCutoff α q Λ m k t ≠ 0 → ∀ ζf : Vec 2,
      IsAdmissibleChain D bw j₀ m k (ch.appendChild D k t ζf) := by
  refine ⟨128, le_refl _, fun Λ hΛ bw hbw _ => ⟨1, 1, le_refl _, one_pos, ?_⟩⟩
  intro D hDα hDq hDΛ hDζ _ j₀ hstart m hm pc ch hch k hk hsch t hcut ζf
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hch hsch
  obtain ⟨hctx, hbase, hlen, hslot, hodd, hsched, hchild⟩ := hch
  have hΛ1 : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hcen := ChildInert.center_bound D (i := i) hΛ1 (by rw [hDζ]; exact hζ) hbw
    (by
      have := hstart.1 i (by omega)
      rw [hDα, hDq, hDΛ]
      linarith) pc k t (by rw [hDα, hDq, hDΛ]; exact hcut) ζf
  have hL : ch.baseLevel + ch.children.length + 1 = i := hctx
  have hslots : ch.slots ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  unfold IsAdmissibleChain IsCarrierChain
  refine ⟨?_, hbase, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RealChain.ctxLevel, RealChain.lastLevel, RealChain.appendChild,
      List.length_append, List.length_singleton]
    omega
  · simp [RealChain.appendChild, hlen]
  · simp [RealChain.slot, RealChain.appendChild]
  · intro q' hq'
    simp only [RealChain.appendChild, List.mem_append, List.mem_singleton] at hq'
    rcases hq' with h | h
    · exact hodd q' h
    · rw [h]; exact hk
  · intro kk hkk
    simp only [RealChain.appendChild, List.length_append, List.length_singleton] at hkk
    by_cases hlt : kk + 1 < ch.slots.length
    · simp only [RealChain.appendChild]
      rw [List.getElem_append_left hlt, List.getElem_append_left (by omega)]
      exact hsched kk hlt
    · have hkk' : kk = ch.children.length := by omega
      subst hkk'
      simp only [RealChain.appendChild]
      have key : ∀ (a b : ℤ) (n : ℕ), a = k → b = pc → n = i → IsScheduledIn D n a b := by
        intro a b n ha hb hn; subst ha hb hn; exact hsch
      refine key _ _ _ ?_ ?_ (by omega)
      · simp [hlen]
      · rw [List.getElem_append_left (by omega)]
        have : ch.slot = pc := hslot
        simp only [RealChain.slot] at this
        rw [← this, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
        simp [hlen]
  · intro kk hkk
    simp only [RealChain.appendChild, List.length_append, List.length_singleton] at hkk
    by_cases hlt : kk < ch.children.length
    · simp only [RealChain.appendChild]
      rw [List.getElem_append_left hlt]
      exact hchild kk hlt
    · have hkk' : kk = ch.children.length := by omega
      subst hkk'
      simp only [RealChain.appendChild]
      rw [List.getElem_append_right (by omega)]
      simp only [Nat.sub_self, List.getElem_singleton]
      have e1 : ch.ctxLevel = i := hctx
      have e2 : ch.slot = pc := hslot
      have e3 : ch.baseLevel + 1 + ch.children.length = i := by omega
      rw [e3, e1, e2]
      have hDe : D.eps i = D.eps i := rfl
      exact hcen

end AVRegularity.Providers
end
end

section
/-! Proof of `fresh_axes_exist`: the reference flux is
continuous and `4τ''`-periodic, so its horizontal entry attains its global maximum on every quiet margin
`[s, s+4h)`; the vertical partner is the half-period shift, the renewal indices are roundings, and
the axes are defined quiet margin by quiet margin from these samples. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

namespace FreshAxes

/-- Every quiet margin has an admissible pulse sample. -/
theorem exists_pulseSample (D : OCData) (b : ℕ) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hν : 0 < D.κ (b + 1)) (s : ℝ) :
    ∃ (tH tV : ℝ) (lH lV : ℤ), IsPulseSample D b s tH tV lH lV := by
  set h := ocTauPP D.α D.q D.Λ (b + 1) with hh
  set J := fun t => ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) t 0 0 with hJ
  have hpos : 0 < h := Construction.Stream.ocTauPP_pos hΛ
  have hper : Function.Periodic J (4 * h) :=
    CycleReference.refFlux_entry_periodic hΛ hζ hν 0 0
  have hcont : Continuous J := refFlux_entry_continuous hΛ hζ hν 0 0
  obtain ⟨tM, htM, hmax⟩ := (isCompact_Icc (a := s) (b := s + 4 * h)).exists_isMaxOn
    (Set.nonempty_Icc.2 (by linarith)) hcont.continuousOn
  set tH := if tM = s + 4 * h then s else tM with htH
  have htHmem : tH ∈ Set.Ico s (s + 4 * h) := by
    rw [htH]; split_ifs with he
    · exact ⟨le_rfl, by linarith⟩
    · exact ⟨htM.1, lt_of_le_of_ne htM.2 he⟩
  have hJtH : J tH = J tM := by
    rw [htH]; split_ifs with he
    · rw [he]; exact (hper s).symm
    · rfl
  have hglob : ∀ t, J t ≤ J tH := by
    intro t
    have hp4 : 0 < 4 * h := by linarith
    have hmem := toIcoMod_mem_Ico hp4 s t
    have heq : J (toIcoMod hp4 s t) = J t := by
      rw [toIcoMod]; exact hper.sub_zsmul_eq _
    rw [← heq, hJtH]
    exact hmax ⟨hmem.1, hmem.2.le⟩
  have hround : ∀ x : ℝ, |x - (⌊x / h + 1 / 2⌋ : ℝ) * h| ≤ h / 2 := by
    intro x
    have h1 := Int.floor_le (x / h + 1 / 2)
    have h2 := Int.lt_floor_add_one (x / h + 1 / 2)
    have hx : x = (x / h) * h := by field_simp
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith
  refine ⟨tH, if tH < s + 2 * h then tH + 2 * h else tH - 2 * h,
    ⌊tH / h + 1 / 2⌋, ⌊(if tH < s + 2 * h then tH + 2 * h else tH - 2 * h) / h + 1 / 2⌋,
    htHmem, hglob, rfl, hround _, hround _⟩

end FreshAxes

end AVRegularity

namespace AVRegularity.Providers

/-- **The fresh kernel axes exist**. -/
theorem fresh_axes_exist (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ →
    ∀ b' : ℕ, 1 ≤ b' → b' < M → ∃ H₁ H₂ : ℝ → Vec 2 →L[ℝ] Vec 2, IsFreshAxes D b' H₁ H₂ := by
  refine ⟨128, le_rfl, fun Λ hΛ D hDα hDq hDΛ hDζ _ M hM b' hb1 hbM => ?_⟩
  have hΛ1 : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hν : 0 < D.κ (b' + 1) :=
    CycleReference.bandChain_pos (by omega) hζ hM (by omega)
  have hsample := fun l : ℤ => FreshAxes.exists_pulseSample D b' hΛ1 hζD hν
    (((l : ℝ) + 1 / 2) * ocTauPP D.α D.q D.Λ (b' + 1))
  choose tH tV lH lV hS using hsample
  set h := ocTauPP D.α D.q D.Λ (b' + 1) with hh
  have hpos : 0 < h := Construction.Stream.ocTauPP_pos hΛ1
  let idx : ℝ → ℤ := fun t => ⌊t / h - 1 / 2⌋
  let axis : (ℤ → ℝ) → (ℤ → ℤ) → ℝ → Vec 2 →L[ℝ] Vec 2 := fun T L t =>
    (Matrix.toLin' (jacMatrix (fun y => D.flowOf b' t y (((idx t : ℝ) + 1 / 2) * h)) 0 *
      sampledEllipse D b' (((idx t : ℝ) + 1 / 2) * h) (T (idx t)) (L (idx t)))).toContinuousLinearMap
  refine ⟨axis tH lH, axis tV lV, fun l => ⟨tH l, tV l, lH l, lV l, hS l, fun t ht => ?_⟩⟩
  have hidx : idx t = l := by
    rw [Int.floor_eq_iff]
    obtain ⟨h1, h2⟩ := ht
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hpos]; linarith
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hpos]; linarith
  simp only [axis, hidx]
  exact ⟨rfl, rfl⟩

end AVRegularity.Providers
end
end

section
/-! Proof of `comparison_lift_initial_layer` (`1 ≤ sZ`). -/

@[expose] public section

open Homogenization

namespace AVRegularity.Providers

/-- **Initial-layer comparison of the original-start and the clipped-start lifts**. -/
theorem comparison_lift_initial_layer {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    {Dm : ℕ} (Q : LiftOperatorData ι h Dm) (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (t₀ t₀' t₁ : ℝ) (N H : ℕ)
    (ht : t₀ ≤ t₀') (_ht' : t₀' ≤ t₁) (hN : 1 ≤ N)
    (Cc Cc' : ℕ → ℕ → LiftCoeff ι h) (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)
    (hC' : IsLiftSequence Q sX sZ t₀' t₁ N H Cc') :
    ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ X,
      IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ t₀' t₁
        (fun z => liftApply 1 (Cc 0 1) (fun _ => a₀) t₀' X z)
        (fun _ _ => 0)
        (fun t z => liftApply 1 (Cc 0 1) (fun _ => a₀) t X z -
          liftApply 1 (Cc' 0 1) (fun _ => a₀) t X z) :=
  InitialLayer.comparison_lift_initial_layer_of_one_le_sZ Q sX sZ hsZ t₀ t₀' t₁ N H ht hN Cc Cc'
    hC hC'

end AVRegularity.Providers
end
end

section
/-! Proof of `lift_sequence_unique_elliptic`: uniqueness of the lift sequence for a
symmetric positive definite metric, from the window uniqueness of the finite-past mean-zero cell
inverse (`AVRegularity.Uniqueness.lift_sequence_unique_window`). -/

@[expose] public section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity.Providers

/-- **Uniqueness of the lift sequence for a symmetric positive definite metric**. -/
theorem lift_sequence_unique_elliptic {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    {Dm : ℕ} (Q : LiftOperatorData ι h Dm) (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁)
    (hsymm : ∀ t X i j, Q.G t X i j = Q.G t X j i)
    (hGmeas : ∀ X i j, Measurable fun t => Q.G t X i j)
    (hpos : ∀ X, ∃ lo hi : ℝ, 0 < lo ∧ ∀ t ∈ Set.Icc t₀ t₁, ∀ ξ : Vec 2,
      lo * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, Q.G t X i j * ξ i * ξ j ∧
        ∑ i, ∑ j, Q.G t X i j * ξ i * ξ j ≤ hi * ∑ i, ξ i ^ 2)
    (hvmeas : ∀ z, Measurable fun t => Q.v t z)
    (hvbd : ∃ Mv : ℝ, ∀ t z, ‖Q.v t z‖ ≤ Mv)
    (sX sZ N H : ℕ) (Cc Cc' : ℕ → ℕ → LiftCoeff ι h)
    (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (hC' : IsLiftSequence Q sX sZ t₀ t₁ N H Cc') :
    ∀ hh ≤ H, ∀ n m (α : DerivativeWord2 m), ∀ t ∈ Set.Icc t₀ t₁, ∀ X z v u,
      Cc hh n m α t X z v u = Cc' hh n m α t X z v u := by
  -- measurability is part of the stated premises; the window argument does not use it
  have _ := hGmeas
  have _ := hvmeas
  obtain ⟨Mv, hMv⟩ := hvbd
  refine AVRegularity.Uniqueness.lift_sequence_unique_window Q t₀ t₁ ht ?_ sX sZ N H Cc Cc' hC hC'
  intro X
  obtain ⟨lo, hi, hlo, hq⟩ := hpos X
  exact ⟨lo, hi, Mv, AVRegularity.Uniqueness.windowData_of_elliptic
    (fun t => Matrix.of (Q.G t X)) Q.v t₀ t₁ lo hi Mv (fun t => hsymm t X 0 1) hlo
    (fun t ht ξ => hq t ht ξ) (fun t _ z => hMv t z)⟩

end AVRegularity.Providers
end
end
end

section
section
/-! Proof of `gen_carrier_calculus`. The proof is the induction on generated expressions
(`ComplexContext.genInv_of_denotes`) with the standing facts of the data
(`ComplexContext.complexContextBase_of_data`), the constants `ComplexContext.complexContextKappa`,
the constructors of `ComplexContext.complexContextInputs`, `Λ₀` of the drift bound
(`ComplexContext.drift_scale_bound`) and `Υ₀ = 100`; the extension is trimmed to the outer carrier
(`ComplexContext.trimExt`). -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.Providers

/-- **The holomorphic carrier calculus of generated expressions**. -/
theorem gen_carrier_calculus (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∃ Υ₀ : ℝ, ∀ (CH Υ : ℝ), CarrierOK Υ₀ CH Υ → ∃ κ : MajConsts, MajOK bw κ ∧
    ∀ (j₀ : ℕ), IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (i : ℕ) (p : ℤ), 1 ≤ i → j₀ ≤ i → Odd p → ∀ (Δ : ℝ), 0 < Δ →
    ∀ (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)),
      LeavesCertified D bw j₀ leaf →
    ∀ (e : Gen .ctx i p), Gen.IsScheduled D e → Gen.SolvedFree leaf e →
    ∀ (f : GenSort.Sem .ctx), Gen.Denotes D bw j₀ e f →
    ∃ F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ,
      IsHolExtension D bw j₀ i p f F ∧
      ∀ (mres : ℝ), 0 ≤ mres → mres ≤ 2 → ∀ h : ℤ, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p,
        ctxModeSupAt D bw j₀ i p F mres h t ≤ genMode D κ Δ leaf e mres h t := by
  obtain ⟨Λ₀, hΛ₀, hdrift⟩ := ComplexContext.drift_scale_bound hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ bw hbw0 hbw1 => ?_⟩
  obtain ⟨Cd, hCd0, hCd⟩ := hdrift Λ hΛ
  refine ⟨100, fun CH Υ hCΥ => ⟨ComplexContext.complexContextKappa bw Cd, ComplexContext.complexContextKappa_majOK hCd0.le, ?_⟩⟩
  intro j₀ hcs D hDα hDq hDΛ hDζ hΦ M hκ hterm i p hi hij hp Δ hΔ leaf hL e hsch hsf f hden
  have hB := ComplexContext.complexContextBase_of_data hα₀ hα₁ hs₀ hs₁ hq hζ (hΛ₀.trans hΛ) Cd hbw0 hbw1 hCΥ hcs
    D hDα hDq hDΛ hDζ hΦ M hκ hterm
  have hP := ComplexContext.complexContextInputs hB hΔ
  have hCd' : ∀ i, (fun _ : ℕ => True) i → 1 ≤ i →
      D.eps i ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap i * D.kap (i - 1)) := by
    subst hDα hDq hDΛ hDζ hterm
    exact fun i _ hi => hCd D.term D.κ hκ i hi
  obtain ⟨F, hF⟩ := ComplexContext.genInv_of_denotes hB hP hL (fun _ => True) hCd' hden hsch hsf
    (ComplexContext.driftIn_true leaf e) hij hi hp
  exact ⟨ComplexContext.trimExt D bw F, hF.isHolExtension hB.env.hΛ1 hbw0,
    fun mres hm0 hm2 h t ht => hF.ctxModeSupAt_trim_le hbw0 hm0 hm2 h ht⟩

end AVRegularity.Providers
end
end

section
/-! Proof of `successor_generated`. With `Λ₀ = 128` and `c₀max = 1`:
* the start bound of the appended children follows from `IsCarrierStart` with `1 ≤ CH`, `1 ≤ Υ`
  (`startBound_of_carrierStart`);
* the generated, slotwise transverse, context-certified stage `G` is read off the stage invariant;
* the context strain along recentering is `C^∞` (`contDiff_contextStrain_recenter`);
* every coefficient of the extended next family is generated (`successorGeneration_isExprFor`: the
  non-diagonal sources through the transfer of their finer outputs, the first source through
  `firstSource_ctxRep`), under the standard lift reserves;
* the next family is slotwise structurally transverse (`successorGeneration_slotTransverse`): the
  exports of a cascade stage are the certified seed exports (`IsSlotParInvCtx`), and the restricted
  parallel invariance applies to scheduled expressions, whose child evaluations pass to odd slots. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.Providers.GenSem
open scoped ENNReal

namespace AVRegularity.Providers

/-- **Generation: the coefficients of the next family are scheduled generated expressions**
    (Definition 10.3 of the paper). -/
theorem successor_generated (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∀ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH → 1 ≤ Υ → ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∀ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ mStar : ℕ,
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      (∃ tA : ℝ, tS ≤ tA ∧
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G) →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
      (∀ v' u' (γ' : G'.fam.Γ v' u') (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2),
        ∃ e : (p : OddSlot) → Gen .ctx G'.level p.1, G'.IsExprFor v' u' γ' d I c e) ∧
      G'.IsSlotTransverse := by
  refine ⟨128, le_refl _, fun Λ hΛ => ⟨1, one_pos, ?_⟩⟩
  intro _ _ _ _ _ _ bw hbw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hsch _ _ _ hsX hsZ _ _ _ hCH hΥ _ _ _ _ _ _ j₀ _ hcs _ D hDα hDq hDΛ hDζ _ _ hκ hterm _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ hseed _ _ hmn hnM G G' hcas hlev hinv hSucc
  have hΛ1 : 1 ≤ D.Λ := by rw [hDΛ]; exact le_trans (by norm_num) hΛ
  have hζD : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hκD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    rw [hDα, hDq, hDΛ, hDζ, hterm]; exact hκ
  have hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ bw / (64 * (8 * Real.pi ^ 2)) := by
    rw [hDα, hDq, hDΛ]; exact startBound_of_carrierStart (hDΛ ▸ hΛ1) hCH hΥ hcs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hH, hN, -, -⟩ := hsch
  obtain ⟨-, -, -, -, -, -, -, -, hexpS, -⟩ := hseed
  obtain ⟨tA, -, hI⟩ := hinv
  obtain ⟨-, -, hG, -, hT, hcert, -⟩ := hI
  have hlevel : G.level ≤ D.term := by rw [hterm, hlev]; exact hmn.trans hnM.le
  have htop : ∀ r : ℕ, ((r : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun r => by
    exact_mod_cast le_top
  have hSreg : ∀ (pc : ℤ) (t : ℝ) (ch : RealChain) (z : Vec 2),
      IsAdmissibleChain D bw j₀ G'.level pc ch → ∀ a c,
        ContDiff ℝ ((4 * p : ℕ) : WithTop ℕ∞) (fun y =>
          contextStrain D G'.level pc t (ch.recenter D y) (z + (D.eps G'.level)⁻¹ • y) a c) :=
    fun pc t ch z hA a c =>
      (contDiff_contextStrain_recenter D hζD G'.level pc t ch hA.2.2.1 z a c).of_le (htop (4 * p))
  have hE := successorGeneration_isExprFor hΛ1 hζD hκD hbw hstart hN hH hsX hsZ G G' hG hT hcert hlevel hSucc
    hSreg
  exact ⟨hE, successorGeneration_slotTransverse hΛ1 hζD hbw hstart (fun i p e he => (hexpS i p e he).2.1) hcas
    hSucc hE⟩

end AVRegularity.Providers
end
end

section
/-! Proof of the positive-layer estimate. The cell-amplitude decay
and same-order entrance/Fourier-window conversions give the statement. -/
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers

/-- **Positive-grade initial layer**. -/
theorem comparison_lift_positive_layer (Dm N H K L k sX sZ : ℕ) (hN : 1 ≤ N) (hD : 2 ≤ Dm)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
      (Q : LiftOperatorData ι h Dm) (π : ι → ℝ) (sOld sNew s₁ e ν B ρ E ℓ dstar εc lam : ℝ)
      (par : Fin 2) (V : ℝ → ℝ → ℝ) (bb : ι → ι → ℝ) (Θ : ℝ),
      IsLiftSetting Q π sOld s₁ e ν B ρ E ℓ dstar εc lam par V H N (K + Dm * (H + 1) * N) k
        (L + Dm * (H + 1) * N + 2) (K + Dm * (H + 1) * N + 4 * (H + 1) * (N + Dm) ^ 2)
        (max k (L + Dm * (H + 1) * N + 4) + H * Dm + 2 * N + 2 * Dm) CG Cw Cj bb Θ →
      sX ≤ K + Dm * (H + 1) * N + 4 * (H + 1) * (N + Dm) ^ 2 →
      sZ ≤ max k (L + Dm * (H + 1) * N + 4) + H * Dm + 2 * N + 2 * Dm →
      sOld ≤ sNew →
    ∀ Cc Cc' : ℕ → ℕ → LiftCoeff ι h,
      IsLiftSequence Q sX sZ sOld s₁ N H Cc → IsLiftSequence Q sX sZ sNew s₁ N H Cc' →
    ∀ a b : ℝ, sNew ≤ a → a ≤ b → b ≤ s₁ →
      (∀ t ∈ Set.Icc a b, ∀ z, Q.v t z = 0) →
      (∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α, IsFastIndependentOn (Set.Icc a b) (γ.coeff α)) →
    ∀ hh ≤ H, ∀ s : ℝ, a ≤ s → s + 1 ≤ b →
      layerNorm π (liftDiff Cc Cc') hh N K L (Set.Icc s (s + 1)) ≤
        ENNReal.ofReal (C * Real.exp (-(c * (s - a)))) *
          ∑ b' ∈ Finset.range (hh + 1), ENNReal.ofReal Θ ^ (hh - b') *
            entranceNorm π (liftDiff Cc Cc') b' N (K + Dm * (H + 1) * N)
              (L + Dm * (H + 1) * N + 4) a :=
  Construction.Preservation.PositiveLayer.comparison_lift_positive_layer_of_ingredients
    Dm N H K L k sX sZ hN hD CG Cw Cj


end AVRegularity.Providers
end
end
end
