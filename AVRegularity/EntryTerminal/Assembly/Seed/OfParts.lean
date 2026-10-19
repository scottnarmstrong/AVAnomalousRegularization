-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Assembly.Seed.PricedSchur
public import AVRegularity.EntryTerminal.Assembly.Seed.SeedLedgerAssembly
import AVRegularity.EntryTerminal.Ingredients.SeedStruct.SeedStruct
import AVRegularity.EntryTerminal.Ingredients.SeedKernel.SeedKernel
import AVRegularity.EntryTerminal.Ingredients.SeedQuiet.Proof
import AVRegularity.EntryTerminal.Ingredients.ScaleFacts.ScaleFacts
import AVRegularity.Construction.Preservation.FullLift.NativeHigherRetainedFromSameOrder
import AVRegularity.Definitions.Finite.FiniteLiftBridge
import AVRegularity.EntryTerminal.Ingredients.Frontier.InnerWrappers

section
section
/-! **`RetainedPricePart` is proved, and with it `SeedRetainedPart`.**

For each order `kk ≤ K̂`, `uniform_native_identity_kernel_price` gives a constant `A_kk` and a level
`m₀(kk)` (independent of the level `M` and of the datum); `C = 1 + Σ A_kk`. The carrier pair and the
`C_w` floor are those of `termCertBlock_exists`; the level threshold is the maximum of the
`m₀`'s, the scale threshold of `seedStruct_scales`, and `j₀ + 1`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity

namespace AVRegularity.EntryTerminal.Route

/-- **The identity price of the retained family.** -/
theorem retainedPricePart : RetainedPricePart := by
  intro X
  obtain ⟨Λc, hΛc, hcert⟩ := termCertBlock_exists X
  obtain ⟨Λs, hΛs, hsc⟩ := AVRegularity.EntryTerminal.Ingredients.seedStruct_scales X
  refine ⟨max Λc Λs, le_trans hΛc (le_max_left _ _), fun A hΛ hA Kout => ?_⟩
  have hΛc' : Λc ≤ A.Λ := le_trans (le_max_left _ _) hΛ
  have hΛs' : Λs ≤ A.Λ := le_trans (le_max_right _ _) hΛ
  have hΛ128 : 128 ≤ A.Λ := le_trans hΛc hΛc'
  refine ⟨max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2, max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2,
    fun sXT sZT hX hZ => ?_⟩
  let F0 : SeedFloors :=
    { cker := fun _ _ => 0
      Γk := fun _ => 0
      Cwid := fun _ => 0
      Ca := fun _ => 0
      Cm := fun _ _ => 0 }
  refine ⟨0, F0, fun Lt nW cr kS hplan cK CL Cχ kW hcK hkW halloc cP CP hcP => ?_⟩
  have hcker : ∀ j, 0 ≤ kS.cker j := fun j => (hplan.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2).1 j
  have hcr0 : 0 < cr := hplan.2.2.2.2.1
  have hcr1 : cr ≤ 1 := hplan.2.2.2.2.2.1
  have hP := termPlanHyp_of_plan hA hΛ128 hplan halloc hX hZ
  show RetainedPriceBlock A Kout sXT sZT nW cr kS CL Cχ kW cP CP
  intro cH hcH
  obtain ⟨Cw₀, CHe, Υe, hCw₀, hCHe, hΥe, hrest⟩ :=
    hcert A hΛc' sXT sZT nW cr kW CL Cχ cP CP hP hcr0 hcr1 cH hcH
  refine ⟨Cw₀, CHe, Υe, hCw₀, hCHe, by linarith, fun Cw hCw j₀ hj => ?_⟩
  -- the constants of the uniform price, one for each order `kk ≤ K̂`
  have hbw : 0 < A.bw := hA.2.2.1.1
  have hprices (i : Fin (A.Khat Kout + 1)) :=
    AVRegularity.Construction.Preservation.FullLift.uniform_native_identity_kernel_price
      X.α X.s X.q X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq A.Λ hΛ128 X.ζ X.hζ A.bw hbw i.1 (i.1 + A.Dt)
      A.Dt le_rfl kS.cker (fun j _ => hcker j)
  choose Ai hAi mo hmo hunif using hprices
  let C : ℝ := 1 + ∑ i : Fin (A.Khat Kout + 1), Ai i
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hAi i)
  have hAC (i : Fin (A.Khat Kout + 1)) : Ai i ≤ C :=
    (Finset.single_le_sum (fun j _ => hAi j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))
  let mp := ∑ i : Fin (A.Khat Kout + 1), mo i
  have hmp (i : Fin (A.Khat Kout + 1)) : mo i ≤ mp :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  obtain ⟨Mc, hMc⟩ := hrest Cw hCw j₀ hj
  obtain ⟨Ms, hMs2, hMs⟩ := hsc A.Λ hΛs' cr A.σw A.tT CL hcr0
    (hA.2.2.2.1.2.2.2.2.1.le) (by
      obtain ⟨-, -, -, -, -, hsched, -⟩ := hA
      obtain ⟨-, -, -, -, -, -, -, -, htT, -⟩ := hsched
      exact htT.le)
  refine ⟨C, hC, max Mc (max Ms (max (mp + 2) (j₀ + 1))), fun M hM => ?_⟩
  have hMc' : Mc ≤ M := le_trans (le_max_left _ _) hM
  have hMs' : Ms ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hMp : mp + 2 ≤ M :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hM
  have hMj : j₀ + 1 ≤ M :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hM
  have hM2 : 2 ≤ M := le_trans hMs2 hMs'
  intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hG
  have hctx' := TermPassCtx.of_seedCtx hctx
  obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := hctx'.1
  obtain ⟨-, hrho, -, hCL⟩ := hMs M hMs' D hα hq hΛD hband
  exact retainedPrice_ctx hctx' hA hΛ128 hcr0 hG (by linarith) (by linarith) hj hX hZ hMj hM2
    hP.hGH hrho hCL (fun kk hkk => ⟨Ai ⟨kk, by omega⟩, hAi _, hAC _, mo ⟨kk, by omega⟩,
      by have := hmp ⟨kk, by omega⟩; omega,
      fun D hDα hDq hDΛ hDζ hseq => hunif ⟨kk, by omega⟩ ScalarH D hDα hDq hDΛ hDζ hseq⟩)

/-- **`SeedRetainedPart` is proved.** -/
theorem seedRetainedPart : SeedRetainedPart :=
  seedRetainedPart_of_price retainedPricePart retainedPricedSchurPart

end AVRegularity.EntryTerminal.Route
end
end

section
/-! Quantitative decay of the retained ledger and the marked ledger. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Ledger
namespace AVRegularity.EntryTerminal.Route

theorem retainedDecayPart : RetainedDecayPart := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ hA Kout => ⟨0, 0, fun sXT sZT _ _ => ?_⟩⟩
  let F0 : SeedFloors :=
    { cker := fun _ _ => 0
      Γk := fun _ => 0
      Cwid := fun _ => 0
      Ca := fun _ => 0
      Cm := fun _ _ => 0 }
  refine ⟨0, F0, fun Lt nW cr kS hplan cK CL Cχ kW hcK hkW halloc cP CP hcP => ?_⟩
  intro cH Cw hcH hCw
  refine ⟨1, 1, 1, le_rfl, one_pos, fun Ce hCe j₀ _ => ?_⟩
  have hA' := hA
  obtain ⟨-, -, -, ⟨-, -, -, -, -, -, hχw, hη₀, -⟩, -⟩ := hA'
  have hθ : 0 < ocDelta X.α X.q - A.η₀ - A.tT * (termExcess A.NT A.pT A.alph : ℝ) - A.η₀ / 4 := by
    have h1 := AVRegularity.Construction.Residual.Presentation.termFresh_exponent_facts (A := A) hA
    have h2 : 0 < ocDelta X.α X.q := ocDelta_pos_of_admissible X.hα₀ X.hq
    linarith
  have hwc : 0 < max 1 A.nWords := lt_of_lt_of_le one_pos (le_max_left _ _)
  set T : ℝ := ((wordsUpTo A.alph (A.RT + 1)).card : ℝ) with hT
  set L : ℝ := (A.alph.card : ℝ) with hL
  have hT0 : 0 ≤ T := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have hCw1 : 0 < Cw + 1 := by linarith
  have hsq : 0 ≤ Real.sqrt (((max 1 A.nWords : ℕ) : ℝ) / cH) := Real.sqrt_nonneg _
  obtain ⟨M₁, hM₁⟩ := small_core X.hq.1 (Nat.le_trans hΛ le_rfl) hχw hθ (half_pos hη₀)
    (4 * (T + 1) * (Cw + 1))
    (2 * (T + 1) * (L + 1) * (Cw + 1) * (1 + Real.sqrt (((max 1 A.nWords : ℕ) : ℝ) / cH)))
    Cχ 1 cH (max 1 A.nWords) (by positivity) (by positivity) (by norm_num) hcH hwc
  obtain ⟨hτpos, hτχ, hτθ, -⟩ := hA.2.2.2.2.2.2.1
  obtain ⟨M₂, hM₂⟩ := child_power_small X.hq.1 X.hq.2.1 hΛ hχw hτχ
    (K := 4 * (T + 1) * (Cw + 1) * (|Cχ| + 1)) (by positivity)
    (c := Ce / 2) (by positivity)
  have hτθ' : A.τe < ocDelta X.α X.q - A.η₀ -
      A.tT * (termExcess A.NT A.pT A.alph : ℝ) - A.η₀ / 4 := by
    linarith only [hτθ]
  obtain ⟨M₃, hM₃⟩ := parent_power_small X.hq.1 hΛ hτθ'
    (2 * (T + 1) * (L + 1) * (Cw + 1) *
      (1 + Real.sqrt (((max 1 A.nWords : ℕ) : ℝ) / cH))) (c := Ce / 2) (by positivity)
  refine ⟨max M₁ (max M₂ M₃), fun M hM => ?_⟩
  intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  refine ⟨zero_le_one.trans hCe, ?_⟩
  have hctx' := TermPassCtx.of_seedCtx hctx
  obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := hctx'.1
  obtain ⟨-, -, hcHeq, hiota, hwcEq, hetaB, -⟩ := hctx'.2.2.2.2.2.1
  obtain ⟨h1, h2, h3⟩ := hM₁ M ((le_max_left _ _).trans hM)
  have hq1 : 1 < D.q := by rw [hq]; exact X.hq.1
  have hΛ128 : 128 ≤ D.Λ := by rw [hΛD]; exact hΛ
  have hepsM : D.eps M = ocEpsilon X.q A.Λ M := by simp only [OCData.eps, hq, hΛD]
  have hepsM1 : D.eps (M - 1) = ocEpsilon X.q A.Λ (M - 1) := by simp only [OCData.eps, hq, hΛD]
  have hF1 : ∀ marked, 1 ≤ birthDiagonalFactor D.q D.Λ M lawT marked := by
    intro marked
    refine birthFactor_ge_one hq1 hΛ128 lawT hiota ?_ marked
    rw [hcHeq, hwcEq, hetaB, hq, hΛD]
    exact h1
  have hSw : max (Cχ * D.eps M ^ A.χw) 0 ≤ (|Cχ| + 1) * ocEpsilon X.q A.Λ M ^ A.χw := by
    rw [hepsM]
    have he : 0 ≤ ocEpsilon X.q A.Λ M ^ A.χw :=
      Real.rpow_nonneg (AVRegularity.Scales.epsilon_basic (m := M) X.hq.1 hΛ).1.le _
    refine max_le ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right
      ((le_abs_self Cχ).trans (by linarith only [abs_nonneg Cχ])) he
  have hsmall : AVRegularity.Construction.Preservation.Assembly.ledgerTransportConstant Cw
      (wordsUpTo A.alph (A.RT + 1)).card * max (Cχ * D.eps M ^ A.χw) 0 ≤ 1 / 2 := by
    have hSw0 : 0 ≤ max (Cχ * D.eps M ^ A.χw) 0 := le_max_right _ _
    have hTc : AVRegularity.Construction.Preservation.Assembly.ledgerTransportConstant Cw
        (wordsUpTo A.alph (A.RT + 1)).card ≤ 4 * (T + 1) * (Cw + 1) := by
      unfold AVRegularity.Construction.Preservation.Assembly.ledgerTransportConstant
      rw [hT]; nlinarith
    have hC16 : 1 / (16 * (1 : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    calc _ ≤ (4 * (T + 1) * (Cw + 1)) * ((|Cχ| + 1) * ocEpsilon X.q A.Λ M ^ A.χw) :=
          mul_le_mul hTc hSw hSw0 (by positivity)
      _ ≤ 1 / (16 * (1 : ℝ)) := h2
      _ ≤ 1 / 2 := hC16
  have hled := termRetained_ledger_le hctx' hA hΛ hCw hF1 hsmall
  rw [hwcEq, hcHeq] at hled
  rw [hepsM1] at hled
  have hd2 := hM₂ M ((le_max_left _ _).trans ((le_max_right _ _).trans hM))
  have hd3 := hM₃ M ((le_max_right _ _).trans ((le_max_right _ _).trans hM))
  have hweak : 4 * (T + 1) * (Cw + 1) * max (Cχ * D.eps M ^ A.χw) 0 ≤
      Ce / 2 * ocEpsilon X.q A.Λ (M - 1) ^ A.τe := calc
    _ ≤ 4 * (T + 1) * (Cw + 1) * ((|Cχ| + 1) * ocEpsilon X.q A.Λ M ^ A.χw) :=
      mul_le_mul_of_nonneg_left hSw (by positivity)
    _ ≤ _ := by rw [← mul_assoc]; exact hd2
  have hfresh : 2 * (T + 1) * (L + 1) * (Cw + 1) *
      ((1 + Real.sqrt (((max 1 A.nWords : ℕ) : ℝ) / cH)) *
        ocEpsilon X.q A.Λ (M - 1) ^
          (ocDelta X.α X.q - A.η₀ - A.tT * (termExcess A.NT A.pT A.alph : ℝ) - A.η₀ / 4)) ≤
      Ce / 2 * ocEpsilon X.q A.Λ (M - 1) ^ A.τe := by
    rw [← mul_assoc]
    exact hd3
  rw [hepsM1]
  linarith only [hled, hweak, hfresh]

/-- the marked ledger: the marked ledger bound of the encoded seed. -/
theorem seedLedgerPart : SeedLedgerPart :=
  seedLedgerPart_of_retainedDecay retainedDecayPart

end AVRegularity.EntryTerminal.Route
end
end
end

section
@[expose] public section
open AVRegularity.EntryTerminal.Ingredients
namespace AVRegularity.EntryTerminal.Route

/-! **The seed clauses statement with its proved parts plugged in.** Four of the six parts of
`seedClauses_of_parts` are proved: the structure (`seedStruct`), the kernels (`seedKernel`), the
quiet structure (`seedQuietPart`) and the retained certificates (`seedRetainedPart`). So the seed clauses statement
depends exactly on the certification (`SeedCertPart`) and the envelopes
(`SeedEnvelopePart`). The certification is proved (`seedCertPart`), so the seed clauses statement depends only on the
envelopes (`seedClauses_of_env`). -/

/-- **The seed clauses statement from the certification and the envelopes.** -/
theorem seedClauses_of_cert_env (hC : SeedCertPart) (hE : SeedEnvelopePart) :
    SeedClausesStatement :=
  seedClauses_of_parts seedStruct hC seedKernel hE seedQuietPart seedRetainedPart scaleFacts

/-- **The seed clauses statement from the envelopes alone.** -/
theorem seedClauses_of_env (hE : SeedEnvelopePart) : SeedClausesStatement :=
  seedClauses_of_cert_env seedCertPart hE

end AVRegularity.EntryTerminal.Route
end
end
