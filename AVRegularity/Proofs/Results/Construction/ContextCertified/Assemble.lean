-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Construction.Gen.Majorant

@[expose] public section

section
open Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.GenStage

/-! Structural reductions for `successor_context_certified`: a context certificate contains the
generation data (`IsContextCertified.isGenerated`), and certificates pass to restrictions, in
particular to the retained part of a next family (`IsContextCertified.retained`). The analytic
content of the statement is therefore exactly the certificate of the extended next family. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- A context certificate contains the generation data. -/
theorem IsContextCertified.isGenerated {k : InvConsts} {G : GenStage D hr Dm b j₀}
    (h : G.IsContextCertified k) : G.IsGenerated := by
  intro p v u γ d I c
  obtain ⟨_, _, _, hc⟩ := h v u γ
  obtain ⟨f, _, hf, _⟩ := hc d I c
  exact ⟨f p, (hf p).1, (hf p).2.2⟩

/-- Context certificates pass to restrictions. -/
theorem IsContextCertified.restrict {k : InvConsts} {G : GenStage D hr Dm b j₀}
    (h : G.IsContextCertified k) (S : Finset Comp) (hS : S ⊆ G.comps) :
    (G.restrict S hS).IsContextCertified k :=
  fun v u γ => h ⟨v.1, hS v.2⟩ ⟨u.1, hS u.2⟩ γ

/-- The retained part of a certified family is generated and certified. -/
theorem IsContextCertified.retained {k : InvConsts} {G' : GenStage D hr Dm b j₀}
    (h : G'.IsContextCertified k) (m H J : ℕ) :
    (G'.retained m H J).IsGenerated ∧ (G'.retained m H J).IsContextCertified k :=
  ⟨(h.restrict _ _).isGenerated, h.restrict _ _⟩

end AVRegularity.GenStage
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.GenStage

/-! Assembly at the instantiated level: the carrier calculus (the conclusion of
`gen_carrier_calculus` at fixed constants `κ`) and the ledger witnesses (the conclusion of
`successor_ledger` for the family) give the context certificate. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem compReserve_le_two (k : InvConsts) (c : Comp) : compReserve k c ≤ 2 := by
  unfold compReserve
  have : 0 ≤ ((k.G0 + compGrade c : ℕ) : ℝ) / ((k.Hprod : ℝ) + 1) := by positivity
  linarith

/-- The mode supremum over the output window is the supremum of the mode suprema at fixed time. -/
theorem ctxModeSup_le_iSup_ctxModeSupAt (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ)
    (F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ) (mres : ℝ) (h : ℤ) :
    ctxModeSup D b j₀ i p F mres h ≤
      ⨆ t ∈ ocPulseWindow D.α D.q D.Λ i p, ctxModeSupAt D b j₀ i p F mres h t := by
  unfold ctxModeSup ctxModeSupAt
  refine iSup₂_le fun dd n => iSup_le fun hex => iSup₂_le fun t ht => iSup₂_le fun x hx =>
    iSup_le fun hre => ?_
  exact le_iSup₂_of_le t ht (le_iSup₂_of_le dd n (le_iSup_of_le hex (le_iSup₂_of_le x hx
    (le_iSup_of_le hre le_rfl))))

/-- **The context certificate from the carrier calculus and the ledger.** -/
theorem isContextCertified_of_gates (G : GenStage D hr Dm b j₀) (k : InvConsts) (κ : MajConsts)
    (hcalc : ∀ (p : ℤ), Odd p → ∀ (Δ : ℝ), 0 < Δ →
      ∀ (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)),
        LeavesCertified D b j₀ leaf →
      ∀ (e : Gen .ctx G.level p), Gen.IsScheduled D e → Gen.SolvedFree leaf e →
      ∀ (f : GenSort.Sem .ctx), Gen.Denotes D b j₀ e f →
      ∃ F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ,
        IsHolExtension D b j₀ G.level p f F ∧
        ∀ (mres : ℝ), 0 ≤ mres → mres ≤ 2 → ∀ h : ℤ, ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p,
          ctxModeSupAt D b j₀ G.level p F mres h t ≤ genMode D κ Δ leaf e mres h t)
    (hres : ∀ v : CompIn G.comps, 0 ≤ compReserve k v.1)
    (hled : ∀ v u (γ : G.fam.Γ v u), ∃ θ : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ,
        (∀ d α c, 0 ≤ θ d α c) ∧
        (∀ d, 2 ≤ d → d ≤ (G.fam.identity v u γ).maxOrder →
          (D.eps G.level / (G.fam.identity v u γ).record.length) ^ (d - 2) *
              ∑ α, ∑ c, θ d α c ≤ (G.fam.identity v u γ).record.size) ∧
        ∀ (d : ℕ) (α : DerivativeWord2 (d - 1)) (c : Fin 2),
          ∃ (e : (p : OddSlot) → Gen .ctx G.level p.1) (Δ : ℝ)
            (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)),
            G.IsExprFor v u γ d α c e ∧ 0 < Δ ∧ LeavesCertified D b j₀ leaf ∧
            (∀ p, Gen.SolvedFree leaf (e p)) ∧
            ∑' h : ℤ, ENNReal.ofReal (Real.exp (3 * Real.pi * b * |(h : ℝ)|) *
                (1 + |(h : ℝ)|) ^ k.Lstar) *
              ⨆ p : OddSlot, ⨆ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
                genMode D κ Δ leaf (e p) (compReserve k v.1) h t
              ≤ ENNReal.ofReal (θ d α c)) :
    G.IsContextCertified k := by
  classical
  intro v u γ
  obtain ⟨θ, hθ0, hθr, hθ⟩ := hled v u γ
  refine ⟨θ, hθ0, hθr, fun d α c => ?_⟩
  obtain ⟨e, Δ, leaf, hE, hΔ, hL, hSF, hsum⟩ := hθ d α c
  choose f hf using fun p : OddSlot => (hE p).2.2
  have hF := fun p : OddSlot =>
    hcalc p.1 p.2 Δ hΔ leaf hL (e p) (hE p).1 (hSF p) (f p) (hf p).1
  choose F hF using hF
  refine ⟨f, F, fun p => ⟨⟨e p, (hE p).1, (hE p).2.1, (hf p).1⟩, (hF p).1, (hf p).2⟩, ?_⟩
  refine le_trans ?_ hsum
  unfold ctxSize
  refine ENNReal.tsum_le_tsum fun h => ?_
  gcongr with p
  exact (ctxModeSup_le_iSup_ctxModeSupAt D b j₀ G.level p.1 (F p) _ h).trans
    (iSup₂_mono fun t ht => (hF p).2 _ (hres v) (compReserve_le_two k v.1) h t ht)

end AVRegularity.GenStage
end
