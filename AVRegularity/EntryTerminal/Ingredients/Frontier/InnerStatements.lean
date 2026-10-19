-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Ledger.ActualSourceSums
public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovTruncGDecomp
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovCommTime
import AVRegularity.EntryTerminal.Ingredients.SeedStruct.SeedStruct
import AVRegularity.IterationPassage.Passage.Profiles.ClausesStatement
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.FluxBoundBasic
import AVRegularity.Construction.Preservation.Frontier.LengthPrice.Producer
public import AVRegularity.Construction.Preservation.Frontier.GradeSourceProduction
public import AVRegularity.Construction.Preservation.Assembly.RetainedMarkedLedgerOfIngredients
import AVRegularity.Construction.Preservation.Ledger.TaggedRecurrence
import AVRegularity.CycleComparison.Error.Main

section
section
section
/-! **Generic fresh-record prices.** The record prices
(`fresh_tag_price_le`, `source_record_price_le`) for provenance parameters
`genProvParams D C η N p Rb rb` with arbitrary birth lengths `Rb` and widths `rb`, subject to
`rb (m-1) = Rb (m-1) * E^σ` at the scale `E = ε_{m-1}` (the width exponent `σ`). The cascade's
`succProvParams` and the terminal's `termProvParams` are instances (`rfl`).

For `σ = 0` the width equals the length. -/

@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.Ledger
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G : GenStage D hr Dm bw j₀}

/-- The generic provenance parameters of the cascade and of the terminal passage. -/
def genProvParams (D : OCData) (C η : ℝ) (N p : ℕ) (Rb rb : ℕ → ℝ) : ProvParams where
  C := C
  w := fun _ => 1
  eps := D.eps
  δ := ocDelta D.α D.q
  η0 := η
  N := N
  p := p
  Rb := Rb
  rb := rb

theorem termProvParams_eq_gen (D : OCData) (Cw cr tT η₀ : ℝ) (N p M : ℕ) :
    termProvParams D Cw cr tT η₀ N p M =
      genProvParams D Cw η₀ N p (fun _ => D.termRho cr M) (fun _ => D.termRNew cr tT M) := rfl

/-- Fresh tags pay their original-order width inflation once. -/
theorem fresh_tag_price_le_gen {C σ η E : ℝ} {Rb rb : ℕ → ℝ} {N p d m : ℕ} {l : WordLetter}
    {path : List (Comp × Comp × Prov)} (r : ConstituentRecord)
    (hE : 0 < E) (hE1 : E ≤ 1) (hσ : 0 ≤ σ) (_hscale : D.eps (m - 1) = E)
    (hrb : rb (m - 1) = Rb (m - 1) * E ^ σ) (hd : letterOrder N p l - 2 ≤ d)
    (hm : ((Prov.letter m l path).tags (genProvParams D C η N p Rb rb)).Matches r) :
    constituentPrice r ≤ E ^ (-σ * (d : ℝ)) := by
  apply fresh_constituentPrice_le r hE hE1 hσ
  · have hw := hm.2.2.2.2.1
    have hl := hm.2.2.2.1
    change r.width = rb (m - 1) at hw
    change r.length = Rb (m - 1) at hl
    rw [hw, hrb, ← hl]
  · exact (hm.2.2.1 ▸ hd)

/-- A nonnegative edge price is preserved by every source's diagonal normalization. -/
theorem source_record_price_le_gen (a : Comp → ℝ) (ha : ∀ v ∈ G.comps, 0 < a v)
    {C σ η E F : ℝ} {Rb rb : ℕ → ℝ} {N p d m : ℕ} {A : Finset WordLetter} {J : ℕ}
    (hC : 0 ≤ C) (hE : 0 < E) (hE1 : E ≤ 1) (hσ : 0 ≤ σ) (hF : 0 ≤ F)
    (hscale : D.eps (m - 1) = E) (hrb : rb (m - 1) = Rb (m - 1) * E ^ σ) (hletters : ∀ l ∈ A, letterOrder N p l - 2 ≤ d)
    (hG : G.HasTags (genProvParams D C η N p Rb rb))
    (s : SuccSource G) (hv : s.Valid A J) (r : ConstituentRecord)
    (hm : ((s.prov m).tags (genProvParams D C η N p Rb rb)).Matches r)
    (r₀ r₁ : ℕ) (b : ℝ)
    (hratio : b ≤ (if s.letter? = none then 1 else F) * (a s.oldTgt / a s.oldSrc)) :
    b * (‖rootPathMap hr r₀ s.maps r₁‖ * r.size * constituentPrice r) ≤
      sourcePrice C (F * E ^ (ocDelta D.α D.q - η - σ * (d : ℝ))) (identityPrice G a) s := by
  have hmultiply : b * (‖rootPathMap hr r₀ s.maps r₁‖ * r.size * constituentPrice r) ≤
      ((if s.letter? = none then 1 else F) * (a s.oldTgt / a s.oldSrc)) *
        (‖rootPathMap hr r₀ s.maps r₁‖ * r.size * constituentPrice r) :=
    mul_le_mul_of_nonneg_right hratio
      (mul_nonneg (mul_nonneg (norm_nonneg _) r.size_nonneg) (le_trans zero_le_one (le_max_left _ _)))
  apply hmultiply.trans
  cases s with
  | copyDir t v u γ =>
    have hold := (hG v u γ).1
    have hs : r.size = C * (G.fam.identity v u γ).record.size := by
      rw [hm.1]
      change C * ((G.prov v u γ).tags (genProvParams D C η N p Rb rb)).witness = _
      rw [← hold.1]
    have hp : constituentPrice r = constituentPrice (G.fam.identity v u γ).record := by
      unfold constituentPrice
      rw [hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1]
      change max 1 ((((G.prov v u γ).tags (genProvParams D C η N p Rb rb)).length /
        ((G.prov v u γ).tags (genProvParams D C η N p Rb rb)).width) ^
          ((G.prov v u γ).tags (genProvParams D C η N p Rb rb)).birthExcess) = _
      rw [← hold.2.2.1, ← hold.2.2.2.1, ← hold.2.2.2.2.1]
    have hn := norm_rootPathMap_le r₀ r₁ (.copyDir t v u γ : SuccSource G).maps
    simp only [SuccSource.maps, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at hn
    simp only [SuccSource.letter?, ↓reduceIte, one_mul, SuccSource.oldTgt, SuccSource.oldSrc,
      sourcePrice, identityPrice]
    rw [hs, hp]
    have hratio0 : 0 ≤ a v.1 / a u.1 := (div_pos (ha _ v.2) (ha _ u.2)).le
    have hprice0 : 0 ≤ constituentPrice (G.fam.identity v u γ).record :=
      le_trans zero_le_one (le_max_left _ _)
    have hh := mul_le_mul_of_nonneg_right hn
      (mul_nonneg (G.fam.identity v u γ).record.size_nonneg hprice0)
    have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg hC hratio0)
    simpa only [SuccSource.maps, mul_assoc, mul_left_comm, mul_comm] using hh'
  | copyQuad t h π =>
    have hs : r.size = C * ∏ i, (G.fam.identity _ _ (π.step i).2.2).record.size := by
      rw [hm.1, SuccSource.prov, Providers.CascadeInvariants.Prov.tags_quad_witness,
        Providers.CascadeInvariants.prod_witness_provList hG]
      rfl
    have hp : constituentPrice r = 1 := by
      simp only [constituentPrice, hm.2.2.1, SuccSource.prov,
        Providers.CascadeInvariants.Prov.tags_quad_birthExcess, pow_zero, max_self]
    have hh := path_record_price_le a ha π hv.2.2 r₀ r₁ r C 1 hC zero_le_one hs hp.le
    simpa only [SuccSource.letter?, ↓reduceIte, one_mul, SuccSource.oldTgt, SuccSource.oldSrc,
      SuccSource.maps, sourcePrice, positivePathWeight, Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hv.2.2),
      ↓reduceIte, mul_one] using hh
  | letterDiag t u =>
    have hd := hletters .diag (hv.2.1 .diag rfl).2
    have hp := fresh_tag_price_le_gen r hE hE1 hσ hscale hrb hd hm
    have hs : r.size = C * E ^ (ocDelta D.α D.q - η) := by
      simpa only [SuccSource.prov, Prov.tags, Prov.pathTags, List.map_nil, List.prod_nil,
        genProvParams, one_mul, mul_one, hscale] using hm.1
    have hn : ‖rootPathMap hr r₀ (.letterDiag t u : SuccSource G).maps r₁‖ ≤ 1 := by
      simpa only [SuccSource.maps, List.map_nil, List.prod_nil] using norm_rootPathMap_le r₀ r₁ []
    have hh := mul_le_mul hn hp (le_trans zero_le_one (le_max_left _ _)) zero_le_one
    have he : E ^ (ocDelta D.α D.q - η) * E ^ (-σ * (d : ℝ)) =
        E ^ (ocDelta D.α D.q - η - σ * (d : ℝ)) := by
      rw [← Real.rpow_add hE]; congr 1; ring
    simp only [SuccSource.letter?, Option.some_ne_none, ↓reduceIte, SuccSource.oldTgt,
      SuccSource.oldSrc, div_self (ha _ u.2).ne', mul_one, sourcePrice]
    rw [hs]
    have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg (mul_nonneg hC hF)
      (Real.rpow_nonneg hE.le (ocDelta D.α D.q - η)))
    calc
      _ ≤ C * F * (E ^ (ocDelta D.α D.q - η) * E ^ (-σ * (d : ℝ))) := by
        nlinarith only [hh']
      _ = _ := by rw [he]; ring
  | letterMean t n h π | letterCov t n h a' a'' π =>
    have hl := (hv.2.1 _ rfl).2
    have hd := hletters _ hl
    have hp := fresh_tag_price_le_gen r hE hE1 hσ hscale hrb hd hm
    have hs : r.size = (C * E ^ (ocDelta D.α D.q - η)) *
        ∏ i, (G.fam.identity _ _ (π.step i).2.2).record.size := by
      rw [hm.1]
      simp only [SuccSource.prov, Prov.tags]
      rw [Providers.CascadeInvariants.prod_witness_provList hG]
      simp only [genProvParams, one_mul, hscale]
    have hh := path_record_price_le a ha π hv.2.2 r₀ r₁ r
      (C * E ^ (ocDelta D.α D.q - η)) (E ^ (-σ * (d : ℝ)))
      (mul_nonneg hC (Real.rpow_nonneg hE.le _)) (Real.rpow_nonneg hE.le _) hs hp
    have he : E ^ (ocDelta D.α D.q - η) * E ^ (-σ * (d : ℝ)) =
        E ^ (ocDelta D.α D.q - η - σ * (d : ℝ)) := by
      rw [← Real.rpow_add hE]; congr 1; ring
    have hh' := mul_le_mul_of_nonneg_left hh hF
    simp only [SuccSource.letter?, Option.some_ne_none, ↓reduceIte, SuccSource.oldTgt,
      SuccSource.oldSrc, SuccSource.maps, sourcePrice, positivePathWeight,
      Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hv.2.2), ↓reduceIte]
    calc
      _ ≤ F * ((C * E ^ (ocDelta D.α D.q - η) * E ^ (-σ * (d : ℝ))) *
          pathWeight (identityPrice G a) π) := by nlinarith only [hh']
      _ = _ := by rw [mul_assoc C, he]; ring

end AVRegularity.Construction.Preservation.Ledger
end
end

section
/-! **The readout of the omitted flux, generic in the stages**: `frontierReadout`, the argument of
`P_p` in `menuFrontierFlux`. It does not use the terminal bounds.

If no row is omitted, the readout is `0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation

section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The readout of the omitted flux on the omitted rows (the argument of `P_p` in
`menuFrontierFlux`). -/
def frontierReadout (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G G' Gr : GenStage D hr Dm b j₀) (m H J : ℕ) (E η₀ : ℝ)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (y : Vec 2) : Fin 2 → hr v.1.root :=
  WithLp.ofLp (readoutFlux (S := G.comps) m E η₀ (fun c => ¬ IsRetained m H J c)
    (fun v' s y' => omittedFluxClassical P seedK freshK φ₀ G' Gr aY v' s y') v t y)

end Generic

end AVRegularity.Construction.Residual.Presentation
end
end
end

section
section
/-! **The response boundary at the terminal menu: the named steps and the assembly of
`TermFrontierStatement`.**

Rows: `c.weak` gives `births = []` on `Gw.comps`, `c.succ` gives
`Gt'.comps = succExtComps M A R_T Gw.comps`, so every component of `Gt'` has grade at most `1` and
`¬ IsRetained M 1 R_T` selects exactly the words of length `R_T + 1`.

The flux of `TermFrontierAt` is `P_p` (covariance anchored at `t_p`) of the readout of the omitted
flux (`menuFrontierFlux`, by definition). Route:
* `FrontierInnerStatement`: the readout of the omitted flux of `x.aY` on the rows of length
  `R_T + 1` is `C^{k_c+2p}`, periodic, with a realization of order `k_c + 2p_T` and mass at most
  `C E^{δ(R_T+1)/2} ‖f‖₂`.
* `FilterPOpStatement` (`filterPOp`) and `CovTruncSizeStatement` (`covTruncSize`) as in
  `termFilter_of_steps`.

For `R_T = 0` the price is `E^{δ/2}`, and for `x.aY = 0` the flux is `0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- **The inner flux at a context**: the readout of the omitted flux on the omitted rows, on the
classical representative `x.aY`, is `C^{k_c+2p_T}`, periodic, and has a realization of order
`k_c + 2p_T` with `B^{-1/2}‖·‖ ≤ C E^{δ(R_T+1)/2}‖f‖₂`. -/
def FrontierInnerAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    ContDiff ℝ ((kc + 2 * A.pT : ℕ) : ℕ∞)
        (fun y => frontierReadout (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
          c.Gw c.Gt' (c.Gt'.retained M 1 A.RT) M 1 A.RT (c.D.eps (M - 1)) A.η₀ x.aY v t y) ∧
      IsZ2Periodic
        (fun y => frontierReadout (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
          c.Gw c.Gt' (c.Gt'.retained M 1 A.RT) M 1 A.RT (c.D.eps (M - 1)) A.η₀ x.aY v t y)) ∧
  HasFluxBound (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (kc + 2 * A.pT)
    (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW)
    (fun v t y => toFluxL
      (frontierReadout (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
        c.Gw c.Gt' (c.Gt'.retained M 1 A.RT) M 1 A.RT (c.D.eps (M - 1)) A.η₀ x.aY v t y))
    (C * c.frontPrice * c.normF)

end Terminal

/-- **The inner flux.** -/
def FrontierInnerStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => FrontierInnerAt c x kc C

/-- **The inner flux bound from its steps.** -/
theorem termFrontier_of_steps (hP : FilterPOpStatement) (hS : CovTruncSizeStatement)
    (hF : FrontierInnerStatement) : TermFrontierStatement := by
  have hjoin := termFluxPrefix_and
    (P₁ := fun c x kc C => CovTruncSizeAt c x kc C)
    (P₂ := fun c x kc C => FrontierInnerAt c x kc C) hS hF
  refine termFluxPrefix_map
    (P := fun c x kc C => CovTruncSizeAt c x kc C ∧ FrontierInnerAt c x kc C)
    (R := fun c x kc C => TermFrontierAt c x kc C) ?_ hjoin
  intro X A kc C₁ hΛ128 hC₁
  obtain ⟨Cp, hCp, hP'⟩ := hP kc A.pT
  refine ⟨Cp * C₁, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hPr C'
    hC'
  obtain ⟨⟨hsz, hsm, hcont⟩, hreg, hF'⟩ := hPr
  obtain ⟨hDα, hDq, hDΛ, -, -, hband, -⟩ := c.data
  have hΛD : 128 ≤ c.D.Λ := hDΛ ▸ hΛ128
  have hq1 : 1 < c.D.q := hDq ▸ X.hq.1
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ128
  have hν : 0 < c.D.κ (M - 1) :=
    CycleReference.bandChain_pos hΛ1 X.hζ hband (Nat.sub_le M 1)
  have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos (le_trans (by norm_num) hΛD)
  have hρ : 0 < c.D.termRho cr M := mul_pos (x.one ▸ one_pos) (Real.sqrt_pos.2 (mul_pos hν hh))
  have hπ : ∀ v, 0 < c.Gw.mass c.lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD c.lawW v.1
  have hε0 : 0 < c.D.eps (M - 1) := (Scales.epsilon_basic hq1 hΛD).1
  have hω : 0 ≤ C₁ * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q :=
    mul_nonneg hC₁ (Real.rpow_pos_of_pos hε0 _).le
  have hop := hP' (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root)
    (Set.Icc c.tp (c.a + A.T₀)) measurableSet_Icc (c.D.κ (M - 1)) (c.D.termRho cr M)
    (c.Gw.mass c.lawW) hν hρ hπ
    (fun t => menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t)
    (C₁ * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q) hcont hω hsm hsz
    (fun v t y => frontierReadout (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
      c.Gw c.Gt' (c.Gt'.retained M 1 A.RT) M 1 A.RT (c.D.eps (M - 1)) A.η₀ x.aY v t y)
    (C₁ * c.frontPrice * c.normF) hreg hF'
  unfold TermFrontierAt FrontierBound
  refine hasFluxBound_mono_Y hop ?_
  have hn : 0 ≤ c.normF := Real.sqrt_nonneg _
  have hfp : 0 ≤ c.frontPrice := (Real.rpow_pos_of_pos hε0 _).le
  calc Cp * (C₁ * c.frontPrice * c.normF) = (Cp * C₁) * c.frontPrice * c.normF := by ring
    _ ≤ C' * c.frontPrice * c.normF :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC' hfp) hn

/-- **The response boundary at the terminal menu**, from the inner flux. -/
theorem termFrontier_of_inner (hF : FrontierInnerStatement) : TermFrontierStatement :=
  termFrontier_of_steps filterPOp covTruncSize hF

end AVRegularity.Construction.Residual.Presentation
end
end

section
/-! **The omitted rows of the terminal successor.**

Every component of the extended set `succExtComps m A J S` over a set `S` of roots has grade at
most `1` and a word of length at most `J + 1`, so `¬ IsRetained m 1 J` selects exactly the words
of length `J + 1` (and these are the fresh children `succComp m x t`, `x ∈ S`, `|t| = J + 1`).
At the terminal context `S = Gw.comps` consists of roots by `c.weak`.

For `J = 0` the omitted rows are the one-letter words, and for `S = ∅` there are no rows. -/

@[expose] public noncomputable section

namespace AVRegularity.Construction.Residual.Presentation

open AVRegularity AVRegularity.EntryTerminal.Route

/-- Components over roots have grade at most `1` and word length at most `J + 1`. -/
theorem frontierRows_grade_len {m J : ℕ} {A : Finset WordLetter} {S : Finset Comp}
    (hS : ∀ c ∈ S, c.births = []) {c : Comp} (hc : c ∈ succExtComps m A J S) :
    compGrade c ≤ 1 ∧ (compWord m c).length ≤ J + 1 := by
  simp only [succExtComps, Finset.mem_union, Finset.mem_image, Finset.mem_product] at hc
  rcases hc with hc | ⟨x, ⟨hx1, hx2⟩, rfl⟩
  · have := hS c hc
    simp [compGrade, compWord, this]
  · have hne : x.2 ≠ [] := by
      intro h
      have := (Providers.CascadeInvariants.length_of_mem_wordsUpTo hx2).1
      rw [h] at this
      simp at this
    refine ⟨?_, ?_⟩
    · rw [Providers.CascadeInvariants.compGrade_succComp_ne m x.1 hne]
      have := hS x.1 hx1
      simp [compGrade, this]
    · rw [EntryTerminal.Ingredients.compWord_succComp_ne m x.1 hne]
      exact (Providers.CascadeInvariants.length_of_mem_wordsUpTo hx2).2

/-- The omitted rows are the words of length `J + 1`. -/
theorem frontierRows_not_retained {m J : ℕ} {A : Finset WordLetter} {S : Finset Comp}
    (hS : ∀ c ∈ S, c.births = []) {c : Comp} (hc : c ∈ succExtComps m A J S) :
    ¬ IsRetained m 1 J c ↔ (compWord m c).length = J + 1 := by
  obtain ⟨hg, hl⟩ := frontierRows_grade_len hS hc
  unfold IsRetained
  constructor
  · intro h
    by_contra hne
    exact h ⟨hg, by omega⟩
  · intro h hr
    have := hr.2
    omega

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **At the terminal context** the omitted rows of `Gt'` are the words of length `R_T + 1`. -/
theorem termRows_not_retained
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (v : CompIn c.Gt'.comps) :
    ¬ IsRetained M 1 A.RT v.1 ↔ (compWord M v.1).length = A.RT + 1 := by
  have hroots : ∀ x ∈ c.Gw.comps, x.births = [] := fun x hx =>
    c.weak.2.2.2.2.1 ⟨x, hx⟩
  have hlev : c.Gw.level = M := c.weak.2.2.1
  have hext : v.1 ∈ succExtComps M (termAlphabet A.NT A.pT A.DW A.dW) A.RT c.Gw.comps := by
    have h1 := (Finset.ext_iff.mp c.succ.2.2.1 v.1).1 v.2
    rw [hlev] at h1
    exact h1
  exact frontierRows_not_retained hroots hext

end Terminal

end AVRegularity.Construction.Residual.Presentation
end
end

section
/-! **Smoothness of the classical omitted flux and of its readout** (generic
in the stages).

`omittedFluxClassical_smooth`: the classical omitted flux of a field `aY` of class `C^{n+D_m-1}`
is `C^n` and `ℤ²`-periodic when the coefficients are. `readoutFlux_smooth`: the same for the
readout (a finite sum of scalar multiples of the flux on the selected rows). For `aY = 0` both
vanish. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation

section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- **The classical omitted flux is smooth and periodic.** -/
theorem omittedFluxClassical_smooth (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    (G' Gr : GenStage D hr Dm bw j₀) (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, hr v.1.root)
    (t : ℝ) (n : ℕ)
    (hcoef : ∀ (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) (d : ℕ),
      ContDiff ℝ (n : ℕ) (G'.physCoeff v u γ d t) ∧ IsZ2Periodic (G'.physCoeff v u γ d t))
    (haY : ∀ u : CompIn Gr.comps, ContDiff ℝ ((n + Dm : ℕ) : ℕ∞) (fun y => aY t y u) ∧
      IsZ2Periodic (fun y => aY t y u)) (v : CompIn G'.comps) :
    ContDiff ℝ (n : ℕ) (fun x => omittedFluxClassical P seedK freshK φ₀ G' Gr aY v t x) ∧
      IsZ2Periodic (fun x => omittedFluxClassical P seedK freshK φ₀ G' Gr aY v t x) := by
  classical
  have term : ∀ (u : CompIn G'.comps) (hu : u.1 ∈ Gr.comps) (γ : G'.fam.Γ v u) (d : ℕ), d ≤ Dm →
      ContDiff ℝ (n : ℕ) (fun x => G'.physCoeff v u γ d t x (WithLp.toLp 2
        fun word : DerivativeWord2 (d - 1) =>
          orderedDerivative word ((G'.kernelOf P seedK freshK v u γ).applyClassical φ₀ t
            (fun y => aY t y ⟨u.1, hu⟩)) x)) ∧
      IsZ2Periodic (fun x => G'.physCoeff v u γ d t x (WithLp.toLp 2
        fun word : DerivativeWord2 (d - 1) =>
          orderedDerivative word ((G'.kernelOf P seedK freshK v u γ).applyClassical φ₀ t
            (fun y => aY t y ⟨u.1, hu⟩)) x)) := by
    intro u hu γ d hd
    obtain ⟨h1, h2⟩ := haY ⟨u.1, hu⟩
    have hK := AVRegularity.IterationPassage.Passage.regularKernel_contDiff_periodic hφs hφsupp
      (G'.kernelOf P seedK freshK v u γ) t h1 h2
    refine ⟨?_, ?_⟩
    · refine (hcoef v u γ d).1.clm_apply ?_
      refine PiLp.contDiff_toLp.comp (contDiff_pi.2 fun word => ?_)
      exact ChartTransport.contDiff_orderedDerivative (p := n) (q := d - 1) word
        (hK.1.of_le (by exact_mod_cast (by omega : n + (d - 1) ≤ n + Dm)))
    · intro m x
      have e1 := (hcoef v u γ d).2 m x
      have e2 : ∀ word : DerivativeWord2 (d - 1), orderedDerivative word
          ((G'.kernelOf P seedK freshK v u γ).applyClassical φ₀ t (fun y => aY t y ⟨u.1, hu⟩))
            (x + latticeShift m) = orderedDerivative word
          ((G'.kernelOf P seedK freshK v u γ).applyClassical φ₀ t (fun y => aY t y ⟨u.1, hu⟩))
            x := fun word => ChartTransport.isZ2Periodic_orderedDerivative word hK.2 m x
      simp only [e1, e2]
  constructor
  · unfold omittedFluxClassical
    refine ContDiff.sum fun u _ => ?_
    by_cases hu : u.1 ∈ Gr.comps
    · simp only [hu, dite_true]
      refine ContDiff.sum fun γ _ => ?_
      refine ContDiff.sum fun d _ => ?_
      exact (term u hu γ d.1 (Finset.mem_Icc.1 d.2).2).1
    · simp only [hu, dite_false]; exact contDiff_const
  · intro m x
    unfold omittedFluxClassical
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u.1 ∈ Gr.comps
    · simp only [hu, dite_true]
      refine Finset.sum_congr rfl fun γ _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      exact (term u hu γ d.1 (Finset.mem_Icc.1 d.2).2).2 m x
    · simp only [hu, dite_false]

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- Transport along an equality of roots preserves smoothness and periodicity. -/
theorem cast_root_smooth {r r' : ℕ} (e : r' = r) (n : ℕ)
    (f : Vec 2 → PiLp 2 (fun _ : Fin 2 => hr r'))
    (hf : ContDiff ℝ (n : ℕ) f ∧ IsZ2Periodic f) :
    ContDiff ℝ (n : ℕ) (fun y => cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) e) (f y)) ∧
      IsZ2Periodic
        (fun y => cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) e) (f y)) := by
  subst e
  simpa using hf

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **The readout of a smooth periodic flux is smooth and periodic.** -/
theorem readoutFlux_smooth (m : ℕ) (E η₀ : ℝ) {S S' : Finset Comp} (sel : Comp → Prop)
    (F : ∀ v' : CompIn S', ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v'.1.root)) (t : ℝ) (n : ℕ)
    (hF : ∀ v', ContDiff ℝ (n : ℕ) (fun y => F v' t y) ∧ IsZ2Periodic (fun y => F v' t y))
    (v : CompIn S) :
    ContDiff ℝ (n : ℕ) (fun y => readoutFlux (hr := hr) m E η₀ sel F v t y) ∧
      IsZ2Periodic (fun y => readoutFlux (hr := hr) m E η₀ sel F v t y) := by
  classical
  unfold readoutFlux
  have term : ∀ v' : CompIn S', ContDiff ℝ (n : ℕ) (fun y => if h : compParent m v'.1 = v.1 ∧ sel v'.1 then
    (E ^ (η₀ * ((compWord m v'.1).length : ℝ))) •
      cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r))
        ((compParent_root m v'.1).symm.trans (congrArg Comp.root h.1))) (F v' t y)
    else 0) ∧ IsZ2Periodic (fun y => if h : compParent m v'.1 = v.1 ∧ sel v'.1 then
    (E ^ (η₀ * ((compWord m v'.1).length : ℝ))) •
      cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r))
        ((compParent_root m v'.1).symm.trans (congrArg Comp.root h.1))) (F v' t y)
    else 0) := by
    intro v'
    by_cases h : compParent m v'.1 = v.1 ∧ sel v'.1
    · simp only [h, and_self, dite_true]
      have hc := cast_root_smooth (hr := hr)
        ((compParent_root m v'.1).symm.trans (congrArg Comp.root h.1)) n _ (hF v')
      exact ⟨hc.1.const_smul _, fun k y => by simp [hc.2 k y]⟩
    · simp only [h, dite_false]
      exact ⟨contDiff_const, fun _ _ => rfl⟩
  exact ⟨ContDiff.sum fun v' _ => (term v').1, fun k y => Finset.sum_congr rfl fun v' _ =>
    (term v').2 k y⟩

end Generic

end AVRegularity.Construction.Residual.Presentation
end
end
end
end

section
@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.Construction.Preservation.Ledger

/-! **the marked ledger of the WHOLE actual successor, generically.**

`retained_ledger_recurrence_gen` restricts to the retained family at its end; its proof first
bounds the ledger of the full successor `G'`. Here that bound is exported (the proof is the same
with the restriction step removed). It is the Schur input of the native kernel operator of `G'`.

For `S = 0` the bound is the fresh part alone. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G G' : GenStage D hr Dm bw j₀}

/-- **The recurrence of the marked ledger, generically**: the actual
successor (all its rows) has marked ledger at most `|W|(4 C_w S + 2 L C_w R)`, enlarged as in `menu_bound_le`. -/
theorem full_ledger_gen {Cw η σ R S : ℝ} {N p d : ℕ} {Rb rb : ℕ → ℝ}
    {Mn : SuccMenu} (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hCw : 0 ≤ Cw) (hσ : 0 ≤ σ)
    (hrb : rb (G.level - 1) = Rb (G.level - 1) * D.eps (G.level - 1) ^ σ)
    (hletters : ∀ l ∈ Mn.A, letterOrder N p l - 2 ≤ d) (law : BirthLaw)
    (hF1 : ∀ marked, 1 ≤ birthDiagonalFactor D.q D.Λ G.level law marked)
    (hbirth : ∀ marked, birthDiagonalFactor D.q D.Λ G.level law marked *
      D.eps (G.level - 1) ^ (ocDelta D.α D.q - η - σ * (d : ℝ)) ≤ R)
    (hG : G.HasTags (genProvParams D Cw η N p Rb rb))
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (hs : IsActualSuccessor D (genProvParams D Cw η N p Rb rb) Mn G G')
    (hS : 0 ≤ S) (hledger : markedLedger (G.mass law) (G.marker law) G.fam ≤ S)
    (hsmall : Assembly.ledgerTransportConstant Cw (wordsUpTo Mn.A (Mn.J + 1)).card * S ≤ 1 / 2) :
    markedLedger (G'.mass law) (G'.marker law) G'.fam ≤
      4 * (((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) + 1) * (Cw + 1) * S +
        2 * (((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) + 1) * ((Mn.A.card : ℝ) + 1) * (Cw + 1) * R := by
  classical
  have hCw0 : 0 ≤ Cw := hCw
  have hqD : 1 < D.q := hq
  have he := Scales.epsilon_basic (m := G.level - 1) hqD hΛ
  have hA : 1 ≤ Assembly.ledgerTransportConstant Cw (wordsUpTo Mn.A (Mn.J + 1)).card := by
    unfold Assembly.ledgerTransportConstant
    have ht : 0 ≤ ((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) := Nat.cast_nonneg _
    nlinarith only [hCw, ht]
  have hhalf : S ≤ 1 / 2 := (le_mul_of_one_le_left hS hA).trans hsmall
  let E := Classical.choice (actual_sources hs)
  let B : ℝ := 4 * (((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) + 1) * (Cw + 1) * S +
    2 * (((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) + 1) * ((Mn.A.card : ℝ) + 1) * (Cw + 1) * R
  have hbound (marked : Bool) :
      fullLedger (pricedRecordMajorant (G'.mass law)
        (fun c => ledgerMarker D.q D.Λ law marked c.1) G'.fam) ≤ B := by
    let a := ledgerDiagonal D.q D.Λ law marked
    let F := birthDiagonalFactor D.q D.Λ G.level law marked
    let Ffresh := F * D.eps (G.level - 1) ^ (ocDelta D.α D.q - η - σ * (d : ℝ))
    have ha : ∀ v ∈ G.comps, 0 < a v := fun v _ => ledgerDiagonal_pos hqD hΛ law marked v
    have hF : 1 ≤ F := hF1 marked
    have hF0 : 0 ≤ Ffresh := mul_nonneg (le_trans zero_le_one hF) (Real.rpow_nonneg he.1.le _)
    have hFR : Ffresh ≤ R := hbirth marked
    let c := identityPrice G a
    have hc : ∀ e, 0 ≤ c e := identityPrice_nonneg G a ha
    have hrowcol : SchurBound S (fun v u => ∑ γ, c ⟨v, u, γ⟩) := by
      have hh : fullLedger (pricedRecordMajorant (G.mass law)
          (fun c => ledgerMarker D.q D.Λ law marked c.1) G.fam) ≤ S := by
        cases marked with
        | false => exact (le_max_left _ _).trans hledger
        | true => exact (le_max_right _ _).trans hledger
      have hb := FullLift.fullLedger_schur_bound (pricedRecordMajorant (G.mass law)
        (fun c => ledgerMarker D.q D.Λ law marked c.1) G.fam)
      simpa only [c, a, sum_identityPrice_eq hqD hΛ law marked] using
        (show SchurBound S (pricedRecordMajorant (G.mass law)
          (fun c => ledgerMarker D.q D.Λ law marked c.1) G.fam) from
            ⟨fun v => (hb.1 v).trans hh, fun u => (hb.2 u).trans hh⟩)
    have hcost (e : LedgerEdge G') : identityPrice G' a e ≤ sourcePrice Cw Ffresh c (E.source e) := by
      have hratio := source_diagonal_ratio_le a ha hF
        (fun v hv t => ledgerDiagonal_succComp hqD hΛ hs.1 law marked v (hold v hv) t)
        (E.source e) (source_old_mem (E.source e) (E.valid e))
      rw [E.tgt e, E.src e] at hratio
      have hh := source_record_price_le_gen a ha hCw he.1 he.2.1 hσ (le_trans zero_le_one hF)
        rfl hrb hletters hG (E.source e) (E.valid e) (G'.fam.identity e.1 e.2.1 e.2.2).record
        (E.tags e) e.2.1.1.root e.1.1.root (a e.1.1 / a e.2.1.1) hratio
      simpa only [identityPrice, E.map_eq e, Ffresh, c, OCData.eps] using hh
    have hschur := actual_diagonal_schur hs hold a Cw Ffresh hCw hF0 c hc hS hhalf
      hrowcol.1 hrowcol.2 E hcost
    have hmenu := menu_bound_le (L := Mn.A.card) (Finset.card_insert_le [] (wordsUpTo Mn.A (Mn.J + 1)))
      hCw hS hF0 hFR
    have hmenu' : ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) *
        (4 * Cw * S + 2 * (Mn.A.card : ℝ) * Cw * Ffresh) ≤ B := hmenu
    have hR0 : 0 ≤ R := hF0.trans hFR
    have hB : 0 ≤ B := by
      dsimp only [B]
      positivity
    apply diagonal_fullLedger_le hqD hΛ law marked hB
    exact ⟨fun v => (hschur.1 v).trans hmenu', fun u => (hschur.2 u).trans hmenu'⟩
  exact max_le (hbound false) (hbound true)

end AVRegularity.Construction.Preservation.Ledger
end

section
open Homogenization
namespace AVRegularity.Construction.Preservation.Frontier.LengthPrice

/-! **The Schur bound of the fresh identity records, generically.**
`fresh_record_schur` for arbitrary provenance parameters `genProvParams` (width exponent `σ`,
decay order `d`), with the birth-diagonal bound as a hypothesis (`hbirth`): the fresh letter costs
`E^{θ₂}` with `θ₂ = δ - η - σ d`, and at the first prefix the birth factor turns it into `Rl E^{θ₁}`. -/

open Ledger
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G G' : GenStage D hr Dm bw j₀}

theorem fresh_record_schur_gen {Cw σ η Rl θ₁ θ₂ : ℝ} {N p d : ℕ} {Rb rb : ℕ → ℝ} {Mn : SuccMenu}
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hCw : 0 ≤ Cw) (hσ : 0 ≤ σ)
    (hrb : rb (G.level - 1) = Rb (G.level - 1) * D.eps (G.level - 1) ^ σ)
    (hletters : ∀ l ∈ Mn.A, letterOrder N p l - 2 ≤ d)
    (law : BirthLaw)
    (hG : G.HasTags (genProvParams D Cw η N p Rb rb))
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (hs : IsActualSuccessor D (genProvParams D Cw η N p Rb rb) Mn G G')
    (hRl : 1 ≤ Rl) (hθ₂ : θ₂ = ocDelta D.α D.q - η - σ * (d : ℝ))
    (hbirth : birthDiagonalFactor D.q D.Λ G.level law true * D.eps (G.level - 1) ^ θ₂ ≤
      Rl * D.eps (G.level - 1) ^ θ₁)
    {S : ℝ} (hS : 0 ≤ S) (hhalf : S ≤ 1 / 2)
    (hledger : markedLedger (G.mass law) (G.marker law) G.fam ≤ S)
    (l : ℕ) (hl : 1 ≤ l) (Q : LedgerEdge G' → Prop) [DecidablePred Q]
    (hQ : ∀ e, Q e → (compWord G.level e.1.1).length = l ∧
      (compWord G.level e.2.1.1).length = l - 1) :
    SchurBound
      ((2 * ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) * (Mn.A.card : ℝ) * Cw * Rl) *
        D.eps (G.level - 1) ^ (if l = 1 then θ₁ else θ₂))
      (fun v u => ∑ γ, if Q ⟨v, u, γ⟩ then
        identityPrice G' (ledgerDiagonal D.q D.Λ law true) ⟨v, u, γ⟩ else 0) := by
  classical
  have hqD : 1 < D.q := hq
  have he := Scales.epsilon_basic (m := G.level - 1) hqD hΛ
  let a := ledgerDiagonal D.q D.Λ law true
  let c := identityPrice G a
  let F := if l = 1 then birthDiagonalFactor D.q D.Λ G.level law true else 1
  let Ffresh := F * D.eps (G.level - 1) ^ (ocDelta D.α D.q - η - σ * (d : ℝ))
  let E := Classical.choice (actual_sources hs)
  have ha : ∀ v ∈ G.comps, 0 < a v := fun v _ => ledgerDiagonal_pos hqD hΛ law true v
  have hc : ∀ e, 0 ≤ c e := identityPrice_nonneg G a ha
  have hF : 0 < F := by
    dsimp only [F]
    split <;> [exact birthDiagonalFactor_pos hqD hΛ _ law true; exact zero_lt_one]
  have hFfresh : 0 ≤ Ffresh := mul_nonneg hF.le (Real.rpow_nonneg he.1.le _)
  have hrowcol : SchurBound S (fun v u => ∑ γ, c ⟨v, u, γ⟩) := by
    have hh := (le_max_right _ _).trans hledger
    have hb := FullLift.fullLedger_schur_bound
      (pricedRecordMajorant (G.mass law) (G.marker law) G.fam)
    have hb' : SchurBound S (pricedRecordMajorant (G.mass law) (G.marker law) G.fam) :=
      ⟨fun v => (hb.1 v).trans hh, fun u => (hb.2 u).trans hh⟩
    have heq : (fun v u => ∑ γ, c ⟨v, u, γ⟩) =
        pricedRecordMajorant (G.mass law) (G.marker law) G.fam := by
      funext v u
      rw [show c = identityPrice G (ledgerDiagonal D.q D.Λ law true) from rfl,
        sum_identityPrice_eq hqD hΛ law true]
      rfl
    rw [heq]
    exact hb'
  have hcost (e : LedgerEdge G') : (if Q e then identityPrice G' a e else 0) ≤
      freshSourceCost Cw Ffresh c (E.source e) := by
    by_cases hsel : Q e
    · have hends := hQ e hsel
      obtain ⟨hfresh, hlen⟩ := fresh_source_of_lengths hs hold E e hl hends.1 hends.2
      have hword : ((E.source e).word = []) ↔ l = 1 := by
        rw [← List.length_eq_zero_iff, hlen]
        omega
      have hratio := fresh_source_diagonal_ratio a
        (birthDiagonalFactor_pos hqD hΛ G.level law true)
        (fun v hv t => ledgerDiagonal_succComp hqD hΛ hs.1 law true v (hold v hv) t)
        (E.source e) (source_old_mem (E.source e) (E.valid e)) hfresh
      rw [E.tgt e, E.src e] at hratio
      simp only [hword] at hratio
      have hratio' : a e.1.1 / a e.2.1.1 ≤
          (if (E.source e).letter? = none then 1 else F) *
            (a (E.source e).oldTgt / a (E.source e).oldSrc) := by
        simpa only [hfresh, ite_false, F] using hratio.le
      have hh := source_record_price_le_gen a ha hCw he.1 he.2.1 hσ hF.le rfl hrb hletters hG
        (E.source e) (E.valid e) (G'.fam.identity e.1 e.2.1 e.2.2).record (E.tags e)
        e.2.1.1.root e.1.1.root (a e.1.1 / a e.2.1.1) hratio'
      simpa only [hsel, ite_true, freshSourceCost, hfresh, ite_false, identityPrice,
        E.map_eq e, Ffresh, c, OCData.eps] using hh
    · simpa only [hsel, ite_false] using
        fresh_source_cost_nonneg Cw Ffresh hCw hFfresh c hc (E.source e)
  have hschur := fresh_actual_schur hs hold (fun e => if Q e then identityPrice G' a e else 0)
    E Cw Ffresh hCw hFfresh c hc hS hhalf hrowcol.1 hrowcol.2 hcost
  have hFF : Ffresh ≤ Rl * D.eps (G.level - 1) ^ (if l = 1 then θ₁ else θ₂) := by
    by_cases hl1 : l = 1
    · simp only [Ffresh, F, hl1, ite_true]
      rw [← hθ₂]
      exact hbirth
    · simp only [Ffresh, F, hl1, ite_false, one_mul]
      rw [← hθ₂]
      exact le_mul_of_one_le_left (Real.rpow_nonneg he.1.le _) hRl
  have hb : ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) *
      (2 * (Mn.A.card : ℝ) * Cw * Ffresh) ≤
        (2 * ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) * (Mn.A.card : ℝ) * Cw * Rl) *
          D.eps (G.level - 1) ^
            (if l = 1 then θ₁ else θ₂) := by
    calc
      _ = (2 * ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) * (Mn.A.card : ℝ) * Cw) * Ffresh := by ring
      _ ≤ (2 * ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) * (Mn.A.card : ℝ) * Cw) *
          (Rl * D.eps (G.level - 1) ^
            (if l = 1 then θ₁ else θ₂)) :=
        mul_le_mul_of_nonneg_left hFF (by positivity)
      _ = _ := by ring
  exact ⟨fun v => (hschur.1 v).trans hb, fun u => (hschur.2 u).trans hb⟩

end AVRegularity.Construction.Preservation.Frontier.LengthPrice
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Frontier
namespace AVRegularity.Construction.Residual.Presentation

/-! **The terminal `Frame` at a context.**

* `termLaw_mass_eq`: the masses of the weak roots agree for the laws `lawW` and `lawT`
  (`IsTerminalLaw`: equal `rootMass`, and the roots have no births).
* `truncTo`: total truncation of a jet space (zero if the order does not decrease); the statements of
  the inner flux use it so that they need no order hypotheses.
* `termFrame`: the `Frame` of the cascade's analytic inputs at the terminal context:
  `G := Gw`, `G' := Gt'`, `law := lawT`, `m := M`, `H := 1`, `J := R_T`, `k := k_c + 2p_T`,
  `θ₁ = θ₂ = δ/2`, window `[t_p, a + T₀]`, data `Y₀ = Z₀`, `Y_w = Z_w` truncated to the order `k`.
* `readoutFlux_congr`: the readout depends only on the selected rows of the flux.

For `R_T = 0` there is a single row length and the exponent is `δ/2`; for an empty weak family all
sums are empty. -/

/-- Total truncation of a jet space to the order `k` (zero when `K < k`). -/
def truncTo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] {K : ℕ} (k : ℕ)
    (f : TorusHk K E) : TorusHk k E :=
  if h : k ≤ K then truncateTorusHk h f else 0

theorem truncTo_of_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] {K k : ℕ}
    (h : k ≤ K) (f : TorusHk K E) : truncTo k f = truncateTorusHk h f := by
  simp only [truncTo, h, dite_true]

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- The weak roots have the same mass for the weak and the terminal law. -/
theorem termLaw_mass_eq (v : CompIn c.Gw.comps) :
    c.Gw.mass c.lawW v = c.Gw.mass c.lawT v := by
  have hb : v.1.births = [] := c.weak.2.2.2.2.1 v
  simp only [GenStage.mass, compMass, hb, List.map_nil, List.prod_nil, mul_one]
  rw [c.law.1]

theorem termLaw_mass_funext : c.Gw.mass c.lawW = c.Gw.mass c.lawT :=
  funext (termLaw_mass_eq c)

/-- The initial value of the retained system at the order `k_c + 2p_T`. -/
def termY0 (kc : ℕ) (v : CompIn (c.Gt'.retained M 1 A.RT).comps) :
    TorusHk (kc + 2 * A.pT) (ScalarH v.1.root) :=
  truncTo _ (c.Z₀ v)

/-- The retained solution's edge-free trajectory at the order `k_c + 2p_T + 1`. -/
def termYw (kc : ℕ) (v : CompIn (c.Gt'.retained M 1 A.RT).comps) (t : ℝ) :
    TorusHk (kc + 2 * A.pT + 1) (ScalarH v.1.root) :=
  truncTo _ (c.Zw v t)

/-- The terminal `Frame` at the context with the lifted edge inputs `yom`. -/
def termFrame (kc : ℕ)
    (yom : ∀ v u (_ : c.Gt'.fam.Γ v u), ℝ →
      TorusHk (kc + 2 * A.pT + A.Dt - 1) (ScalarH u.1.root)) :
    Frame c.D ScalarH A.Dt A.bw j₀ :=
  { G := c.Gw, G' := c.Gt', law := c.lawT, m := M, H := 1, J := A.RT, k := kc + 2 * A.pT,
    cr := cr, η := A.η₀, θ₁ := ocDelta c.D.α c.D.q / 2, θ₂ := ocDelta c.D.α c.D.q / 2,
    tp := c.tp, tf := c.a + A.T₀, Y0 := termY0 c kc, Yw := termYw c kc, yom := yom }

/-- The condition on the edge inputs `yom`: on the edges out of retained rows they are the kernel
operators applied to `Y_w` (the pattern of the cascade's statement). -/
def TermYomSpec (kc : ℕ)
    (yom : ∀ v u (_ : c.Gt'.fam.Γ v u), ℝ →
      TorusHk (kc + 2 * A.pT + A.Dt - 1) (ScalarH u.1.root)) : Prop :=
  ∀ v u (γ : c.Gt'.fam.Γ v u) (hu : IsRetained M 1 A.RT u.1),
    ∀ᵐ s ∂(volume.restrict (Set.Icc c.tp (c.a + A.T₀))),
      (yom v u γ s).val (valueIndex2 (kc + 2 * A.pT + A.Dt - 1)) =
        c.Gt'.sysS (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ A.hφ₀ v u γ s
          ((termYw c kc ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ s).val
            (valueIndex2 (kc + 2 * A.pT + 1)))

end Terminal

section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The readout of rows depends only on the selected rows. -/
theorem readoutFlux_congr {S S' : Finset Comp} (m : ℕ) (E η₀ : ℝ) (sel sel' : Comp → Prop)
    (hsel : ∀ c ∈ S', sel c ↔ sel' c)
    (F F' : ∀ v' : CompIn S', ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v'.1.root))
    (v : CompIn S) (t : ℝ) (x : Vec 2) (hF : ∀ v', F v' t x = F' v' t x) :
    readoutFlux (hr := hr) m E η₀ sel F v t x = readoutFlux m E η₀ sel' F' v t x := by
  unfold readoutFlux
  refine Finset.sum_congr rfl fun v' _ => ?_
  by_cases h : compParent m v'.1 = v.1 ∧ sel v'.1
  · have h' : compParent m v'.1 = v.1 ∧ sel' v'.1 := ⟨h.1, (hsel v'.1 v'.2).1 h.2⟩
    simp only [h, h', hF v', and_self, dite_true]
  · have h' : ¬ (compParent m v'.1 = v.1 ∧ sel' v'.1) := fun h2 =>
      h ⟨h2.1, (hsel v'.1 v'.2).2 h2.2⟩
    simp only [h, h', dite_false]

end Generic

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Frontier
namespace AVRegularity.Construction.Residual.Presentation

/-! **The inner flux from its six parts.**

`FrontierInnerStatement` is assembled from six statements about a terminal context, each in the
form `TermResPrefix fun c x kc _ C _ _ => _` (so that the joins of prefix statements and the
change of constant apply):

* `TermInnerRowsStatement`: row Cauchy at the terminal `Frame` (word-length case: the
  last prefix `l = R_T + 1` of the fresh-prefix price, per letter `E^{δ/2}`);
* `TermInnerMarkerStatement`: readout estimate on arbitrary selected rows;
* `TermInnerLayerStatement`: source-layer energy `sourceDissipation ≤ (C·layerGain·‖Y₀‖)²`;
* `TermInnerInitialStatement`: `‖Y₀‖_{ρ,k;π} ≤ C‖f‖₂` (energy of the coarse family,
  `c.prepB`, `energySolution`);
* `TermInnerIdentStatement`: the classical omitted flux of `x.aY` is a.e. the omitted
  flux of lifted edge inputs `yom` obeying the cascade's compatibility with `Y_w`;
* `TermInnerSmoothStatement`: the classical readout is `C^{k_c+2p_T}` and periodic.

The assembly: the join `frontierInner_of_parts`, the stage lemma
`frame_readout_energy_le` (the cascade's `frontier_at_stage_of_analytic_inputs` with the time
integrability of the readout kept), and the identification of the realization with the readout
of the classical flux.

For `R_T = 0` the exponent is `δ/2` and there is one prefix; for `x.aY = 0` all parts are
trivial. -/

section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem frame_initialNorm_nonneg (F : Frame D hr Dm bw j₀) : 0 ≤ F.initialNorm := by
  unfold Frame.initialNorm weightedNorm
  exact Real.sqrt_nonneg _

/-- The cascade's `frontier_at_stage_of_analytic_inputs`, in the form needed here: the energy of
the given readout realization (whose time integrability is kept by the caller). -/
theorem frame_readout_energy_le (F : Frame D hr Dm bw j₀) (hν : 0 ≤ D.κ (F.m - 1)) (C g : ℝ)
    (hg : F.rowGain false * F.markerGain false * F.layerGain false = g)
    (OF : F.RowFlux) (hOFlp : ∀ v, MemLp (OF v) 2 (volume.restrict (Set.Icc F.tp F.tf)))
    (hrow : F.rowEnergy OF ≤ (C * F.rowGain false) ^ 2 * F.sourceDissipation false)
    (hsource : F.sourceDissipation false ≤ (C * F.layerGain false * F.initialNorm) ^ 2)
    (RF : F.ReadoutFlux) (hRFlp : ∀ v, MemLp (RF v) 2 (volume.restrict (Set.Icc F.tp F.tf)))
    (hpoint : ∀ t ∈ Set.Icc F.tp F.tf,
        massNormSq (rhoEnh D F.cr F.m) (F.G.mass F.law) (fun v => (RF v t).val) ≤
          (C * F.markerGain false) ^ 2 *
            massNormSq (rhoEnh D F.cr F.m)
              (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2) (fun v => (OF v t).val)) :
    F.readoutEnergy RF ≤ (C ^ 3 * g * F.initialNorm) ^ 2 := by
  have hRi := CycleComparison.Error.integrable_massNormSq
    (rhoEnh D F.cr F.m) (F.G.mass F.law) RF hRFlp
  have hOi := CycleComparison.Error.integrable_massNormSq
    (rhoEnh D F.cr F.m)
    (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2) OF hOFlp
  have hi := integral_mono_ae hRi (hOi.const_mul ((C * F.markerGain false) ^ 2))
    ((ae_restrict_mem measurableSet_Icc).mono fun t ht => hpoint t ht)
  have hR : F.readoutEnergy RF ≤ (C * F.markerGain false) ^ 2 * F.rowEnergy OF := by
    dsimp only [Frame.readoutEnergy, Frame.rowEnergy]
    rw [integral_const_mul] at hi
    exact (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hν)).trans_eq (by ring)
  calc
    F.readoutEnergy RF ≤ (C * F.markerGain false) ^ 2 * F.rowEnergy OF := hR
    _ ≤ (C * F.markerGain false) ^ 2 * ((C * F.rowGain false) ^ 2 * F.sourceDissipation false) :=
      mul_le_mul_of_nonneg_left hrow (sq_nonneg _)
    _ ≤ (C * F.markerGain false) ^ 2 *
        ((C * F.rowGain false) ^ 2 * (C * F.layerGain false * F.initialNorm) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsource (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by rw [← hg]; ring

/-- The three analytic inputs at a frame give the readout realization with its energy bound. -/
theorem frame_stage_generic (F : Frame D hr Dm bw j₀) (hν : 0 ≤ D.κ (F.m - 1)) (C g : ℝ)
    (hg : F.rowGain false * F.markerGain false * F.layerGain false = g)
    (hR : OutsideRowCauchyStatement F false C) (hM : MarkerReadoutStatement F false C)
    (hL : SourceLayerEnergyStatement F false C) :
    ∃ RF : F.ReadoutFlux, F.RealizesReadout false RF ∧
      (∀ v, MemLp (RF v) 2 (volume.restrict (Set.Icc F.tp F.tf))) ∧
      F.readoutEnergy RF ≤ (C ^ 3 * g * F.initialNorm) ^ 2 := by
  obtain ⟨OF, hOF, hOFlp, hrow⟩ := hR
  obtain ⟨RF, hRF, hRFlp, hpoint⟩ := hM OF hOF hOFlp
  exact ⟨RF, hRF, hRFlp, frame_readout_energy_le F hν C g hg OF hOFlp hrow hL RF hRFlp hpoint⟩

end Generic

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- Every component of the terminal successor has grade at most `1`. -/
theorem termGrade_le (v : CompIn c.Gt'.comps) : compGrade v.1 ≤ 1 := by
  have hroots : ∀ x ∈ c.Gw.comps, x.births = [] := fun x hx => c.weak.2.2.2.2.1 ⟨x, hx⟩
  have hlev : c.Gw.level = M := c.weak.2.2.1
  have hext : v.1 ∈ succExtComps M (termAlphabet A.NT A.pT A.DW A.dW) A.RT c.Gw.comps := by
    have h1 := (Finset.ext_iff.mp c.succ.2.2.1 v.1).1 v.2
    rw [hlev] at h1
    exact h1
  exact (frontierRows_grade_len hroots hext).1

/-- The row selection of the length frame is the complement of the retained rows. -/
theorem termSelect_iff (v : CompIn c.Gt'.comps) :
    (compGrade v.1 ≤ 1 ∧ (compWord M v.1).length = A.RT + 1) ↔ ¬ IsRetained M 1 A.RT v.1 := by
  have hg := termGrade_le c v
  rw [termRows_not_retained c v]
  exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩

/-- **Row Cauchy** at the terminal frame (length case; the fresh-prefix price). -/
def TermInnerRowsAt (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M) (kc : ℕ) (C : ℝ) : Prop :=
  ∀ yom, TermYomSpec c kc yom → OutsideRowCauchyStatement (termFrame c kc yom) false C

/-- **Marker readout** at the terminal frame. -/
def TermInnerMarkerAt (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M) (kc : ℕ) (C : ℝ) : Prop :=
  ∀ yom, TermYomSpec c kc yom → MarkerReadoutStatement (termFrame c kc yom) false C

/-- **Source-layer energy** at the terminal frame. -/
def TermInnerLayerAt (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M) (kc : ℕ) (C : ℝ) : Prop :=
  ∀ yom, TermYomSpec c kc yom → SourceLayerEnergyStatement (termFrame c kc yom) false C

/-- **The energy of the coarse family**: `‖Y₀‖_{ρ,k;π} ≤ C‖f‖₂`. -/
def TermInnerInitialAt (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M) (kc : ℕ) (C : ℝ) : Prop :=
  ∀ yom, (termFrame c kc yom).initialNorm ≤ C * c.normF

/-- **Identification** of the realization: some lifted edge inputs `yom` compatible with `Y_w`
have the omitted flux of `Gt'` a.e. equal to the classical omitted flux of `x.aY`. -/
def TermInnerIdentAt {c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M} (x : TermResAux c) (kc : ℕ) : Prop :=
  ∃ yom, TermYomSpec c kc yom ∧ ∀ v : CompIn c.Gt'.comps, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    ∀ᵐ y ∂(volume.restrict AVenhance.unitCube),
      omittedFlux c.Gt' (kc + 2 * A.pT) (IsRetained M 1 A.RT) yom v t y =
        omittedFluxClassical (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
          c.Gt' (c.Gt'.retained M 1 A.RT) x.aY v t y

/-- **Smoothness** of the classical readout of the omitted flux (the first clause of
`FrontierInnerAt`; classical order `K̂ - 2`, `applyClassical` of the kernels). -/
def TermInnerSmoothAt {c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M} (x : TermResAux c) (kc : ℕ) : Prop :=
  ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    ContDiff ℝ ((kc + 2 * A.pT : ℕ) : ℕ∞)
        (fun y => frontierReadout (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
          c.Gw c.Gt' (c.Gt'.retained M 1 A.RT) M 1 A.RT (c.D.eps (M - 1)) A.η₀ x.aY v t y) ∧
      IsZ2Periodic
        (fun y => frontierReadout (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
          c.Gw c.Gt' (c.Gt'.retained M 1 A.RT) M 1 A.RT (c.D.eps (M - 1)) A.η₀ x.aY v t y)

/-- The realization of the readout of the omitted flux of `yom` realizes the readout of the
classical flux. -/
theorem termInner_realizes (x : TermResAux c) (kc : ℕ) (yom)
    (hid : ∀ v : CompIn c.Gt'.comps, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      ∀ᵐ y ∂(volume.restrict AVenhance.unitCube),
        omittedFlux c.Gt' (kc + 2 * A.pT) (IsRetained M 1 A.RT) yom v t y =
          omittedFluxClassical (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
            c.Gt' (c.Gt'.retained M 1 A.RT) x.aY v t y)
    (RF : (termFrame c kc yom).ReadoutFlux)
    (hRF : (termFrame c kc yom).RealizesReadout false RF) :
    IsFluxRealization (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (kc + 2 * A.pT)
      (Set.Icc c.tp (c.a + A.T₀))
      (fun v t y => toFluxL
        (frontierReadout (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
          c.Gw c.Gt' (c.Gt'.retained M 1 A.RT) M 1 A.RT (c.D.eps (M - 1)) A.η₀ x.aY v t y))
      RF := by
  intro v t ht
  have h1 := hRF v t ht
  have h2 : ∀ᵐ y ∂(volume.restrict AVenhance.unitCube), ∀ v', omittedFlux c.Gt'
      (kc + 2 * A.pT) (IsRetained M 1 A.RT) yom v' t y =
      omittedFluxClassical (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
        c.Gt' (c.Gt'.retained M 1 A.RT) x.aY v' t y :=
    ae_all_iff.2 fun v' => hid v' t ht
  filter_upwards [h1, h2] with y hy1 hy2
  refine hy1.trans ?_
  unfold frontierReadout
  simp only [toFluxL, WithLp.toLp_ofLp]
  have hsel : ∀ c' ∈ c.Gt'.comps, (termFrame c kc yom).select false c' ↔ ¬ IsRetained M 1 A.RT c' := by
    intro c' hc'
    have := termSelect_iff c ⟨c', hc'⟩
    simpa only [Frame.select, termFrame, Bool.false_eq_true, ite_false] using this
  exact readoutFlux_congr M _ _ _ _ hsel _ _ v t y hy2

/-- The mass bound of the realization from the energy bound. -/
theorem termInner_massLe (kc : ℕ) (yom)
    (RF : (termFrame c kc yom).ReadoutFlux) (Y : ℝ)
    (hRFlp : ∀ v, MemLp (RF v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀))))
    (hY : Real.sqrt ((termFrame c kc yom).readoutEnergy RF) ≤ Y) :
    FluxMassLe (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root)
      (K := fun _ => kc + 2 * A.pT) (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW)
      (Set.Icc c.tp (c.a + A.T₀)) RF Y := by
  refine ⟨hRFlp, ?_⟩
  have hlaw := termLaw_mass_funext c
  rw [hlaw]
  exact hY

/-- The gains of the terminal frame multiply to the price of the response boundary. -/
theorem termFrame_gain (kc : ℕ) (yom) (hE : 0 < c.D.eps (M - 1)) :
    (termFrame c kc yom).rowGain false * (termFrame c kc yom).markerGain false *
      (termFrame c kc yom).layerGain false = c.frontPrice := by
  have hgain := frontier_gain_product (termFrame c kc yom) hE false
  refine hgain.trans ?_
  unfold TermResCtx.frontPrice
  show c.D.eps (M - 1) ^ (ocDelta c.D.α c.D.q / 2 + (A.RT : ℝ) * (ocDelta c.D.α c.D.q / 2)) = _
  congr 1
  ring

theorem termFrontPrice_nonneg (hE : 0 < c.D.eps (M - 1)) : 0 ≤ c.frontPrice := by
  unfold TermResCtx.frontPrice
  exact (Real.rpow_pos_of_pos hE _).le

theorem termNormF_nonneg : 0 ≤ c.normF := Real.sqrt_nonneg _

theorem termInner_real_chain {R n F fp C C' : ℝ} (hC : 0 ≤ C) (hfp : 0 ≤ fp) (hF : 0 ≤ F)
    (hn : 0 ≤ n) (hR : R ≤ (C ^ 3 * fp * n) ^ 2) (hI : n ≤ C * F) (hC' : C ^ 4 ≤ C') :
    Real.sqrt R ≤ C' * fp * F := by
  refine (Real.sqrt_le_sqrt hR).trans ?_
  rw [Real.sqrt_sq (by positivity)]
  calc C ^ 3 * fp * n ≤ C ^ 3 * fp * (C * F) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = C ^ 4 * fp * F := by ring
    _ ≤ C' * fp * F := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC' hfp) hF

/-- The readout realization with its energy bound, from the three analytic inputs. -/
theorem termInner_stage (kc : ℕ) {C₁ : ℝ} (yom) (hspec : TermYomSpec c kc yom)
    (hE : 0 < c.D.eps (M - 1)) (hν : 0 ≤ c.D.κ (M - 1))
    (hR : TermInnerRowsAt c kc C₁) (hM : TermInnerMarkerAt c kc C₁)
    (hL : TermInnerLayerAt c kc C₁) :
    ∃ RF : (termFrame c kc yom).ReadoutFlux, (termFrame c kc yom).RealizesReadout false RF ∧
      (∀ v, MemLp (RF v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀)))) ∧
      (termFrame c kc yom).readoutEnergy RF ≤
        (C₁ ^ 3 * c.frontPrice * (termFrame c kc yom).initialNorm) ^ 2 := by
  exact frame_stage_generic (termFrame c kc yom) hν C₁ c.frontPrice (termFrame_gain c kc yom hE)
    (hR yom hspec) (hM yom hspec) (hL yom hspec)

/-- **The inner flux at a context from its six parts.** -/
theorem frontierInnerAt_of_parts (x : TermResAux c) (kc : ℕ) {C₁ C' : ℝ} (hC₁ : 0 ≤ C₁)
    (hC' : C₁ ^ 4 ≤ C') (hE : 0 < c.D.eps (M - 1)) (hν : 0 ≤ c.D.κ (M - 1))
    (hR : TermInnerRowsAt c kc C₁) (hM : TermInnerMarkerAt c kc C₁)
    (hL : TermInnerLayerAt c kc C₁) (hI : TermInnerInitialAt c kc C₁)
    (hId : TermInnerIdentAt x kc) (hS : TermInnerSmoothAt x kc) :
    FrontierInnerAt c x kc C' := by
  refine ⟨hS, ?_⟩
  obtain ⟨yom, hspec, hid⟩ := hId
  obtain ⟨RF, hRF, hRFlp, hen⟩ := termInner_stage c kc yom hspec hE hν hR hM hL
  have h1 : 0 ≤ c.frontPrice := termFrontPrice_nonneg c hE
  have h2 : 0 ≤ c.normF := termNormF_nonneg c
  have h3 : 0 ≤ (termFrame c kc yom).initialNorm := frame_initialNorm_nonneg _
  have h4 : (termFrame c kc yom).initialNorm ≤ C₁ * c.normF := hI yom
  have hsq : Real.sqrt ((termFrame c kc yom).readoutEnergy RF) ≤ C' * c.frontPrice * c.normF :=
    termInner_real_chain hC₁ h1 h2 h3 hen h4 hC'
  have hreal := termInner_realizes c x kc yom hid RF hRF
  have hmass := termInner_massLe c kc yom RF _ hRFlp hsq
  exact ⟨RF, hreal, hmass⟩

end Terminal

/-- Positivity of `E_{M-1}` and `κ_{M-1}` at a context. -/
theorem termInner_pos {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
    {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
    {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (hΛ128 : 128 ≤ A.Λ) :
    0 < c.D.eps (M - 1) ∧ 0 ≤ c.D.κ (M - 1) := by
  obtain ⟨hDα, hDq, hDΛ, -, -, hband, -⟩ := c.data
  have hΛD : 128 ≤ c.D.Λ := hDΛ ▸ hΛ128
  have hq1 : 1 < c.D.q := hDq ▸ X.hq.1
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ128
  exact ⟨(Scales.epsilon_basic hq1 hΛD).1,
    (CycleReference.bandChain_pos hΛ1 X.hζ hband (Nat.sub_le M 1)).le⟩

/-- **Row Cauchy at the terminal frame**. -/
def TermInnerRowsStatement : Prop :=
  TermResPrefix fun c _ kc _ C _ _ => TermInnerRowsAt c kc C

/-- **Marker readout at the terminal frame**. -/
def TermInnerMarkerStatement : Prop :=
  TermResPrefix fun c _ kc _ C _ _ => TermInnerMarkerAt c kc C

/-- **Source-layer energy at the terminal frame**. -/
def TermInnerLayerStatement : Prop :=
  TermResPrefix fun c _ kc _ C _ _ => TermInnerLayerAt c kc C

/-- **The energy of the coarse family**. -/
def TermInnerInitialStatement : Prop :=
  TermResPrefix fun c _ kc _ C _ _ => TermInnerInitialAt c kc C

/-- **Identification of the realization**. -/
def TermInnerIdentStatement : Prop :=
  TermResPrefix fun _ x kc _ _ _ _ => TermInnerIdentAt x kc

/-- **Smoothness and periodicity of the classical readout**. -/
def TermInnerSmoothStatement : Prop :=
  TermResPrefix fun _ x kc _ _ _ _ => TermInnerSmoothAt x kc

/-- **The inner flux from its six parts.** -/
theorem frontierInner_of_parts (hR : TermInnerRowsStatement) (hM : TermInnerMarkerStatement)
    (hL : TermInnerLayerStatement) (hI : TermInnerInitialStatement)
    (hId : TermInnerIdentStatement) (hS : TermInnerSmoothStatement) :
    FrontierInnerStatement := by
  have j5 := termFluxPrefix_and (P₁ := fun c x kc _ => TermInnerIdentAt x kc)
    (P₂ := fun c x kc _ => TermInnerSmoothAt x kc) hId hS
  have j4 := termFluxPrefix_and (P₁ := fun c _ kc C => TermInnerInitialAt c kc C)
    (P₂ := fun c x kc _ => TermInnerIdentAt x kc ∧ TermInnerSmoothAt x kc) hI j5
  have j3 := termFluxPrefix_and (P₁ := fun c _ kc C => TermInnerLayerAt c kc C)
    (P₂ := fun c x kc C => TermInnerInitialAt c kc C ∧
      (TermInnerIdentAt x kc ∧ TermInnerSmoothAt x kc)) hL j4
  have j2 := termFluxPrefix_and (P₁ := fun c _ kc C => TermInnerMarkerAt c kc C)
    (P₂ := fun c x kc C => TermInnerLayerAt c kc C ∧ (TermInnerInitialAt c kc C ∧
      (TermInnerIdentAt x kc ∧ TermInnerSmoothAt x kc))) hM j3
  have j1 := termFluxPrefix_and (P₁ := fun c _ kc C => TermInnerRowsAt c kc C)
    (P₂ := fun c x kc C => TermInnerMarkerAt c kc C ∧ (TermInnerLayerAt c kc C ∧
      (TermInnerInitialAt c kc C ∧ (TermInnerIdentAt x kc ∧ TermInnerSmoothAt x kc)))) hR j2
  refine termFluxPrefix_map (R := fun c x kc C => FrontierInnerAt c x kc C) ?_ j1
  intro X A kc C₁ hΛ hC₁
  refine ⟨C₁ ^ 4, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hP
    C' hC'
  obtain ⟨hRr, hMm, hLl, hIi, hIdd, hSs⟩ := hP
  obtain ⟨hE, hν⟩ := termInner_pos c hΛ
  exact frontierInnerAt_of_parts c x kc hC₁ hC' hE hν hRr hMm hLl hIi hIdd hSs

end AVRegularity.Construction.Residual.Presentation
end
end
end
