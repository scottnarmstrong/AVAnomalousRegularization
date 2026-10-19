-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.Construction.Preservation.FullLift.LiftCellSourceEffectiveAllDegrees

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Route

/-! Exact tail truncation assembled from three closed order-consistency ingredients. -/

/-- Postcompose the preparation map with componentwise Sobolev truncation. -/
def terminalTruncateMap {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (Gw : GenStage D ScalarH Dm b j₀) {Kw K L : ℕ} (hKL : K ≤ L)
    (P : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk L (ScalarH v.1.root))) :
    (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk K (ScalarH v.1.root)) :=
  (LinearMap.pi
    (φ := fun v : CompIn Gw.comps => TorusHk K (ScalarH v.1.root))
    (fun v : CompIn Gw.comps =>
      (truncateTorusHk (E := ScalarH v.1.root) hKL).toLinearMap.comp
        (LinearMap.proj (R := ℝ)
          (φ := fun v : CompIn Gw.comps => TorusHk L (ScalarH v.1.root)) v))).comp P

/-- Preparation normalization and its three estimates survive output truncation. -/
def TerminalPrepTruncationStatement : Prop :=
  ∀ {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (Gw : GenStage D ScalarH Dm b j₀)
    (M Kw K L k₀ : ℕ) (hKL : K ≤ L) (hk₀w : k₀ ≤ Kw) (hk₀K : k₀ ≤ K)
    (c C cr cK QT aM tp : ℝ) (law : BirthLaw) (_hmass : ∀ v, 0 ≤ Gw.mass law v) (f : Vec 2 → ℝ)
    (P : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk L (ScalarH v.1.root)))
    (V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root)),
    (IsTerminalPrepMap M Kw L c C Gw aM tp P →
      IsTerminalPrepMap M Kw K c C Gw aM tp (terminalTruncateMap Gw hKL P)) ∧
    (IsTerminalPrepBounds law M Kw L k₀ hk₀w (hk₀K.trans hKL) cr cK C QT f Gw aM tp P V →
      IsTerminalPrepBounds law M Kw K k₀ hk₀w hk₀K cr cK C QT f Gw aM tp (terminalTruncateMap Gw hKL P) V)

/-- The regularized solution, energy and outgoing datum survive truncation. -/
def TerminalFamilyTruncationStatement : Prop :=
  ∀ {D : OCData} {Dm Ds : ℕ} {b : ℝ} {j₀ : ℕ}
    (Gw Gt : GenStage D ScalarH Dm b j₀) (seed : GenStage D ScalarH Ds b j₀)
    (ι : CompIn Gt.comps ≃ CompIn seed.comps) (Pt : ProvParams) (seedKt freshKt : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (lawW lawT : BirthLaw)
    (_hmass : ∀ v, 0 ≤ Gw.mass lawW v) (rootM : ℕ → ℝ)
    (M K L : ℕ) (hKL : K ≤ L) (cr C Centry tp sn tf : ℝ) (f : Vec 2 → ℝ)
    (g : ∀ v : CompIn Gw.comps, TorusHk L (ScalarH v.1.root))
    (Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk L (ScalarH v.1.root)),
    TerminalFamilyClauses Pt seedKt freshKt φ₀ hφ₀ lawW lawT rootM M L cr C Centry tp sn tf f
      Gw Gt seed ι g Z →
    TerminalFamilyClauses Pt seedKt freshKt φ₀ hφ₀ lawW lawT rootM M K cr C Centry tp sn tf f
      Gw Gt seed ι (fun v => truncateTorusHk hKL (g v)) (fun v t => truncateTorusHk hKL (Z v t))

/-- Every lower covariance representative has the same readout as its higher canonical field. -/
def TerminalIdentityTruncationStatement : Prop :=
  ∀ {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (Gw Gt : GenStage D ScalarH Dm b j₀)
    (M pT K L Kw Lw NT depth sX sZ : ℕ) (hKL : K ≤ L)
    (η₀ tp a τ T₀ s Pw PT C cr : ℝ) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ)
    (V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
    (Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk L (ScalarH v.1.root)),
    EntryIdentityClauses Gw Gt M pT L Kw Lw NT depth sX sZ η₀ tp a τ T₀ s Pw PT C cr f θ Ww V Z →
    EntryIdentityClauses Gw Gt M pT K Kw Lw NT depth sX sZ η₀ tp a τ T₀ s Pw PT C cr f θ Ww V
      (fun v t => truncateTorusHk hKL (Z v t))

/-- Truncate the exact public tail, retaining all choices before its output objects. -/
theorem truncation_of_ingredients (hprep : TerminalPrepTruncationStatement)
    (hfamily : TerminalFamilyTruncationStatement) (hidentity : TerminalIdentityTruncationStatement) :
    TruncationStatement := by
  intro X A _ Kout Kout' hKK htail
  change BTail A Kout' at htail
  change BTail A Kout
  obtain ⟨SX, SZ, htail⟩ := htail
  refine ⟨SX, SZ, ?_⟩
  intro sXT sZT hSX hSZ
  obtain ⟨Kw, Lt, nW, hkw, hLw, cr, kS, hLt, hLp, hn, hk, hcr, hkcr, hc0, hcmax, hcr1,
    hσ, hlam, halloc, hplanS, hfloor, hcrone, htail⟩ := htail sXT sZT hSX hSZ
  refine ⟨Kw, Lt, nW, hkw, hLw, cr, kS, hLt, hLp, hn, hk, hcr, hkcr, hc0, hcmax, hcr1,
    hσ, hlam, halloc, hplanS, hfloor, hcrone, ?_⟩
  intro cK CK CL Cχ Cread Cid kW hcK hkW hweak
  obtain ⟨c, C, Centry, cH, Ce, Cw, hc, hcH, hCe, CHt, Υt, hCH, hΥ, htail⟩ :=
    htail cK CK CL Cχ Cread Cid kW hcK hkW hweak
  refine ⟨c, C, Centry, cH, Ce, Cw, hc, hcH, hCe, CHt, Υt, hCH, hΥ, ?_⟩
  intro j₀ hstart
  obtain ⟨M₀, htail⟩ := htail j₀ hstart
  refine ⟨M₀, ?_⟩
  intro M hM D hα hq hΛ hζ hΦ hκ hterm a lawW PW Gw aM Ww hstage
  have hmass : ∀ v, 0 ≤ Gw.mass lawW v := by
    intro v
    simpa only [GenStage.mass, compMass, hstage.2.2.2.2.1 v, List.map_nil,
      List.prod_nil, mul_one] using (lawW.rootMass_pos v.1.root).le
  obtain ⟨tp, P, lawT, Gt', seed, rootM, rootR, seedKc, ι, hp, hlaw, hsucc, hseed, hclauses,
    hdeadline, hdata⟩ := htail M hM D hα hq hΛ hζ hΦ hκ hterm a lawW PW Gw aM Ww hstage
  have hhat : A.Khat Kout ≤ A.Khat Kout' := max_le_max hKK le_rfl
  have hkh : A.k₀ ≤ A.Khat Kout := by dsimp only [TermArgs.Khat]; omega
  refine ⟨tp, terminalTruncateMap Gw hhat P, lawT, Gt', seed, rootM, rootR, seedKc, ι,
    (hprep Gw M Kw _ _ A.k₀ hhat hkw hkh c C cr cK A.QT aM tp lawW hmass (fun _ => 0) P
      (fun _ _ => 0)).1 hp, hlaw, hsucc, hseed, hclauses, hdeadline, ?_⟩
  intro f θ U₀ U V Uw Vw Uk Vk hpaired hread
  obtain ⟨hb, Z, hf, hi⟩ := hdata f θ U₀ U V Uw Vw Uk Vk hpaired hread
  refine ⟨(hprep Gw M Kw _ _ A.k₀ hhat hkw hkh c C cr cK A.QT aM tp lawW hmass f P V).2 hb,
    (fun v t => truncateTorusHk hhat (Z v t)), ?_, ?_⟩
  · exact hfamily Gw (Gt'.retained M 1 A.RT) seed ι _ _ _ _ _ lawW lawT hmass rootM M _ _ hhat
      cr C Centry tp (tp + D.termH M) (a + A.T₀) f _ Z hf
  · exact hidentity Gw (Gt'.retained M 1 A.RT) M A.pT _ _ Kw A.Lw A.NT A.dW sXT sZT hhat
      A.η₀ tp a A.τ A.T₀ X.s A.Pw A.PT C cr f θ Ww V Z hi

end AVRegularity.EntryTerminal.Route
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.EntryTerminal.Route

/-! Transfer the universal identity through the canonical higher covariance carrier. -/

/-- Both the canonical lift and every lower-order lift retain the terminal readout. -/
theorem terminalIdentityTruncation : TerminalIdentityTruncationStatement := by
  intro D Dm b j₀ Gw Gt M pT K L Kw Lw NT depth sX sZ hKL
    η₀ tp a τ T₀ s Pw PT C cr f θ Ww V Z h
  obtain ⟨⟨Cc₀, PZ₀, a₀, u₀, hf₀⟩, hall⟩ := h
  have hsub : K - 2 * pT ≤ L - 2 * pT := Nat.sub_le_sub_right hKL _
  let PZK := fun v t => truncateTorusHk hsub (PZ₀ v t)
  have hcov v t (ht : t ∈ Set.Icc tp (a + T₀)) :
      IsCovImage (covPolyP (termCovPrimitive D M tp t) pT)
        (succReadout M (D.eps (M - 1)) η₀ K (fun v' => truncateTorusHk hKL (Z v' t)) v)
        (PZK v t) := by
    rw [← truncate_succReadout (hr := ScalarH) hKL]
    exact covImage_truncate_input hKL _ _ _
      (covImage_truncate hsub _ _ _ (hf₀.2.1 v t ht).1)
  have hrep v t (ht : t ∈ Set.Icc tp (a + T₀)) :
      IsClassicalRep (PZK v t) (fun x => a₀ t x v) (K - 2 * pT) :=
    classicalRep_truncate hsub le_rfl _ _
      (classicalRep_order_mono _ _ (hf₀.2.1 v t ht).2 hsub)
  constructor
  · exact ⟨Cc₀, PZK, a₀, u₀, hf₀.1, fun v t ht => ⟨hcov v t ht, hrep v t ht⟩, hf₀.2.2⟩
  · intro Cc PZ aRep u hf
    have heq v t (ht : t ∈ Set.Icc tp (a + T₀)) :
        (fun x => aRep t x v) = fun x => a₀ t x v :=
      classical_covImage_rep_unique _ _ (PZ v t) (PZK v t)
        (hf.2.1 v t ht).1 (hcov v t ht) _ _ (hf.2.1 v t ht).2 (hrep v t ht)
    have hhigh : IsTerminalLiftedField Gw Gt M pT L NT depth sX sZ η₀ tp (a + T₀) cr
        Z Cc PZ₀ aRep u := by
      refine ⟨hf.1, ?_, hf.2.2⟩
      intro v t ht
      refine ⟨(hf₀.2.1 v t ht).1, ?_⟩
      rw [heq v t ht]
      exact (hf₀.2.1 v t ht).2
    exact hall Cc PZ₀ aRep u hhigh

/-! Preparation normalization and estimates at lower output order. -/

/-- Positive component masses make Sobolev truncation contract the weighted norm. -/
theorem terminalWeightedNorm_truncate_le {S : Finset Comp} {K L : ℕ} (hKL : K ≤ L)
    (ρ : ℝ) (π : CompIn S → ℝ) (hπ : ∀ v, 0 ≤ π v)
    (g : ∀ v : CompIn S, TorusHk L (ScalarH v.1.root)) :
    weightedNorm ρ π (fun _ => 1) (fun v => truncateTorusHk hKL (g v)) ≤
      weightedNorm ρ π (fun _ => 1) g := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_left
    (CycleComparison.Error.factorialNormSq_truncateTorusHk_le hKL ρ (g v))
  simpa only [one_pow, div_one] using inv_nonneg.mpr (hπ v)

/-- The three preparation bounds and preservation of constants are order consistent. -/
theorem terminalPrepTruncation : TerminalPrepTruncationStatement := by
  intro D Dm b j₀ Gw M Kw K L k₀ hKL hk₀w hk₀K c C cr cK QT aM tp law hmass f P V
  constructor
  · rintro ⟨hq, ha, hb, hn, hcol⟩
    refine ⟨hq, ha, hb, ?_, hcol⟩
    intro cv X hX v
    exact (KernelEnergy.truncateTorusHk_toFunction_jet_ae hKL (P X v)
      (valueIndex2 K)).trans (hn cv X hX v)
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨(terminalWeightedNorm_truncate_le hKL _ _ hmass _).trans h₁, ?_, ?_⟩
    · simpa only [terminalTruncateMap, LinearMap.comp_apply, LinearMap.pi_apply,
        LinearMap.proj_apply, ContinuousLinearMap.coe_coe, truncateTorusHk_comp_apply] using h₂
    · simpa only [terminalTruncateMap, LinearMap.comp_apply, LinearMap.pi_apply,
        LinearMap.proj_apply, ContinuousLinearMap.coe_coe, truncateTorusHk_comp_apply] using h₃

/-! Truncation of the coarse terminal solution, its trace, energy and seed datum. -/

private theorem trace_truncate {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ K L : ℕ}
    (Gw Gt : GenStage D ScalarH Dm b j₀) (hKL : K ≤ L)
    (g : CompIn Gw.comps → TorusHk L ℝ)
    (Z₀ : CompIn Gt.comps → TorusHk L ℝ)
    (h : IsTerminalTrace Gw Gt g Z₀) :
    IsTerminalTrace Gw Gt (fun v => truncateTorusHk hKL (g v))
      (fun v => truncateTorusHk hKL (Z₀ v)) := by
  constructor
  · intro v hv
    exact congrArg (fun u : TorusHk L ℝ => truncateTorusHk hKL u) (h.1 v hv)
  · intro v hv
    simpa only [map_zero] using
      congrArg (fun u : TorusHk L ℝ => truncateTorusHk hKL u) (h.2 v hv)

/-- The native family certificate and all its estimates persist at lower order. -/
theorem terminalFamilyTruncation : TerminalFamilyTruncationStatement := by
  intro D Dm Ds b j₀ Gw Gt seed ι Pt seedKt freshKt φ₀ hφ₀ lawW lawT hmass rootM
    M K L hKL cr C Centry tp sn tf f g Z h
  obtain ⟨Z₀, Zw, Zk, htrace, hsol, henergy, fn, hfn, hbound⟩ := h
  change IsTerminalTrace Gw Gt g Z₀ at htrace
  have ht := trace_truncate Gw Gt hKL g Z₀ htrace
  have hs := native_reg_solution_truncate (hr := ScalarH) Pt seedKt freshKt φ₀ hφ₀ Gt
    (D.termB M) tp tf (streamVel (D.Φ (M - 1))) K L hKL Z₀ Z Zw Zk hsol
  have he := (add_le_add
    (ENNReal.ofReal_le_ofReal (terminalWeightedNorm_truncate_le hKL _ _ hmass g))
    (strongEnergy_truncate_le (h := fun v : CompIn Gt.comps => ScalarH v.1.root)
      hKL (D.termRho cr M) (D.termB M) (Gt.mass lawT) tp tf Z Zw)).trans henergy
  have hn : ∀ v, fn (ι v) = truncateTorusHk (Nat.zero_le K)
      (truncateTorusHk hKL (Z v sn)) := by
    intro v
    simpa only [truncateTorusHk_comp_apply] using hfn v
  exact ⟨_, _, _, ht, hs, he, fn, hn, hbound⟩

end AVRegularity.EntryTerminal.Route
end

section
namespace AVRegularity.EntryTerminal.Route

/-! The public terminal tail follows at every smaller output order. -/

/-- Truncate the same terminal model without changing its plans, constants or readouts. -/
theorem truncation : TruncationStatement :=
  truncation_of_ingredients terminalPrepTruncation terminalFamilyTruncation terminalIdentityTruncation

end AVRegularity.EntryTerminal.Route
end
