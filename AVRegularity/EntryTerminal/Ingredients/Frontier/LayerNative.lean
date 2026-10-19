-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Assembly.Seed.PricedSchur
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.SchurF
public import AVRegularity.EntryTerminal.Ingredients.Frontier.InnerWrappers
public import AVRegularity.Construction.Preservation.RetainedEnergy.UniformInputs
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.EntryTerminal.Ingredients.SeedStruct.SeedStruct
import AVRegularity.Construction.Preservation.FullLift.NativeHigherRetainedFromSameOrder
import AVRegularity.Construction.Preservation.Frontier.LengthEnergy.AtData
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Definitions.Finite.FiniteLiftBridge
import AVRegularity.EntryWeakAssembly.PositiveCutoffMetricEllipticity
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup

section
@[expose] public noncomputable section

section
open Homogenization AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.EntryTerminal.Ingredients.Frontier

/-! Scalar thresholds for the terminal frontier. The weak ledger and the fresh
birth ledger decay at positive exponents. Their prices, including the native
operator constant, are fixed before the level and the terminal context. -/

private theorem Rows_absorption {tc a b r A Cχ e z K₁ K₂ : ℝ}
    (htc : 0 ≤ tc) (ha : 0 ≤ a)
    (hA : 0 ≤ A) (he : 0 ≤ e) (hz : 0 ≤ z)
    (htK : tc ≤ K₁) (haK : A * a ≤ K₁) (hbK : A * b * r ≤ K₂)
    (h₁ : K₁ * ((|Cχ| + 1) * e) ≤ 1 / 16)
    (h₂ : K₂ * z ≤ 1 / 16) :
    tc * max (Cχ * e) 0 ≤ 1 / 2 ∧
      A * (a * max (Cχ * e) 0 + b * (r * z)) ≤ 1 / 8 := by
  have he' : 0 ≤ (|Cχ| + 1) * e := mul_nonneg (by positivity) he
  have hmax : max (Cχ * e) 0 ≤ (|Cχ| + 1) * e := max_le
    (mul_le_mul_of_nonneg_right ((le_abs_self Cχ).trans (by linarith only [abs_nonneg Cχ])) he) he'
  have ht : tc * max (Cχ * e) 0 ≤ 1 / 16 :=
    (mul_le_mul_of_nonneg_left hmax htc).trans
      ((mul_le_mul_of_nonneg_right htK he').trans h₁)
  refine ⟨ht.trans (by norm_num), ?_⟩
  calc A * (a * max (Cχ * e) 0 + b * (r * z))
      ≤ A * (a * ((|Cχ| + 1) * e) + b * (r * z)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hmax ha) le_rfl) hA
    _ = (A * a) * ((|Cχ| + 1) * e) + (A * b * r) * z := by ring
    _ ≤ K₁ * ((|Cχ| + 1) * e) + K₂ * z :=
      add_le_add (mul_le_mul_of_nonneg_right haK he') (mul_le_mul_of_nonneg_right hbK hz)
    _ ≤ 1 / 8 := by linarith only [h₁, h₂]

/-- One threshold gives the birth-factor bound and both ledger absorption bounds. -/
theorem Rows_small {q χ θ η : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (hχ : 0 < χ) (hθ : 0 < θ) (hη : 0 < η)
    (Cw A Cχ cH : ℝ) (wc T L : ℕ) (hCw : 0 ≤ Cw) (hA : 0 ≤ A)
    (hcH : 0 < cH) (hwc : 0 < wc) :
    ∃ Ms : ℕ, ∀ M, Ms ≤ M →
      cH / (wc : ℝ) * ocEpsilon q Λ (M - 1) ^ η ≤ 1 ∧
      ledgerTransportConstant Cw T * max (Cχ * ocEpsilon q Λ M ^ χ) 0 ≤ 1 / 2 ∧
      A * (4 * ((T : ℝ) + 1) * (Cw + 1) * max (Cχ * ocEpsilon q Λ M ^ χ) 0 +
        2 * ((T : ℝ) + 1) * ((L : ℝ) + 1) * (Cw + 1) *
          ((1 + Real.sqrt ((wc : ℝ) / cH)) * ocEpsilon q Λ (M - 1) ^ θ)) ≤ 1 / 8 := by
  let tc := ledgerTransportConstant Cw T
  let a := 4 * ((T : ℝ) + 1) * (Cw + 1)
  let b := 2 * ((T : ℝ) + 1) * ((L : ℝ) + 1) * (Cw + 1)
  let r := 1 + Real.sqrt ((wc : ℝ) / cH)
  have htc : 0 ≤ tc := by unfold tc ledgerTransportConstant; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  let K₁ := 1 + tc + A * a
  let K₂ := 1 + A * b * r
  have hK₁ : 0 < K₁ := by dsimp [K₁]; positivity
  have hK₂ : 0 < K₂ := by dsimp [K₂]; positivity
  obtain ⟨Ms, hMs⟩ := small_core hq hΛ hχ hθ hη K₁ K₂ Cχ 1 cH wc
    hK₁ hK₂ le_rfl hcH hwc
  refine ⟨Ms, fun M hM => ?_⟩
  obtain ⟨hbirth, h₁, h₂⟩ := hMs M hM
  have he := Real.rpow_nonneg (Scales.epsilon_basic (m := M) hq hΛ).1.le χ
  have hz := Real.rpow_nonneg (Scales.epsilon_basic (m := M - 1) hq hΛ).1.le θ
  have hAbs := Rows_absorption htc ha hA he hz
    (b := b) (r := r) (Cχ := Cχ) (K₁ := K₁) (K₂ := K₂) (by dsimp [K₁]; linarith only [mul_nonneg hA ha])
    (by dsimp [K₁]; linarith only [htc])
    (by dsimp [K₂]; linarith only []) (by simpa only [mul_one] using h₁)
    (by simpa only [mul_one] using h₂)
  exact ⟨hbirth, hAbs⟩

end AVRegularity.EntryTerminal.Ingredients.Frontier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.Construction.Preservation.Ledger
open AVRegularity.Construction.Preservation.RetainedEnergy
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux
namespace AVRegularity.EntryTerminal.Ingredients.Frontier

/-! **the native kernel operator of the terminal successor `Gt'`, all rows.**

`kernelZero_all` is the zero-order regularizer of every row of `Gt'` (the kernel families are
the constant isotropic paired kernels of `A.Kw_`, `A.Kn_`).
`operator'` applies the native kernel operator of the cascade (`NativeKernelOperatorsAt`) to
`Gt'` at the terminal data, with the widths of every row (`width_all`) and the full marked
ledger of `Gt'` (`full_ledger_gen`). If there are no identities the statement is vacuous. -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **Zero-order regularizer.** The zero-order regularizer, at every radius, of every row of `Gt'`, from the isotropic
constants `c₁` (order `n_W`) and `c₂` (order `n_T`) below `cc`. -/
theorem kernelZero_all
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (hΛ : 128 ≤ A.Λ) (hcr : 0 < cr) (c₁ c₂ cc : ℕ → ℝ)
    (h₁ : ∀ r : ℝ, 0 < r → ∀ ρ a b k Dm',
      IsSpatialRegularizerTorus (G := ℝ) ρ k Dm' a b c₁ r ((isoPairedKernel r nW).op A.φ₀ A.hφ₀))
    (h₂ : ∀ r : ℝ, 0 < r → ∀ ρ a b k Dm',
      IsSpatialRegularizerTorus (G := ℝ) ρ k Dm' a b c₂ r ((isoPairedKernel r A.nT).op A.φ₀ A.hφ₀))
    (hc₁ : ∀ j, c₁ j ≤ cc j) (hc₂ : ∀ j, c₂ j ≤ cc j) :
    ∀ v u (γ : c.Gt'.fam.Γ v u), ∀ ϱ : ℝ, 0 < ϱ →
      IsSpatialRegularizerTorus ϱ 0 A.Dt c.tp (c.a + A.T₀) cc
        (c.Gt'.kernelOf (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) v u γ).width
        (c.Gt'.sysS (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ A.hφ₀ v u γ) := by
  obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := by rw [hΛD]; omega
  have hε : ∀ i, 0 < c.D.eps i := fun i => Construction.Stream.ocEpsilon_pos hΛ1
  have hν : 0 < c.D.κ (M - 1) :=
    CycleReference.bandChain_pos (by omega : 1 ≤ A.Λ) X.hζ hband (Nat.sub_le M 1)
  have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos hΛ1
  have hρ : 0 < c.D.termRho cr M := mul_pos hcr (Real.sqrt_pos.2 (mul_pos hν hh))
  exact kernelOf_zero_regularizer_of_iso c.Gt' (A.Pt c.D Cw cr M) A.φ₀ A.hφ₀
    (c.D.termRW A.σw M) (c.D.termRNew cr A.tT M) nW A.nT
    (Real.rpow_pos_of_pos (hε M) _) (mul_pos hρ (Real.rpow_pos_of_pos (hε (M - 1)) _))
    c₁ c₂ cc c.tp (c.a + A.T₀) h₁ h₂ hc₁ hc₂

/-- **The native kernel operator of `Gt'`** at the order `kk`, the radius `ρ_T = rhoEnh`, the
diffusivity `κ_{M-1}` and the weights `π/marker²`, with the data of the terminal passage. -/
theorem operator'
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) {CH Υ : ℝ} (hV : A.Valid) (hΛ : 128 ≤ A.Λ)
    (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ) (hcar : IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀)
    (hX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT)
    (hj : j₀ + 1 ≤ M) (hM2 : 2 ≤ M) (hρε : c.D.termRho cr M ≤ c.D.eps (M - 1))
    (hCL : CL * c.D.eps (M + 1) ≤ c.D.eps (M - 1)) (htptf : c.tp ≤ c.a + A.T₀)
    (cc : ℕ → ℝ) (kk : ℕ) (A₁ : ℝ) (m₁ : ℕ)
    (hreg0 : ∀ v u (γ : c.Gt'.fam.Γ v u), ∀ ϱ : ℝ, 0 < ϱ →
      IsSpatialRegularizerTorus ϱ 0 A.Dt c.tp (c.a + A.T₀) cc
        (c.Gt'.kernelOf (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) v u γ).width
        (c.Gt'.sysS (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ A.hφ₀ v u γ))
    (hop : NativeKernelOperatorsAt X.α X.q X.ζ A.Λ A.bw kk A.Dt cc A₁ m₁) (hm₁ : m₁ + 2 ≤ M)
    {Sb : ℝ} (hSb : markedLedger (c.Gt'.mass c.lawT) (c.Gt'.marker c.lawT) c.Gt'.fam ≤ Sb)
    (hsm : A₁ * Sb ≤ 1 / 8) :
    ∃ R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn c.Gt'.comps => ScalarH v.1.root)
        (Γ := c.Gt'.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) c.tp (c.a + A.T₀)
        (rhoEnh c.D cr M) (c.D.κ (M - 1)) kk A.Dt,
      R.B = (fun (v u : CompIn c.Gt'.comps) (γ : c.Gt'.fam.Γ v u)
          (d : ↥(Finset.Icc 2 A.Dt)) => c.Gt'.physCoeff v u γ d.1) ∧
      R.C = (fun (v u : CompIn c.Gt'.comps) (_ : c.Gt'.fam.Γ v u) =>
          ContinuousLinearMap.id ℝ (ScalarH u.1.root)) ∧
      R.S = c.Gt'.sysS (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ A.hφ₀ ∧
      R.π = (fun v => c.Gt'.mass c.lawT v / c.Gt'.marker c.lawT v ^ 2) ∧
      R.r = (fun v u γ => (c.Gt'.kernelOf (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr)
        v u γ).width) ∧ R.c = cc ∧ R.θ = A₁ * Sb := by
  have hST := termCtx_slotTransverse c x hV hΛ hCH hΥ hcar hX hZ
  have hsh := termCtx_shiftInvariant c hΛ
  obtain ⟨hα, hq, hΛD, hζD, hseq, hband, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := by rw [hΛD]; omega
  have hΛ128 : 128 ≤ c.D.Λ := by rw [hΛD]; exact hΛ
  have hq1 : 1 < c.D.q := by rw [hq]; exact X.hq.1
  have hlevW : c.Gw.level = M := c.weak.2.2.1
  have hbirth : ∀ w : CompIn c.Gw.comps, w.1.births = [] := c.weak.2.2.2.2.1
  have hlev : c.Gt'.level = M - 1 := by rw [c.succ.2.1, hlevW]
  have hres : ∀ w : CompIn c.Gt'.comps, 0 ≤ compReserve kW w.1 := fun w =>
    termReserve_nonneg x.reserve1
      (termGrade_le_one (fun u => by simp [compGrade, hbirth u]) c.succ w)
  have hres2 : ∀ w : CompIn c.Gt'.comps, compReserve kW w.1 ≤ 2 := fun w =>
    (AVRegularity.Providers.CascadeInvariants.compReserve_le_one kW w.1).trans (by norm_num)
  have hnat := c.succ.2.2.2.1
  have hεpos : 0 < c.D.eps (M - 1 - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hν : 0 < c.D.κ (M - 1) :=
    CycleReference.bandChain_pos (by omega : 1 ≤ A.Λ) X.hζ hband (Nat.sub_le M 1)
  have hρ0 : 0 < c.D.termRho cr M := by
    unfold OCData.termRho OCData.termB
    have h1 : 0 < cr := by rw [x.one]; exact one_pos
    have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos hΛ1
    exact mul_pos h1 (Real.sqrt_pos.2 (mul_pos hν hh))
  have hρ' : c.D.termRho cr M ≤ c.D.eps (c.Gt'.level - 1) := by
    rw [hlev]
    exact hρε.trans (EntryScales.epsilon_antitone hq1 hΛ128 (Nat.sub_le (M - 1) 1))
  have hρ2 : c.D.termRho cr M ≤ c.D.eps c.Gt'.level := by rw [hlev]; exact hρε
  have hWL := width_all (passCtx c) hq1 hΛ128 hCL (by
    rw [← hlev]; exact hρ')
  have hkap : c.D.kap c.Gt'.level = c.D.κ (M - 1) := by
    unfold OCData.kap
    rw [hlev, Nat.min_eq_left (by rw [hterm]; omega)]
  have hν' : 0 < c.D.kap c.Gt'.level := by rw [hkap]; exact hν
  have hlen : ∀ v u (γ : c.Gt'.fam.Γ v u), 3 ≤ (c.Gt'.fam.identity v u γ).maxOrder →
      (c.Gt'.fam.identity v u γ).record.length ≤ c.D.eps (c.Gt'.level - 1) := fun v u γ _ =>
    le_of_le_of_eq (hWL v u γ).2.1 (by rw [hlev])
  have hop' := hop ScalarH c.D hα hq hΛD hζD hseq j₀ _ c.Gt' kW x.cert hnat hsh
    (by rw [hlev]; omega) (by rw [hlev]; omega) (by rw [hlev]; omega)
    (by rw [hlev]; exact hεpos) (by rw [hlev]; exact Construction.Stream.ocEpsilon_pos hΛ1)
    hν' hST hres hres2 (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr)
    (fun v u γ => (hWL v u γ).1) A.φ₀ A.hφ₀ c.tp (c.a + A.T₀) (c.D.termRho cr M) Sb
    (c.Gt'.mass c.lawT) (c.Gt'.marker c.lawT) htptf hρ0 hρ' hρ2 hlen
    (fun v => AVRegularity.Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛ128 c.lawT v.1)
    (fun v => AVRegularity.Construction.Preservation.Buffer.birth_compMarker_pos hq1 hΛ128 c.lawT v.1) hSb hsm
    (fun v u γ => hreg0 v u γ _ hρ0) (c.Gt'.marker c.lawT) (Or.inr rfl)
  rw [hkap] at hop'
  exact hop'

end AVRegularity.EntryTerminal.Ingredients.Frontier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.Construction.Preservation.Ledger
open AVRegularity.Construction.Preservation.Frontier AVRegularity.Construction.Preservation.Frontier.LengthPrice
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux
namespace AVRegularity.EntryTerminal.Ingredients.Frontier

/-! **the fresh-prefix price of the terminal successor at one context.**

At a `TermResCtx` with the thresholds of the uniform native estimates (the operator constant `A₁`,
the identity-price constant `A₂`), the smallness of the ledger and a nonempty window, the price
`FreshPrefixPriceStatement (termFrame c kc yom) l (freshPrefixConstantGen Cw A₂ R_l Mn)` holds for
every `l ≥ 1` and every `yom` satisfying `TermYomSpec`. The proof is
`fresh_prefix_price_of_actual_gen` at the frame with exponents `(θ_T - η₀/4, θ_T)`, followed by
`freshPrice_of_larger_exponent`.

For `C_w = 0` or `A₂ = 0` the price constant is `0`. -/

/-- The bound of the marked ledger of the successor (`full_ledger_gen`). -/
def Bound (Cw : ℝ) (Mn : SuccMenu) (S R : ℝ) : ℝ :=
  4 * (((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) + 1) * (Cw + 1) * S +
    2 * (((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) + 1) * ((Mn.A.card : ℝ) + 1) * (Cw + 1) * R

/-- The exponent `θ_T = δ - η₀ - t_T s_T` of the later prefixes. -/
def laterPrefixExponent {X : TermConstruction} (D : OCData) (A : TermArgs X) : ℝ :=
  ocDelta D.α D.q - A.η₀ - A.tT * (termExcess A.NT A.pT A.alph : ℝ)

/-- The first-prefix birth factor `R_l = 1 + √(#words / c_H)` of the terminal law. -/
def firstPrefixBirthFactor (law : BirthLaw) : ℝ := 1 + Real.sqrt ((law.wordCount : ℝ) / law.cH)

/-- The price is monotone in its constant. -/
theorem price_mono {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (F : Frame D hr Dm bw j₀)
    (hE : 0 < D.eps (F.m - 1)) (l : ℕ) {C C' : ℝ} (hCC : C ≤ C')
    (h : FreshPrefixPriceStatement F l C) : FreshPrefixPriceStatement F l C' := by
  obtain ⟨hprov, P, hB, hC', hπ, hθ0, hθ, hy⟩ := h
  refine ⟨hprov, P, hB, hC', hπ, hθ0, hθ.trans ?_, hy⟩
  exact mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg hE.le _)

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **The fresh-prefix price of the terminal successor at one context.** -/
theorem price_ctx
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) {CH Υ : ℝ} (hV : A.Valid) (hΛ : 128 ≤ A.Λ)
    (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ) (hcar : IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀)
    (hX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT)
    (hj : j₀ + 1 ≤ M) (hM2 : 2 ≤ M) (hρε : c.D.termRho cr M ≤ c.D.eps (M - 1))
    (hCL : CL * c.D.eps (M + 1) ≤ c.D.eps (M - 1)) (htptf : c.tp ≤ c.a + A.T₀)
    (kc : ℕ) (cc : ℕ → ℝ) (hcc : ∀ j, 0 ≤ cc j)
    (hreg0 : ∀ v u (γ : c.Gt'.fam.Γ v u), ∀ ϱ : ℝ, 0 < ϱ →
      IsSpatialRegularizerTorus ϱ 0 A.Dt c.tp (c.a + A.T₀) cc
        (c.Gt'.kernelOf (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) v u γ).width
        (c.Gt'.sysS (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ A.hφ₀ v u γ))
    (A₁ : ℝ) (m₁ : ℕ) (hA₁ : 0 ≤ A₁)
    (hop : Construction.Preservation.RetainedEnergy.NativeKernelOperatorsAt X.α X.q X.ζ A.Λ A.bw
      (kc + 2 * A.pT) A.Dt cc A₁ m₁) (hm₁ : m₁ + 2 ≤ M)
    (A₂ : ℝ) (m₂ : ℕ) (hA₂ : 0 ≤ A₂)
    (hu : UnifPriceAt X.α X.q A.Λ X.ζ A.bw (kc + 2 * A.pT) A.Dt cc A₂ m₂) (hm₂ : m₂ + 2 ≤ M)
    (hF1 : ∀ marked, 1 ≤ Construction.Preservation.Ledger.birthDiagonalFactor c.D.q c.D.Λ M
      c.lawT marked)
    (hsmL : Construction.Preservation.Assembly.ledgerTransportConstant Cw
      (wordsUpTo (A.Mt M sXT sZT c.tp cr).A ((A.Mt M sXT sZT c.tp cr).J + 1)).card *
        max (Cχ * c.D.eps M ^ A.χw) 0 ≤ 1 / 2)
    (hsmA : A₁ * Bound Cw (A.Mt M sXT sZT c.tp cr) (max (Cχ * c.D.eps M ^ A.χw) 0)
      (firstPrefixBirthFactor c.lawT * c.D.eps (M - 1) ^ (laterPrefixExponent c.D A - A.η₀ / 4)) ≤ 1 / 8)
    (yom : ∀ v u (_ : c.Gt'.fam.Γ v u), ℝ →
      TorusHk (kc + 2 * A.pT + A.Dt - 1) (ScalarH u.1.root))
    (hy : TermYomSpec c kc yom) (l : ℕ) (hl : 1 ≤ l) :
    FreshPrefixPriceStatement (termFrame c kc yom) l
      (freshPrefixConstantGen Cw A₂ (firstPrefixBirthFactor c.lawT) (A.Mt M sXT sZT c.tp cr)) := by
  classical
  have hCw : 0 ≤ Cw := x.cwNonneg
  obtain ⟨hα, hq, hΛD, hζD, hseq, hband, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := by rw [hΛD]; omega
  have hΛ128 : 128 ≤ c.D.Λ := by rw [hΛD]; exact hΛ
  have hq1 : 1 < c.D.q := by rw [hq]; exact X.hq.1
  have hlevW : c.Gw.level = M := c.weak.2.2.1
  have hlev : c.Gt'.level = M - 1 := by rw [c.succ.2.1, hlevW]
  obtain ⟨-, -, hlevW', -, hbirths, ⟨hseedprov, -, -⟩, -, -, -, hinv⟩ := c.weak
  obtain ⟨hmass, -, -, hiota, -, hetaB, -⟩ := c.law
  obtain ⟨-, htags, -, -, -, -, -, hled, -⟩ := hinv
  have hV' := hV
  obtain ⟨-, -, -, -, -, hsched, -⟩ := hV'
  obtain ⟨-, -, -, -, -, -, -, -, htT, -⟩ := hsched
  have hPeq : A.Pt c.D Cw cr M = genProvParams c.D Cw A.η₀ A.NT A.pT
      (fun _ => c.D.termRho cr M) (fun _ => c.D.termRNew cr A.tT M) :=
    termProvParams_eq_gen c.D Cw cr A.tT A.η₀ A.NT A.pT M
  have hsucc := c.succ
  rw [hPeq] at hsucc
  have hG : c.Gw.HasTags (genProvParams c.D Cw A.η₀ A.NT A.pT
      (fun _ => c.D.termRho cr M) (fun _ => c.D.termRNew cr A.tT M)) :=
    hasTags_of_seed_prov hseedprov htags
  have hold : ∀ v ∈ c.Gw.comps, ∀ e ∈ v.births, c.Gw.level ≤ e.scale := by
    intro v hv e he
    have h0 : v.births = [] := hbirths ⟨v, hv⟩
    rw [h0] at he
    exact absurd he (by simp)
  have hrb : (fun _ => c.D.termRNew cr A.tT M) (c.Gw.level - 1) =
      (fun _ => c.D.termRho cr M) (c.Gw.level - 1) * c.D.eps (c.Gw.level - 1) ^ A.tT := by
    rw [hlevW]; rfl
  have hled' : markedLedger (c.Gw.mass c.lawT) (c.Gw.marker c.lawT) c.Gw.fam ≤
      max (Cχ * c.D.eps M ^ A.χw) 0 :=
    (weak_ledger_lawT hbirths hmass hled).trans (le_max_left _ _)
  have hS0 : 0 ≤ max (Cχ * c.D.eps M ^ A.χw) 0 := le_max_right _ _
  have hA1 : 1 ≤ Construction.Preservation.Assembly.ledgerTransportConstant Cw
      (wordsUpTo (A.Mt M sXT sZT c.tp cr).A ((A.Mt M sXT sZT c.tp cr).J + 1)).card := by
    unfold Construction.Preservation.Assembly.ledgerTransportConstant
    have ht : 0 ≤ ((wordsUpTo (A.Mt M sXT sZT c.tp cr).A
      ((A.Mt M sXT sZT c.tp cr).J + 1)).card : ℝ) := Nat.cast_nonneg _
    nlinarith only [hCw, ht]
  have hhalf : max (Cχ * c.D.eps M ^ A.χw) 0 ≤ 1 / 2 :=
    (le_mul_of_one_le_left hS0 hA1).trans hsmL
  -- the ledger of the whole successor
  have hbirthR : ∀ marked, birthDiagonalFactor c.D.q c.D.Λ c.Gw.level c.lawT marked *
      c.D.eps (c.Gw.level - 1) ^ (ocDelta c.D.α c.D.q - A.η₀ - A.tT *
        (termExcess A.NT A.pT A.alph : ℝ)) ≤
      firstPrefixBirthFactor c.lawT * c.D.eps (M - 1) ^ (laterPrefixExponent c.D A - A.η₀ / 4) := by
    intro marked
    have hb := birth_bound_any hq1 hΛ128 c.lawT (by rw [hiota]) c.Gw.level
      (θ₁ := laterPrefixExponent c.D A - A.η₀ / 4) (θ₂ := laterPrefixExponent c.D A) (by rw [hiota, hetaB]; ring) marked
    rw [hlevW] at hb ⊢
    exact hb
  have hfull := full_ledger_gen (G := c.Gw) (G' := c.Gt') (Mn := A.Mt M sXT sZT c.tp cr)
    hq1 hΛ128 hCw htT.le hrb (fun l hl => termFresh_letters l hl) c.lawT
    (fun marked => by rw [hlevW]; exact hF1 marked) hbirthR hG hold hsucc hS0 hled' hsmL
  have hfull' : markedLedger (c.Gt'.mass c.lawT) (c.Gt'.marker c.lawT) c.Gt'.fam ≤
      Bound Cw (A.Mt M sXT sZT c.tp cr) (max (Cχ * c.D.eps M ^ A.χw) 0)
        (firstPrefixBirthFactor c.lawT * c.D.eps (M - 1) ^ (laterPrefixExponent c.D A - A.η₀ / 4)) := hfull
  have hB0 : 0 ≤ Bound Cw (A.Mt M sXT sZT c.tp cr) (max (Cχ * c.D.eps M ^ A.χw) 0)
      (firstPrefixBirthFactor c.lawT * c.D.eps (M - 1) ^ (laterPrefixExponent c.D A - A.η₀ / 4)) := by
    unfold Bound firstPrefixBirthFactor
    have hε : 0 < c.D.eps (M - 1) := Construction.Stream.ocEpsilon_pos hΛ1
    positivity
  obtain ⟨R, hRB, hRC, hRS, hRπ, hRr, hRc, hRθ⟩ := operator' c x hV hΛ hCH hΥ hcar hX hZ hj
    hM2 hρε hCL htptf cc (kc + 2 * A.pT) A₁ m₁ hreg0 hop hm₁ hfull' hsmA
  have hWL := width_all (passCtx c) hq1 hΛ128 hCL (by
    exact hρε.trans (EntryScales.epsilon_antitone hq1 hΛ128 (Nat.sub_le (M - 1) 1)))
  have hprice := price_all c x hV hΛ hCH hΥ hcar hX hZ hj hM2 hρε hCL (kc + 2 * A.pT)
    cc A₂ m₂ hm₂ hu
  have hε : 0 < c.D.eps (M - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hε1 : c.D.eps (M - 1) ≤ 1 := (Scales.epsilon_basic (m := M - 1) hq1 hΛ128).2.1
  have hfacts := termFresh_exponent_facts hV
  rw [← hα, ← hq] at hfacts
  have hη0 : 0 ≤ A.η₀ := by
    obtain ⟨-, -, -, -, -, hsch, -⟩ := hV
    obtain ⟨-, -, -, -, -, -, hη, -⟩ := hsch
    exact hη.le
  have hRl1 : 1 ≤ firstPrefixBirthFactor c.lawT := by
    unfold firstPrefixBirthFactor; linarith [Real.sqrt_nonneg ((c.lawT.wordCount : ℝ) / c.lawT.cH)]
  let F' : Frame c.D ScalarH A.Dt A.bw j₀ :=
    { termFrame c kc yom with θ₁ := laterPrefixExponent c.D A - A.η₀ / 4, θ₂ := laterPrefixExponent c.D A }
  have hmain : FreshPrefixPriceStatement F' l
      (freshPrefixConstantGen Cw A₂ (firstPrefixBirthFactor c.lawT) (A.Mt M sXT sZT c.tp cr)) := by
    refine fresh_prefix_price_of_actual_gen F' (Mn := A.Mt M sXT sZT c.tp cr) (S := max
      (Cχ * c.D.eps M ^ A.χw) 0) hq1 hΛ128 hCw htT.le hA₂ hrb
      (fun l hl => termFresh_letters l hl) hG hold hsucc hlevW rfl rfl hRl1 rfl
      ?_ hS0 hhalf (by exact hled') l hl R hRB hRC hRπ (by rw [hRc]; exact fun d _ => hcc d)
      (by rw [hRθ]; exact mul_nonneg hA₁ hB0) ?_ ?_
    · exact birth_bound_any hq1 hΛ128 c.lawT (by rw [hiota]) c.Gw.level
        (θ₁ := laterPrefixExponent c.D A - A.η₀ / 4) (θ₂ := laterPrefixExponent c.D A) (by rw [hiota, hetaB]; ring) true
    · intro v u γ
      rw [hRc, hRr]
      simp only [(hWL v u γ).1]
      exact hprice v u γ
    · intro v u γ hu'
      rw [hRS]
      exact hy v u γ hu'
  have hC0 : 0 ≤ freshPrefixConstantGen Cw A₂ (firstPrefixBirthFactor c.lawT) (A.Mt M sXT sZT c.tp cr) := by
    unfold freshPrefixConstantGen
    have := hRl1
    positivity
  refine freshPrice_of_larger_exponent (termFrame c kc yom) (laterPrefixExponent c.D A - A.η₀ / 4)
    (laterPrefixExponent c.D A) ?_ ?_ ?_ hε1 l _ hC0 hmain
  · show ocDelta c.D.α c.D.q / 2 ≤ laterPrefixExponent c.D A - A.η₀ / 4
    unfold laterPrefixExponent
    linarith
  · show ocDelta c.D.α c.D.q / 2 ≤ laterPrefixExponent c.D A
    unfold laterPrefixExponent
    linarith
  · exact hε

end AVRegularity.EntryTerminal.Ingredients.Frontier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Frontier
open AVRegularity.EntryTerminal.Ingredients.Frontier
namespace AVRegularity.Construction.Residual.Presentation

/-! Terminal frontier rows, assembled through fresh-prefix-price reduction.
The native operator, all-row widths and context price are proved elsewhere. The remaining inputs are the uniform prefix production and the integrability
of the retained gradient lift.

An empty family has no rows or integrability obligations; `R_T = 0`
needs only prefix length one; zero data does not change the operator price.
The truncation leaf also covers orders above `Khat`, where `truncTo` is zero.
All scalar prices and thresholds precede the terminal context. -/

/-- Uniform production of all terminal fresh-prefix prices at one common constant. -/
def RowsPricesAt {X : TermConstruction} {A : TermArgs X}
    {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+} {hk₀w : A.k₀ ≤ Kw}
    {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
    {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (kc : ℕ) (C : ℝ) : Prop :=
  c.tp ≤ c.a + A.T₀ →
  ∀ yom, TermYomSpec c kc yom → ∀ l : ℕ, 1 ≤ l → l ≤ A.RT + 1 →
    FreshPrefixPriceStatement (termFrame c kc yom) l C

/-- The terminal prefix around the fresh prices. -/
def RowsPriceStatement : Prop :=
  TermResPrefix fun c _ kc _ C _ _ => RowsPricesAt c kc C

/-- Time integrability of the total truncation of the retained solution's gradient lift. -/
def RowsMemStatement : Prop :=
  ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
    {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
    {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (kc : ℕ),
    ∀ u, MemLp (termYw c kc u) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀)))

private theorem Rows_empty {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (F : Frame D hr Dm bw j₀)
    (C : ℝ) (ht : F.tf < F.tp) : OutsideRowCauchyStatement F false C := by
  have he : Set.Icc F.tp F.tf = ∅ := Set.Icc_eq_empty_of_lt ht
  refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩
  · intro v t ht
    rw [he] at ht
    exact ht.elim
  · intro v
    exact MemLp.zero' (ε := TorusHk F.k (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
  · simp only [Frame.rowEnergy, Frame.sourceDissipation, he, Measure.restrict_empty, integral_zero_measure, mul_zero, le_refl]

/-- Exact terminal-row assembly: fresh prices and lift integrability give row Cauchy. -/
theorem Rows_of_ingredients (hprice : RowsPriceStatement)
    (hmem : RowsMemStatement) : TermInnerRowsStatement := by
  apply termFluxPrefix_map (P := fun c _ kc C => RowsPricesAt c kc C)
    (R := fun c _ kc C => TermInnerRowsAt c kc C) _ hprice
  intro X A kc C hΛ _
  refine ⟨C, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M
    c _ hp C' hC'
  by_cases hwin : c.tp ≤ c.a + A.T₀
  · apply termInnerRowsAt_of_price c kc C'
    · intro yom hy l hl hlt
      exact price_mono (termFrame c kc yom) (termInner_pos c hΛ).1 l hC'
        (hp hwin yom hy l hl hlt)
    · exact hmem c kc
  · intro yom _
    exact Rows_empty (termFrame c kc yom) C' (lt_of_not_ge hwin)

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
namespace AVRegularity.Construction.Residual.Presentation

/-! Integrability of the retained gradient at the frontier order. Total truncation
is a continuous linear map when the requested order is available, and is zero
otherwise. This includes empty families, empty time windows and all orders. -/

/-- The retained gradient lift stays in time L² after total truncation. -/
theorem Rows_mem : RowsMemStatement := by
  intro X A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M
    c kc u
  by_cases h : kc + 2 * A.pT + 1 ≤ A.Khat Kout + 1
  · change MemLp (fun t => truncTo (kc + 2 * A.pT + 1) (c.Zw u t)) 2
      (volume.restrict (Set.Icc c.tp (c.a + A.T₀)))
    simp only [truncTo, h, dite_true]
    exact (truncateTorusHk (E := ScalarH u.1.root) h).comp_memLp' (c.sol.2.1 u)
  · change MemLp (fun t => truncTo (kc + 2 * A.pT + 1) (c.Zw u t)) 2
      (volume.restrict (Set.Icc c.tp (c.a + A.T₀)))
    simp only [truncTo, h, dite_false]
    exact MemLp.zero' (ε := TorusHk (kc + 2 * A.pT + 1) (ScalarH u.1.root))

end AVRegularity.Construction.Residual.Presentation
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.Construction.Preservation.Ledger
open AVRegularity.Construction.Preservation.Frontier
open AVRegularity.Construction.Preservation.Frontier.LengthPrice
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.EntryTerminal.Ingredients.Frontier

/-! Uniform terminal frontier prices. All regularizer and native prices depend
only on the data and orders preceding the context; eventual scale smallness
absorbs the weak ledger and the fresh birth ledger. -/

/-- Uniform fresh-prefix prices on every ordered terminal window. -/
theorem Rows_prices : RowsPriceStatement := by
  classical
  intro X
  obtain ⟨Λc, hΛc, hcore⟩ := AVRegularity.EntryTerminal.Ingredients.seedStruct_scales X
  refine ⟨max Λc 128, le_max_right _ _, fun A hΛ hV => ?_⟩
  have hΛc' : Λc ≤ A.Λ := le_trans (le_max_left _ _) hΛ
  have h128 : 128 ≤ A.Λ := le_trans (le_max_right _ _) hΛ
  have hbw : 0 < A.bw := hV.2.2.1.1
  have hDt : 2 ≤ A.Dt := le_max_left _ _
  obtain ⟨hφsmooth, -, -, hφsupp⟩ := hV.2.1
  have hcompact := Providers.hasCompactSupport_of_unitBall hφsupp
  have hV' := hV
  obtain ⟨-, -, -, ⟨-, -, -, -, hσw, -, hχw, hη₀, -⟩, -, hsch, -⟩ := hV'
  have htT : 0 ≤ A.tT := hsch.2.2.2.2.2.2.2.2.1.le
  have hθ : 0 < ocDelta X.α X.q - A.η₀ -
      A.tT * (termExcess A.NT A.pT A.alph : ℝ) - A.η₀ / 4 :=
    lt_of_lt_of_le (half_pos (ocDelta_pos_of_admissible X.hα₀ X.hq))
      (termFresh_exponent_facts hV)
  refine ⟨0, fun kc _ => ?_⟩
  let S := max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2
  refine ⟨S, S, 0, fun sXT sZT hX hZ Kout _ => ⟨0, fun Kw Lt nW hk₀w _ cr kS _ _ _ _ _
    hcr0 _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _ cP CP cHP Cw Ce cker _ Cfl => ?_⟩⟩
  obtain ⟨c₁, hc₁, hr₁⟩ := WeakEntryProofs.exists_isoPairedKernel_regularizer_constants
    A.φ₀ hcompact hφsmooth A.hφ₀ nW
  obtain ⟨c₂, hc₂, hr₂⟩ := WeakEntryProofs.exists_isoPairedKernel_regularizer_constants
    A.φ₀ hcompact hφsmooth A.hφ₀ A.nT
  let cc : ℕ → ℝ := fun j => max (c₁ j) (c₂ j)
  have hcc : ∀ j, 0 ≤ cc j := fun j => (hc₁ j).trans (le_max_left _ _)
  obtain ⟨A₁, hA₁, m₁, _, hop⟩ := uniform_native_kernel_operator_of_certificates
    X.α X.s X.q X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq A.Λ h128 X.ζ X.hζ A.bw hbw
    (kc + 2 * A.pT) A.Dt hDt cc (fun j _ => hcc j)
  obtain ⟨A₂, hA₂, m₂, _, hunif⟩ := uniform_native_identity_kernel_price
    X.α X.s X.q X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq A.Λ h128 X.ζ X.hζ A.bw hbw
    (kc + 2 * A.pT) (kc + 2 * A.pT + A.Dt) A.Dt le_rfl cc (fun j _ => hcc j)
  have hu : UnifPriceAt X.α X.q A.Λ X.ζ A.bw
      (kc + 2 * A.pT) A.Dt cc A₂ m₂ :=
    fun D hDα hDq hDΛ hDζ hseq => hunif ScalarH D hDα hDq hDΛ hDζ hseq
  obtain ⟨Ms, hMs2, hMs⟩ := hcore A.Λ hΛc' cr A.σw A.tT CL hcr0 hσw.le htT
  by_cases hCw : 0 ≤ Cw
  swap
  · refine ⟨0, 1, 0, one_pos, 1, 1, le_rfl, one_pos,
      fun _ _ _ _ => ⟨0, fun _ _ _ x => ?_⟩⟩
    exact (hCw x.cwNonneg).elim
  by_cases hcHP : 0 < cHP
  swap
  · refine ⟨0, 1, 0, one_pos, 1, 1, le_rfl, one_pos,
      fun _ _ _ _ => ⟨0, fun _ _ c _ => ?_⟩⟩
    have hcH : 0 < cHP := by rw [← c.law.2.2.1]; exact c.lawT.cH_pos
    exact (hcHP hcH).elim
  let Rl : ℝ := 1 + Real.sqrt (((max 1 A.nWords : ℕ) : ℝ) / cHP)
  obtain ⟨Ma, hMa⟩ := Rows_small X.hq.1 h128 hχw hθ (half_pos hη₀)
    Cw A₁ Cχ cHP (max 1 A.nWords) (wordsUpTo A.alph (A.RT + 1)).card A.alph.card
    hCw hA₁ hcHP (lt_of_lt_of_le one_pos (le_max_left _ _))
  refine ⟨freshPrefixConstantGen Cw A₂ Rl (A.Mt 0 sXT sZT 0 cr), 1, 0, one_pos,
    1, 1, le_rfl, one_pos, fun C hC j₀ hcar => ?_⟩
  refine ⟨max Ms (max Ma (max (m₁ + 2) (max (m₂ + 2) (j₀ + 1)))),
    fun M hM c x hwin yom hy l hl _ => ?_⟩
  have hMs' : Ms ≤ M := le_trans (le_max_left _ _) hM
  have hMa' : Ma ≤ M := le_trans (le_max_left _ _) ((le_max_right _ _).trans hM)
  have hm₁ : m₁ + 2 ≤ M := le_trans (le_max_left _ _)
    ((le_max_right _ _).trans ((le_max_right _ _).trans hM))
  have hm₂ : m₂ + 2 ≤ M := by omega
  have hj : j₀ + 1 ≤ M := by omega
  obtain ⟨hDα, hDq, hDΛ, _, _, hband, _⟩ := c.data
  obtain ⟨-, hρε, -, hCL⟩ := hMs M hMs' c.D hDα hDq hDΛ hband
  obtain ⟨_, _, hcHeq, hiota, hwc, hetaB, _⟩ := c.law
  have hRl : firstPrefixBirthFactor c.lawT = Rl := by simp only [firstPrefixBirthFactor, hcHeq, hwc, Rl]
  obtain ⟨hbirth, hsmL, hsmA⟩ := hMa M hMa'
  have hF1 : ∀ marked, 1 ≤ birthDiagonalFactor c.D.q c.D.Λ M c.lawT marked := by
    intro marked
    refine birthFactor_ge_one (by rw [hDq]; exact X.hq.1)
      (by rw [hDΛ]; exact h128) c.lawT hiota ?_ marked
    rw [hcHeq, hwc, hetaB, hDq, hDΛ]
    exact hbirth
  have hsmallL : Construction.Preservation.Assembly.ledgerTransportConstant Cw
      (wordsUpTo (A.Mt M sXT sZT c.tp cr).A ((A.Mt M sXT sZT c.tp cr).J + 1)).card *
        max (Cχ * c.D.eps M ^ A.χw) 0 ≤ 1 / 2 := by
    simpa only [TermArgs.Mt, termMenu, OCData.eps, hDq, hDΛ] using hsmL
  have hsmallA : A₁ * Bound Cw (A.Mt M sXT sZT c.tp cr)
      (max (Cχ * c.D.eps M ^ A.χw) 0)
      (firstPrefixBirthFactor c.lawT * c.D.eps (M - 1) ^ (laterPrefixExponent c.D A - A.η₀ / 4)) ≤ 1 / 8 := by
    simpa only [Bound, TermArgs.Mt, termMenu, laterPrefixExponent, hRl, Rl, OCData.eps, hDα, hDq, hDΛ] using hsmA
  have hprice := price_ctx c x hV h128 le_rfl le_rfl hcar hX hZ hj
    (hMs2.trans hMs') hρε hCL hwin kc cc hcc
    (kernelZero_all c h128 hcr0 c₁ c₂ cc hr₁ hr₂
      (fun j => le_max_left _ _) (fun j => le_max_right _ _))
    A₁ m₁ hA₁ hop hm₁ A₂ m₂ hA₂ hu hm₂ hF1 hsmallL hsmallA yom hy l hl
  apply price_mono (termFrame c kc yom) (termInner_pos c h128).1 l _ hprice
  simpa only [freshPrefixConstantGen, TermArgs.Mt, termMenu, hRl] using hC

/-- The terminal outside rows satisfy the Cauchy estimate. -/
theorem termInnerRows : TermInnerRowsStatement :=
  Rows_of_ingredients Rows_prices Rows_mem

end AVRegularity.EntryTerminal.Ingredients.Frontier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.EntryTerminal.Ingredients.Frontier
open AVRegularity.Construction.Preservation.Frontier
open AVRegularity.Construction.Preservation.Frontier.LengthEnergy
namespace AVRegularity.Construction.Residual.Presentation

/-! Terminal source-layer energy: the proved fresh-prefix rows and scalar
induction reduce the statement to homogeneous empty-word contraction and forced
copied-block energy. The proved fixed-stage theorem combines these estimates from the native
kernel operator and the truncated retained solution, with zero new-word trace.

For `R_T = 0` only the empty-word contraction is needed; empty components and zero data require
no division; a singleton window has zero dissipation, and an empty window is handled directly.
All constants precede the context and level. -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- The actual all-row native operator and analytic drift budget of the terminal frame. -/
structure LayerNativeData (kc : ℕ) where
  R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn c.Gt'.comps => ScalarH v.1.root)
    (Γ := c.Gt'.fam.Γ) (G := fun _ u _ => ScalarH u.1.root)
    c.tp (c.a + A.T₀) (rhoEnh c.D cr M) (c.D.κ (M - 1)) (kc + 2 * A.pT) A.Dt
  coeff : R.B = fun (v u : CompIn c.Gt'.comps) (γ : c.Gt'.fam.Γ v u)
    (d : ↥(Finset.Icc 2 A.Dt)) => c.Gt'.physCoeff v u γ d.1
  identification : R.C = fun (v u : CompIn c.Gt'.comps) (_ : c.Gt'.fam.Γ v u) =>
    ContinuousLinearMap.id ℝ (ScalarH u.1.root)
  regularizer : R.S = c.Gt'.sysS (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW)
    (A.Kn_ c.D M cr) A.φ₀ A.hφ₀
  weight : R.π = fun v => c.Gt'.mass c.lawT v / c.Gt'.marker c.lawT v ^ 2
  admissible : IsAdmissibleStream (c.D.Φ (M - 1))
  αv : ℝ
  B : ℝ
  lam : ℝ
  alpha_nonneg : 0 ≤ αv
  drift_base : 1 ≤ B
  scale_pos : 0 < lam
  drift_small : B * rhoEnh c.D cr M / lam ≤ 1 / 2
  strain : αv * B * rhoEnh c.D cr M ^ 2 ≤ c.D.κ (M - 1) / 8
  jets : ∀ t ∈ Set.Icc c.tp (c.a + A.T₀), ∀ j, 1 ≤ j → j ≤ kc + 2 * A.pT → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (streamVel (c.D.Φ (M - 1)) t)) j x‖ ≤
      αv * B ^ j * (j.factorial : ℝ) * lam ^ ((1 : ℤ) - j)

/-- The retained solution at the frontier order, with zero trace on new words. -/
def LayerSolutionAt (kc : ℕ) : Prop :=
  let G := c.Gt'.retained M 1 A.RT
  ∃ Y : ∀ v : CompIn G.comps, ℝ → TorusHk (kc + 2 * A.pT) (ScalarH v.1.root),
  ∃ Yk : ∀ v u (_ : G.fam.Γ v u), ℝ →
      TorusHk (kc + 2 * A.pT + A.Dt - 1) (ScalarH u.1.root),
    G.IsRegSolution (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ A.hφ₀
      (c.D.κ (M - 1)) (streamVel (c.D.Φ (M - 1))) (kc + 2 * A.pT) c.tp (c.a + A.T₀)
      (termY0 c kc) (fun _ _ => 0) (fun _ _ => 0) Y (termYw c kc) Yk ∧
    ∀ v : CompIn G.comps, v.1 ∉ c.Gw.comps → termY0 c kc v = 0

/-- Native data are needed only on an ordered terminal window. -/
def LayerNativeAt (kc : ℕ) : Prop :=
  c.tp ≤ c.a + A.T₀ → Nonempty (LayerNativeData c kc)

/-- Uniform native operator and drift data on ordered terminal windows. -/
def LayerNativeStatement : Prop :=
  TermResPrefix fun c _ kc _ _ _ _ => LayerNativeAt c kc

/-- Uniform production of the honest truncation of the retained solution. -/
def LayerSolutionStatement : Prop :=
  TermResPrefix fun c _ kc _ _ _ _ => LayerSolutionAt c kc

private theorem Layer_empty {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (F : Frame D hr Dm bw j₀)
    (C : ℝ) (ht : F.tf < F.tp) : SourceLayerEnergyStatement F false C := by
  have he : Set.Icc F.tp F.tf = ∅ := Set.Icc_eq_empty_of_lt ht
  simp only [SourceLayerEnergyStatement, Frame.sourceDissipation, he,
    Measure.restrict_empty, integral_zero_measure, mul_zero]
  exact sq_nonneg _

/-- Exact layer assembly from native data and the truncated retained solution. -/
theorem Layer_of_ingredients (hnative : LayerNativeStatement)
    (hsolution : LayerSolutionStatement) : TermInnerLayerStatement := by
  apply termFluxPrefix_map
    (P := fun c _ kc C => RowsPricesAt c kc C ∧
      LayerNativeAt c kc ∧ LayerSolutionAt c kc)
    (R := fun c _ kc C => TermInnerLayerAt c kc C) _
    (termFluxPrefix_and Rows_prices (termFluxPrefix_and hnative hsolution))
  intro X A kc C hΛ hC
  refine ⟨(4 * C) ^ A.RT, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M
    c _ hparts C' hC' yom hy
  by_cases hwin : c.tp ≤ c.a + A.T₀
  · have hrows : WordLengthRowsStatement (termFrame c kc yom) C := by
      intro l hl hlJ
      exact word_length_row_of_price (termFrame c kc yom) l C hl hlJ
        (hparts.1 hwin yom hy l hl hlJ) (Rows_mem c kc)
    obtain ⟨d⟩ := hparts.2.1 hwin
    obtain ⟨Y, Yk, hsol, hzero⟩ := hparts.2.2
    have hold : ∀ v ∈ c.Gw.comps, ∀ e ∈ v.births, c.Gw.level ≤ e.scale := by
      intro v hv e he
      rw [c.weak.2.2.2.2.1 ⟨v, hv⟩] at he
      exact absurd he (by simp)
    have hq : 1 < c.D.q := by rw [c.data.2.1]; exact X.hq.1
    have hΛD : 128 ≤ c.D.Λ := by rw [c.data.2.2.1]; exact hΛ
    have henergy := length_source_energy_of_extended_operator (termFrame c kc yom) hq hΛD
      (A.Pt c.D Cw cr M) (A.Mt M sXT sZT c.tp cr) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr)
      A.φ₀ A.hφ₀ c.succ hold c.weak.2.2.1 d.R d.coeff d.identification d.regularizer d.weight
      d.admissible d.αv d.B d.lam d.alpha_nonneg d.drift_base d.scale_pos d.drift_small d.strain
      d.jets Y Yk hsol hzero (by rw [d.regularizer]; exact hy) C hrows (termInner_pos c hΛ).1
    apply SourceLayerEnergyStatement.mono (termFrame c kc yom) false _ henergy
    rw [abs_of_nonneg (pow_nonneg (mul_nonneg (by norm_num) hC) _)]
    exact hC'
  · exact Layer_empty (termFrame c kc yom) C' (lt_of_not_ge hwin)

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.Construction.Preservation
open AVRegularity.Construction.Preservation.Ledger
open AVRegularity.Construction.Preservation.RetainedEnergy
namespace AVRegularity.EntryTerminal.Ingredients.Frontier

/-! Native data at one terminal context. The full marked successor ledger is
obtained from the proved generic recurrence under lawT; the resulting operator
and the enhanced drift budget are the inputs of the generic layer theorem. -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The all-row operator and analytic drift data at sufficiently late levels. -/
theorem Layer_native_ctx
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c) {CH Υ : ℝ} (hV : A.Valid) (hΛ : 128 ≤ A.Λ)
    (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ) (hcar : IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀)
    (hX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT)
    (hj : j₀ + 1 ≤ M) (hM2 : 2 ≤ M) (hρε : c.D.termRho cr M ≤ c.D.eps (M - 1))
    (hCL : CL * c.D.eps (M + 1) ≤ c.D.eps (M - 1)) (hwin : c.tp ≤ c.a + A.T₀)
    (kc : ℕ) (cc : ℕ → ℝ)
    (hreg0 : ∀ v u (γ : c.Gt'.fam.Γ v u), ∀ ϱ : ℝ, 0 < ϱ →
      IsSpatialRegularizerTorus ϱ 0 A.Dt c.tp (c.a + A.T₀) cc
        (c.Gt'.kernelOf (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) v u γ).width
        (c.Gt'.sysS (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ A.hφ₀ v u γ))
    (A₁ : ℝ) (m₁ : ℕ)
    (hop : NativeKernelOperatorsAt X.α X.q X.ζ A.Λ A.bw (kc + 2 * A.pT) A.Dt cc A₁ m₁)
    (hm₁ : m₁ + 2 ≤ M)
    (hF1 : ∀ marked, 1 ≤ birthDiagonalFactor c.D.q c.D.Λ M c.lawT marked)
    (hsmL : Construction.Preservation.Assembly.ledgerTransportConstant Cw
      (wordsUpTo (A.Mt M sXT sZT c.tp cr).A ((A.Mt M sXT sZT c.tp cr).J + 1)).card *
        max (Cχ * c.D.eps M ^ A.χw) 0 ≤ 1 / 2)
    (hsmA : A₁ * Bound Cw (A.Mt M sXT sZT c.tp cr) (max (Cχ * c.D.eps M ^ A.χw) 0)
      (firstPrefixBirthFactor c.lawT * c.D.eps (M - 1) ^ (laterPrefixExponent c.D A - A.η₀ / 4)) ≤ 1 / 8)
    (md : ℕ) (hdrift : EnhancedDriftAt X.α X.q X.ζ A.Λ cr md) (hmd : md ≤ M) :
    Nonempty (LayerNativeData c kc) := by
  have hCw : 0 ≤ Cw := x.cwNonneg
  obtain ⟨hα, hq, hΛD, _, hseq, hband, _⟩ := c.data
  have hΛ128 : 128 ≤ c.D.Λ := by rw [hΛD]; exact hΛ
  have hq1 : 1 < c.D.q := by rw [hq]; exact X.hq.1
  have hlevW : c.Gw.level = M := c.weak.2.2.1
  obtain ⟨-, -, -, -, hbirths, ⟨hseedprov, -, -⟩, -, -, -, hinv⟩ := c.weak
  obtain ⟨hmass, -, -, hiota, -, hetaB, -⟩ := c.law
  obtain ⟨-, htags, -, -, -, -, -, hled, -⟩ := hinv
  have hV' := hV
  obtain ⟨-, -, -, -, -, hsched, -⟩ := hV'
  have htT : 0 ≤ A.tT := hsched.2.2.2.2.2.2.2.2.1.le
  have hPeq : A.Pt c.D Cw cr M = genProvParams c.D Cw A.η₀ A.NT A.pT
      (fun _ => c.D.termRho cr M) (fun _ => c.D.termRNew cr A.tT M) :=
    termProvParams_eq_gen c.D Cw cr A.tT A.η₀ A.NT A.pT M
  have hsucc := c.succ
  rw [hPeq] at hsucc
  have hG : c.Gw.HasTags (genProvParams c.D Cw A.η₀ A.NT A.pT
      (fun _ => c.D.termRho cr M) (fun _ => c.D.termRNew cr A.tT M)) :=
    hasTags_of_seed_prov hseedprov htags
  have hold : ∀ v ∈ c.Gw.comps, ∀ e ∈ v.births, c.Gw.level ≤ e.scale := by
    intro v hv e he
    rw [hbirths ⟨v, hv⟩] at he
    exact absurd he (by simp)
  have hrb : (fun _ => c.D.termRNew cr A.tT M) (c.Gw.level - 1) =
      (fun _ => c.D.termRho cr M) (c.Gw.level - 1) * c.D.eps (c.Gw.level - 1) ^ A.tT := by
    rw [hlevW]; rfl
  have hled' : markedLedger (c.Gw.mass c.lawT) (c.Gw.marker c.lawT) c.Gw.fam ≤
      max (Cχ * c.D.eps M ^ A.χw) 0 :=
    (weak_ledger_lawT hbirths hmass hled).trans (le_max_left _ _)
  have hbirthR : ∀ marked, birthDiagonalFactor c.D.q c.D.Λ c.Gw.level c.lawT marked *
      c.D.eps (c.Gw.level - 1) ^ (ocDelta c.D.α c.D.q - A.η₀ - A.tT *
        (termExcess A.NT A.pT A.alph : ℝ)) ≤
      firstPrefixBirthFactor c.lawT * c.D.eps (M - 1) ^ (laterPrefixExponent c.D A - A.η₀ / 4) := by
    intro marked
    have hb := birth_bound_any hq1 hΛ128 c.lawT (by rw [hiota]) c.Gw.level
      (θ₁ := laterPrefixExponent c.D A - A.η₀ / 4) (θ₂ := laterPrefixExponent c.D A) (by rw [hiota, hetaB]; ring) marked
    rw [hlevW] at hb ⊢
    exact hb
  have hfull := full_ledger_gen (G := c.Gw) (G' := c.Gt') (Mn := A.Mt M sXT sZT c.tp cr)
    hq1 hΛ128 hCw htT hrb (fun l hl => termFresh_letters l hl) c.lawT
    (fun marked => by rw [hlevW]; exact hF1 marked) hbirthR hG hold hsucc
    (le_max_right _ _) hled' hsmL
  have hfull' : markedLedger (c.Gt'.mass c.lawT) (c.Gt'.marker c.lawT) c.Gt'.fam ≤
      Bound Cw (A.Mt M sXT sZT c.tp cr) (max (Cχ * c.D.eps M ^ A.χw) 0)
        (firstPrefixBirthFactor c.lawT * c.D.eps (M - 1) ^ (laterPrefixExponent c.D A - A.η₀ / 4)) := hfull
  obtain ⟨R, hRB, hRC, hRS, hRπ, _, _, _⟩ := operator' c x hV hΛ hCH hΥ hcar hX hZ hj
    hM2 hρε hCL hwin cc (kc + 2 * A.pT) A₁ m₁ hreg0 hop hm₁ hfull' hsmA
  have hd := hdrift c.D.Φ hseq M c.D.κ hband M hmd le_rfl
  let αv := Buffer.actualDriftJetConstant * ocA X.α X.q A.Λ (M - 1)
  have he : 0 < ocEpsilon X.q A.Λ (M - 1) :=
    Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ A.Λ)
  refine ⟨{
    R := R,
    coeff := hRB,
    identification := hRC,
    regularizer := hRS,
    weight := hRπ,
    admissible := (hseq.2 M (by omega)).choose,
    αv := αv, B := 1024, lam := c.D.eps (M - 1),
    alpha_nonneg := mul_nonneg Buffer.actualDriftJetConstant_nonneg
      (Real.rpow_pos_of_pos he _).le,
    drift_base := by norm_num,
    scale_pos := by simpa only [OCData.eps, hq, hΛD] using he,
    drift_small := by simpa only [rhoEnh, OCData.eps, hα, hq, hΛD] using hd.2.2.1,
    strain := by simpa only [αv, rhoEnh, hα, hq, hΛD] using hd.2.2.2.1,
    jets := ?_
  }⟩
  intro t _ j hj _ y
  simpa only [αv, OCData.eps, hq, hΛD] using hd.2.2.2.2 t j hj y

end AVRegularity.EntryTerminal.Ingredients.Frontier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
namespace AVRegularity.Construction.Residual.Presentation

/-! The retained terminal trajectory at the frontier order. Truncation preserves
the regularized equation and its gradient/kernel lifts. The terminal trace
vanishes on every new word, and this property survives the same linear map. -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

private theorem Layer_native_truncate
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (kc : ℕ) (hk : kc + 2 * A.pT ≤ A.Khat Kout) :
    (c.Gt'.retained M 1 A.RT).IsRegSolution
      (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ A.hφ₀
      (c.D.κ (M - 1)) (streamVel (c.D.Φ (M - 1))) (kc + 2 * A.pT) c.tp (c.a + A.T₀)
      (fun v => truncateTorusHk hk (c.Z₀ v)) (fun _ _ => 0) (fun _ _ => 0)
      (fun v t => truncateTorusHk hk (c.Z v t))
      (fun v t => truncateTorusHk (Nat.succ_le_succ hk) (c.Zw v t))
      (fun v u γ t => truncateTorusHk
        (by omega : kc + 2 * A.pT + A.Dt - 1 ≤ A.Khat Kout + A.Dt - 1) (c.Zk v u γ t)) := by
  exact Construction.Preservation.FullLift.native_reg_solution_truncate
    (hr := ScalarH) (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ A.hφ₀
    (c.Gt'.retained M 1 A.RT) (c.D.κ (M - 1)) c.tp (c.a + A.T₀)
    (streamVel (c.D.Φ (M - 1))) (kc + 2 * A.pT) (A.Khat Kout) hk c.Z₀ c.Z c.Zw c.Zk c.sol

/-- Honest truncation supplies the retained equation and the zero new-word datum. -/
theorem Layer_solution_at
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (kc : ℕ) (hk : kc + 2 * A.pT ≤ A.Khat Kout) :
    LayerSolutionAt c kc := by
  let G := c.Gt'.retained M 1 A.RT
  let Y : ∀ v : CompIn G.comps, ℝ → TorusHk (kc + 2 * A.pT) (ScalarH v.1.root) :=
    fun v t => truncateTorusHk hk (c.Z v t)
  let Yk : ∀ v u (_ : G.fam.Γ v u), ℝ →
      TorusHk (kc + 2 * A.pT + A.Dt - 1) (ScalarH u.1.root) :=
    fun v u γ t => truncateTorusHk (by omega) (c.Zk v u γ t)
  refine ⟨Y, Yk, ?_, ?_⟩
  · have hkw : kc + 2 * A.pT + 1 ≤ A.Khat Kout + 1 := Nat.succ_le_succ hk
    have hY0 : termY0 c kc = fun v => truncateTorusHk hk (c.Z₀ v) := by
      funext v
      exact truncTo_of_le hk _
    have hYw : termYw c kc = fun v t => truncateTorusHk hkw (c.Zw v t) := by
      funext v t
      exact truncTo_of_le hkw _
    rw [hY0, hYw]
    exact Layer_native_truncate c kc hk
  · intro v hv
    rw [termY0_eq_trace c kc]
    simp only [AVRegularity.EntryTerminal.Ingredients.terminalTrace, hv, dite_false]

/-- A coarse order floor makes the retained truncation available uniformly. -/
theorem Layer_solution : LayerSolutionStatement := by
  intro X
  refine ⟨128, le_rfl, fun A _ _ => ⟨0, fun kc _ => ?_⟩⟩
  refine ⟨0, 0, kc + 2 * A.pT + 1, fun sXT sZT _ _ Kout hK => ⟨0, ?_⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
    cP CP cHP Cw Ce cker _ Cfl
  refine ⟨0, 1, 0, one_pos, 1, 1, le_rfl, one_pos, fun _ _ _ _ => ⟨0, ?_⟩⟩
  intro M _ c _
  exact Layer_solution_at c kc
    (le_trans (by omega : kc + 2 * A.pT ≤ Kout) (le_max_left _ _))

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.Construction.Preservation.Ledger
open AVRegularity.Construction.Preservation.Frontier
open AVRegularity.Construction.Preservation.Frontier.LengthPrice
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.EntryTerminal.Ingredients.Frontier

/-! Uniform native data for terminal layer energy. Isotropic regularizer constants,
the native operator price and the analytic drift threshold precede the context.
The proved ledger absorption supplies the all-row operator at every late level. -/

/-- Uniform native operator and drift budget on every ordered terminal window. -/
theorem Layer_native : LayerNativeStatement := by
  classical
  intro X
  obtain ⟨Λc, hΛc, hcore⟩ := AVRegularity.EntryTerminal.Ingredients.seedStruct_scales X
  obtain ⟨Λd, _, hDrift⟩ := actual_enhanced_drift_budget
    X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  refine ⟨max Λc (max Λd 128), le_trans (le_max_right _ _) (le_max_right _ _),
    fun A hΛ hV => ?_⟩
  have hΛc' : Λc ≤ A.Λ := le_trans (le_max_left _ _) hΛ
  have hΛd' : Λd ≤ A.Λ := le_trans (le_max_left _ _) ((le_max_right _ _).trans hΛ)
  have h128 : 128 ≤ A.Λ := le_trans (le_max_right _ _) ((le_max_right _ _).trans hΛ)
  have hbw : 0 < A.bw := hV.2.2.1.1
  have hDt : 2 ≤ A.Dt := le_max_left _ _
  obtain ⟨hφsmooth, -, -, hφsupp⟩ := hV.2.1
  have hcompact := Providers.hasCompactSupport_of_unitBall hφsupp
  have hV' := hV
  obtain ⟨-, -, -, ⟨-, -, -, -, hσw, -, hχw, hη₀, -⟩, -, hsch, -⟩ := hV'
  have htT : 0 ≤ A.tT := hsch.2.2.2.2.2.2.2.2.1.le
  have hθ : 0 < ocDelta X.α X.q - A.η₀ -
      A.tT * (termExcess A.NT A.pT A.alph : ℝ) - A.η₀ / 4 :=
    lt_of_lt_of_le (half_pos (ocDelta_pos_of_admissible X.hα₀ X.hq))
      (termFresh_exponent_facts hV)
  refine ⟨0, fun kc _ => ?_⟩
  let S := max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2
  refine ⟨S, S, 0, fun sXT sZT hX hZ Kout _ => ⟨0, fun Kw Lt nW hk₀w _ cr kS _ _ _ _ _
    hcr0 _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _ cP CP cHP Cw Ce cker _ Cfl => ?_⟩⟩
  obtain ⟨c₁, hc₁, hr₁⟩ := WeakEntryProofs.exists_isoPairedKernel_regularizer_constants
    A.φ₀ hcompact hφsmooth A.hφ₀ nW
  obtain ⟨c₂, hc₂, hr₂⟩ := WeakEntryProofs.exists_isoPairedKernel_regularizer_constants
    A.φ₀ hcompact hφsmooth A.hφ₀ A.nT
  let cc : ℕ → ℝ := fun j => max (c₁ j) (c₂ j)
  have hcc : ∀ j, 0 ≤ cc j := fun j => (hc₁ j).trans (le_max_left _ _)
  obtain ⟨A₁, hA₁, m₁, _, hop⟩ := uniform_native_kernel_operator_of_certificates
    X.α X.s X.q X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq A.Λ h128 X.ζ X.hζ A.bw hbw
    (kc + 2 * A.pT) A.Dt hDt cc (fun j _ => hcc j)
  obtain ⟨md, _, hDriftAt⟩ := hDrift A.Λ hΛd' cr hcr0
  have hdrift : Construction.Preservation.RetainedEnergy.EnhancedDriftAt
      X.α X.q X.ζ A.Λ cr md := hDriftAt
  obtain ⟨Ms, hMs2, hMs⟩ := hcore A.Λ hΛc' cr A.σw A.tT CL hcr0 hσw.le htT
  by_cases hCw : 0 ≤ Cw
  swap
  · refine ⟨0, 1, 0, one_pos, 1, 1, le_rfl, one_pos,
      fun _ _ _ _ => ⟨0, fun _ _ _ x => ?_⟩⟩
    exact (hCw x.cwNonneg).elim
  by_cases hcHP : 0 < cHP
  swap
  · refine ⟨0, 1, 0, one_pos, 1, 1, le_rfl, one_pos,
      fun _ _ _ _ => ⟨0, fun _ _ c _ => ?_⟩⟩
    have hcH : 0 < cHP := by rw [← c.law.2.2.1]; exact c.lawT.cH_pos
    exact (hcHP hcH).elim
  let Rl : ℝ := 1 + Real.sqrt (((max 1 A.nWords : ℕ) : ℝ) / cHP)
  obtain ⟨Ma, hMa⟩ := Rows_small X.hq.1 h128 hχw hθ (half_pos hη₀)
    Cw A₁ Cχ cHP (max 1 A.nWords) (wordsUpTo A.alph (A.RT + 1)).card A.alph.card
    hCw hA₁ hcHP (lt_of_lt_of_le one_pos (le_max_left _ _))
  refine ⟨0, 1, 0, one_pos,
    1, 1, le_rfl, one_pos, fun _ _ j₀ hcar => ?_⟩
  refine ⟨max Ms (max Ma (max (m₁ + 2) (max md (j₀ + 1)))),
    fun M hM c x hwin => ?_⟩
  have hMs' : Ms ≤ M := le_trans (le_max_left _ _) hM
  have hMa' : Ma ≤ M := le_trans (le_max_left _ _) ((le_max_right _ _).trans hM)
  have hm₁ : m₁ + 2 ≤ M := le_trans (le_max_left _ _)
    ((le_max_right _ _).trans ((le_max_right _ _).trans hM))
  have hmd : md ≤ M := by omega
  have hj : j₀ + 1 ≤ M := by omega
  obtain ⟨hDα, hDq, hDΛ, _, _, hband, _⟩ := c.data
  obtain ⟨-, hρε, -, hCL⟩ := hMs M hMs' c.D hDα hDq hDΛ hband
  obtain ⟨_, _, hcHeq, hiota, hwc, hetaB, _⟩ := c.law
  have hRl : firstPrefixBirthFactor c.lawT = Rl := by simp only [firstPrefixBirthFactor, hcHeq, hwc, Rl]
  obtain ⟨hbirth, hsmL, hsmA⟩ := hMa M hMa'
  have hF1 : ∀ marked, 1 ≤ birthDiagonalFactor c.D.q c.D.Λ M c.lawT marked := by
    intro marked
    refine birthFactor_ge_one (by rw [hDq]; exact X.hq.1)
      (by rw [hDΛ]; exact h128) c.lawT hiota ?_ marked
    rw [hcHeq, hwc, hetaB, hDq, hDΛ]
    exact hbirth
  have hsmallL : Construction.Preservation.Assembly.ledgerTransportConstant Cw
      (wordsUpTo (A.Mt M sXT sZT c.tp cr).A ((A.Mt M sXT sZT c.tp cr).J + 1)).card *
        max (Cχ * c.D.eps M ^ A.χw) 0 ≤ 1 / 2 := by
    simpa only [TermArgs.Mt, termMenu, OCData.eps, hDq, hDΛ] using hsmL
  have hsmallA : A₁ * Bound Cw (A.Mt M sXT sZT c.tp cr)
      (max (Cχ * c.D.eps M ^ A.χw) 0)
      (firstPrefixBirthFactor c.lawT * c.D.eps (M - 1) ^ (laterPrefixExponent c.D A - A.η₀ / 4)) ≤ 1 / 8 := by
    simpa only [Bound, TermArgs.Mt, termMenu, laterPrefixExponent, hRl, Rl, OCData.eps, hDα, hDq, hDΛ] using hsmA
  exact Layer_native_ctx c x hV h128 le_rfl le_rfl hcar hX hZ hj
    (hMs2.trans hMs') hρε hCL hwin kc cc
    (kernelZero_all c h128 hcr0 c₁ c₂ cc hr₁ hr₂
      (fun j => le_max_left _ _) (fun j => le_max_right _ _))
    A₁ m₁ hop hm₁ hF1 hsmallL hsmallA md hdrift hmd

/-- The last open terminal frontier component: energy of the source word layer. -/
theorem termInnerLayer : TermInnerLayerStatement :=
  Layer_of_ingredients Layer_native Layer_solution

end AVRegularity.EntryTerminal.Ingredients.Frontier
end
end
end
