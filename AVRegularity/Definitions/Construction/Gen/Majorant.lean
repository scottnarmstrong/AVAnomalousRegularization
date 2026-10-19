-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Construction.ScheduleFloor

/-! Definition: the structural majorant of generated expressions and
the threshold predicates of the statements `successor_generated`, `gen_carrier_calculus`,
`successor_ledger`.

* `MajConsts`: the letter profiles and the derivative constants of the carrier calculus.
* `genMode D κ Δ leaf e mres h t ∈ [0, ∞]`: a majorant of the mode `h` (Fourier mode in the final
  transverse phase, resp. in the internal transverse phase for a cell function) of the expression
  `e` at the reserve `mres` and the time `t` (the majorant is resolved in time,
  so that a sum over the finer slots is a convex combination of the cutoff weights at each time),
  by structural recursion on `e`, with the following factors:
  - sums add, products convolve the mode profiles;
  - the old-label recentering derivative costs `C_old/(ε_i Δ)` and a slow derivative at fixed
    internal phase `C_slow/(ε_{i-1} Δ)`, each spending the reserve `Δ`; past the outer reserve `2`
    the majorant is `⊤`; the recentering derivative along the transverse coordinate also moves the
    final phase by `h/ε_i`, which adds `2π|h|/ε_i` times the mode;
  - the derivatives in the final phase and in the internal phase multiply the mode `h` by `2π|h|`;
  - the transverse inverse keeps the initial modes (at its recorded start `t₀`) and gains
    `(4/3)(2π|h|)⁻¹` on the supremum of the transverse flux over the history `[t₀, t]` (`h ≠ 0`;
    the zero mode of the flux does not enter the inverse; the inverse integrates the
    flux over its history). The clause is a bound only for `t ≥ t₀`; a scheduled cell node is
    observed only through `evalChild`, whose cutoff vanishes before the slot start;
  - the transverse primitive gains `(2π|h|)⁻¹` (`h ≠ 0`) and kills the zero mode;
  - the cell mean keeps only the zero mode, and so does a family function read as a cell function
    (`famCell`, independent of the internal phase);
  - restriction keeps the profile; evaluation at the appended child bounds the final-phase mode
    `h` by the cutoff weight `ϖ_{i+1,𝗉'}(t)` times the child profile `κ.child h` times the zero
    mode of the evaluated family at the same time: the appended child depends on the final phase
    through the relative shear (the Piola factors are separate products), and the
    weights `ϖ_{i+1,·}(t) ∈ [0,1]` add up to one;
  - the geometric, drift and child letters have the profiles of `κ`; a time-only letter has its
    exact value `|L(t)|` at the zero mode; a solved seed node has
    majorant `⊤` (it must lie inside a certified leaf).
  A certified leaf (`leaf e = some B`) is not expanded: its majorant is the time-independent `B`.
* `ctxModeSupAt`: the mode supremum of `ctxModeSup` at a fixed time (the carrier calculus
  bounds it by `genMode` at that time).
* `Gen.SolvedFree leaf e`: every solved node of `e` lies inside a certified leaf.
* `LeavesCertified D b j₀ leaf`: the certified leaves are context expressions whose functions have
  holomorphic extensions with mode sizes below their certified profiles.
* `MajOK bw κ`: the letter and child profiles of `κ` decay like `e^{-6π bw|h|}`
  (the final-phase modes of a function holomorphic on the narrowest strip `|Im ζ_q| < 3 bw`) with
  a finite constant, and the Cauchy constants are finite.
* `CarrierOK Υ₀ CH Υ`: `1 ≤ CH` and `Υ ≥ max{Υ₀, 4C_s}`, `C_s = 8π²` (the constants of the
  domains paragraph; `Υ₀` stands for `2A_v`).
* `LedgerOK`: the ledger admissibility and the starting level of the ledger.
* `GenStage.IsExprFor G v u γ d I c e`: the slot-indexed scheduled expressions `e`, with seed
  provenance (`Gen.FromSeed G.exports`, no fresh solved node), denote functions giving
  the component `c` of the coefficient `(γ, d, I)` on the admissible recentered contexts, and zero
  off them. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity

/-- The letter profiles and derivative constants of the carrier calculus. -/
structure MajConsts where
  /-- Mode profiles of the geometric letters. -/
  geo : GenFrame → GeoLetter → ℤ → ℝ≥0∞
  /-- Mode profiles of the drift letters. -/
  drift : Fin 2 → ℤ → ℝ≥0∞
  /-- Final-phase mode profile of the evaluation at the appended child (K6), per unit of the
  supremum of the evaluated family. -/
  child : ℤ → ℝ≥0∞
  /-- The Cauchy constant of the old-label recentering derivative. -/
  Cold : ℝ≥0∞
  /-- The Cauchy constant of a slow derivative at fixed internal phase. -/
  Cslow : ℝ≥0∞

/-- The cost of one derivative with Cauchy constant `C` on the scale `ε` at the reserve loss `Δ`,
from the reserve `mres` (`⊤` past the outer reserve `2`). -/
def derivCost (C : ℝ≥0∞) (ε Δ mres : ℝ) (x : ℝ≥0∞) : ℝ≥0∞ :=
  if mres + Δ ≤ 2 then C / ENNReal.ofReal (ε * Δ) * x else ⊤

/-- The mode multiplier `2π|h|`. -/
def modeMul (h : ℤ) : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi * |(h : ℝ)|)

/-- The mode gain `(2π|h|)⁻¹` for `h ≠ 0`, and `0` for `h = 0`. -/
def modeGain (h : ℤ) : ℝ≥0∞ := if h = 0 then 0 else (modeMul h)⁻¹

/-- The supremum of the mode `h` of `F` at the time `t` over the scheduled discrete data over the
slot `p` of level `i` and the families of `𝔉_{i-1}(𝗆;𝗉)` (real final phase): `ctxModeSup` without
its supremum over the output times. -/
def ctxModeSupAt (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ)
    (F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ) (mres : ℝ) (h : ℤ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (dd : ChainData) (n : ℕ)
    (_ : ∃ ch : RealChain, IsAdmissibleChain D b j₀ i p ch ∧ ch.data = dd ∧ ch.children.length = n)
    (x : ChainParamsC n) (_ : x ∈ carrierC D b dd n mres) (_ : ∀ a, (x.2.2 a).im = 0),
    ‖finalPhaseCoeff (transverseIndex p) (F dd n t) x h‖ₑ

/-- **The structural mode majorant** at the reserve `mres`, the mode `h` and the time `t`. -/
def genMode (D : OCData) (κ : MajConsts) (Δ : ℝ)
    (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)) :
    {s : GenSort} → {i : ℕ} → {p : ℤ} → Gen s i p → ℝ → ℤ → ℝ → ℝ≥0∞
  | _, _, _, e@(.geo fr L), mres, h, _ => (leaf e).elim (κ.geo fr L h) fun B => B mres h
  | _, _, _, e@(.drift c), mres, h, _ => (leaf e).elim (κ.drift c h) fun B => B mres h
  | _, _, _, e@(.time L), mres, h, t =>
      (leaf e).elim (if h = 0 then ENNReal.ofReal |L.eval D t| else 0) fun B => B mres h
  | _, _, _, e@(.add a b), mres, h, t =>
      (leaf e).elim (genMode D κ Δ leaf a mres h t + genMode D κ Δ leaf b mres h t)
        fun B => B mres h
  | _, _, _, e@(.mul a b), mres, h, t =>
      (leaf e).elim
        (∑' k : ℤ, genMode D κ Δ leaf a mres k t * genMode D κ Δ leaf b mres (h - k) t)
        fun B => B mres h
  | _, i, p, e@(.dOld j a), mres, h, t =>
      (leaf e).elim (derivCost κ.Cold (D.eps i) Δ mres (genMode D κ Δ leaf a (mres + Δ) h t) +
          (if j = transverseIndex p then ENNReal.ofReal (2 * Real.pi * |(h : ℝ)| / D.eps i)
            else 0) * genMode D κ Δ leaf a mres h t)
        fun B => B mres h
  | _, _, _, e@(.dPhase a), mres, h, t =>
      (leaf e).elim (modeMul h * genMode D κ Δ leaf a mres h t) fun B => B mres h
  | _, i, _, e@(.dSlowFam _ c), mres, h, t =>
      (leaf e).elim
        (derivCost κ.Cslow (D.eps (i - 1)) Δ mres (genMode D κ Δ leaf c (mres + Δ) h t))
        fun B => B mres h
  | _, i, _, e@(.dSlowCell _ w), mres, h, t =>
      (leaf e).elim
        (derivCost κ.Cslow (D.eps (i - 1)) Δ mres (genMode D κ Δ leaf w (mres + Δ) h t))
        fun B => B mres h
  | _, _, _, e@(.dInternal w), mres, h, t =>
      (leaf e).elim (modeMul h * genMode D κ Δ leaf w mres h t) fun B => B mres h
  | _, _, _, e@(.restrict a), mres, h, t =>
      (leaf e).elim (genMode D κ Δ leaf a mres h t) fun B => B mres h
  | _, _, p, e@(.cellInv F t₀ ι), mres, h, t =>
      (leaf e).elim (genMode D κ Δ leaf ι mres h t₀ +
          ENNReal.ofReal (4 / 3) * modeGain h *
            ⨆ s ∈ Set.Icc t₀ t, genMode D κ Δ leaf (F (transverseIndex p)) mres h s)
        fun B => B mres h
  | _, _, _, e@(.transPrim w), mres, h, t =>
      (leaf e).elim (modeGain h * genMode D κ Δ leaf w mres h t) fun B => B mres h
  | _, _, _, e@(.solved ..), mres, h, _ => (leaf e).elim ⊤ fun B => B mres h
  | _, _, _, e@(.mean w), mres, h, t =>
      (leaf e).elim (if h = 0 then genMode D κ Δ leaf w mres 0 t else 0) fun B => B mres h
  | _, _, _, e@(.famCell c), mres, h, t =>
      (leaf e).elim (if h = 0 then genMode D κ Δ leaf c mres 0 t else 0) fun B => B mres h
  | _, i, _, e@(.evalChild p' c), mres, h, t =>
      (leaf e).elim
        (ENNReal.ofReal (ocCutoff D.α D.q D.Λ (i + 1) p' t) * κ.child h *
          genMode D κ Δ leaf c mres 0 t)
        fun B => B mres h

/-- Every solved node of `e` lies inside a certified leaf. -/
def Gen.SolvedFree
    (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)) :
    {s : GenSort} → {i : ℕ} → {p : ℤ} → Gen s i p → Prop
  | _, _, _, e@(.add a b) => (leaf e).isSome ∨ (Gen.SolvedFree leaf a ∧ Gen.SolvedFree leaf b)
  | _, _, _, e@(.mul a b) => (leaf e).isSome ∨ (Gen.SolvedFree leaf a ∧ Gen.SolvedFree leaf b)
  | _, _, _, e@(.dOld _ a) => (leaf e).isSome ∨ Gen.SolvedFree leaf a
  | _, _, _, e@(.dPhase a) => (leaf e).isSome ∨ Gen.SolvedFree leaf a
  | _, _, _, e@(.dSlowFam _ c) => (leaf e).isSome ∨ Gen.SolvedFree leaf c
  | _, _, _, e@(.dSlowCell _ w) => (leaf e).isSome ∨ Gen.SolvedFree leaf w
  | _, _, _, e@(.dInternal w) => (leaf e).isSome ∨ Gen.SolvedFree leaf w
  | _, _, _, e@(.restrict a) => (leaf e).isSome ∨ Gen.SolvedFree leaf a
  | _, _, _, e@(.cellInv F _ ι) =>
      (leaf e).isSome ∨ ((∀ k, Gen.SolvedFree leaf (F k)) ∧ Gen.SolvedFree leaf ι)
  | _, _, _, e@(.transPrim w) => (leaf e).isSome ∨ Gen.SolvedFree leaf w
  | _, _, _, e@(.solved ..) => (leaf e).isSome
  | _, _, _, e@(.mean w) => (leaf e).isSome ∨ Gen.SolvedFree leaf w
  | _, _, _, e@(.famCell c) => (leaf e).isSome ∨ Gen.SolvedFree leaf c
  | _, _, _, e@(.evalChild _ c) => (leaf e).isSome ∨ Gen.SolvedFree leaf c
  | _, _, _, .geo .. => True
  | _, _, _, .drift .. => True
  | _, _, _, .time .. => True

/-- The certified leaves are context expressions whose denoted functions have holomorphic
extensions with mode sizes below their certified profiles. -/
def LeavesCertified (D : OCData) (b : ℝ) (j₀ : ℕ)
    (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)) : Prop :=
  (∀ (s : GenSort) (i : ℕ) (p : ℤ) (e : Gen s i p), s ≠ .ctx → leaf e = none) ∧
  ∀ (i : ℕ) (p : ℤ) (e : Gen .ctx i p) (B : ℝ → ℤ → ℝ≥0∞), leaf e = some B →
    ∀ f : GenSort.Sem .ctx, Gen.Denotes D b j₀ e f →
      ∃ F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ,
        IsHolExtension D b j₀ i p f F ∧
        ∀ (mres : ℝ) (h : ℤ), ctxModeSup D b j₀ i p F mres h ≤ B mres h

/-- **Finiteness and decay of the carrier constants**: the mode profiles of the
geometric, drift and child-evaluation letters decay like `e^{-6π bw|h|}` with one finite
constant, and the Cauchy constants are finite (the time letters carry their exact bounds). -/
def MajOK (bw : ℝ) (κ : MajConsts) : Prop :=
  ∃ C : ℝ,
    (∀ (fr : GenFrame) (L : GeoLetter) (h : ℤ),
      κ.geo fr L h ≤ ENNReal.ofReal (C * Real.exp (-(6 * Real.pi * bw * |(h : ℝ)|)))) ∧
    (∀ (c : Fin 2) (h : ℤ),
      κ.drift c h ≤ ENNReal.ofReal (C * Real.exp (-(6 * Real.pi * bw * |(h : ℝ)|)))) ∧
    (∀ h : ℤ, κ.child h ≤ ENNReal.ofReal (C * Real.exp (-(6 * Real.pi * bw * |(h : ℝ)|)))) ∧
    κ.Cold ≠ ⊤ ∧ κ.Cslow ≠ ⊤

/-- The carrier constants: `1 ≤ CH` and `Υ ≥ max{Υ₀, 4C_s}`, `C_s = 8π²`. -/
def CarrierOK (Υ₀ CH Υ : ℝ) : Prop :=
  1 ≤ CH ∧ max Υ₀ (4 * (8 * Real.pi ^ 2)) ≤ Υ

/-- The ledger constants: ledger admissibility and the starting level of the ledger. -/
def LedgerOK (Ce CI Cw CIthr Cwthr : ℝ) (mStar m : ℕ) : Prop :=
  IsLedgerAdmissible Ce CI Cw CIthr Cwthr ∧ mStar ≤ m

namespace GenStage

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The slot-indexed scheduled expressions `e` give the component `c` of the coefficient
`(γ, d, I)` on the admissible recentered contexts, and zero off them. -/
def IsExprFor (G : GenStage D hr Dm b j₀) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2) (e : (p : OddSlot) → Gen .ctx G.level p.1) :
    Prop :=
  ∀ p : OddSlot, Gen.IsScheduled D (e p) ∧ Gen.FromSeed G.exports (e p) ∧
    ∃ f : GenSort.Sem .ctx, Gen.Denotes D b j₀ (e p) f ∧
    ∀ (ctx : StageCtx D b j₀ G.level p) (t : ℝ), t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
            ∀ (X z : Vec 2),
      G.fam.flux p ctx v u γ d I t X z c =
        haveI := Classical.propDecidable
          (IsAdmissibleChain D b j₀ G.level p.1 (ctx.1.recenter D (D.eps (G.level - 1) • X)))
        if IsAdmissibleChain D b j₀ G.level p.1 (ctx.1.recenter D (D.eps (G.level - 1) • X))
        then f t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0

end GenStage

end AVRegularity
