-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleOutput.OcPulseChartIndex
public import AVRegularity.Definitions.Construction.Gen.ParShift
public import AVRegularity.Analysis.Convolution.Kernel.PairedSmoothing
public import AVRegularity.Statements.Intermediate.CycleComparison.IsLiftSequence
public import AVRegularity.Statements.Intermediate.Families.ConstituentPhysical
public import AVRegularity.Statements.Intermediate.CycleOutput.LiftEdges
public import AVRegularity.Statements.Intermediate.CycleReference.OcDStar
public import AVRegularity.Definitions.Construction.Words
public import AVRegularity.Statements.Intermediate.CycleComparison.CovPolyP
public import AVRegularity.Statements.Intermediate.CycleComparison.CovPolyQ
import Mathlib.Data.Int.Star

section
section
@[expose] public noncomputable section
namespace AVRegularity

/-! The admissible starting level `j₀` of the generated
carriers: with the strain rate `a_k = ε_k^{β-2}` (`ocA`), the renewal period `h_k = τ''_k`
(`ocTauPP`), the history constant `C_H`, the chain constant `Υ` and `C_s = 8π²`,
`2ΥC_H a_k h_{k+1} ≤ b/(64C_s)` for every `k ≥ j₀ - 1`, and `2C_H h_{m+1} < τ_m/24` for every
`m ≥ j₀` (the construction uses this for `j₀ ≤ m < M`; requiring it for all `m ≥ j₀` is
independent of the terminal level and holds for large `j₀` since `h_{m+1}/τ_m → 0`).
`IsCarrierStart.mono`: the
condition is monotone in `C_H` and `Υ`, so one starting level serves several statements. -/

/-- The starting level `j₀` satisfies the chain smallness and the history separation. -/
def IsCarrierStart (α q : ℝ) (Λ : ℕ) (b CH Υ : ℝ) (j₀ : ℕ) : Prop :=
  (∀ k : ℕ, j₀ ≤ k + 1 →
      2 * Υ * CH * ocA α q Λ k * ocTauPP α q Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2))) ∧
    ∀ m : ℕ, j₀ ≤ m → 2 * CH * ocTauPP α q Λ (m + 1) < ocTau α q Λ m / 24

/-- Monotonicity in the constants (nonnegative strain rates and renewal periods). -/
theorem IsCarrierStart.mono {α q : ℝ} {Λ : ℕ} {b CH Υ CH' Υ' : ℝ} {j₀ : ℕ}
    (hA : ∀ k, 0 ≤ ocA α q Λ k) (hT : ∀ k, 0 ≤ ocTauPP α q Λ k)
    (hCH : CH ≤ CH') (hΥ : Υ ≤ Υ') (hCH0 : 0 ≤ CH) (hΥ0 : 0 ≤ Υ)
    (h : IsCarrierStart α q Λ b CH' Υ' j₀) : IsCarrierStart α q Λ b CH Υ j₀ := by
  refine ⟨fun k hk => le_trans ?_ (h.1 k hk), fun m hm => lt_of_le_of_lt ?_ (h.2 m hm)⟩
  · have h1 : 2 * Υ * CH ≤ 2 * Υ' * CH' := by
      have := mul_le_mul hΥ hCH hCH0 (le_trans hΥ0 hΥ)
      linarith
    have h2 : 0 ≤ ocA α q Λ k * ocTauPP α q Λ (k + 1) := mul_nonneg (hA k) (hT (k + 1))
    have := mul_le_mul_of_nonneg_right h1 h2
    calc 2 * Υ * CH * ocA α q Λ k * ocTauPP α q Λ (k + 1)
        = 2 * Υ * CH * (ocA α q Λ k * ocTauPP α q Λ (k + 1)) := by ring
      _ ≤ 2 * Υ' * CH' * (ocA α q Λ k * ocTauPP α q Λ (k + 1)) := this
      _ = 2 * Υ' * CH' * ocA α q Λ k * ocTauPP α q Λ (k + 1) := by ring
  · have := mul_le_mul_of_nonneg_right hCH (hT (m + 1))
    linarith

end AVRegularity
end
end

section
@[expose] public section
namespace AVRegularity

/-! Bridge lemma: the renewal label
`l_{m,k} = ocLabel` and the chart index `ocPulseChartIndex`
of `pulseLiftData` and `cycle_comparison` are equal for every integer `k`. With
`d = L_m²` odd (`L_m = 4⌈ε_{m-1}^{-δ}⌉ + 1`) and `τ_m = τ_m''/d`, both floors are
`⌊(2k + d - 1)/(2d)⌋`, because `2k + d - 1` and `2d` are even. The only hypothesis is the
positivity of the renewal period `τ_m''` (a scale hypothesis of the construction). -/

/-- For integers `a` and `b > 0`, `⌊2a/2b⌋ = ⌊(2a+1)/2b⌋`. -/
theorem floor_even_div_succ (a b : ℤ) (hb : 0 < b) :
    ⌊((2 * a : ℤ) : ℝ) / ((2 * b : ℤ) : ℝ)⌋ = ⌊(((2 * a : ℤ) : ℝ) + 1) / ((2 * b : ℤ) : ℝ)⌋ := by
  set q := ⌊((2 * a : ℤ) : ℝ) / ((2 * b : ℤ) : ℝ)⌋ with hq
  have hM : (0 : ℝ) < ((2 * b : ℤ) : ℝ) := by exact_mod_cast (by omega : (0:ℤ) < 2 * b)
  have h1 := Int.floor_le (((2 * a : ℤ) : ℝ) / ((2 * b : ℤ) : ℝ))
  have h2 := Int.lt_floor_add_one (((2 * a : ℤ) : ℝ) / ((2 * b : ℤ) : ℝ))
  rw [← hq] at h1 h2
  rw [le_div_iff₀ hM] at h1
  rw [div_lt_iff₀ hM] at h2
  have i1 : q * (2 * b) ≤ 2 * a := by exact_mod_cast h1
  have i2 : 2 * a < (q + 1) * (2 * b) := by exact_mod_cast h2
  symm
  rw [Int.floor_eq_iff, le_div_iff₀ hM, div_lt_iff₀ hM]
  have j2 : 2 * a + 1 < (q + 1) * (2 * b) := by
    have : (q + 1) * (2 * b) = 2 * ((q + 1) * b) := by ring
    rw [this] at i2 ⊢
    omega
  constructor
  · have : (q : ℝ) * ((2 * b : ℤ) : ℝ) ≤ ((2 * a : ℤ) : ℝ) := by exact_mod_cast i1
    linarith
  · exact_mod_cast j2


/-- **Chart-index bridge**: `ocLabel = ocPulseChartIndex` when `τ_m'' > 0`. -/
theorem ocLabel_eq_ocPulseChartIndex (α q : ℝ) (Λ m : ℕ) (k : ℤ)
    (hτ : 0 < ocTauPP α q Λ m) :
    ocLabel α q Λ m k = ocPulseChartIndex α q Λ m k := by
  unfold ocLabel ocPulseChartIndex ocTau
  set T := ocTauPP α q Λ m
  set n : ℕ := ⌈ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)⌉₊
  have hL : (ocL α q Λ m : ℝ) = 4 * (n : ℝ) + 1 := by
    simp [ocL, n]
  rw [hL]
  have hpos : (0 : ℝ) < 4 * (n : ℝ) + 1 := by positivity
  have hT : T ≠ 0 := hτ.ne'
  have e1 : ((k : ℝ) * (T / (4 * (n : ℝ) + 1) ^ 2) + (T - T / (4 * (n : ℝ) + 1) ^ 2) / 2) / T
      = ((2 * (k + 8 * (n : ℤ) ^ 2 + 4 * n) : ℤ) : ℝ) / ((2 * ((4 * (n : ℤ) + 1) ^ 2) : ℤ) : ℝ) := by
    push_cast
    field_simp
    ring
  have e2 : (k : ℝ) * (T / (4 * (n : ℝ) + 1) ^ 2) / T + 1 / 2
      = (((2 * (k + 8 * (n : ℤ) ^ 2 + 4 * n) : ℤ) : ℝ) + 1) / ((2 * ((4 * (n : ℤ) + 1) ^ 2) : ℤ) : ℝ) := by
    push_cast
    field_simp
    ring
  rw [e1, e2]
  exact floor_even_div_succ _ _ (by positivity)

end AVRegularity
end
end

section
/-! **Trimmed quiet times**. The definition `ocTrimmedQuietTimes` is in the module
`Statements.Intermediate.CycleJoint.OcTrimmedQuietTimes`;
this module keeps the import path. -/

@[expose] public section
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution
namespace AVRegularity

/-! Definition: moving paired kernels and the fresh
kernels of a birth.

* `KernelSpec`: a moving paired kernel of width `r`, order `n` and matrices `H_1(t), H_2(t)`:
  `S(t) = S_{r,H_1(t)} S_{r,H_2(t)}`. Seed
  kernels keep their original width, paired matrices and measurable selector,
  so every kernel of the construction is of this form.
* `KernelSpec.op φ₀ hφ₀ S t`: the operator on `L²(𝕋²; E)`, through the library's periodic
  moment-kernel averages with the signed kernel `𝗄_n` (`momentKernel φ₀ n`): `S_{r,H₂}` acts
  first.
* `IsFreshAxes D b H₁ H₂`: the matrices of the fresh kernel born at the level `b` (display (10.18)
  of the paper).
  With `m = b + 1`,
  `h = τ_m''`, the quiet margin centres `s_l = (l + 1/2)h`, the reference flux `𝖩 = 𝖩_m` at `κ_m`, the
  label-zero trajectory, the coarser flow `X_{m-1} = X_b` and `B = κ_b`: on `[s_l, s_{l+1})`,
  `H_i(t) = D_yX_b(t, 0, s_l) T_i (𝖩(t_i)/κ_b)^{1/2}`, `T_i = D_yX_b(s_l, y_i, l_i h)`,
  `y_i = X_b(l_i h, X_b(t_i, 0, s_l), t_i)`, where `t_H ∈ [s_l, s_l + 4h)` attains
  `max_t 𝖩(t)_{11}`, `t_V = t_H + 2h` if `t_H < s_l + 2h` and `t_V = t_H - 2h` otherwise, and
  `|t_i - l_i h| ≤ h/2`. The construction chooses `t_H` and `l_i`; the relation accepts every
  admissible choice, fixed once per quiet margin and retained
  (any maximizer and any admissible labels work, chosen per quiet margin, not per time).
  `𝖩(t)` is diagonal (`ocRefFlux = νI + scalar·ocPi`, `ocPi` diagonal), so its square root is
  the entrywise square root of the diagonal.
* `IsFreshKernel D cr σ₀ nk b S`: the fresh kernel of a birth at `b` has width
  `r_b = R_b ε_b^{σ₀}`, `R_b = c_r √(κ_b τ_{b+1}'')`, order `n_k`, and the axes of `IsFreshAxes`. -/

/-- A moving paired kernel: width, order and the two time-dependent matrices. -/
structure KernelSpec where
  /-- The width `r`. -/
  width : ℝ
  /-- The order `n` of the signed kernel `𝗄_n`. -/
  order : ℕ+
  /-- The first matrix `H_1(t) = H_H(t)`. -/
  H₁ : ℝ → Vec 2 →L[ℝ] Vec 2
  /-- The second matrix `H_2(t) = H_V(t)`. -/
  H₂ : ℝ → Vec 2 →L[ℝ] Vec 2

/-- The operator `S(t) = S_{r,H_1(t)} S_{r,H_2(t)}` on `L²(𝕋²; E)`. -/
def KernelSpec.op (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (S : KernelSpec) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] (t : ℝ) :
    Lp E 2 (volume.restrict AVenhance.unitCube) →L[ℝ] Lp E 2 (volume.restrict AVenhance.unitCube) :=
  (periodicComponentAverage (E := E) (displacement S.width (S.H₁ t))
      (continuous_displacement S.width (S.H₁ t)) (momentKernel φ₀ S.order)
      (integrable_momentKernel hφ₀ S.order)).comp
    (periodicComponentAverage (E := E) (displacement S.width (S.H₂ t))
      (continuous_displacement S.width (S.H₂ t)) (momentKernel φ₀ S.order)
      (integrable_momentKernel hφ₀ S.order))

/-- The spanning matrix `[H_1 e_1, H_2 e_2]` of a moving paired kernel at time `t`. -/
def KernelSpec.span (S : KernelSpec) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun a c => if c = 0 then S.H₁ t (basisVec 0) a else S.H₂ t (basisVec 1) a

/-- A moving paired kernel of bound `Γ` with moment cancellation through `L` (Borel matrices,
`‖H_i(t)‖ ≤ Γ`, invertible spanning matrix with `‖[H_1e_1, H_2e_2]⁻¹‖ ≤ Γ`, `2n - 1 ≥ L`;
invertibility is explicit since Lean's inverse of a singular matrix is `0`). -/
def KernelSpec.IsAdmissible (S : KernelSpec) (Γ : ℝ) (L : ℕ) : Prop :=
  Measurable S.H₁ ∧ Measurable S.H₂ ∧ (∀ t, ‖S.H₁ t‖ ≤ Γ ∧ ‖S.H₂ t‖ ≤ Γ ∧
    IsUnit (S.span t).det ∧ ‖(Matrix.toLin' (S.span t)⁻¹).toContinuousLinearMap‖ ≤ Γ) ∧
    L + 1 ≤ 2 * (S.order : ℕ)

/-- The square root of a diagonal matrix with nonnegative diagonal, entrywise. -/
def diagSqrt (J : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal fun a => Real.sqrt (J a a)

/-- The matrix of the transported sampled ellipse at the sampled time `ti` with the renewal index
`li`, for the quiet margin centre `s` (display (10.18) of the paper, patch centre `0`). -/
def sampledEllipse (D : OCData) (b : ℕ) (s ti : ℝ) (li : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  jacMatrix (fun y => D.flowOf b s y ((li : ℝ) * ocTauPP D.α D.q D.Λ (b + 1)))
      (D.flowOf b ((li : ℝ) * ocTauPP D.α D.q D.Λ (b + 1)) (D.flowOf b ti 0 s) ti) *
    diagSqrt ((D.κ b)⁻¹ • ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) ti)

/-- An admissible sampling of the horizontal maximum and its vertical partner on the quiet margin
`[s, s + 4h)`, `h = τ_{b+1}''`, with renewal indices `lH, lV`. -/
def IsPulseSample (D : OCData) (b : ℕ) (s tH tV : ℝ) (lH lV : ℤ) : Prop :=
  let h := ocTauPP D.α D.q D.Λ (b + 1)
  let J := ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1))
  tH ∈ Set.Ico s (s + 4 * h) ∧ (∀ t, J t 0 0 ≤ J tH 0 0) ∧
    tV = (if tH < s + 2 * h then tH + 2 * h else tH - 2 * h) ∧
    |tH - (lH : ℝ) * h| ≤ h / 2 ∧ |tV - (lV : ℝ) * h| ≤ h / 2

/-- The matrices `H_1 = H_H`, `H_2 = H_V` of the fresh kernel born at the level `b`. -/
def IsFreshAxes (D : OCData) (b : ℕ) (H₁ H₂ : ℝ → Vec 2 →L[ℝ] Vec 2) : Prop :=
  ∀ l : ℤ, ∃ (tH tV : ℝ) (lH lV : ℤ),
    IsPulseSample D b (((l : ℝ) + 1 / 2) * ocTauPP D.α D.q D.Λ (b + 1)) tH tV lH lV ∧
    ∀ t ∈ Set.Ico (((l : ℝ) + 1 / 2) * ocTauPP D.α D.q D.Λ (b + 1))
        (((l : ℝ) + 3 / 2) * ocTauPP D.α D.q D.Λ (b + 1)),
      H₁ t = (Matrix.toLin' (jacMatrix (fun y => D.flowOf b t y
          (((l : ℝ) + 1 / 2) * ocTauPP D.α D.q D.Λ (b + 1))) 0 *
        sampledEllipse D b (((l : ℝ) + 1 / 2) * ocTauPP D.α D.q D.Λ (b + 1)) tH lH)).toContinuousLinearMap ∧
      H₂ t = (Matrix.toLin' (jacMatrix (fun y => D.flowOf b t y
          (((l : ℝ) + 1 / 2) * ocTauPP D.α D.q D.Λ (b + 1))) 0 *
        sampledEllipse D b (((l : ℝ) + 1 / 2) * ocTauPP D.α D.q D.Λ (b + 1)) tV lV)).toContinuousLinearMap

/-- The fresh birth length `R_b = c_r √(κ_b τ_{b+1}'')`. -/
def freshLength (D : OCData) (cr : ℝ) (b : ℕ) : ℝ :=
  cr * Real.sqrt (D.κ b * ocTauPP D.α D.q D.Λ (b + 1))

/-- The fresh kernel width `r_b = R_b ε_b^{σ₀}`. -/
def freshWidth (D : OCData) (cr σ₀ : ℝ) (b : ℕ) : ℝ :=
  freshLength D cr b * D.eps b ^ σ₀

/-- `S` is the fresh kernel born at the level `b`: width `r_b`, order `n_k`, fresh axes. -/
def IsFreshKernel (D : OCData) (cr σ₀ : ℝ) (nk : ℕ+) (b : ℕ) (S : KernelSpec) : Prop :=
  S.width = freshWidth D cr σ₀ b ∧ S.order = nk ∧ IsFreshAxes D b S.H₁ S.H₂

end AVRegularity
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity

/-! The lift sequence is triangular in the grade, so a
lift sequence through the grade `H` restricts to one through any grade `H' ≤ H` (same data,
window, cutoff and coefficients). With `lift_path_decomposition` at the top grade of the restricted
sequence this identifies every grade `h ≤ depth` of the comparison lift of `IsLiftedField`. -/

/-- **Grade restriction of a lift sequence.** -/
theorem IsLiftSequence.restrict {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    {Dm : ℕ} {Q : LiftOperatorData ι h Dm} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H H' : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (hH : H' ≤ H) :
    IsLiftSequence Q sX sZ t₀ t₁ N H' Cc := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hC
  exact ⟨h0, fun hh h1' hh' => h1 hh h1' (le_trans hh' hH),
    fun hh hh' => h2 hh (le_trans hh' hH), fun hh hh' => h3 hh (le_trans hh' hH),
    fun hh hh' => h4 hh (le_trans hh' hH), fun hh hh' => h5 hh (le_trans hh' hH),
    fun hh hh' => h6 hh (le_trans hh' hH)⟩

end AVRegularity
end
end

section
/-! Definition: slots, admissible real contexts and natural chart pieces of a
generated family of level `i`.

* `OddSlot`: the slots of a level are the odd integers.
* `IsAdmissibleChain D b j₀ i p ch`: the real chain `ch` is a scheduled chain over the slot `p` of
  level `i` with base level at least `j₀ - 1` (the starting level), odd
  slots, and the centers of its children in the real carrier, `|c_k|₁ < λ ε_k` with
  `λ = λ₂ = 3b/4`; the base label and the
  phases are arbitrary reals (the strips contain all real points). These are the contexts of the
  family (all admissible scheduled chains of the carrier, recorded construction
  fixed).
* `StageCtx D b j₀ i p`: the type of these chains.
* `nativeChain i p`: the native context of the slot (base family of level `i-1`, no child, base
  label `0`); recentering by `y` gives the native context of the label `y`, so the physical
  sample of a piece uses it.
* `availInterval D M i p`: the availability interval `I(𝗉)`: at the terminal level `M`,
  `hull({s_𝗉} ∪ J_𝗉)`; below, `hull({s_𝗉} ∪ J_𝗉 ∪ ⋃_{𝗉'≺𝗉} I(𝗉'))`.
* `IsNaturalPiece D M i p P`: the chart piece of the slot is its natural renewal chart: label
  `l_{i,p}`, output `J_𝗉`, geometry `I(𝗉)`, anchor `s_𝗉`, material map
  `Φ_𝗉(t,y) = X_{i-1}(t, y, s_𝗉)`. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- The slots of a level: the odd integers. -/
abbrev OddSlot : Type := {k : ℤ // Odd k}

/-- The admissible real chains over the slot `p` of level `i`. -/
abbrev StageCtx (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : OddSlot) : Type :=
  {ch : RealChain // IsAdmissibleChain D b j₀ i p.1 ch}

/-- The native context of the slot `p` of level `i`, at base label `0`. -/
def nativeChain (i : ℕ) (p : ℤ) : RealChain :=
  ⟨i - 1, [p], 0, []⟩

/-- The availability interval `I(𝗉)`, with `f` levels to the terminal level. -/
def availAux (D : OCData) : ℕ → ℕ → ℤ → Set ℝ
  | 0, i, p => intervalHull (insert (D.slotAnchor i p) (ocPulseWindow D.α D.q D.Λ i p))
  | f + 1, i, p => intervalHull (insert (D.slotAnchor i p) (ocPulseWindow D.α D.q D.Λ i p ∪
      ⋃ (p' : ℤ) (_ : Odd p' ∧ IsScheduledIn D i p' p), availAux D f (i + 1) p'))

/-- The availability interval `I(𝗉)` of the slot `p` of level `i ≤ M`. -/
def availInterval (D : OCData) (M i : ℕ) (p : ℤ) : Set ℝ :=
  availAux D (M - i) i p

/-- The piece `P` is the natural renewal chart of the slot `p` of level `i`. -/
def IsNaturalPiece (D : OCData) (M i : ℕ) (p : ℤ) (P : ChartPiece) : Prop :=
  P.label = ocLabel D.α D.q D.Λ i p ∧ P.output = ocPulseWindow D.α D.q D.Λ i p ∧
    P.geometry = availInterval D M i p ∧ P.anchor = D.slotAnchor i p ∧
    ∀ t, ⇑(P.material t) = fun y => D.flowOf (i - 1) t y (D.slotAnchor i p)

end AVRegularity

namespace AVRegularity

/-- Recentering a native context moves its base label. -/
theorem nativeChain_recenter (D : OCData) (i : ℕ) (p : ℤ) (Y : Vec 2) :
    (nativeChain i p).recenter D Y = ⟨i - 1, [p], Y, []⟩ := by
  simp [RealChain.recenter, nativeChain]

/-- Native contexts with arbitrary real base label lie in every carrier reserve (the
real base labels are unrestricted). -/
theorem nativeChain_isCarrier (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (mres : ℝ) (hi : 1 ≤ i)
    (hj : j₀ ≤ i) (hp : Odd p) (Y : Vec 2) :
    IsCarrierChain D b j₀ i p mres ⟨i - 1, [p], Y, []⟩ := by
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · simp [RealChain.ctxLevel, RealChain.lastLevel]; omega
  · simp; omega
  · simpa using hp
  · intro k hk; simp at hk
  · intro k hk; simp at hk

end AVRegularity
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! Definition: the lift
relation of the successor, localized to an open set of slow offsets.

`IsLiftSequence` asks for box smoothness and the cell-inverse clause at every slow
offset `X : Vec 2`. The successor lifts the edges of the old stage, which are pinned to zero off
the (bounded, open) admissible set of slow offsets (`GenStage.IsGenerated`), so that relation
is unsatisfiable there. The construction never needs smoothness across the carrier boundary:
the domains are open, recentering is licensed only inside, and functions are asserted only on
their carriers.

* `IsBoxSmoothOn Ω sX sZ f`: the conditions of `IsBoxSmooth` for slow offsets in `Ω`
  (`ContDiffOn` in the slow variable on `Ω`, joint continuity on `Ω ×ˢ univ`).
* `IsLiftSequenceOn Ω`: the clauses of `IsLiftSequence`, with the box-smoothness clause
  and the cell-inverse clause required only for `X ∈ Ω`; the periodicity clause and the algebraic
  clauses keep their all-`X` form.
* `ladderOmega D b j₀ m k A ρ`: the admissible slow offsets
  `{X | IsAdmissibleChain D b j₀ m k (A.recenter D (ρ • X))}` of the lift of the base chain `A`
  over the slot `k` of level `m`. -/

/-- Box regularity of `f(X,z)` for slow offsets `X` in the (open) set `Ω`. -/
def IsBoxSmoothOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ω : Set (Vec 2))
    (sX sZ : ℕ) (f : Vec 2 → Vec 2 → E) : Prop :=
  (∀ X ∈ Ω, ContDiff ℝ (sZ : ℕ∞) (f X)) ∧
  (∀ b, b ≤ sZ → ∀ z, ContDiffOn ℝ (sX : ℕ∞) (fun X => iteratedFDeriv ℝ b (f X) z) Ω) ∧
  ∀ a b, a ≤ sX → b ≤ sZ →
    ContinuousOn (fun p : Vec 2 × Vec 2 =>
      iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b (f X') p.2) p.1) (Ω ×ˢ Set.univ)

/-- `Cc` is the lift sequence (grades `0..H`, degrees up to `N`) of the operator data `Q` on
`[t₀,t₁]`, for the slow offsets of `Ω`. -/
def IsLiftSequenceOn {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ} (Ω : Set (Vec 2))
    (Q : LiftOperatorData ι h D) (sX sZ : ℕ) (t₀ t₁ : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h) :
    Prop :=
  (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X z,
    liftApply 0 (Cc 0 0) (fun _ => a₀) t X z = a₀ X) ∧
  (∀ hh, 1 ≤ hh → hh ≤ H → ∀ m α t X z v u, Cc hh 0 m α t X z v u = 0) ∧
  (∀ hh, hh ≤ H → ∀ n, N < n → ∀ m α t X z v u, Cc hh n m α t X z v u = 0) ∧
  (∀ hh, hh ≤ H → ∀ n m, n < m → ∀ α t X z v u, Cc hh n m α t X z v u = 0) ∧
  (∀ hh, hh ≤ H → ∀ n m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)),
    Cc hh n m (α ∘ σ) = Cc hh n m α) ∧
  (∀ hh, hh ≤ H → ∀ n m α v u, ∀ t ∈ Set.Icc t₀ t₁,
    IsBoxSmoothOn Ω sX sZ (fun X z => Cc hh n m α t X z v u) ∧
    ∀ X, AVenhance.IsZ2Periodic (fun z => Cc hh n m α t X z v u)) ∧
  (∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
    ∀ X ∈ Ω, IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ t₀ t₁ (fun _ => 0)
      (fun t z => liftCellSource Q Cc (fun _ => a₀) hh n t X z)
      (fun t z => liftApply n (Cc hh n) (fun _ => a₀) t X z))

/-- The admissible slow offsets of the lift of the base chain `A` over the slot `k` of level `m`,
with lift slow length `ρ`. -/
def ladderOmega (D : OCData) (b : ℝ) (j₀ m : ℕ) (k : ℤ) (A : RealChain) (ρ : ℝ) : Set (Vec 2) :=
  {X | IsAdmissibleChain D b j₀ m k (A.recenter D (ρ • X))}

end AVRegularity
end
end
end

section
@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! Definition: a generated family of a level, as a stage of
the construction.

A stage of level `i` consists of a finite set of components `comps : Finset Comp` (the value
space of a component is the space `hr root` of its root,
since a word copies the space of its parent, `𝗁_{(v,ς)} = 𝗁_v`), a
charted family `fam` over `{c // c ∈ comps}` whose pieces are the odd slots of the level and whose
contexts are the admissible real chains over the slot (`StageCtx`), the positive path provenance
`prov` of every identity, and the actual (native) context of every piece.

The family's chart representative of an identity at the context `ch`, slow offset `X` and fast
phase `z` is the context function of the identity evaluated at the recentered context
`ch^{[E X]}` and the phase `z`, `E = ε_{i-1}` (the source is
`div[κ_i ε_i^{d-2} ∑ a(t, x/ε_{i-1}, x/ε_i) ∂^α f]`). The predicates:
* `IsNatural`: natural renewal pieces of the level (`IsNaturalPiece`), partition weights
  `ϖ_{i,p} = ocCutoff`, native actual contexts, injective provenance;
* `HasTags P`: every record is the structural recursion `Prov.tags` (records and orders);
* `IsGenerated`: every scalar coefficient is a context function generated with the schedule
  (`IsGeneratedCtxFrom`), the same expression for every context of the slot (generated
  membership);
* `kernelOf`: the kernel of an identity, from its provenance (seed kernels kept, fresh kernels of
  their birth). -/

/-- The components of a stage as a type. -/
abbrev CompIn (S : Finset Comp) : Type := {c : Comp // c ∈ S}

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]

/-- A generated family of level `level` (a stage of the construction). -/
structure GenStage (D : OCData) (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, NormedSpace ℝ (hr r)] (Dm : ℕ) (b : ℝ) (j₀ : ℕ) where
  /-- The level `i` of the family. -/
  level : ℕ
  /-- The components. -/
  comps : Finset Comp
  /-- The charted family of the components: pieces are the odd slots of the level, contexts the
  admissible real chains over the slot. -/
  fam : ChartedFamily (CompIn comps) (fun c => hr c.1.root) Dm OddSlot (StageCtx D b j₀ level)
  /-- The positive path provenance of every identity. -/
  prov : ∀ v u, fam.Γ v u → Prov
  /-- The actual context of every piece. -/
  actual : ∀ p, StageCtx D b j₀ level p
  /-- The certified context exports of the supplied seed, with their full occurrence trees:
  the only places where two-dimensional inverses (`solved` nodes) may occur.
  Inherited unchanged by restrictions and successors. -/
  exports : SeedExports

namespace GenStage

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The pieces are the natural renewal charts of the level (terminal level `M`), the weights are
the partition `ϖ_{i,p}`, the actual contexts are native, and the provenance is injective. -/
def IsNatural (M : ℕ) (G : GenStage D hr Dm b j₀) : Prop :=
  (∀ p, IsNaturalPiece D M G.level p.1 (G.fam.piece p)) ∧
    (∀ p t, G.fam.weight p t = ocCutoff D.α D.q D.Λ G.level p.1 t) ∧
    (∀ p, (G.actual p).1 = nativeChain G.level p.1) ∧
    ∀ v u, Function.Injective (G.prov v u)

/-- The records and maximal orders of the identities are the tags of their provenance. -/
def HasTags (P : ProvParams) (G : GenStage D hr Dm b j₀) : Prop :=
  ∀ v u (γ : G.fam.Γ v u), ((G.prov v u γ).tags P).Matches (G.fam.identity v u γ).record ∧
    (G.fam.identity v u γ).maxOrder = ((G.prov v u γ).tags P).order

open scoped Classical in
/-- Every scalar coefficient is a context function generated with the schedule, evaluated at the
recentered context and the fast phase when the recentered context lies in the outer carrier, and
zero off the carrier (off-carrier values are pinned, so that predicates over
every slow offset see no junk). The equality is asserted on the output domain `J_𝗉` of the slot
only (the construction neither asserts nor continues these functions outside their output
intervals). The expression has seed provenance (`Gen.FromSeed G.exports`):
its two-dimensional inverses occur only inside the certified seed exports. -/
def IsGenerated (G : GenStage D hr Dm b j₀) : Prop :=
  ∀ (p : OddSlot) v u (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (k : Fin 2),
    ∃ f : GenSort.Sem .ctx, IsGeneratedCtxFrom D b j₀ G.exports G.level p.1 f ∧
      ∀ (c : StageCtx D b j₀ G.level p) (t : ℝ), t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
        ∀ (X z : Vec 2),
        G.fam.flux p c v u γ d I t X z k =
          if IsAdmissibleChain D b j₀ G.level p.1 (c.1.recenter D (D.eps (G.level - 1) • X)) then
            f t (c.1.recenter D (D.eps (G.level - 1) • X)) z else 0

/-- The inner domain of the envelopes at the reserve `𝗆` over the window `W`: the
pairs `(t, Y)` of an output time in `W` and a dimensional slow offset whose recentered context
`c^{[Y]}` lies in the carrier `𝔇(𝗆)` (recentering is licensed only inside the carrier).
Native contexts cover every physical label
(`nativeChain_isCarrier`, `GenStage.innerDomain_native`). -/
def innerDomain (G : GenStage D hr Dm b j₀) (W : Set ℝ) (mres : ℝ) : G.fam.Domain :=
  fun p c => {tY | tY.1 ∈ (G.fam.piece p).output ∩ W ∧
    IsCarrierChain D b j₀ G.level p.1 mres (c.1.recenter D tY.2)}

/-- The kernel of an identity: its seed kernel or the fresh kernel of its birth. -/
def kernelOf (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (G : GenStage D hr Dm b j₀)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) : KernelSpec :=
  match ((G.prov v u γ).tags P).kernel with
  | .seed k => seedK k
  | .fresh b' => freshK b'

/-- The physical (Eulerian) coefficient of the order-`d` part of an identity, at the diffusivity
`κ_i` and the wavelengths `(ε_i, ε_{i-1})` of the level (`constituentPhysical`). -/
def physCoeff (G : GenStage D hr Dm b j₀) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) :
    ℝ → Vec 2 → (PiLp 2 (fun _ : DerivativeWord2 (d - 1) => hr u.1.root)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => hr v.1.root)) :=
  constituentPhysical G.fam (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) G.actual v u γ d

/-- The restriction of a stage to a subset of its components (the retained family). -/
def restrict (G : GenStage D hr Dm b j₀) (S : Finset Comp) (hS : S ⊆ G.comps) :
    GenStage D hr Dm b j₀ where
  level := G.level
  comps := S
  fam :=
    { Γ := fun v u => G.fam.Γ ⟨v.1, hS v.2⟩ ⟨u.1, hS u.2⟩
      fintypeΓ := fun v u => G.fam.fintypeΓ ⟨v.1, hS v.2⟩ ⟨u.1, hS u.2⟩
      identity := fun v u γ => G.fam.identity ⟨v.1, hS v.2⟩ ⟨u.1, hS u.2⟩ γ
      piece := G.fam.piece
      flux := fun p c v u γ => G.fam.flux p c ⟨v.1, hS v.2⟩ ⟨u.1, hS u.2⟩ γ
      flux_periodic := fun p c v u γ => G.fam.flux_periodic p c ⟨v.1, hS v.2⟩ ⟨u.1, hS u.2⟩ γ
      flux_zero := fun p c v u γ => G.fam.flux_zero p c ⟨v.1, hS v.2⟩ ⟨u.1, hS u.2⟩ γ
      weight := G.fam.weight
      weight_nonneg := G.fam.weight_nonneg
      weight_zero := G.fam.weight_zero
      locally_finite := G.fam.locally_finite
      weight_sum := G.fam.weight_sum }
  prov := fun v u γ => G.prov ⟨v.1, hS v.2⟩ ⟨u.1, hS u.2⟩ γ
  actual := G.actual
  exports := G.exports

/-- Coverage of every physical label by the native context. -/
theorem innerDomain_native (G : GenStage D hr Dm b j₀) (W : Set ℝ) (mres : ℝ) (p : OddSlot)
    (hact : (G.actual p).1 = nativeChain G.level p.1) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (t : ℝ) (ht : t ∈ (G.fam.piece p).output ∩ W) (Y : Vec 2) :
    (t, Y) ∈ G.innerDomain W mres p (G.actual p) := by
  refine ⟨ht, ?_⟩
  show IsCarrierChain D b j₀ G.level p.1 mres ((G.actual p).1.recenter D Y)
  rw [hact, nativeChain_recenter]
  exact nativeChain_isCarrier D b j₀ G.level p.1 mres hi hj p.2 Y

end GenStage

end AVRegularity
end

section
open Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity

/-! **The carried history invariant of a stage**. Two contexts of a slot have the same
history geometry when their centered material maps and physical centers agree over the slot's
availability interval (`SameHistoryGeometry`). A stage carries the history invariant when its
fluxes at two such contexts agree as germs in the slow offset (`StageHistoryInvariant`). The
definitions are those of `Providers/QuietAtlas/Statement.lean`, moved unchanged so that the stage
invariant (`IsStageInvariant`, `Construction/Invariant.lean`) can carry the clause. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Equality of the centered material maps and their physical centers over the complete common
slot history. Centered maps alone would identify unrelated translates of a seed family. -/
def SameHistoryGeometry (D : OCData) (Mtop m : ℕ) (p : ℤ) (ch ch' : RealChain) : Prop :=
  ∀ s ∈ availInterval D Mtop m p,
    ch.famMap D s = ch'.famMap D s ∧
      (ch.geom D).1 s (ch.geom D).2.1 (ch.geom D).2.2 =
        (ch'.geom D).1 s (ch'.geom D).2.1 (ch'.geom D).2.2

/-- The carried invariant for the produced stage, with complete contexts retained. -/
def StageHistoryInvariant (G : GenStage D hr Dm b j₀) (Mtop : ℕ) : Prop :=
  ∀ (p : OddSlot) (ch ch' : StageCtx D b j₀ G.level p),
    SameHistoryGeometry D Mtop G.level p.1 ch.1 ch'.1 →
    ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
      ∀ v u (γ : G.fam.Γ v u) d (I : DerivativeWord2 (d - 1)) (z : Vec 2),
        (fun Y => G.fam.flux p ch v u γ d I t Y z) =ᶠ[𝓝 0]
          (fun Y => G.fam.flux p ch' v u γ d I t Y z)

end AVRegularity
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! Definition: the context-level torus law of a
stage, the induction invariant of the construction that yields the torus compatibility.

`RealChain.shiftBase ch n` moves the base label of a real chain by the integer vector `n`.
The flows of
the construction are lifts of torus maps, so the centered
families are unchanged, `𝒜^{Y+n}_u(h) = 𝒜^Y_u(h)`, and so are the children at
fixed relative centers, phases and anchors, their metrics, Jacobians and Piola factors, the
zero-past cell inverses (same operator, forcing, start and history) and every recorded expression
built from them. `GenStage.IsShiftInvariant G`: every independent field of the stage
is unchanged when its context is replaced by the same context with an integer-shifted base label,
at all times, slow offsets and fast variables; and on contexts without children the slow offset
`X + ε_{i-1}⁻¹ n` gives the field of the base-shifted context at `X`, at all times (the generated representation is asserted only on `J_𝗉`, so the torus law that
`IsTorusCompatible` needs at every time is carried by the invariant itself). It is a statement about **all** admissible contexts,
not only the selected ones: the successor reads the incoming stage on non-native contexts (the
path families `pathEdges G π k A` over every admissible real chain `A`), so the law at the selected
contexts alone does not propagate. Admissibility does not see the base label
(`isAdmissibleChain_shiftBase`). -/

section
/-- The real chain `ch` with its base label moved by the integer vector `n`. -/
def RealChain.shiftBase (ch : RealChain) (n : Fin 2 → ℤ) : RealChain :=
  { ch with base := ch.base + AVenhance.latticeShift n }

/-- Admissibility does not see the base label. -/
theorem isAdmissibleChain_shiftBase (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (ch : RealChain)
    (n : Fin 2 → ℤ) :
    IsAdmissibleChain D b j₀ i p (ch.shiftBase n) ↔ IsAdmissibleChain D b j₀ i p ch :=
  Iff.rfl

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

namespace GenStage

/-- The context-level torus law: the independent fields of the stage at a context with an
integer-shifted base label equal those at the context itself; and
the slow-offset torus law at every time: on a context without children (a base family, such as the
native selected contexts), moving the slow offset by `ε_{i-1}⁻¹ n` is the same as shifting the base
label by `n`. -/
def IsShiftInvariant (G : GenStage D hr Dm b j₀) : Prop :=
  (∀ (p : OddSlot) (c c' : StageCtx D b j₀ G.level p) (n : Fin 2 → ℤ), c'.1 = c.1.shiftBase n →
    ∀ v u (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)),
      G.fam.flux p c' v u γ d I = G.fam.flux p c v u γ d I) ∧
  ∀ (p : OddSlot) (c c' : StageCtx D b j₀ G.level p) (n : Fin 2 → ℤ), c.1.children = [] →
    c'.1 = c.1.shiftBase n →
    ∀ v u (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2),
      G.fam.flux p c v u γ d I t (X + (D.eps (G.level - 1))⁻¹ • AVenhance.latticeShift n) z =
        G.fam.flux p c' v u γ d I t X z

/-- Restriction to a subset of the components keeps the law. -/
theorem IsShiftInvariant.restrict {G : GenStage D hr Dm b j₀} (hG : G.IsShiftInvariant)
    (S : Finset Comp) (hS : S ⊆ G.comps) : (G.restrict S hS).IsShiftInvariant :=
  ⟨fun p c c' n hc v u γ d I => hG.1 p c c' n hc ⟨v.1, hS v.2⟩ ⟨u.1, hS u.2⟩ γ d I,
    fun p c c' n h0 hc v u γ d I => hG.2 p c c' n h0 hc ⟨v.1, hS v.2⟩ ⟨u.1, hS u.2⟩ γ d I⟩

end GenStage
end

/-! Definition: path summands of the pulse-local lift on a real family,
their means in the left flux presentation, and the canonical coefficient arrays.

The production runs the pulse-local lift on every slot of level `m`, in its native cell chart,
with the molecular metric and the actual normalized drift of the pulse and zero value at the
original start `inf J_𝗉`, and expands every lift and mean of source degree `h` into a sum over
the directed paths `𝔭` with `h` edges and over the choices of one constituent on each edge.
Every
operation acts on the scalar coefficients and the constant maps multiply in path order, so
a path summand is the grade-`h` entry `(h ← 0)` of the lift of the *scalar path family*: components
`0, …, h`, one edge `k → k+1` carrying the scalar coefficients of the chosen identity of the `k`-th
step, identity maps.

* `StagePath G h`: a directed path of `h` edges of the stage `G` with one identity on each edge.
* `pathEdges G π p c`: the scalar path family at the piece `p` and context `c` (one constituent per
  edge, its orders `2 ≤ d ≤ D_γ`).
* `familyLiftData D m k A ρ edge`: the lift operator data on the real family `A` (a chain over the
  slot `k` of level `m`): contrast `η = κ_m/κ_{m-1}`, metric `G(𝗍,X) = 𝒢_{ℓ²𝗍}(0)` of the recentered
  family `A^{[ρX]}`, the actual cell drift of the pulse `k`, and the source edges in the lift
  variables `(𝗍, X) = (t/ℓ², y/ρ)` (`liftEdges`). On the native physical family this is
  `pulseLiftData` (up to the chart-index convention, see `ocLabel_eq_ocPulseChartIndex`).
* `liftFluxX Q Cc a hh n`: the slow (`X`-) flux of `𝐀_n^{(hh)} = ℬ₁C_{n-1} + ℬ₂C_{n-2} - ∑_j 𝒮_jC_{n-j}`
  (`liftA`): `ℬ₁Φ` has slow flux `√η v Φ - √η G∇_zΦ` (`w·∇_X Φ = div_X(wΦ)`, `w` independent
  of `X`), `ℬ₂Φ` has `-ηG∇_XΦ`, and `𝒮_ε = D_ε·flux_ε` has slow flux `√η ε flux_ε`, whose `ε^j`
  coefficient is `√η (j-1)!⁻¹ ∂_ε^{j-1} flux_ε|_{ε=0}`. Fast divergences have zero cell mean, so
  `L_n^{(hh)} = P₀𝐀_n^{(hh)} = div_X P₀(liftFluxX)`: this is the left flux presentation of the
  means.
* `fluxCoeff L d α y`: the coefficient of `∂^α`, `|α| = d-1`, of a flux operator `L` (scalar field
  ↦ flux field) at `y`, in the symmetric ordered-word convention: `L[(·-y)^α](y)/(d-1)!`.
* `pathMeanFlux`: the physical (label-variable) flux of the grade-`h` degree-`n` path mean
  `ℓ^{-2}η_cell^n 𝐄_n^{(h)} = -ℓ^{-2}ε_c^n L_n^{(h)}` (the convention `M I - 𝐄`),
  `ε_c = d_*/ρ`, read at the entry `(h ← 0)`. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- A directed path of `h` edges of the stage `G`, with one identity on each edge: step `j` is an
identity of the edge `u_j → v_j`, and `u_{j+1} = v_j`. -/
structure StagePath (G : GenStage D hr Dm b j₀) (h : ℕ) where
  /-- The steps `(v_j, u_j, γ_j)`. -/
  step : Fin h → Σ (v u : CompIn G.comps), G.fam.Γ v u
  /-- Consecutive steps are joined. -/
  joined : ∀ (j : ℕ) (hj : j + 1 < h), (step ⟨j + 1, hj⟩).2.1 = (step ⟨j, by omega⟩).1

namespace StagePath

variable {G : GenStage D hr Dm b j₀} {h : ℕ}

/-- The provenance list of the path (target, source, identity). -/
def provList (π : StagePath G h) : List (Comp × Comp × Prov) :=
  List.ofFn fun j => ((π.step j).1.1, (π.step j).2.1.1, G.prov _ _ (π.step j).2.2)

/-- The maps of the path, with the roots of their spaces. -/
def mapList (π : StagePath G h) : List (Σ (a c : ℕ), hr a →L[ℝ] hr c) :=
  List.ofFn fun j => ⟨(π.step j).2.1.1.root, (π.step j).1.1.root,
    (G.fam.identity _ _ (π.step j).2.2).map⟩

end StagePath

/-- The scalar path family of `π` at the piece `p` and context `c`. -/
def pathEdges (G : GenStage D hr Dm b j₀) {h : ℕ} (π : StagePath G h) (p : OddSlot)
    (c : StageCtx D b j₀ G.level p) : ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ) :=
  fun v u d =>
    if hvu : (v : ℕ) = u + 1 ∧ (u : ℕ) < h then
      if hd : d.1 ≤ (G.fam.identity _ _ (π.step ⟨u, hvu.2⟩).2.2).maxOrder then
        [{ map := ContinuousLinearMap.id ℝ ℝ
           coeff := G.fam.flux p c _ _ (π.step ⟨u, hvu.2⟩).2.2 d.1
           periodic := G.fam.flux_periodic p c _ _ (π.step ⟨u, hvu.2⟩).2.2 d.1
           record := (G.fam.identity _ _ (π.step ⟨u, hvu.2⟩).2.2).record
           birthExcess_ge := le_trans hd (G.fam.identity _ _ (π.step ⟨u, hvu.2⟩).2.2).le_birth }]
      else []
    else []

/-- The lift operator data of a family (a scalar path family, or the Hilbert family itself) on the
real family `A` over the slot `k` of level `m`, with lift slow length `ρ`. The cell contrast and
the drift use the terminal-diffusivity convention `OCData.kap` (`η = 1` at weak levels); at the cascade levels `m ≤ M = D.term` this is `κ_m/κ_{m-1}`. -/
def familyLiftData {ι : Type*} {hv : ι → Type*} [∀ i, NormedAddCommGroup (hv i)]
    [∀ i, NormedSpace ℝ (hv i)] (D : OCData) (m : ℕ) (k : ℤ) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm hv) : LiftOperatorData ι hv Dm where
  η := D.kap m / D.kap (m - 1)
  G := fun s X a c => (A.recenter D (ρ • X)).famMetric D (D.cellScaleSq m * s) a c
  v := ocPulseCellDrift D.α D.q D.Λ D.ζ m (D.kap m) k
  edge := liftEdges (D.cellScaleSq m) (ρ / D.eps (m - 1)) edge

/-- The slow flux of `𝐀_n^{(hh)}` applied to the coarse field `a`, at time `t`. -/
def liftFluxX {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ} (Q : LiftOperatorData ι h Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ) :
    Vec 2 → Vec 2 → Fin 2 → ∀ i, h i :=
  fun X z k =>
    ((Real.sqrt Q.η * Q.v t z k) • liftApply (n - 1) (Cc hh (n - 1)) a t X z
      - Real.sqrt Q.η • ∑ j : Fin 2,
          Q.G t X k j • fastPartial j (liftApply (n - 1) (Cc hh (n - 1)) a t) X z)
    + (if 2 ≤ n then -(Q.η • ∑ j : Fin 2,
          Q.G t X k j • slowPartial j (liftApply (n - 2) (Cc hh (n - 2)) a t) X z) else 0)
    - (if hh = 0 then 0 else ∑ j ∈ Finset.Icc 1 (min Dm n),
        (Real.sqrt Q.η * ((j - 1).factorial : ℝ)⁻¹) •
          iteratedDeriv (j - 1) (fun ε : ℝ =>
            sourceFlux Q.edge Q.η ε t (liftApply (n - j) (Cc (hh - 1) (n - j)) a t) k X z) 0)

/-- The coefficient of `∂^α` (`|α| = d - 1`) of a flux operator at `y`. -/
def fluxCoeff (L : (Vec 2 → ℝ) → Vec 2 → Vec 2) (d : ℕ) (α : DerivativeWord2 (d - 1))
    (y : Vec 2) : Vec 2 :=
  ((d - 1).factorial : ℝ)⁻¹ • L (fun Y => ∏ j, (Y - y) (α j)) y

/-- The physical flux of the grade-`h` degree-`n` path mean on the family `A` over the slot `k` of
level `m`, in the label variables of its chart, at time `t`: `-ℓ^{-2} ε_c^n ρ P₀(liftFluxX)(y/ρ)`
read at the entry `(h ← 0)`, `ε_c = d_*/ρ`. -/
def pathMeanFlux (D : OCData) (m : ℕ) (ρ : ℝ) {h : ℕ}
    (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (t : ℝ) :
    (Vec 2 → ℝ) → Vec 2 → Vec 2 :=
  fun f y k =>
    -((D.cellScaleSq m)⁻¹ * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ) *
      fieldCellMean (fun z => liftFluxX Q Cc (fun _ X => Pi.single (0 : Fin (h + 1)) (f (ρ • X)))
        h n ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z k) (Fin.last h)

/-- The all-slow direct part `ℓ^{-2}η^d P₀𝐒_d I` of the identity `γ` (physical: the cell-averaged
coefficient `κ_m ε_m^{d-2} ⟨a♭_{γ,d}⟩_z`) for the orders `d ∈ ords`, at the context `c` of the
piece `p`, as a flux operator in the label variables. -/
def directFlux (G : GenStage D hr Dm b j₀) (p : OddSlot) (c : StageCtx D b j₀ G.level p)
    {v u : CompIn G.comps} (γ : G.fam.Γ v u) (ords : Finset ℕ) (t : ℝ) :
    (Vec 2 → ℝ) → Vec 2 → Vec 2 :=
  fun f y => ∑ d ∈ ords, ∑ α : DerivativeWord2 (d - 1),
    (D.kap G.level * D.eps G.level ^ (d - 2) * orderedDerivative α f y) •
      fieldCellMean (fun z => G.fam.flux p c v u γ d α t ((D.eps (G.level - 1))⁻¹ • y) z)
end

/-! Definition: the transfer of a finer output to the coarser chart.

A family function of level `m-1` over a finer slot `𝗉 = k` of level `m` (an output of the
level-`m` passage, given here by its flux operator `fop k t 𝒜` in the label variables of the
chart of `k`, centered at the family `𝒜`) is written in the native chart of a coarser slot `p̃`
of level `m-1` with `𝗉 ≺ p̃`: at the context `(ch, z)` the child `𝒜^♮ = ch.appendChild k t z` is
appended, `J = F^♮_t(0)⁻¹ F_t(0)` (`childTransition`), the outer divergence is pulled back by
Piola and the derivatives by the vector fields `J^{-T}∇` (`transportedCoeff` with `K = J⁻¹`; a
derivative falling on an entry of `J^{-T}` is the old-label derivative of the coarser context,
here the derivative in the recentering offset `h` of `(ch^{[h]}, z + h/ε_{m-1})`); the finer slot
occurrences are grouped with the partition weights `ϖ_{m,k}(t)` before any size is taken.
For `d' = 2` this is `ϖ J⁻¹ 𝔠 J⁻ᵀ`. The finer coefficients are
dimensional; the coarser array is normalized by `κ_{m-1} ε_{m-1}^{d'-2}`
(the normalization of the sources at level `m-1`), and multiplied by `lam`
(`λ_{m-1}⁻¹ = ε_{m-1}^{-η₀}` on a letter edge; `1` on a copy). -/

/-- The Eulerian pushforward of a label flux operator by the chart germ `Ψ` with inverse `Ψinv`:
`(Ψ_*L)f = [DΨ · L(f∘Ψ)]∘Ψ⁻¹`. -/
def pushFlux (Ψ Ψinv : Vec 2 → Vec 2) (L : (Vec 2 → ℝ) → Vec 2 → Vec 2) :
    (Vec 2 → ℝ) → Vec 2 → Vec 2 :=
  fun f x => (jacMatrix Ψ (Ψinv x)).mulVec (L (f ∘ Ψ) (Ψinv x))

/-- The Piola pullback of a physical flux operator by the chart germ `Φ` with inverse `Φinv`:
`(Φ^*F)u = (DΦ)⁻¹[F(u∘Φ⁻¹)]∘Φ`; it keeps the outer Piola factor and every
lower tested order. -/
def pullFlux (Φ Φinv : Vec 2 → Vec 2) (F : (Vec 2 → ℝ) → Vec 2 → Vec 2) :
    (Vec 2 → ℝ) → Vec 2 → Vec 2 :=
  fun u y => ((jacMatrix Φ y)⁻¹).mulVec (F (u ∘ Φinv) (Φ y))

/-- `J = F^♮_t(0)⁻¹ F_t(0)` for the child appended for the finer slot `k` at the context `(ch, z)`. -/
def childTransition (D : OCData) (k : ℤ) (t : ℝ) (ch : RealChain) (z : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  ((ch.appendChild D k t z).famJac D t)⁻¹ * ch.famJac D t

/-- A finer output: for each finer slot, time and family, its flux operator in the label
variables of the chart of the slot. -/
abbrev FamFluxOp : Type := ℤ → ℝ → RealChain → (Vec 2 → ℝ) → Vec 2 → Vec 2

/-- The order-`d'` word-`β` array, in the native chart of the slot `p̃` of level `m-1` at the
context `(ch, z)` and time `t`, of the finer output `fop` of maximal order `Dγ`. -/
def transferAt (D : OCData) (m : ℕ) (pc : ℤ) (lam : ℝ) (Dγ : ℕ) (fop : FamFluxOp) (t : ℝ)
    (ch : RealChain) (z : Vec 2) (d' : ℕ) (β : DerivativeWord2 (d' - 1)) : Vec 2 :=
  ((D.kap (m - 1) * D.eps (m - 1) ^ (d' - 2))⁻¹ * lam) •
    ∑ᶠ (k : ℤ) (_ : Odd k ∧ IsScheduledIn D (m - 1) k pc),
      ocCutoff D.α D.q D.Λ m k t •
        transportedCoeff
          (fun h => (childTransition D k t (ch.recenter D h) (z + (D.eps (m - 1))⁻¹ • h))⁻¹) Dγ
          (fun d I => fluxCoeff (fop k t (ch.appendChild D k t z)) d I 0) (d' - 1) β 0

/-! Definition: the sources of the identities of the next
family, the pieces of the operator of display (12.20) of the paper.

An identity of the extended next family of the passage `m → m-1` is one of:
* `copyDir t v u γ`: the copy into the word `𝔱` of the direct transport of the old identity `γ`
  of `u → v` (its all-slow orders `3 ≤ d ≤ D_γ`, part of `𝖤_{dir,>2}`), on the edge
  `(u,𝔱) → (v,𝔱)`;
* `copyQuad t h π`: the copy into `𝔱` of the quadratic conversion of the cell-degree-two mean of the
  path `π` (part of `𝖤_2`), on `(src π, 𝔱) → (tgt π, 𝔱)`;
* `letterDiag t u`: the first source `𝖣`, acting as the identity map, on `(u,𝔱) → (u,𝔱𝖣)`;
* `letterMean t n h π`: the path summand of `𝖬_{n,h}` (the part of `𝐄_int` of cell degree `n ≥ 3`
  and source degree `h`: the path mean minus, for a one-edge path, its all-slow order-`n` part),
  on `(src π, 𝔱) → (tgt π, 𝔱𝖬_{n,h})`;
* `letterCov t n h a a' π`: the path summand of `𝖵_{n,h,a,a'} = (-𝒞)^a 𝐄_n^{(h)} 𝒞^{a'}/(a!a'!)`,
  expanded by Leibniz' rule inside the outer divergence, on `(src π, 𝔱) → (tgt π, 𝔱𝖵_{n,h,a,a'})`.
`Valid A J s`: the word is empty or in `𝔗` (length at most `J+1`), a letter edge starts from a word
of length at most `J` and its letter is in the alphabet, a direct transport has `D_γ ≥ 3`, a path
has at least one edge.

`SuccSource.fluxOp`: the finer output of the source on a real family (the flux operator in the
label variables of the chart of the finer slot), from the lift coefficients `Cc` of the path's
scalar family on that family. The covariance operator `𝒞 = 𝖧:D²` uses the covariance primitive of
level `m` with its original anchor `0` (`H(0) = 0`) and acts by **Eulerian** derivatives:
the label mean flux is pushed forward by the chart germ of
the family (`pushFlux`), the letter `(-1)^a 𝒞_x^a 𝐄^flux 𝒞_x^{a'}/(a!a'!)` is formed in Eulerian
variables (the covariance derivatives act on coefficients and fields), and the result is
Piola-pulled back to the labels (`pullFlux`). -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The ordered product of maps `hr a_j → hr c_j` (first map first), from `hr r₀` to `hr r`;
consecutive spaces must agree (`0` otherwise). -/
def rootPathMap (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)] :
    (r₀ : ℕ) → List (Σ (a c : ℕ), hr a →L[ℝ] hr c) → (r : ℕ) → (hr r₀ →L[ℝ] hr r)
  | r₀, [], r => if h : r₀ = r then h ▸ ContinuousLinearMap.id ℝ (hr r₀) else 0
  | r₀, ⟨a, c, f⟩ :: rest, r =>
      if h : r₀ = a then (rootPathMap hr c rest r).comp (h ▸ f) else 0

namespace StagePath

variable {G : GenStage D hr Dm b j₀} {h : ℕ}

/-- The source component of a path (of at least one edge). -/
def src (π : StagePath G h) : Comp :=
  if hh : 0 < h then (π.step ⟨0, hh⟩).2.1.1 else ⟨0, []⟩

/-- The target component of a path (of at least one edge). -/
def tgt (π : StagePath G h) : Comp :=
  if hh : 0 < h then (π.step ⟨h - 1, by omega⟩).1.1 else ⟨0, []⟩

end StagePath

/-- The source of an identity of the next family. -/
inductive SuccSource (G : GenStage D hr Dm b j₀) : Type
  /-- The copy into `t` of the direct transport of `γ`. -/
  | copyDir (t : List WordLetter) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
  /-- The copy into `t` of the quadratic conversion of the path `π`. -/
  | copyQuad (t : List WordLetter) (h : ℕ) (π : StagePath G h)
  /-- The first source on the component `u`, from the word `t`. -/
  | letterDiag (t : List WordLetter) (u : CompIn G.comps)
  /-- The path summand of `𝖬_{n,h}` from the word `t`. -/
  | letterMean (t : List WordLetter) (n h : ℕ) (π : StagePath G h)
  /-- The path summand of `𝖵_{n,h,a,a'}` from the word `t`. -/
  | letterCov (t : List WordLetter) (n h a a' : ℕ) (π : StagePath G h)

namespace SuccSource

variable {G : GenStage D hr Dm b j₀}

/-- The word of the source component. -/
def word : SuccSource G → List WordLetter
  | .copyDir t .. | .copyQuad t .. | .letterDiag t .. | .letterMean t .. | .letterCov t .. => t

/-- The letter appended on a letter edge. -/
def letter? : SuccSource G → Option WordLetter
  | .copyDir .. | .copyQuad .. => none
  | .letterDiag .. => some .diag
  | .letterMean _ n h _ => some (.mean n h)
  | .letterCov _ n h a a' _ => some (.covariance n h a a')

/-- The old source component. -/
def oldSrc : SuccSource G → Comp
  | .copyDir _ _ u _ => u.1
  | .copyQuad _ _ π | .letterMean _ _ _ π | .letterCov _ _ _ _ _ π => π.src
  | .letterDiag _ u => u.1

/-- The old target component. -/
def oldTgt : SuccSource G → Comp
  | .copyDir _ v _ _ => v.1
  | .copyQuad _ _ π | .letterMean _ _ _ π | .letterCov _ _ _ _ _ π => π.tgt
  | .letterDiag _ u => u.1

/-- The word of the target component. -/
def newWord (s : SuccSource G) : List WordLetter :=
  match s.letter? with
  | none => s.word
  | some l => s.word ++ [l]

/-- The source component `(u, 𝔱)` in the next family. -/
def srcComp (m : ℕ) (s : SuccSource G) : Comp := succComp m s.oldSrc s.word

/-- The target component in the next family. -/
def tgtComp (m : ℕ) (s : SuccSource G) : Comp := succComp m s.oldTgt s.newWord

/-- The validity of a source for the alphabet `A` and the word length `J`. -/
def Valid (A : Finset WordLetter) (J : ℕ) (s : SuccSource G) : Prop :=
  s.word ∈ insert [] (wordsUpTo A (J + 1)) ∧
    (∀ l, s.letter? = some l → s.word.length ≤ J ∧ l ∈ A) ∧
    match s with
    | .copyDir _ v u γ => 3 ≤ (G.fam.identity v u γ).maxOrder
    | .copyQuad _ h _ | .letterMean _ _ h _ | .letterCov _ _ h _ _ _ => 1 ≤ h
    | .letterDiag .. => True

/-- The provenance of the new identity at the passage `m`. -/
def prov (m : ℕ) : SuccSource G → Prov
  | .copyDir _ v u γ => .dir m (G.prov v u γ)
  | .copyQuad _ _ π => .quad m π.provList
  | .letterDiag _ _ => .letter m .diag []
  | .letterMean _ n h π => .letter m (.mean n h) π.provList
  | .letterCov _ n h a a' π => .letter m (.covariance n h a a') π.provList

/-- The maps of the new identity, in path order (the identity for `𝖣`). -/
def maps : SuccSource G → List (Σ (a c : ℕ), hr a →L[ℝ] hr c)
  | .copyDir _ v u γ => [⟨u.1.root, v.1.root, (G.fam.identity v u γ).map⟩]
  | .copyQuad _ _ π | .letterMean _ _ _ π | .letterCov _ _ _ _ _ π => π.mapList
  | .letterDiag _ _ => []

/-- The number of edges of the path of the source (`0` without a path). -/
def pathLen : SuccSource G → ℕ
  | .copyDir .. | .letterDiag .. => 0
  | .copyQuad _ h _ | .letterMean _ _ h _ | .letterCov _ _ h _ _ _ => h

/-- The normalization of the edge: `1` on a copy, `λ_{m-1}⁻¹ = ε_{m-1}^{-η₀}` on a letter. -/
def lam (m : ℕ) (η₀ : ℝ) (s : SuccSource G) : ℝ :=
  match s.letter? with
  | none => 1
  | some _ => D.eps (m - 1) ^ (-η₀)

/-- The covariance operator `𝒞 = 𝖧_m(t):D²` of level `m` with the anchor `s₀` of its primitive
(`0` in the cascade; the quiet endpoint `t_p` at terminal entry). -/
def covAt (D : OCData) (m : ℕ) (s₀ t : ℝ) : (Vec 2 → ℝ) → Vec 2 → ℝ :=
  covOperator (ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t)

/-- The covariance operator on flux fields. -/
def covAtFlux (D : OCData) (m : ℕ) (s₀ t : ℝ) : (Vec 2 → Vec 2) → Vec 2 → Vec 2 :=
  covOperator (ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t)

open scoped Classical in
/-- The finer output of a source with a path on the family `A` over the slot `k` (level
`m = G.level`), at time `t`, from the lift coefficients `Cc` of the path's scalar family. -/
def fluxOp (ρ s₀ : ℝ) (s : SuccSource G)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)) : FamFluxOp :=
  fun k t A =>
    if hA : IsAdmissibleChain D b j₀ G.level k A ∧ Odd k then
      match s, Cc with
      | .copyDir _ _ _ γ, _ =>
          directFlux G ⟨k, hA.2⟩ ⟨A, hA.1⟩ γ (Finset.Icc 3 (Dm)) t
      | .copyQuad _ _ π, Cc =>
          pathMeanFlux D G.level ρ
            (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩)) (Cc k A) 2 t
      | .letterDiag _ _, _ => fun _ _ => 0
      | .letterMean _ n h π, Cc => fun f y =>
          pathMeanFlux D G.level ρ
              (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩)) (Cc k A) n t f y
            - (if hh : h = 1 then
                directFlux G ⟨k, hA.2⟩ ⟨A, hA.1⟩ (π.step ⟨0, by omega⟩).2.2 {n} t f y
              else 0)
      | .letterCov _ n h a a' π, Cc =>
          pullFlux (A.famMap D t) (A.famMapInv D t) (fun g x =>
            ((a.factorial * a'.factorial : ℝ)⁻¹ * (-1) ^ a) •
              (covAtFlux D G.level s₀ t)^[a]
                (pushFlux (A.famMap D t) (A.famMapInv D t)
                  (pathMeanFlux D G.level ρ
                    (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩)) (Cc k A) n t)
                  ((covAt D G.level s₀ t)^[a'] g)) x)
    else fun _ _ => 0

end SuccSource
end

end AVRegularity
end

section
open Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity

/-! Definition: the physical operator of the first source `𝖣` of the
passage `m → m-1` (the defect letter of display (12.20) of the paper) and the physical
divergence of an identity.

The first source is the full diagonal flux defect of the coarse conjugation, including the
spatial mean/reference bridge; the exact temporal flux `𝒟` of the coarse conjugation gives the
split `-Q_p𝒟 + Q_p𝐄^flux P_p = 𝖮 + ∑ 𝖥_𝔩`. Here
`M P_p = P_p L_c + div 𝓕_p - (𝖩 - BI):D² 𝒞^p/p!`,
`𝓕_p f = ∑_{l=1}^p (1/l!) ∑_{a<l} 𝒞^a 𝒥_H 𝒞^{l-1-a} f - 𝓕_A P_p f`,
`𝒥_H f = -(D𝐛 H + H D𝐛ᵀ)∇f`, with `M = ∂_t + 𝐛·∇ - 𝖩:D² - div 𝓕_A` the diagonal mean, so that
`div(𝓕_A g) = -ℳ^{(0)} g - 𝖩:D² g` with the grade-zero glued mean `ℳ^{(0)}` (the convention of
`IsMeanPresentation`). The first-source letter is `-Q_p 𝒟`, acting as the identity map on each
component; its physical operator is `f ↦ -Q_p div(𝓕_p f)` (`Q_p` has constant coefficients). The
drift is `𝐛 = 𝐛_{m-1}`, the covariance primitive `𝖧 = 𝖧_m` has its original anchor `0`, the
reference flux is `𝖩_m` at `κ_m`.

The grade-zero lifts are those of the empty path on the native physical family of every pulse
(`familyLiftData` with no edge), glued with `gluedMean` (Eulerian, through the natural
chart of the pulse and its inverse). The independent-context
representative of `𝖣` is fixed by the construction: at the context `(𝒜, ζ)` of level
`m-1`, the grade-zero means `K^lab_{n,k}` of the appended children `𝒜^♮_k` (`diagLabelFlux`) are
pushed forward and assembled with `ϖ_{m,k}` (`diagMeanFluxCtx`), `𝓕_A = (K_2 - 𝖩_m∇) +
∑_{n=3}^{N+1} K_n` (`diagFluxCtx`), and `D_c` is the Piola pullback of
`-Q_p ∑ 𝒞^a𝒥_H𝒞^{l-1-a}/l! + Q_p𝓕_AP_p` (`firstSourceFlux`), whose coefficients are extracted at
the centered point (`fluxCoeff`). -/

/-- The gradient of a scalar field. -/
def gradField (f : Vec 2 → ℝ) (x : Vec 2) : Vec 2 :=
  fun k => fderiv ℝ f x (basisVec k)

/-- `𝒥_H g = -(D𝐛 H + H D𝐛ᵀ)∇g` at time `t`. -/
def commutatorFluxJH (bv : Vec 2 → Vec 2) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (g : Vec 2 → ℝ) :
    Vec 2 → Vec 2 :=
  fun x => -((jacMatrix bv x * Hc + Hc * Matrix.transpose (jacMatrix bv x)).mulVec (gradField g x))

/-- The level-`i` label shear `U_i(t, ζ) = p_{pc}(t) 𝐮_{i,pc}(ε_i ζ)` of the pulse `pc`. -/
def labelShear (D : OCData) (i : ℕ) (pc : ℤ) (t : ℝ) (ζ : Vec 2) : Vec 2 :=
  ocPulse D.α D.q D.Λ D.ζ i pc t • ocShearVel D.α D.q D.Λ i pc (D.eps i • ζ)

/-- The context representative `S_c` of `D𝐛_i` at the context `(ch, ζ)`:
`S_c = (∂_tF)F⁻¹ + ((∂_{U_i}F) + F ε_i⁻¹ D_ζU_i) F⁻¹`, with `F = F_t(0)` and the directional
derivative `∂_{U_i}F` taken through the recentered family. -/
def contextStrain (D : OCData) (i : ℕ) (pc : ℤ) (t : ℝ) (ch : RealChain) (ζ : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  ch.famStrain D t +
    (Matrix.of (fun a c => fderiv ℝ (fun h : Vec 2 => (ch.recenter D h).famJac D t a c) 0
        (labelShear D i pc t ζ)) +
      ch.famJac D t * ((D.eps i)⁻¹ • jacMatrix (labelShear D i pc t) ζ)) * (ch.famJac D t)⁻¹

/-- The grade-zero label mean flux `K^lab_{n,k}` on the family `B` over the
finer slot `k` of level `m`, from its grade-zero lift coefficients. -/
def diagLabelFlux (D : OCData) (Dm m : ℕ) (ρ : ℝ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (k : ℤ) (B : RealChain)
    (n : ℕ) (t : ℝ) : (Vec 2 → ℝ) → Vec 2 → Vec 2 :=
  pathMeanFlux (Dm := Dm) D m ρ (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k B ρ
    (fun _ _ _ => [])) (Cc0 k B) n t

open scoped Classical in
/-- The assembled diagonal mean flux `K_n = ∑_k ϖ_{m,k}(t) (Ψ_k)_* K^lab_{n,k}` at the context
`(ch, ζ)` of level `m-1`, with the appended children `𝒜^♮_k`; a child
outside the outer carrier contributes zero, so that the grade-zero lifts are used only where they
are constrained (`IsDiagLifts`). -/
def diagMeanFluxCtx (D : OCData) (b : ℝ) (j₀ : ℕ) (Dm m : ℕ) (ρ : ℝ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (t : ℝ) (ch : RealChain)
    (ζ : Vec 2) (n : ℕ) : (Vec 2 → ℝ) → Vec 2 → Vec 2 :=
  fun f x => ∑ᶠ (k : ℤ) (_ : Odd k ∧ IsScheduledIn D (m - 1) k ch.slot),
    if IsAdmissibleChain D b j₀ m k (ch.appendChild D k t ζ) then
      ocCutoff D.α D.q D.Λ m k t • pushFlux ((ch.appendChild D k t ζ).famMap D t)
        ((ch.appendChild D k t ζ).famMapInv D t)
        (diagLabelFlux D Dm m ρ Cc0 k (ch.appendChild D k t ζ) n t) f x
    else 0

/-- `𝓕_A = (K_2 - 𝖩_m∇) + ∑_{n=3}^{N+1} K_n` (the spatial mean/reference
bridge subtracts the flat reference `𝖩_m`; zero-past means, no switch tensor). -/
def diagFluxCtx (D : OCData) (b : ℝ) (j₀ : ℕ) (Dm m : ℕ) (ρ : ℝ) (N : ℕ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (t : ℝ) (ch : RealChain)
    (ζ : Vec 2) : (Vec 2 → ℝ) → Vec 2 → Vec 2 :=
  fun f x => (diagMeanFluxCtx D b j₀ Dm m ρ Cc0 t ch ζ 2 f x -
      (ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t).mulVec (gradField f x)) +
    ∑ n ∈ Finset.Icc 3 (N + 1), diagMeanFluxCtx D b j₀ Dm m ρ Cc0 t ch ζ n f x

/-- The first-source flux `D_c` in the labels of the context `(ch, ζ)` of level `m-1`:
the Piola pullback by `Φ = 𝒜_t` of
`-Q_p ∑_{l=1}^p (1/l!) ∑_{a<l} 𝒞_x^a 𝒥_H 𝒞_x^{l-1-a} + Q_p 𝓕_A P_p`, with Eulerian covariance
`𝒞_x = 𝖧_m:D_x²` at the anchor `s₀` of the primitive (`0` in the cascade; `t_p` at terminal
entry) and `𝒥_H = -(S_c H + H S_cᵀ)∇_x`, where `S_c` is the
context strain evaluated at the recentered context of each point. -/
def firstSourceFlux (D : OCData) (b : ℝ) (j₀ : ℕ) (Dm m : ℕ) (ρ : ℝ) (N p : ℕ) (s₀ : ℝ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (t : ℝ) (ch : RealChain)
    (ζ : Vec 2) : (Vec 2 → ℝ) → Vec 2 → Vec 2 :=
  let Hc := ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t
  let JH : (Vec 2 → ℝ) → Vec 2 → Vec 2 := fun g x =>
    -((contextStrain D (m - 1) ch.slot t (ch.recenter D (ch.famMapInv D t x))
          (ζ + (D.eps (m - 1))⁻¹ • ch.famMapInv D t x) * Hc +
        Hc * Matrix.transpose (contextStrain D (m - 1) ch.slot t
          (ch.recenter D (ch.famMapInv D t x)) (ζ + (D.eps (m - 1))⁻¹ • ch.famMapInv D t x))).mulVec
        (gradField g x))
  pullFlux (ch.famMap D t) (ch.famMapInv D t) (fun g x => covPolyQ Hc p (fun x' =>
    -(∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a ∈ Finset.range l,
        (covOperator Hc)^[a] (JH ((covOperator Hc)^[l - 1 - a] g)) x') +
      diagFluxCtx D b j₀ Dm m ρ N Cc0 t ch ζ (covPolyP Hc p g) x') x)

end AVRegularity
end
end
end
