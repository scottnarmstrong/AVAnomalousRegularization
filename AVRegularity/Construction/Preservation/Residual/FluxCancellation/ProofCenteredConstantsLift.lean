-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Coarse.Fact.GradWord
import AVRegularity.Proofs.GenSem.Finer.CovLetterArr
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import AVRegularity.Construction.Uniqueness.CellFieldUnique
public import AVRegularity.Definitions.Construction.Preparation

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! **Source mean, Right: the covariance operators on finite sums of regular functions.**

`𝒞^a` and `Q_p` are additive and homogeneous on `C^{2a}` (`C^{2p}`) functions: the glue between
the pointwise path-sum reading of `𝐄^flux P_p g` and the dressed path terms. -/

/-- `𝒞^a` of a finite combination of `C^{2a}` functions. -/
theorem right_covIter_sum {ι : Type*} (H : Matrix (Fin 2) (Fin 2) ℝ) (s : Finset ι)
    (c : ι → ℝ) (f : ι → Vec 2 → ℝ) :
    ∀ (a : ℕ), (∀ i ∈ s, ContDiff ℝ ((2 * a : ℕ) : WithTop ℕ∞) (f i)) →
      (covOperator H)^[a] (fun y => ∑ i ∈ s, c i * f i y) =
        fun y => ∑ i ∈ s, c i * (covOperator H)^[a] (f i) y
  | 0, _ => by simp
  | a + 1, hf => by
      have hf' : ∀ i ∈ s, ContDiff ℝ ((2 * a : ℕ) : WithTop ℕ∞) (f i) := fun i hi =>
        (hf i hi).of_le (by exact_mod_cast (by omega : 2 * a ≤ 2 * (a + 1)))
      have h2 : ∀ i ∈ s, ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) ((covOperator H)^[a] (f i)) :=
        fun i hi => Providers.GenSem.contDiff_covOperator_iterate H a
          (by rw [show 2 * a + 2 = 2 * (a + 1) by ring]; exact hf i hi)
      rw [Function.iterate_succ_apply', right_covIter_sum H s c f a hf']
      have h3 : ∀ i ∈ s, ContDiff ℝ 2 (fun y => c i * (covOperator H)^[a] (f i) y) :=
        fun i hi => contDiff_const.mul (by exact_mod_cast h2 i hi)
      rw [CycleComparison.Coarse.covOperator_sum H s (fun i y => c i * (covOperator H)^[a] (f i) y) h3]
      funext x
      refine Finset.sum_congr rfl fun i hi => ?_
      have := congrFun (CycleComparison.Coarse.covOperator_smul H (c i)
        (f := (covOperator H)^[a] (f i)) (by exact_mod_cast h2 i hi)) x
      simpa [smul_eq_mul, Function.iterate_succ_apply'] using this

/-- `Q_p` of a finite combination of `C^{2p}` functions. -/
theorem right_covPolyQ_sum {ι : Type*} (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (s : Finset ι)
    (c : ι → ℝ) (f : ι → Vec 2 → ℝ) (hf : ∀ i ∈ s, ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) (f i))
    (x : Vec 2) :
    covPolyQ H p (fun y => ∑ i ∈ s, c i * f i y) x = ∑ i ∈ s, c i * covPolyQ H p (f i) x := by
  unfold covPolyQ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have : ∀ l ∈ Finset.range (p + 1), (covOperator H)^[l] (fun y => ∑ i ∈ s, c i * f i y) x =
      ∑ i ∈ s, c i * (covOperator H)^[l] (f i) x := fun l hl => by
    rw [right_covIter_sum H s c f l (fun i hi => (hf i hi).of_le (by
      exact_mod_cast (by have := Finset.mem_range.mp hl; omega : 2 * l ≤ 2 * p)))]
  rw [Finset.sum_congr rfl fun l hl => by rw [this l hl]]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

/-- `Q_p` of a finite sum of `C^{2p}` functions. -/
theorem right_covPolyQ_sum1 {ι : Type*} (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (s : Finset ι)
    (f : ι → Vec 2 → ℝ) (hf : ∀ i ∈ s, ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) (f i))
    (x : Vec 2) :
    covPolyQ H p (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, covPolyQ H p (f i) x := by
  simpa using right_covPolyQ_sum H p s (fun _ => 1) f hf x

/-- `Q_p` of a finite `finsum` of `C^{2p}` functions. -/
theorem right_covPolyQ_finsum {ι : Type*} [Finite ι] (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ)
    (f : ι → Vec 2 → ℝ) (hf : ∀ i, ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) (f i)) (x : Vec 2) :
    covPolyQ H p (fun y => ∑ᶠ i, f i y) x = ∑ᶠ i, covPolyQ H p (f i) x := by
  have := Fintype.ofFinite ι
  simp only [finsum_eq_sum_of_fintype]
  exact right_covPolyQ_sum1 H p Finset.univ f (fun i _ => hf i) x

/-- `Q_p` as the sum of the `𝒞^a`. -/
theorem right_covPolyQ_apply (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (f : Vec 2 → ℝ) (x : Vec 2) :
    covPolyQ H p f x = ∑ a ∈ Finset.range (p + 1),
      (((-1 : ℝ) ^ a / (a.factorial : ℝ)) * (covOperator H)^[a] f x) := by
  simp [covPolyQ, Finset.sum_apply]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.OrderBound

/-! The statements of the cascade flux order bound.

`CascadeFluxOrderBoundWeak` is the cascade flux order bound (`cascadeFluxOrderBound`) with the
conclusion restricted to `2 < d`: for `d = 2` the quadratic conversion of a path has a non-zero
array in a component of grade `0`, whose bound `D₀` may be below `2` (`D_H ≥ 2` holds at the call
site, so `SplitInput.range` can live with the weak form).

The proof is the induction on the cascade, one step of which unpacks `IsActualSuccessor` through the
source bijection and splits on the recorded order `R` of the new identity (its `maxOrder`, by
`HasTags` of the successor and the provenance clause). An array of order `d > R` vanishes by
`flux_zero`. For `d ≤ R` and `d` above the bound `D_{g+1}` of the target: a quadratic conversion
(`R = 2`) and the first source (`R = N + 1 + 4p`) do not occur; a direct copy is
`DirectOrderStatement`; a mean letter (`R = n`) or a covariance letter (`R = n + 2(a + a')`) has
degree `n > N + max 2 D_g`, where the path mean vanishes: the two statements below.

No certificate of the incoming stage is used: operator statements on the orders of the quadratic
conversion, of the letters in the whole range of `n` and of the first source would need a
coefficient certificate of the old stage for the degrees `1 ≤ n ≤ N + max 2 E`, so they are not used.

The two statements are stated at the times of the pulse window of the finer slot only:
`IsLiftFamily` constrains the lift coefficients on the cell-time window, and `transferAt`
multiplies the slot `k` by its cutoff. Their setting is the stream data (`1 ≤ Λ`, the fast
profile, the band chain: positivity of the cell scale and `0 ∈ ladderOmega`) and the floors
`Dm ≤ sX, sZ` of the lift coefficients. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The coefficients of order `d > K` of a flux operator at the origin vanish. -/
def FluxOrderLE (K : ℕ) (L : (Vec 2 → ℝ) → Vec 2 → Vec 2) : Prop :=
  ∀ (d : ℕ) (I : DerivativeWord2 (d - 1)), K < d → fluxCoeff L d I 0 = 0

/-- The flux arrays of the identity `γ` vanish for the orders `d > max 2 E`. -/
def EdgeVanish (G : GenStage D hr Dm b j₀) (E : ℕ) {v u : CompIn G.comps} (γ : G.fam.Γ v u) :
    Prop :=
  ∀ (p : OddSlot) (c : StageCtx D b j₀ G.level p) (d : ℕ) (I : DerivativeWord2 (d - 1)),
    2 < d → E < d → G.fam.flux p c v u γ d I = fun _ _ _ => 0

/-! ### The three statements on the finer outputs -/

/-- A direct copy: `directFlux` over the orders `3..Dm` of an identity vanishing above `E`. -/
def DirectOrderStatement : Prop :=
  ∀ (G : GenStage D hr Dm b j₀) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (E : ℕ),
    EdgeVanish G E γ → ∀ (p : OddSlot) (c : StageCtx D b j₀ G.level p) (t : ℝ),
      FluxOrderLE (max 2 E) (directFlux G p c γ (Finset.Icc 3 Dm) t)

/-- The letter `𝖬_{n,h}` of degree `n > N + max 2 E` over a path whose edges vanish above
`max 2 E`: its finer output has no coefficient at the label `0`, at the times of the pulse window
(`C_n = 0` for `n > N` and the `ε^{j-1}` coefficient of `sourceFlux` vanishes for `j` above the
order of the edges; for a one-edge path the all-slow part of the order `n` is subtracted, and it
vanishes too). -/
def MeanHighDegreeStatement : Prop :=
  ∀ (G : GenStage D hr Dm b j₀) (Mn : SuccMenu) (t : List WordLetter) (n h : ℕ)
    (π : StagePath G h) (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (E : ℕ), 1 ≤ D.Λ → IsFastProfile D.ζ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    Dm ≤ Mn.sX → Dm ≤ Mn.sZ → (∀ j, EdgeVanish G E (π.step j).2.2) →
    (SuccSource.letterMean t n h π).IsLiftFamily Mn Cc → Mn.N + max 2 E < n →
    ∀ (k : ℤ) (τ : ℝ) (A : RealChain), τ ∈ ocPulseWindow D.α D.q D.Λ G.level k →
      FluxOrderLE 0 ((SuccSource.letterMean t n h π).fluxOp
        (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k τ A)

/-- The letter `𝖵_{n,h,a,a'}` of degree `n > N + max 2 E`, likewise: the path mean vanishes near
the label `0` on smooth fields, and the push, the covariance iterates and the pull keep germs. -/
def CovHighDegreeStatement : Prop :=
  ∀ (G : GenStage D hr Dm b j₀) (Mn : SuccMenu) (t : List WordLetter) (n h a a' : ℕ)
    (π : StagePath G h) (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (E : ℕ), 1 ≤ D.Λ → IsFastProfile D.ζ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    Dm ≤ Mn.sX → Dm ≤ Mn.sZ → (∀ j, EdgeVanish G E (π.step j).2.2) →
    (SuccSource.letterCov t n h a a' π).IsLiftFamily Mn Cc → Mn.N + max 2 E < n →
    ∀ (k : ℤ) (τ : ℝ) (A : RealChain), τ ∈ ocPulseWindow D.α D.q D.Λ G.level k →
      FluxOrderLE 0 ((SuccSource.letterCov t n h a a' π).fluxOp
        (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k τ A)

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.OrderBound
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! The finer outputs annihilate constants, abstract part: **the order-`0` entries of the
lifts vanish**.

For a lift sequence `Cc` of operator data `Q` on an open set `Ω` of slow offsets (with window data
at each `X ∈ Ω`), the order-`0` entry `Cc hh n 0 α t X z v u` of the coefficient array vanishes on
the window and on `Ω` for every `(hh, n) ≠ (0, 0)`. The proof is the induction of
`lift_sequence_unique_window_on`: the cell source of a constant field is built from the lower
lifts through `ℬ_1`, `ℬ_2` (which differentiate), the source operator (whose edges have orders
`d ≥ 2`, so the words `dEpsWord` are not empty) and the means of these, so it vanishes when the
lower order-`0` entries do (the lift of grade `0` and degree `0` is the identity, a constant field
for a constant field); the cell inverse of the zero source is then the one of the zero field
(`cellField_unique_window`, against the lift relation at the zero field). -/

open Uniqueness

section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set (Vec 2)}

/-- The field `Ψ` is the constant `c` for the slow offsets of `Ω`. -/
def PccConstOn (Ω : Set (Vec 2)) (Ψ : Vec 2 → Vec 2 → E) (c : E) : Prop :=
  ∀ X ∈ Ω, ∀ z, Ψ X z = c

theorem pcc_slowPartial_zero (hΩ : IsOpen Ω) {Ψ : Vec 2 → Vec 2 → E} {c : E}
    (h : PccConstOn Ω Ψ c) (i : Fin 2) : PccConstOn Ω (slowPartial i Ψ) 0 := by
  intro X hX z
  have : (fun X' => Ψ X' z) =ᶠ[𝓝 X] fun _ => c := by
    filter_upwards [hΩ.mem_nhds hX] with X' hX' using h X' hX' z
  rw [slowPartial, this.fderiv_eq]
  simp

theorem pcc_fastPartial_zero {Ψ : Vec 2 → Vec 2 → E} {c : E}
    (h : PccConstOn Ω Ψ c) (i : Fin 2) : PccConstOn Ω (fastPartial i Ψ) 0 := by
  intro X hX z
  have : (fun z' => Ψ X z') = fun _ => c := funext (h X hX)
  rw [fastPartial, this]
  simp

theorem pcc_dEps_zero (hΩ : IsOpen Ω) {Ψ : Vec 2 → Vec 2 → E} {c : E}
    (h : PccConstOn Ω Ψ c) (η ε : ℝ) (i : Fin 2) : PccConstOn Ω (dEps η ε i Ψ) 0 := by
  intro X hX z
  simp [dEps, pcc_fastPartial_zero h i X hX z, pcc_slowPartial_zero hΩ h i X hX z]

theorem pcc_dEps_foldl_zero (hΩ : IsOpen Ω) (η ε : ℝ) :
    ∀ (l : List (Fin 2)) (Ψ : Vec 2 → Vec 2 → E), PccConstOn Ω Ψ 0 →
      PccConstOn Ω (l.foldl (fun Ψ' i => dEps η ε i Ψ') Ψ) 0
  | [], _, h => h
  | i :: l, _, h => pcc_dEps_foldl_zero hΩ η ε l _ (pcc_dEps_zero hΩ h η ε i)

/-- A word of length at least `1` in the operators `dEps` kills a constant field. -/
theorem pcc_dEpsWord_zero (hΩ : IsOpen Ω) {Ψ : Vec 2 → Vec 2 → E} {c : E}
    (h : PccConstOn Ω Ψ c) (η ε : ℝ) {m : ℕ} (hm : 1 ≤ m) (α : DerivativeWord2 m) :
    PccConstOn Ω (dEpsWord η ε α Ψ) 0 := by
  cases m with
  | zero => exact absurd hm (by norm_num)
  | succ m =>
    unfold dEpsWord
    rw [List.ofFn_succ, List.foldl_cons]
    exact pcc_dEps_foldl_zero hΩ η ε _ _ (pcc_dEps_zero hΩ h η ε _)

theorem pcc_orderedDerivative_foldl (hΩ : IsOpen Ω) :
    ∀ (l : List (Fin 2)) (g : Vec 2 → E), (∀ X ∈ Ω, g X = 0) →
      ∀ X ∈ Ω, (l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) g) X = 0
  | [], g, hg => hg
  | i :: l, g, hg => by
    refine pcc_orderedDerivative_foldl hΩ l _ (fun X hX => ?_)
    have : g =ᶠ[𝓝 X] fun _ => 0 := by
      filter_upwards [hΩ.mem_nhds hX] with X' hX' using hg X' hX'
    show fderiv ℝ g X (basisVec i) = 0
    rw [this.fderiv_eq]
    simp

/-- Derivatives of a field vanishing on an open set vanish there. -/
theorem pcc_orderedDerivative_zero (hΩ : IsOpen Ω) {g : Vec 2 → E} (hg : ∀ X ∈ Ω, g X = 0)
    {m : ℕ} (α : DerivativeWord2 m) : ∀ X ∈ Ω, orderedDerivative α g X = 0 :=
  pcc_orderedDerivative_foldl hΩ _ g hg

/-- Derivatives of positive order of a constant field vanish. -/
theorem pcc_orderedDerivative_const (c : E) {m : ℕ} (hm : 1 ≤ m) (α : DerivativeWord2 m)
    (X : Vec 2) : orderedDerivative α (fun _ => c) X = 0 := by
  cases m with
  | zero => exact absurd hm (by norm_num)
  | succ m =>
    unfold orderedDerivative
    rw [List.ofFn_succ, List.foldl_cons]
    refine pcc_orderedDerivative_foldl (Ω := Set.univ) isOpen_univ _ _ (fun Y _ => ?_) X
      (Set.mem_univ X)
    simp

end Calculus

section Operators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set (Vec 2)}

theorem pcc_smul_zero {F : Vec 2 → Vec 2 → E} (h : PccConstOn Ω F 0) (g : Vec 2 → ℝ) :
    PccConstOn Ω (fun X z => g X • F X z) 0 := fun X hX z => by simp [h X hX z]

theorem pcc_cellB1_zero (hΩ : IsOpen Ω) {Φ : Vec 2 → Vec 2 → E} {c : E} (h : PccConstOn Ω Φ c)
    (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ) :
    PccConstOn Ω (cellB1 η G v t Φ) 0 := by
  intro X hX z
  have h1 : ∀ k, slowPartial k Φ X z = 0 := fun k => pcc_slowPartial_zero hΩ h k X hX z
  have h2 : ∀ i j, fastPartial i (slowPartial j Φ) X z = 0 := fun i j =>
    pcc_fastPartial_zero (pcc_slowPartial_zero hΩ h j) i X hX z
  have h3 : ∀ i j, slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z') X z = 0 :=
    fun i j => pcc_slowPartial_zero hΩ
      (pcc_smul_zero (pcc_fastPartial_zero h j) (fun X' => G t X' i j)) i X hX z
  simp [cellB1, h1, h2, h3]

theorem pcc_cellB2_zero (hΩ : IsOpen Ω) {Φ : Vec 2 → Vec 2 → E} {c : E} (h : PccConstOn Ω Φ c)
    (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ) :
    PccConstOn Ω (cellB2 η G t Φ) 0 := by
  intro X hX z
  have h3 : ∀ i j, slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z') X z = 0 :=
    fun i j => pcc_slowPartial_zero hΩ
      (pcc_smul_zero (pcc_slowPartial_zero hΩ h j) (fun X' => G t X' i j)) i X hX z
  simp [cellB2, h3]

end Operators

section Source
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ} {Ω : Set (Vec 2)}

theorem pcc_sourceFlux_zero (hΩ : IsOpen Ω) (edge : ConstituentEdges Dm h) (η ε t : ℝ)
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {c : ∀ i, h i} (hc : PccConstOn Ω Φ c) (k : Fin 2) :
    PccConstOn Ω (sourceFlux edge η ε t Φ k) 0 := by
  intro X hX z
  funext v
  unfold sourceFlux
  refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun d _ => ?_
  have hd : 1 ≤ d.1 - 1 := by have := (Finset.mem_Icc.mp d.2).1; omega
  have hw : ∀ α : DerivativeWord2 (d.1 - 1), dEpsWord η ε α Φ X z = 0 := fun α =>
    pcc_dEpsWord_zero hΩ hc η ε hd α X hX z
  simp [hw]

theorem pcc_sourceOp_zero (hΩ : IsOpen Ω) (edge : ConstituentEdges Dm h) (η ε t : ℝ)
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {c : ∀ i, h i} (hc : PccConstOn Ω Φ c) :
    PccConstOn Ω (sourceOp edge η ε t Φ) 0 := by
  intro X hX z
  unfold sourceOp
  exact Finset.sum_eq_zero fun k _ =>
    pcc_dEps_zero hΩ (pcc_sourceFlux_zero hΩ edge η ε t hc k) η ε k X hX z

theorem pcc_sourceCoeff_zero (hΩ : IsOpen Ω) (edge : ConstituentEdges Dm h) (η t : ℝ) (j : ℕ)
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {c : ∀ i, h i} (hc : PccConstOn Ω Φ c) :
    PccConstOn Ω (sourceCoeff edge η j t Φ) 0 := by
  intro X hX z
  unfold sourceCoeff
  have : (fun ε : ℝ => sourceOp edge η ε t Φ X z) = fun _ => 0 :=
    funext fun ε => pcc_sourceOp_zero hΩ edge η ε t hc X hX z
  rw [this]
  cases j <;> simp

theorem pcc_sourceFlux_iteratedDeriv_zero (hΩ : IsOpen Ω) (edge : ConstituentEdges Dm h)
    (η t : ℝ) (j : ℕ) (k : Fin 2) {Φ : Vec 2 → Vec 2 → ∀ i, h i} {c : ∀ i, h i}
    (hc : PccConstOn Ω Φ c) {X : Vec 2} (hX : X ∈ Ω) (z : Vec 2) :
    iteratedDeriv j (fun ε : ℝ => sourceFlux edge η ε t Φ k X z) 0 = 0 := by
  have : (fun ε : ℝ => sourceFlux edge η ε t Φ k X z) = fun _ => 0 :=
    funext fun ε => pcc_sourceFlux_zero hΩ edge η ε t hc k X hX z
  rw [this]
  cases j <;> simp

end Source

section Lifts
variable {ι : Type} [Fintype ι] {Dm : ℕ} {Ω : Set (Vec 2)}

/-- The order-`0` entries of the coefficient array `Cc hh n` vanish on the window and on `Ω`. -/
def PccZero (Ω : Set (Vec 2)) (t₀ t₁ : ℝ) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (hh n : ℕ) : Prop :=
  ∀ t ∈ Set.Icc t₀ t₁, ∀ X ∈ Ω, ∀ z v u (α : DerivativeWord2 0), Cc hh n 0 α t X z v u = 0

/-- The lift of a constant field is read at the order `0`. -/
theorem pcc_liftApply_const (k : ℕ) (c : LiftCoeff ι (fun _ => ℝ)) (c0 : ι → ℝ) (t : ℝ)
    (X z : Vec 2) (v : ι) (α0 : DerivativeWord2 0) :
    liftApply k c (fun _ _ => c0) t X z v = ∑ u, c 0 α0 t X z v u (c0 u) := by
  unfold liftApply
  rw [Finset.sum_range_succ']
  have hpos : ∀ m ∈ Finset.range k, ∑ α : DerivativeWord2 (m + 1), ∑ u : ι,
      c (m + 1) α t X z v u (orderedDerivative α (fun _ => c0) X u) = 0 := by
    intro m _
    refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun u _ => ?_
    rw [pcc_orderedDerivative_const c0 (by omega) α X]
    simp
  rw [Finset.sum_eq_zero hpos, zero_add]
  have hα : ∀ α : DerivativeWord2 0, α = α0 := fun α => Subsingleton.elim _ _
  simp only [hα, Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem pcc_liftApply_zeroField (k : ℕ) (c : LiftCoeff ι (fun _ => ℝ)) (t : ℝ) (X z : Vec 2)
    (v : ι) : liftApply k c (fun _ _ => (0 : ι → ℝ)) t X z v = 0 := by
  rw [pcc_liftApply_const k c 0 t X z v (fun i => i.elim0)]
  simp

theorem pcc_liftApply_constOn {t₀ t₁ : ℝ} {Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)}
    {hh k : ℕ} (hZ : PccZero Ω t₀ t₁ Cc hh k) (c0 : ι → ℝ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    PccConstOn Ω (liftApply k (Cc hh k) (fun _ _ => c0) t) 0 := by
  intro X hX z
  funext v
  rw [pcc_liftApply_const k (Cc hh k) c0 t X z v (fun i => i.elim0)]
  simp [hZ t ht X hX z v _ (fun i => i.elim0)]

/-- The lower lifts of a constant field are constants on `Ω` at the time `t` (the identity at
`(0, 0)`, the zero field elsewhere). -/
def PccGood (Ω : Set (Vec 2))
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (c0 : ι → ℝ) (t : ℝ) (hh n : ℕ) : Prop :=
  ∀ hh' n', (hh' < hh ∨ (hh' = hh ∧ n' < n)) →
    ∃ c : ι → ℝ, PccConstOn Ω (liftApply n' (Cc hh' n') (fun _ _ => c0) t) c

theorem PccGood.mono {Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)} {c0 : ι → ℝ} {t : ℝ} {hh n hh₂ n₂ : ℕ}
    (hg : PccGood Ω Cc c0 t hh n) (h : hh₂ < hh ∨ (hh₂ = hh ∧ n₂ < n)) :
    PccGood Ω Cc c0 t hh₂ n₂ := by
  intro hh' n' hlt
  refine hg hh' n' ?_
  rcases h with h | ⟨rfl, h⟩ <;> rcases hlt with hlt | ⟨rfl, hlt⟩
  · exact Or.inl (by omega)
  · exact Or.inl h
  · exact Or.inl hlt
  · exact Or.inr ⟨rfl, by omega⟩

theorem pcc_liftA_zero (hΩ : IsOpen Ω) (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (c0 : ι → ℝ) {t : ℝ} {hh n : ℕ} (hn : 1 ≤ n)
    (hg : PccGood Ω Cc c0 t hh n) :
    PccConstOn Ω (liftA Q Cc (fun _ _ => c0) hh n t) 0 := by
  intro X hX z
  obtain ⟨c1, h1⟩ := hg hh (n - 1) (Or.inr ⟨rfl, by omega⟩)
  have e1 := pcc_cellB1_zero hΩ h1 Q.η Q.G Q.v t X hX z
  have e2 : (if 2 ≤ n then cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2))
      (fun _ _ => c0) t) X z else 0) = 0 := by
    split_ifs with h2
    · obtain ⟨c2, h2'⟩ := hg hh (n - 2) (Or.inr ⟨rfl, by omega⟩)
      exact pcc_cellB2_zero hΩ h2' Q.η Q.G t X hX z
    · rfl
  have e3 : (if hh = 0 then (0 : ι → ℝ) else ∑ j ∈ Finset.range (min Dm n + 1),
      sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ _ => c0) t)
        X z) = 0 := by
    split_ifs with h0
    · rfl
    · refine Finset.sum_eq_zero fun j _ => ?_
      obtain ⟨c3, h3⟩ := hg (hh - 1) (n - j) (Or.inl (by omega))
      exact pcc_sourceCoeff_zero hΩ Q.edge Q.η t j h3 X hX z
  unfold liftA
  rw [e1, e2, e3]
  simp

theorem pcc_liftMean_zero (hΩ : IsOpen Ω) (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (c0 : ι → ℝ) {t : ℝ} {hh n : ℕ} (hn : 1 ≤ n)
    (hg : PccGood Ω Cc c0 t hh n) {X : Vec 2} (hX : X ∈ Ω) :
    liftMean Q Cc (fun _ _ => c0) hh n t X = 0 := by
  unfold liftMean
  have : (fun z => liftA Q Cc (fun _ _ => c0) hh n t X z) = fun _ => 0 :=
    funext fun z => pcc_liftA_zero hΩ Q Cc c0 hn hg X hX z
  rw [this]
  simp [fieldCellMean]

theorem pcc_liftCellSource_zero (hΩ : IsOpen Ω) (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (c0 : ι → ℝ) {t : ℝ} {hh n : ℕ} (hn : 1 ≤ n)
    (hg : PccGood Ω Cc c0 t hh n) {X : Vec 2} (hX : X ∈ Ω) (z : Vec 2) :
    liftCellSource Q Cc (fun _ _ => c0) hh n t X z = 0 := by
  unfold liftCellSource
  have hA := pcc_liftA_zero hΩ Q Cc c0 hn hg X hX z
  have hM := pcc_liftMean_zero hΩ Q Cc c0 hn hg hX
  have hsum : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean Q Cc (fun _ _ => c0) p.2 (n - j)) t X z = 0 := by
    intro j hj p hp
    have hj' := Finset.mem_Icc.mp hj
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hlt : p.2 < hh ∨ (p.2 = hh ∧ n - j < n) := by
      by_cases h2 : p.2 < hh
      · exact Or.inl h2
      · exact Or.inr ⟨by omega, by omega⟩
    have hz : ∀ X' ∈ Ω, liftMean Q Cc (fun _ _ => c0) p.2 (n - j) t X' = 0 := fun X' hX' =>
      pcc_liftMean_zero hΩ Q Cc c0 (by omega) (hg.mono hlt) hX'
    funext v
    unfold liftApply
    refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun u _ => ?_
    have := congrFun (pcc_orderedDerivative_zero hΩ hz α X hX) u
    simp [this]
  rw [Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero (hsum j hj)]
  simp [hA, hM]

theorem pcc_good_of_zero [∀ i, FiniteDimensional ℝ ((fun _ : ι => ℝ) i)]
    {Q : LiftOperatorData ι (fun _ => ℝ) Dm} {t₀ t₁ : ℝ} {sX sZ N H : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)} (hC : IsLiftSequenceOn Ω Q sX sZ t₀ t₁ N H Cc)
    (c0 : ι → ℝ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) {hh n : ℕ}
    (hZ : ∀ hh' n', (hh' < hh ∨ (hh' = hh ∧ n' < n)) → (hh' ≠ 0 ∨ n' ≠ 0) →
      PccZero Ω t₀ t₁ Cc hh' n') :
    PccGood Ω Cc c0 t hh n := by
  intro hh' n' hlt
  by_cases h00 : hh' = 0 ∧ n' = 0
  · obtain ⟨rfl, rfl⟩ := h00
    refine ⟨c0, fun X _ z => ?_⟩
    exact hC.1 (fun _ => c0) contDiff_const t ht X z
  · refine ⟨0, ?_⟩
    have h' : hh' ≠ 0 ∨ n' ≠ 0 := by
      by_contra hcon
      rcases not_or.mp hcon with ⟨a, b⟩
      exact h00 ⟨not_not.mp a, not_not.mp b⟩
    exact pcc_liftApply_constOn (hZ hh' n' hlt h') c0 ht

/-- **The order-`0` entries of the lifts vanish.** For a lift sequence on an open set `Ω` with
window data at each point of `Ω`, the order-`0` entry of `Cc hh n` vanishes on the window and on
`Ω` for every `(hh, n) ≠ (0, 0)` (`hh ≤ H`). -/
theorem pcc_order_zero_vanish [DecidableEq ι] [∀ i, FiniteDimensional ℝ ((fun _ : ι => ℝ) i)]
    (Q : LiftOperatorData ι (fun _ => ℝ) Dm) (t₀ t₁ : ℝ) (hab : t₀ ≤ t₁) (hΩ : IsOpen Ω)
    (hW : ∀ X ∈ Ω, ∃ lo A Mv : ℝ,
      WindowData (fun t => Matrix.of (Q.G t X)) Q.v t₀ t₁ lo A Mv)
    (sX sZ N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (hC : IsLiftSequenceOn Ω Q sX sZ t₀ t₁ N H Cc) :
    ∀ hh ≤ H, ∀ n, (hh ≠ 0 ∨ n ≠ 0) → PccZero Ω t₀ t₁ Cc hh n := by
  intro hh
  induction hh using Nat.strong_induction_on with
  | _ hh ihh =>
  intro hhH n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro hne
  have IH : ∀ hh' n', (hh' < hh ∨ (hh' = hh ∧ n' < n)) → (hh' ≠ 0 ∨ n' ≠ 0) →
      PccZero Ω t₀ t₁ Cc hh' n' := by
    intro hh' n' hlt h'
    rcases hlt with hlt | ⟨rfl, hn⟩
    · exact ihh hh' hlt (by omega) n' h'
    · exact ihn n' hn h'
  intro t ht X hX z v u α
  by_cases hn0 : n = 0
  · subst hn0
    have hh0 : 1 ≤ hh := by
      rcases hne with h | h
      · omega
      · exact absurd rfl h
    exact hC.2.1 hh hh0 hhH 0 α t X z v u
  · by_cases hnN : N < n
    · exact hC.2.2.1 hh hhH n hnN 0 α t X z v u
    · have hnN' := not_lt.mp hnN
      have hn1 : 1 ≤ n := by omega
      obtain ⟨lo, A, Mv, hWX⟩ := hW X hX
      have hgood : ∀ c0 : ι → ℝ, PccGood Ω Cc c0 t hh n := fun c0 =>
        pcc_good_of_zero hC c0 ht IH
      -- the cell inverse of the constant field `single u 1` and of the zero field
      have hc1 := hC.2.2.2.2.2.2 hh hhH n hn1 hnN' (fun _ => (Pi.single u 1 : ι → ℝ))
        contDiff_const X hX
      have hc0 := hC.2.2.2.2.2.2 hh hhH n hn1 hnN' (fun _ => (0 : ι → ℝ)) contDiff_const X hX
      have hsrc : ∀ t ∈ Set.Icc t₀ t₁, ∀ z, liftCellSource Q Cc (fun _ _ => (Pi.single u 1 : ι → ℝ))
          hh n t X z = liftCellSource Q Cc (fun _ _ => (0 : ι → ℝ)) hh n t X z := by
        intro t' ht' z'
        have g1 : PccGood Ω Cc (Pi.single u 1) t' hh n := pcc_good_of_zero hC _ ht' IH
        have g0 : PccGood Ω Cc 0 t' hh n := pcc_good_of_zero hC _ ht' IH
        rw [pcc_liftCellSource_zero hΩ Q Cc _ hn1 g1 hX z',
          pcc_liftCellSource_zero hΩ Q Cc _ hn1 g0 hX z']
      have hu := cellField_unique_window hab hWX
        (g := fun t z => liftCellSource Q Cc (fun _ _ => (Pi.single u 1 : ι → ℝ)) hh n t X z)
        (g' := fun t z => liftCellSource Q Cc (fun _ _ => (0 : ι → ℝ)) hh n t X z)
        (fun t ht z => hsrc t ht z) hc1 hc0 t ht z
      have h0 := pcc_liftApply_zeroField n (Cc hh n) t X z v
      have h1 : liftApply n (Cc hh n) (fun _ _ => (Pi.single u 1 : ι → ℝ)) t X z v = 0 := by
        have := congrFun hu v
        rw [h0] at this
        exact this
      rw [pcc_liftApply_const n (Cc hh n) _ t X z v α] at h1
      rw [Finset.sum_eq_single u (fun u' _ hu' => by simp [Pi.single_eq_of_ne hu']) (by simp)]
        at h1
      simp only [Pi.single_eq_same] at h1
      exact ContinuousLinearMap.ext_ring h1

end Lifts

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
