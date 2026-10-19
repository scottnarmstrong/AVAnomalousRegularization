-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.BlochContinuity
import AVRegularity.CycleWords.MixedWords.FibreDuality
public import AVRegularity.CycleWords.MixedWords.RetainedAssign
public import AVRegularity.CycleWords.Seam.CutoffComplementJetScale
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleWords.Seam

/-! **The transposed letter** `L*` on plane fields (adjoint of a word letter in the duality of the
word chains): for an adjoint family `Ψ_v`, the test for the source component `u` is

`(L*Ψ)_u = ∑_v (π_u/π_v) ∑_{o, γ ∈ L.edge v u o, α, k} (-1)^{o-1} D_α^{rev}(c_{γ,α,k} • γ.map† ∂_k Ψ_v)`,

with `c_{γ,α,k}(z) = taylorSlow lo K (fun X => γ.coeff α s X z k) X₀ (δ • z)`, the coefficient of the
letter flux `letterAdmissibleFlux`. It is defined here on raw jets (no hypotheses); the carrier
version and the duality identity with the letter flux follow. Orders above the letter's order `d`
contribute nothing (their edge lists are empty for a cycle letter); the adjoint family is taken at
order `n + d` and the transposed test has order `n`. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, CompleteSpace (h i)] {D : ℕ}

/-- The scalar coefficient of one constituent at time `s`. -/
def letterCoeff (L : CycleLetter ι h D) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ) (v u : ι)
    (o : Finset.Icc 2 D) (q : Fin (L.edge v u o).length) (α : DerivativeWord2 (o.1 - 1))
    (k : Fin 2) (z : Vec 2) : ℝ :=
  taylorSlow lo L.slow (fun X => ((L.edge v u o).get q).coeff α s X z k) X₀ (δ • z)

/-- The operator coefficient `c • γ.map†` of one transposed constituent. -/
def letterCoeffOp (L : CycleLetter ι h D) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ) (v u : ι)
    (o : Finset.Icc 2 D) (q : Fin (L.edge v u o).length) (α : DerivativeWord2 (o.1 - 1))
    (k : Fin 2) (z : Vec 2) : h v →L[ℝ] h u :=
  letterCoeff L lo X₀ δ s v u o q α k z •
    ContinuousLinearMap.adjoint ((L.edge v u o).get q).map

/-- Restriction of a raw jet to the orders `≤ K`. -/
def truncateRawJet {E : Type*} {K L : ℕ} (hKL : K ≤ L) (Dj : RawJet2 L E) : RawJet2 K E :=
  fun a => Dj ⟨⟨a.1.val, by omega⟩, a.2⟩

/-- One transposed term: `D_α^{rev}(c • γ.map† ∂_k Ψ)`, at order `n`. -/
def letterTransposeTermJet (L : CycleLetter ι h D) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ) (v u : ι)
    (o : Finset.Icc 2 D) (q : Fin (L.edge v u o).length) (α : DerivativeWord2 (o.1 - 1))
    (k : Fin 2) (n d : ℕ) (hod : o.1 ≤ d) (Ψ : RawJet2 (n + d) (h v)) : RawJet2 n (h u) :=
  wordPartialRawJet α (multiplicationRawJet (letterCoeffOp L lo X₀ δ s v u o q α k)
    (partialRawJet k (truncateRawJet (K := n + (o.1 - 1) + 1)
      (by have := (Finset.mem_Icc.mp o.2).1; omega) Ψ)))

/-- **The transposed letter** on raw jets: the test for the source component `u`. The target
slots `a v`, source slots `b u` and the slot map `κ` select the admissible orders, as in
`letterAdmissibleFlux`. -/
def letterTransposeJet {σ : Type*} (π : ι → ℝ) (L : CycleLetter ι h D) (κ : σ → ℕ)
    (a b : ι → σ) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ) (n d : ℕ) (Ψ : ∀ v, RawJet2 (n + d) (h v))
    (u : ι) : RawJet2 n (h u) :=
  fun idx z => ∑ v, ∑ o : admissibleOrders κ D (a v) (b u),
    if hod : o.1 ≤ d then
      ((-1 : ℝ) ^ (o.1 - 1) * (π u / π v)) •
        ∑ q : Fin (L.edge v u (admissibleLetterOrder κ D (a v) (b u) o)).length,
          ∑ α : DerivativeWord2 (o.1 - 1), ∑ k : Fin 2,
            letterTransposeTermJet L lo X₀ δ s v u (admissibleLetterOrder κ D (a v) (b u) o) q α k
              n d hod (Ψ v) idx z
    else 0

section Congr

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, CompleteSpace (h i)] [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem wordPartialRawJet_congr_ae :
    ∀ {m c : ℕ} (β : DerivativeWord2 c) (Dj Dj' : RawJet2 (m + c) E),
      (∀ q, Dj q =ᵐ[volume] Dj' q) → ∀ q, wordPartialRawJet β Dj q =ᵐ[volume]
        wordPartialRawJet β Dj' q
  | _, 0, _, _, _, hD, q => hD q
  | _, c + 1, β, _, _, hD, q => wordPartialRawJet_congr_ae (c := c) (Fin.init β) _ _
      (fun _ => hD _) q

omit [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, CompleteSpace (h i)] [Fintype ι] in
theorem multiplicationRawJet_congr_ae {K : ℕ} (C : Vec 2 → E →L[ℝ] F) (Dj Dj' : RawJet2 K E)
    (hD : ∀ q, Dj q =ᵐ[volume] Dj' q) (a : JetIndex2 K) :
    multiplicationRawJet C Dj a =ᵐ[volume] multiplicationRawJet C Dj' a := by
  have hall : ∀ᵐ x ∂volume, ∀ q, Dj q x = Dj' q x := ae_all_iff.mpr hD
  filter_upwards [hall] with x hx
  simp only [multiplicationRawJet, multiplicationTerm, hx]

end Congr

variable [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)]

omit [Fintype ι] in
/-- **One transposed term.** One constituent of the letter flux paired with `∂_k Ψ_v` is the value
of the source carrier paired with the transposed term, with the sign `(-1)^{o-1}`. -/
theorem letterTransposeTerm_duality (L : CycleLetter ι h D) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ)
    (v u : ι) (o : Finset.Icc 2 D) (q : Fin (L.edge v u o).length)
    (α : DerivativeWord2 (o.1 - 1)) (k : Fin 2) (n d : ℕ) (hod : o.1 ≤ d)
    {Kw : ℕ} (hKw : o.1 - 1 ≤ Kw) (W : PlaneHk Set.univ Kw (h u))
    (Ψ : PlaneHk Set.univ (n + d) (h v))
    (hC : ContDiff ℝ ((n + (o.1 - 1) : ℕ) : ℕ∞) (letterCoeffOp L lo X₀ δ s v u o q α k))
    (ρ : Vec 2 → ℝ)
    (hρ : ∀ idx, MemLp (fun x => ρ x * ‖(planeHkPartial k (truncatePlaneHk
      (K := n + (o.1 - 1) + 1) (by have := (Finset.mem_Icc.mp o.2).1; omega) Ψ)).toFunction.jet
        idx x‖) 2 volume)
    {A : Fin (n + (o.1 - 1) + 1) → ℝ}
    (hA : ∀ l x, ‖coefficientDerivativeArray (letterCoeffOp L lo X₀ δ s v u o q α k) l.val x‖ ≤
      A l * ρ x) :
    ∫ z, letterCoeff L lo X₀ δ s v u o q α k z *
        inner ℝ (((L.edge v u o).get q).map (W.toFunction.jet ⟨⟨o.1 - 1, by omega⟩, α⟩ z))
          (Ψ.toFunction.jet ⟨⟨1, by have := (Finset.mem_Icc.mp o.2).1; omega⟩,
            fun _ => k⟩ z) =
      (-1) ^ (o.1 - 1) * ∫ z, inner ℝ (W.toFunction.jet (valueIndex2 Kw) z)
        (letterTransposeTermJet L lo X₀ δ s v u o q α k n d hod Ψ.toFunction.jet
          (valueIndex2 n) z) := by
  set C := letterCoeffOp L lo X₀ δ s v u o q α k
  set Ψk := planeHkPartial k (truncatePlaneHk (K := n + (o.1 - 1) + 1)
    (by have := (Finset.mem_Icc.mp o.2).1; omega) Ψ)
  set T := PlaneHk.mulCoefficientWeighted Ψk C hC ρ hρ hA
  have hibp := planeHk_ibp W (o.1 - 1) hKw α (n := n) T
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at hibp
  have hTval : (planeJetL2 T (valueIndex2 (n + (o.1 - 1))) : Vec 2 → h u) =ᵐ[volume]
      fun z => C z (Ψ.toFunction.jet ⟨⟨1, by have := (Finset.mem_Icc.mp o.2).1; omega⟩,
        fun _ => k⟩ z) := by
    refine (planeJetL2_ae T _).trans ?_
    refine (PlaneHk.mulCoefficientWeighted_jet_ae Ψk C hC ρ hρ hA _).trans ?_
    have hv := planeHkPartial_jet_ae k (truncatePlaneHk (K := n + (o.1 - 1) + 1)
      (by have := (Finset.mem_Icc.mp o.2).1; omega) Ψ) (valueIndex2 (n + (o.1 - 1)))
    filter_upwards [hv] with z hz
    rw [multiplicationRawJet_value, hz]
    have hidx : (Fin.cons k Fin.elim0 : DerivativeWord2 1) = fun _ => k := by
      funext r
      obtain rfl : r = 0 := Fin.fin_one_eq_zero r
      rfl
    change C z (Ψ.toFunction.jet ⟨⟨1, _⟩, Fin.cons k Fin.elim0⟩ z) = _
    rw [hidx]
  have hWP : (planeJetL2 (planeHkWordPartial α T) (valueIndex2 n) : Vec 2 → h u) =ᵐ[volume]
      letterTransposeTermJet L lo X₀ δ s v u o q α k n d hod Ψ.toFunction.jet
        (valueIndex2 n) := by
    refine (planeJetL2_ae _ _).trans ((planeHkWordPartial_jet_ae α T _).trans ?_)
    apply wordPartialRawJet_congr_ae
    intro r
    refine (PlaneHk.mulCoefficientWeighted_jet_ae Ψk C hC ρ hρ hA r).trans ?_
    apply multiplicationRawJet_congr_ae
    intro r'
    exact planeHkPartial_jet_ae k _ r'
  have hWv : (planeJetL2 W (valueIndex2 Kw) : Vec 2 → h u) =ᵐ[volume]
      W.toFunction.jet (valueIndex2 Kw) := planeJetL2_ae W _
  have hWα : (planeJetL2 W ⟨⟨o.1 - 1, Nat.lt_succ_of_le hKw⟩, α⟩ : Vec 2 → h u) =ᵐ[volume]
      W.toFunction.jet ⟨⟨o.1 - 1, by omega⟩, α⟩ := planeJetL2_ae W _
  have hL : (∫ z, inner ℝ (planeJetL2 W ⟨⟨o.1 - 1, Nat.lt_succ_of_le hKw⟩, α⟩ z)
      (planeJetL2 T (valueIndex2 (n + (o.1 - 1))) z)) =
      ∫ z, letterCoeff L lo X₀ δ s v u o q α k z *
        inner ℝ (((L.edge v u o).get q).map (W.toFunction.jet ⟨⟨o.1 - 1, by omega⟩, α⟩ z))
          (Ψ.toFunction.jet ⟨⟨1, by have := (Finset.mem_Icc.mp o.2).1; omega⟩,
            fun _ => k⟩ z) := by
    apply integral_congr_ae
    filter_upwards [hWα, hTval] with z h1 h2
    rw [h1, h2]
    simp only [C, letterCoeffOp, smul_apply, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_right]
  have hR : (∫ z, inner ℝ (planeJetL2 W (valueIndex2 Kw) z)
      (planeJetL2 (planeHkWordPartial α T) (valueIndex2 n) z)) =
      ∫ z, inner ℝ (W.toFunction.jet (valueIndex2 Kw) z)
        (letterTransposeTermJet L lo X₀ δ s v u o q α k n d hod Ψ.toFunction.jet
          (valueIndex2 n) z) := by
    apply integral_congr_ae
    filter_upwards [hWv, hWP] with z h1 h2
    rw [h1, h2]
  rw [← hL, ← hR]
  exact hibp

omit [Fintype ι] in
/-- The transposed term paired with the source value is integrable. -/
theorem letterTransposeTerm_integrable (L : CycleLetter ι h D) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ)
    (v u : ι) (o : Finset.Icc 2 D) (q : Fin (L.edge v u o).length)
    (α : DerivativeWord2 (o.1 - 1)) (k : Fin 2) (n d : ℕ) (hod : o.1 ≤ d)
    {Kw : ℕ} (W : PlaneHk Set.univ Kw (h u))
    (Ψ : PlaneHk Set.univ (n + d) (h v))
    (hC : ContDiff ℝ ((n + (o.1 - 1) : ℕ) : ℕ∞) (letterCoeffOp L lo X₀ δ s v u o q α k))
    (ρ : Vec 2 → ℝ)
    (hρ : ∀ idx, MemLp (fun x => ρ x * ‖(planeHkPartial k (truncatePlaneHk
      (K := n + (o.1 - 1) + 1) (by have := (Finset.mem_Icc.mp o.2).1; omega) Ψ)).toFunction.jet
        idx x‖) 2 volume)
    {A : Fin (n + (o.1 - 1) + 1) → ℝ}
    (hA : ∀ l x, ‖coefficientDerivativeArray (letterCoeffOp L lo X₀ δ s v u o q α k) l.val x‖ ≤
      A l * ρ x) :
    Integrable (fun z => inner ℝ (W.toFunction.jet (valueIndex2 Kw) z)
      (letterTransposeTermJet L lo X₀ δ s v u o q α k n d hod Ψ.toFunction.jet
        (valueIndex2 n) z)) volume := by
  set C := letterCoeffOp L lo X₀ δ s v u o q α k
  set Ψk := planeHkPartial k (truncatePlaneHk (K := n + (o.1 - 1) + 1)
    (by have := (Finset.mem_Icc.mp o.2).1; omega) Ψ)
  set T := PlaneHk.mulCoefficientWeighted Ψk C hC ρ hρ hA
  have hWP : (planeJetL2 (planeHkWordPartial α T) (valueIndex2 n) : Vec 2 → h u) =ᵐ[volume]
      letterTransposeTermJet L lo X₀ δ s v u o q α k n d hod Ψ.toFunction.jet
        (valueIndex2 n) := by
    refine (planeJetL2_ae _ _).trans ((planeHkWordPartial_jet_ae α T _).trans ?_)
    apply wordPartialRawJet_congr_ae
    intro r
    refine (PlaneHk.mulCoefficientWeighted_jet_ae Ψk C hC ρ hρ hA r).trans ?_
    apply multiplicationRawJet_congr_ae
    intro r'
    exact planeHkPartial_jet_ae k _ r'
  refine (MeasureTheory.L2.integrable_inner (planeJetL2 W (valueIndex2 Kw))
    (planeJetL2 (planeHkWordPartial α T) (valueIndex2 n))).congr ?_
  filter_upwards [planeJetL2_ae W (valueIndex2 Kw), hWP] with z h1 h2
  rw [h1, h2]

omit [Fintype ι] in
/-- One constituent of the letter flux paired with `∂_k Ψ_v` is integrable. -/
theorem letterFluxTerm_integrable (L : CycleLetter ι h D) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ)
    (v u : ι) (o : Finset.Icc 2 D) (q : Fin (L.edge v u o).length)
    (α : DerivativeWord2 (o.1 - 1)) (k : Fin 2) (n d : ℕ) (hod : o.1 ≤ d)
    {Kw : ℕ} (hKw : o.1 - 1 ≤ Kw) (W : PlaneHk Set.univ Kw (h u))
    (Ψ : PlaneHk Set.univ (n + d) (h v))
    (hC : ContDiff ℝ ((n + (o.1 - 1) : ℕ) : ℕ∞) (letterCoeffOp L lo X₀ δ s v u o q α k))
    (ρ : Vec 2 → ℝ)
    (hρ : ∀ idx, MemLp (fun x => ρ x * ‖(planeHkPartial k (truncatePlaneHk
      (K := n + (o.1 - 1) + 1) (by have := (Finset.mem_Icc.mp o.2).1; omega) Ψ)).toFunction.jet
        idx x‖) 2 volume)
    {A : Fin (n + (o.1 - 1) + 1) → ℝ}
    (hA : ∀ l x, ‖coefficientDerivativeArray (letterCoeffOp L lo X₀ δ s v u o q α k) l.val x‖ ≤
      A l * ρ x) :
    Integrable (fun z => letterCoeff L lo X₀ δ s v u o q α k z *
        inner ℝ (((L.edge v u o).get q).map (W.toFunction.jet ⟨⟨o.1 - 1, by omega⟩, α⟩ z))
          (Ψ.toFunction.jet ⟨⟨1, by have := (Finset.mem_Icc.mp o.2).1; omega⟩,
            fun _ => k⟩ z)) volume := by
  set C := letterCoeffOp L lo X₀ δ s v u o q α k
  set Ψk := planeHkPartial k (truncatePlaneHk (K := n + (o.1 - 1) + 1)
    (by have := (Finset.mem_Icc.mp o.2).1; omega) Ψ)
  have hval : Ψk.toFunction.jet (valueIndex2 (n + (o.1 - 1))) =ᵐ[volume]
      Ψ.toFunction.jet ⟨⟨1, by have := (Finset.mem_Icc.mp o.2).1; omega⟩, fun _ => k⟩ := by
    have hv := planeHkPartial_jet_ae k (truncatePlaneHk (K := n + (o.1 - 1) + 1)
      (by have := (Finset.mem_Icc.mp o.2).1; omega) Ψ) (valueIndex2 (n + (o.1 - 1)))
    refine hv.trans (Filter.EventuallyEq.of_eq ?_)
    have hidx : (Fin.cons k Fin.elim0 : DerivativeWord2 1) = fun _ => k := by
      funext r
      obtain rfl : r = 0 := Fin.fin_one_eq_zero r
      rfl
    change Ψ.toFunction.jet ⟨⟨1, _⟩, Fin.cons k Fin.elim0⟩ = _
    rw [hidx]
  have hW : MemLp (fun z => ‖W.toFunction.jet ⟨⟨o.1 - 1, by omega⟩, α⟩ z‖) 2 volume := by
    have := W.toFunction.memL2 ⟨⟨o.1 - 1, by omega⟩, α⟩
    rw [Measure.restrict_univ] at this
    exact this.norm
  have hY : MemLp (fun z => ρ z * ‖Ψ.toFunction.jet
      ⟨⟨1, by have := (Finset.mem_Icc.mp o.2).1; omega⟩, fun _ => k⟩ z‖) 2 volume := by
    refine (hρ (valueIndex2 (n + (o.1 - 1)))).ae_eq ?_
    filter_upwards [hval] with z hz
    rw [hz]
  have hWm := W.toFunction.memL2 ⟨⟨o.1 - 1, by omega⟩, α⟩
  rw [Measure.restrict_univ] at hWm
  have hΨm := Ψ.toFunction.memL2 ⟨⟨1, by have := (Finset.mem_Icc.mp o.2).1; omega⟩,
    fun _ => k⟩
  rw [Measure.restrict_univ] at hΨm
  have hfun : (fun z => letterCoeff L lo X₀ δ s v u o q α k z *
      inner ℝ (((L.edge v u o).get q).map (W.toFunction.jet ⟨⟨o.1 - 1, by omega⟩, α⟩ z))
        (Ψ.toFunction.jet ⟨⟨1, by have := (Finset.mem_Icc.mp o.2).1; omega⟩,
          fun _ => k⟩ z)) =
      fun z => inner ℝ (W.toFunction.jet ⟨⟨o.1 - 1, by omega⟩, α⟩ z)
        (C z (Ψ.toFunction.jet ⟨⟨1, by have := (Finset.mem_Icc.mp o.2).1; omega⟩,
          fun _ => k⟩ z)) := by
    funext z
    simp only [C, letterCoeffOp, smul_apply, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_right]
  rw [hfun]
  have hprod := (hW.integrable_mul hY.norm).const_mul (|A 0|)
  refine hprod.mono' ?_ ?_
  · exact hWm.aestronglyMeasurable.inner
      ((ContinuousLinearMap.apply ℝ (h u)).flip.aestronglyMeasurable_comp₂
        hC.continuous.aestronglyMeasurable hΨm.aestronglyMeasurable)
  · filter_upwards with z
    have hCz : ‖C z‖ ≤ |A 0| * |ρ z| := by
      have h0 := orderedCoefficientDerivative_norm_le_array C 0 Fin.elim0 z
      refine (h0.trans (hA 0 z)).trans ?_
      rw [← abs_mul]
      exact le_abs_self _
    rw [Real.norm_eq_abs]
    calc |inner ℝ (W.toFunction.jet ⟨⟨o.1 - 1, by omega⟩, α⟩ z)
          (C z (Ψ.toFunction.jet ⟨⟨1, by have := (Finset.mem_Icc.mp o.2).1; omega⟩,
            fun _ => k⟩ z))|
        ≤ ‖W.toFunction.jet ⟨⟨o.1 - 1, by omega⟩, α⟩ z‖ *
            (‖C z‖ * ‖Ψ.toFunction.jet ⟨⟨1, by have := (Finset.mem_Icc.mp o.2).1; omega⟩,
              fun _ => k⟩ z‖) :=
          (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
            ((C z).le_opNorm _) (norm_nonneg _))
      _ ≤ ‖W.toFunction.jet ⟨⟨o.1 - 1, by omega⟩, α⟩ z‖ *
            ((|A 0| * |ρ z|) * ‖Ψ.toFunction.jet ⟨⟨1, by
              have := (Finset.mem_Icc.mp o.2).1; omega⟩, fun _ => k⟩ z‖) := by
          gcongr
      _ = |A 0| * (‖W.toFunction.jet ⟨⟨o.1 - 1, by omega⟩, α⟩ z‖ *
            ‖ρ z * ‖Ψ.toFunction.jet ⟨⟨1, by
              have := (Finset.mem_Icc.mp o.2).1; omega⟩, fun _ => k⟩ z‖‖) := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _)]
          ring

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The letter flux paired with a vector `y` of the target space, constituent by constituent. -/
theorem letterAdmissibleFlux_inner_expand {σ : Type*} (L : CycleLetter ι h D) (κ : σ → ℕ)
    (a : σ) (b : ι → σ) (v : ι) (lo : ℕ) (X₀ : Vec 2) (δ : ℝ)
    (W : ∀ u, PlaneHk Set.univ (κ (b u) + 1) (h u)) (s : ℝ) (z : Vec 2) (y : Fin 2 → h v) :
    ∑ k : Fin 2, inner ℝ ((letterAdmissibleFlux L κ a b v lo X₀ δ W s z) k) (y k) =
      ∑ u, ∑ o : admissibleOrders κ D a (b u),
        ∑ q : Fin (L.edge v u (admissibleLetterOrder κ D a (b u) o)).length,
          ∑ α : DerivativeWord2 (o.1 - 1), ∑ k : Fin 2,
            letterCoeff L lo X₀ δ s v u (admissibleLetterOrder κ D a (b u) o) q α k z *
              inner ℝ (((L.edge v u (admissibleLetterOrder κ D a (b u) o)).get q).map
                ((W u).toFunction.jet (admissibleLetterSourceIndex κ D a (b u) o α) z)) (y k) := by
  unfold letterAdmissibleFlux
  simp only [WithLp.ofLp_sum, Finset.sum_apply, sum_inner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => ?_
  unfold slowEvalCoefficient
  rw [← Fin.sum_univ_fun_getElem]
  simp only [sum_apply, WithLp.ofLp_sum, Finset.sum_apply, sum_inner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [ContinuousLinearEquiv.coe_coe,
    PiLp.continuousLinearEquiv_symm_apply, ContinuousLinearMap.pi_apply,
    sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, sum_inner, inner_smul_left, letterCoeff, List.get_eq_getElem]
  rw [Finset.sum_comm]
  rfl
end

/-! **Duality of a letter with its transpose** (the step of the adjoint word chain): the letter flux
of the target family paired with the gradient of an adjoint family `Ψ` (inverse-mass sum) equals the
source family paired with the transposed letter `L*Ψ`:

`∑_v π_v⁻¹ ∫ ⟨F_v, ∇Ψ_v⟩ = ∑_u π_u⁻¹ ∫ ⟨W_u, (L*Ψ)_u⟩`.

Orders above the letter's order `d` have empty edge lists; for the others the identity is
`letterTransposeTerm_duality`, summed over constituents, words, directions and orders, with the
masses rebalanced as `π_v⁻¹ = π_u⁻¹ (π_u/π_v)`. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] {D : ℕ}

/-- The hypotheses of one transposed constituent: smoothness of the coefficient, and a weight
`ρ` dominating its jets and absorbed by the adjoint family's derivative. -/
def LetterTermRegular (L : CycleLetter ι h D) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ) (n d : ℕ)
    (Ψ : ∀ v, PlaneHk Set.univ (n + d) (h v)) : Prop :=
  ∀ v u (o : Finset.Icc 2 D) (hod : o.1 ≤ d) (q : Fin (L.edge v u o).length)
    (α : DerivativeWord2 (o.1 - 1)) (k : Fin 2),
    ContDiff ℝ ((n + (o.1 - 1) : ℕ) : ℕ∞) (letterCoeffOp L lo X₀ δ s v u o q α k) ∧
    ∃ (ρ : Vec 2 → ℝ) (A : Fin (n + (o.1 - 1) + 1) → ℝ),
      (∀ idx, MemLp (fun x => ρ x * ‖(planeHkPartial k (truncatePlaneHk
        (K := n + (o.1 - 1) + 1) (by have := (Finset.mem_Icc.mp o.2).1; omega) (Ψ v))).toFunction.jet
          idx x‖) 2 volume) ∧
      ∀ l x, ‖coefficientDerivativeArray (letterCoeffOp L lo X₀ δ s v u o q α k) l.val x‖ ≤
        A l * ρ x

theorem letterTranspose_duality {σ : Type*} (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (L : CycleLetter ι h D) (κ : σ → ℕ) (a b : ι → σ) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ)
    (n d : ℕ) (hd : 1 ≤ d)
    (hempty : ∀ v u (o : Finset.Icc 2 D), d < o.1 → L.edge v u o = [])
    (W : ∀ u, PlaneHk Set.univ (κ (b u) + 1) (h u)) (Ψ : ∀ v, PlaneHk Set.univ (n + d) (h v))
    (hreg : LetterTermRegular L lo X₀ δ s n d Ψ) :
    ∑ v, (π v)⁻¹ * ∫ z, ∑ k : Fin 2,
        inner ℝ ((letterAdmissibleFlux L κ (a v) b v lo X₀ δ W s z) k)
          ((Ψ v).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z) =
      ∑ u, (π u)⁻¹ * ∫ z, inner ℝ ((W u).toFunction.jet (valueIndex2 (κ (b u) + 1)) z)
        (letterTransposeJet π L κ a b lo X₀ δ s n d (fun v => (Ψ v).toFunction.jet) u
          (valueIndex2 n) z) := by
  classical
  -- the leaves
  have hsrc : ∀ v u (o : admissibleOrders κ D (a v) (b u)), o.1 - 1 ≤ κ (b u) + 1 := by
    intro v u o
    have := admissible_letter_source_reserve κ D (a v) (b u) o
    omega
  let Fl := fun (v u : ι) (o : admissibleOrders κ D (a v) (b u))
      (q : Fin (L.edge v u (admissibleLetterOrder κ D (a v) (b u) o)).length) (α : DerivativeWord2 (o.1 - 1)) (k : Fin 2)
      (z : Vec 2) =>
    letterCoeff L lo X₀ δ s v u (admissibleLetterOrder κ D (a v) (b u) o) q α k z *
      inner ℝ (((L.edge v u (admissibleLetterOrder κ D (a v) (b u) o)).get q).map
        ((W u).toFunction.jet (admissibleLetterSourceIndex κ D (a v) (b u) o α) z))
        ((Ψ v).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z)
  -- a nonempty edge list has order at most `d`
  have hle : ∀ v u (o : admissibleOrders κ D (a v) (b u))
      (q : Fin (L.edge v u (admissibleLetterOrder κ D (a v) (b u) o)).length), o.1 ≤ d := by
    intro v u o q
    by_contra hcon
    have he := hempty v u (admissibleLetterOrder κ D (a v) (b u) o)
      (by simp only [admissibleLetterOrder]; omega)
    have hlen : (L.edge v u (admissibleLetterOrder κ D (a v) (b u) o)).length = 0 := by
      rw [he]; rfl
    exact absurd q.isLt (by omega)
  have hFl_int : ∀ v u o q α k, Integrable (Fl v u o q α k) volume := by
    intro v u o q α k
    have hod := hle v u o q
    obtain ⟨hC, ρ, A, hρ, hA⟩ := hreg v u (admissibleLetterOrder κ D (a v) (b u) o) hod q α k
    exact letterFluxTerm_integrable L lo X₀ δ s v u (admissibleLetterOrder κ D (a v) (b u) o) q α k n d hod (hsrc v u o) (W u)
      (Ψ v) hC ρ hρ hA
  have hFl_dual : ∀ v u o q α k, ∫ z, Fl v u o q α k z =
      (-1) ^ (o.1 - 1) * ∫ z, inner ℝ ((W u).toFunction.jet (valueIndex2 (κ (b u) + 1)) z)
        (letterTransposeTermJet L lo X₀ δ s v u (admissibleLetterOrder κ D (a v) (b u) o) q α k n d (hle v u o q)
          (Ψ v).toFunction.jet (valueIndex2 n) z) := by
    intro v u o q α k
    have hod := hle v u o q
    obtain ⟨hC, ρ, A, hρ, hA⟩ := hreg v u (admissibleLetterOrder κ D (a v) (b u) o) hod q α k
    exact letterTransposeTerm_duality L lo X₀ δ s v u (admissibleLetterOrder κ D (a v) (b u) o) q α k n d hod (hsrc v u o) (W u)
      (Ψ v) hC ρ hρ hA
  have hT_int : ∀ v u (o : admissibleOrders κ D (a v) (b u)) (hod : o.1 ≤ d)
      (q : Fin (L.edge v u (admissibleLetterOrder κ D (a v) (b u) o)).length)
      (α : DerivativeWord2 (o.1 - 1)) (k : Fin 2), Integrable (fun z =>
      inner ℝ ((W u).toFunction.jet (valueIndex2 (κ (b u) + 1)) z)
        (letterTransposeTermJet L lo X₀ δ s v u (admissibleLetterOrder κ D (a v) (b u) o) q α k n d hod
          (Ψ v).toFunction.jet (valueIndex2 n) z)) volume := by
    intro v u o hod q α k
    obtain ⟨hC, ρ, A, hρ, hA⟩ := hreg v u (admissibleLetterOrder κ D (a v) (b u) o) hod q α k
    exact letterTransposeTerm_integrable L lo X₀ δ s v u (admissibleLetterOrder κ D (a v) (b u) o) q α k n d hod (W u)
      (Ψ v) hC ρ hρ hA
  -- the left side, leaf by leaf
  have hLHS : ∀ v, ∫ z, ∑ k : Fin 2,
      inner ℝ ((letterAdmissibleFlux L κ (a v) b v lo X₀ δ W s z) k)
        ((Ψ v).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z) =
      ∑ u, ∑ o : admissibleOrders κ D (a v) (b u),
        ∑ q : Fin (L.edge v u (admissibleLetterOrder κ D (a v) (b u) o)).length, ∑ α : DerivativeWord2 (o.1 - 1), ∑ k : Fin 2,
          ∫ z, Fl v u o q α k z := by
    intro v
    rw [show (fun z => ∑ k : Fin 2,
        inner ℝ ((letterAdmissibleFlux L κ (a v) b v lo X₀ δ W s z) k)
          ((Ψ v).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z)) =
        fun z => ∑ u, ∑ o : admissibleOrders κ D (a v) (b u),
          ∑ q : Fin (L.edge v u (admissibleLetterOrder κ D (a v) (b u) o)).length, ∑ α : DerivativeWord2 (o.1 - 1),
            ∑ k : Fin 2, Fl v u o q α k z from
      funext fun z => letterAdmissibleFlux_inner_expand L κ (a v) b v lo X₀ δ W s z _]
    rw [integral_finsetSum _ fun u _ => integrable_finsetSum _ fun o _ =>
      integrable_finsetSum _ fun q _ => integrable_finsetSum _ fun α _ =>
        integrable_finsetSum _ fun k _ => hFl_int v u o q α k]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [integral_finsetSum _ fun o _ => integrable_finsetSum _ fun q _ =>
      integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun k _ => hFl_int v u o q α k]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [integral_finsetSum _ fun q _ => integrable_finsetSum _ fun α _ =>
      integrable_finsetSum _ fun k _ => hFl_int v u o q α k]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun k _ => hFl_int v u o q α k]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_finsetSum _ fun k _ => hFl_int v u o q α k]
  -- the right side, leaf by leaf
  have hRHS : ∀ u, ∫ z, inner ℝ ((W u).toFunction.jet (valueIndex2 (κ (b u) + 1)) z)
      (letterTransposeJet π L κ a b lo X₀ δ s n d (fun v => (Ψ v).toFunction.jet) u
        (valueIndex2 n) z) =
      ∑ v, ∑ o : admissibleOrders κ D (a v) (b u),
        if hod : o.1 ≤ d then ((-1 : ℝ) ^ (o.1 - 1) * (π u / π v)) *
          ∑ q : Fin (L.edge v u (admissibleLetterOrder κ D (a v) (b u) o)).length, ∑ α : DerivativeWord2 (o.1 - 1),
            ∑ k : Fin 2, ∫ z, inner ℝ ((W u).toFunction.jet (valueIndex2 (κ (b u) + 1)) z)
              (letterTransposeTermJet L lo X₀ δ s v u (admissibleLetterOrder κ D (a v) (b u) o) q α k n d hod
                (Ψ v).toFunction.jet (valueIndex2 n) z)
        else 0 := by
    intro u
    have hint : ∀ v (o : admissibleOrders κ D (a v) (b u)), Integrable (fun z =>
        inner ℝ ((W u).toFunction.jet (valueIndex2 (κ (b u) + 1)) z)
          (if hod : o.1 ≤ d then ((-1 : ℝ) ^ (o.1 - 1) * (π u / π v)) •
            ∑ q : Fin (L.edge v u (admissibleLetterOrder κ D (a v) (b u) o)).length, ∑ α : DerivativeWord2 (o.1 - 1),
              ∑ k : Fin 2, letterTransposeTermJet L lo X₀ δ s v u (admissibleLetterOrder κ D (a v) (b u) o) q α k n d hod
                (Ψ v).toFunction.jet (valueIndex2 n) z
          else 0)) volume := by
      intro v o
      by_cases hod : o.1 ≤ d
      · simp only [hod, dite_true, inner_smul_right, inner_sum]
        exact (integrable_finsetSum _ fun q _ => integrable_finsetSum _ fun α _ =>
          integrable_finsetSum _ fun k _ => hT_int v u o hod q α k).const_mul _
      · simp only [hod, dite_false, inner_zero_right]
        exact integrable_zero _ _ _
    simp only [letterTransposeJet, inner_sum]
    rw [integral_finsetSum _ fun v _ => integrable_finsetSum _ fun o _ => hint v o]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [integral_finsetSum _ fun o _ => hint v o]
    refine Finset.sum_congr rfl fun o _ => ?_
    by_cases hod : o.1 ≤ d
    · simp only [hod, dite_true, inner_smul_right, inner_sum]
      rw [integral_const_mul]
      congr 1
      rw [integral_finsetSum _ fun q _ => integrable_finsetSum _ fun α _ =>
        integrable_finsetSum _ fun k _ => hT_int v u o hod q α k]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun k _ =>
        hT_int v u o hod q α k]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [integral_finsetSum _ fun k _ => hT_int v u o hod q α k]
    · simp only [hod, dite_false, inner_zero_right, integral_zero]
  -- assemble
  simp only [hLHS, hRHS, hFl_dual]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
    Finset.sum_congr rfl fun o _ => ?_
  by_cases hod : o.1 ≤ d
  · simp only [hod, dite_true, Finset.mul_sum]
    have hu := (hπ u).ne'
    have hv := (hπ v).ne'
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun k _ => ?_
    field_simp
  · simp only [hod, dite_false, mul_zero]
    apply Finset.sum_eq_zero
    intro q _
    exact absurd (hle v u o q) hod
end

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane
namespace AVRegularity.CycleWords.Seam

/-! **The transposed letter as a plane carrier.** Under `LetterTermRegular`, every transposed
constituent `D_α^{rev}(c • γ.map† ∂_k Ψ)` is a plane carrier of order `n` (weighted coefficient
multiplication, then the nested partials), and so is the transposed letter `L*Ψ`; its jets are those
of `letterTransposeJet` almost everywhere. -/

section Jets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHk_jet_ae_val {K : ℕ} (P : PlaneHk Set.univ K E) (idx : JetIndex2 K) :
    P.toFunction.jet idx = ⇑(P.val idx) := rfl

theorem planeHk_jet_sum_ae {n : Type*} [Fintype n] {K : ℕ} (P : n → PlaneHk Set.univ K E)
    (idx : JetIndex2 K) :
    (∑ i, P i).toFunction.jet idx =ᵐ[volume] fun x => ∑ i, (P i).toFunction.jet idx x := by
  rw [planeHk_jet_ae_val, planeHk_sum_component]
  have h := (ae_restrict_iff' MeasurableSet.univ).mp
    (Lp.coeFn_finsetSum (μ := volume.restrict Set.univ) Finset.univ (fun i => (P i).val idx))
  filter_upwards [h] with x hx
  rw [hx (Set.mem_univ x), Finset.sum_apply]
  rfl

theorem planeHk_jet_smul_ae {K : ℕ} (c : ℝ) (P : PlaneHk Set.univ K E) (idx : JetIndex2 K) :
    (c • P).toFunction.jet idx =ᵐ[volume] fun x => c • P.toFunction.jet idx x := by
  rw [planeHk_jet_ae_val, planeHk_smul_component]
  have h := (ae_restrict_iff' MeasurableSet.univ).mp
    (Lp.coeFn_smul (μ := volume.restrict Set.univ) c (P.val idx))
  filter_upwards [h] with x hx
  rw [hx (Set.mem_univ x)]
  rfl

theorem planeHk_jet_zero_ae {K : ℕ} (idx : JetIndex2 K) :
    (0 : PlaneHk Set.univ K E).toFunction.jet idx =ᵐ[volume] 0 := by
  rw [planeHk_jet_ae_val]
  have h0 : (0 : PlaneHk Set.univ K E).val idx = 0 := rfl
  rw [h0]
  have h := (ae_restrict_iff' MeasurableSet.univ).mp
    (Lp.coeFn_zero E 2 ((volume : Measure (Vec 2)).restrict Set.univ))
  filter_upwards [h] with x hx
  exact hx (Set.mem_univ x)

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem ae_finsetSum_congr {n : Type*} [Fintype n] {f g : n → Vec 2 → E}
    (h : ∀ i, f i =ᵐ[volume] g i) :
    (fun x => ∑ i, f i x) =ᵐ[volume] fun x => ∑ i, g i x := by
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact Finset.sum_congr rfl fun i _ => hx i

end Jets

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] {D : ℕ}

/-- One transposed constituent as a plane carrier. -/
def letterTransposeTermHk (L : CycleLetter ι h D) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ) (v u : ι)
    (o : Finset.Icc 2 D) (q : Fin (L.edge v u o).length) (α : DerivativeWord2 (o.1 - 1))
    (k : Fin 2) (n d : ℕ) (hod : o.1 ≤ d) (Ψ : PlaneHk Set.univ (n + d) (h v))
    (hC : ContDiff ℝ ((n + (o.1 - 1) : ℕ) : ℕ∞) (letterCoeffOp L lo X₀ δ s v u o q α k))
    (ρ : Vec 2 → ℝ)
    (hρ : ∀ idx, MemLp (fun x => ρ x * ‖(planeHkPartial k (truncatePlaneHk
      (K := n + (o.1 - 1) + 1) (by have := (Finset.mem_Icc.mp o.2).1; omega) Ψ)).toFunction.jet
        idx x‖) 2 volume)
    {A : Fin (n + (o.1 - 1) + 1) → ℝ}
    (hA : ∀ l x, ‖coefficientDerivativeArray (letterCoeffOp L lo X₀ δ s v u o q α k) l.val x‖ ≤
      A l * ρ x) :
    PlaneHk Set.univ n (h u) :=
  planeHkWordPartial α (PlaneHk.mulCoefficientWeighted (planeHkPartial k (truncatePlaneHk
    (K := n + (o.1 - 1) + 1) (by have := (Finset.mem_Icc.mp o.2).1; omega) Ψ))
    (letterCoeffOp L lo X₀ δ s v u o q α k) hC ρ hρ hA)

omit [Fintype ι] in
theorem letterTransposeTermHk_jet_ae (L : CycleLetter ι h D) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ)
    (v u : ι) (o : Finset.Icc 2 D) (q : Fin (L.edge v u o).length)
    (α : DerivativeWord2 (o.1 - 1)) (k : Fin 2) (n d : ℕ) (hod : o.1 ≤ d)
    (Ψ : PlaneHk Set.univ (n + d) (h v))
    (hC : ContDiff ℝ ((n + (o.1 - 1) : ℕ) : ℕ∞) (letterCoeffOp L lo X₀ δ s v u o q α k))
    (ρ : Vec 2 → ℝ)
    (hρ : ∀ idx, MemLp (fun x => ρ x * ‖(planeHkPartial k (truncatePlaneHk
      (K := n + (o.1 - 1) + 1) (by have := (Finset.mem_Icc.mp o.2).1; omega) Ψ)).toFunction.jet
        idx x‖) 2 volume)
    {A : Fin (n + (o.1 - 1) + 1) → ℝ}
    (hA : ∀ l x, ‖coefficientDerivativeArray (letterCoeffOp L lo X₀ δ s v u o q α k) l.val x‖ ≤
      A l * ρ x) (idx : JetIndex2 n) :
    (letterTransposeTermHk L lo X₀ δ s v u o q α k n d hod Ψ hC ρ hρ hA).toFunction.jet idx
      =ᵐ[volume] letterTransposeTermJet L lo X₀ δ s v u o q α k n d hod Ψ.toFunction.jet idx := by
  unfold letterTransposeTermHk letterTransposeTermJet
  refine (planeHkWordPartial_jet_ae α _ idx).trans ?_
  refine wordPartialRawJet_congr_ae α _ _ (fun q' => ?_) idx
  refine (PlaneHk.mulCoefficientWeighted_jet_ae _ _ hC ρ hρ hA q').trans ?_
  refine multiplicationRawJet_congr_ae _ _ _ (fun q'' => ?_) q'
  exact planeHkPartial_jet_ae k _ q''

/-- **The transposed letter** as a family of plane carriers of order `n`. -/
def letterTransposeHk {σ : Type*} (π : ι → ℝ) (L : CycleLetter ι h D) (κ : σ → ℕ)
    (a b : ι → σ) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ) (n d : ℕ)
    (Ψ : ∀ v, PlaneHk Set.univ (n + d) (h v)) (hreg : LetterTermRegular L lo X₀ δ s n d Ψ)
    (u : ι) : PlaneHk Set.univ n (h u) :=
  ∑ v, ∑ o : admissibleOrders κ D (a v) (b u),
    if hod : o.1 ≤ d then
      ((-1 : ℝ) ^ (o.1 - 1) * (π u / π v)) •
        ∑ q : Fin (L.edge v u (admissibleLetterOrder κ D (a v) (b u) o)).length,
          ∑ α : DerivativeWord2 (o.1 - 1), ∑ k : Fin 2,
            letterTransposeTermHk L lo X₀ δ s v u (admissibleLetterOrder κ D (a v) (b u) o) q α k
              n d hod (Ψ v)
              (hreg v u (admissibleLetterOrder κ D (a v) (b u) o) hod q α k).1
              (hreg v u (admissibleLetterOrder κ D (a v) (b u) o) hod q α k).2.choose
              (hreg v u (admissibleLetterOrder κ D (a v) (b u) o) hod q α k).2.choose_spec.choose_spec.1
              (hreg v u (admissibleLetterOrder κ D (a v) (b u) o) hod q α k).2.choose_spec.choose_spec.2
    else 0

theorem letterTransposeHk_jet_ae {σ : Type*} (π : ι → ℝ) (L : CycleLetter ι h D) (κ : σ → ℕ)
    (a b : ι → σ) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ) (n d : ℕ)
    (Ψ : ∀ v, PlaneHk Set.univ (n + d) (h v)) (hreg : LetterTermRegular L lo X₀ δ s n d Ψ)
    (u : ι) (idx : JetIndex2 n) :
    (letterTransposeHk π L κ a b lo X₀ δ s n d Ψ hreg u).toFunction.jet idx =ᵐ[volume]
      letterTransposeJet π L κ a b lo X₀ δ s n d (fun v => (Ψ v).toFunction.jet) u idx := by
  have hterm : ∀ v (o : admissibleOrders κ D (a v) (b u)),
      (if hod : o.1 ≤ d then
        ((-1 : ℝ) ^ (o.1 - 1) * (π u / π v)) •
          ∑ q : Fin (L.edge v u (admissibleLetterOrder κ D (a v) (b u) o)).length,
            ∑ α : DerivativeWord2 (o.1 - 1), ∑ k : Fin 2,
              letterTransposeTermHk L lo X₀ δ s v u (admissibleLetterOrder κ D (a v) (b u) o) q α
                k n d hod (Ψ v)
                (hreg v u (admissibleLetterOrder κ D (a v) (b u) o) hod q α k).1
                (hreg v u (admissibleLetterOrder κ D (a v) (b u) o) hod q α k).2.choose
                (hreg v u (admissibleLetterOrder κ D (a v) (b u) o) hod q α
                  k).2.choose_spec.choose_spec.1
                (hreg v u (admissibleLetterOrder κ D (a v) (b u) o) hod q α
                  k).2.choose_spec.choose_spec.2
      else (0 : PlaneHk Set.univ n (h u))).toFunction.jet idx =ᵐ[volume]
      fun x => if hod : o.1 ≤ d then ((-1 : ℝ) ^ (o.1 - 1) * (π u / π v)) •
        ∑ q : Fin (L.edge v u (admissibleLetterOrder κ D (a v) (b u) o)).length,
          ∑ α : DerivativeWord2 (o.1 - 1), ∑ k : Fin 2,
            letterTransposeTermJet L lo X₀ δ s v u (admissibleLetterOrder κ D (a v) (b u) o) q α k
              n d hod (Ψ v).toFunction.jet idx x
      else 0 := by
    intro v o
    by_cases hod : o.1 ≤ d
    · simp only [hod, dite_true]
      refine (planeHk_jet_smul_ae _ _ idx).trans ?_
      refine Filter.EventuallyEq.fun_comp ?_ (fun y => ((-1 : ℝ) ^ (o.1 - 1) * (π u / π v)) • y)
      refine (planeHk_jet_sum_ae _ idx).trans ?_
      refine ae_finsetSum_congr fun q => (planeHk_jet_sum_ae _ idx).trans ?_
      refine ae_finsetSum_congr fun α => (planeHk_jet_sum_ae _ idx).trans ?_
      exact ae_finsetSum_congr fun k => letterTransposeTermHk_jet_ae L lo X₀ δ s v u _ q α k n d
        hod (Ψ v) _ _ _ _ idx
    · simp only [hod, dite_false]
      exact planeHk_jet_zero_ae idx
  unfold letterTransposeHk
  exact (planeHk_jet_sum_ae _ idx).trans (ae_finsetSum_congr fun v =>
    (planeHk_jet_sum_ae _ idx).trans (ae_finsetSum_congr fun o => hterm v o))

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # Leibniz for the weighted jet norm

`weightedJetNorm_smul_le`: multiplying a test family by a smooth scalar `s` whose derivatives of
order `i ≤ L` are bounded by `B r^{-i} ⟨ϖz⟩^d` costs `(L+1) 4^L B` and `d` powers of the weight:
`‖sφ‖_{r,L;q} ≤ (L+1) 4^L B ‖φ‖_{r,L;q+d}`.

Two multipliers: the spatial cutoff `spatialCutoff R` (`d = 0`, for `R ≥ r`) and the coordinate
`ϖ z_i` (`d = 1`, for `ϖ ≤ r⁻¹`), hence the word monomials `ϖ^j z^w` (`d = j`). -/

open AVRegularity.CycleWords.Assembly

section Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An ordered derivative is a value of the iterated derivative on a basis tuple. -/
theorem norm_orderedDerivative_le' {a : ℕ} (w : DerivativeWord2 a) {f : Vec 2 → E}
    (hf : ContDiff ℝ (a : ℕ∞) f) (z : Vec 2) :
    ‖orderedDerivative w f z‖ ≤ ‖iteratedFDeriv ℝ a f z‖ := by
  rw [orderedDerivative_eq_iteratedFDeriv w hf]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans (le_of_eq ?_)
  rw [Finset.prod_eq_one fun i _ => norm_basisVec_eq_one _, mul_one]

/-- The iterated derivative is bounded by the size of the array of ordered derivatives. -/
theorem norm_iteratedFDeriv_le_wordSize {j : ℕ} {φ : Vec 2 → E}
    (hφ : ContDiff ℝ (j : ℕ∞) φ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ j φ z‖ ≤
      2 ^ j * wordSize j (fun w : DerivativeWord2 j => orderedDerivative w φ z) := by
  refine (norm_le_sum_basis _).trans ?_
  have hterm : ∀ idx : Fin j → Fin 2, ‖iteratedFDeriv ℝ j φ z fun l => basisVec (idx l)‖ ≤
      wordSize j (fun w : DerivativeWord2 j => orderedDerivative w φ z) := by
    intro idx
    have h : ‖orderedDerivative (fun i : Fin j => idx (Fin.rev i)) φ z‖ ≤
        wordSize j (fun w : DerivativeWord2 j => orderedDerivative w φ z) :=
      norm_le_wordSize (fun w : DerivativeWord2 j => orderedDerivative w φ z) _
    rw [orderedDerivative_eq_iteratedFDeriv _ hφ] at h
    simpa only [Fin.rev_rev] using h
  refine (Finset.sum_le_sum fun idx _ => hterm idx).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring

/-- **Pointwise Leibniz** for an ordered derivative of a product. -/
theorem norm_orderedDerivative_smul_le {a : ℕ} (w : DerivativeWord2 a) {s : Vec 2 → ℝ}
    {φ : Vec 2 → E} (hs : ContDiff ℝ (a : ℕ∞) s) (hφ : ContDiff ℝ (a : ℕ∞) φ) (z : Vec 2) :
    ‖orderedDerivative w (fun y => s y • φ y) z‖ ≤
      ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * ‖iteratedFDeriv ℝ i s z‖ *
        (2 ^ (a - i) * wordSize (a - i)
          (fun v : DerivativeWord2 (a - i) => orderedDerivative v φ z)) := by
  refine (norm_orderedDerivative_le' w (hs.smul hφ) z).trans ?_
  refine (norm_iteratedFDeriv_smul_le hs hφ z le_rfl).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact norm_iteratedFDeriv_le_wordSize (hφ.of_le (by exact_mod_cast Nat.sub_le a i)) z

omit [NormedSpace ℝ E] in
theorem wordSize_nonneg {a : ℕ} (J : DerivativeWord2 a → E) : 0 ≤ wordSize a J := by
  unfold wordSize
  exact Real.sqrt_nonneg _

end Pointwise

section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem cutoffJetSize_eq_familyNorm (π : ι → ℝ) (p s : ℝ) (φ : ∀ v, Vec 2 → h v) (a : ℕ) :
    cutoffJetSize π p s φ a = familyNorm (fun v => ENNReal.ofReal ((π v)⁻¹))
      (fun v => eLpNorm (fun z => cutoffBracket s z ^ (p / 2) *
        wordSize a (fun w : DerivativeWord2 a => orderedDerivative w (φ v) z)) 2 volume) := rfl

/-- One order of the Leibniz estimate. -/
theorem cutoffJetSize_smul_le (π : ι → ℝ) (q : ℝ) (d : ℕ) {ϖ ρ B : ℝ} (hρ : 0 ≤ ρ)
    (hB : 0 ≤ B) (a : ℕ) {s : Vec 2 → ℝ} (hs : ContDiff ℝ (⊤ : ℕ∞) s)
    (hsb : ∀ i ≤ a, ∀ z, ‖iteratedFDeriv ℝ i s z‖ ≤
      B * ρ ^ i * cutoffBracket ϖ z ^ ((d : ℝ) / 2))
    (φ : ∀ v, Vec 2 → h v) (hφ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v)) :
    cutoffJetSize π q ϖ (fun v z => s z • φ v z) a ≤
      ∑ i ∈ Finset.range (a + 1), ENNReal.ofReal (4 ^ a * (a.choose i : ℝ) * B * ρ ^ i) *
        cutoffJetSize π (q + d) ϖ φ (a - i) := by
  rw [cutoffJetSize_eq_familyNorm]
  simp only [cutoffJetSize_eq_familyNorm]
  refine familyNorm_eLpNorm_majorant (fun v => ENNReal.ofReal ((π v)⁻¹)) (Finset.range (a + 1))
    (fun i => 4 ^ a * (a.choose i : ℝ) * B * ρ ^ i) (fun i _ => by positivity)
    (fun v z => cutoffBracket ϖ z ^ (q / 2) *
      wordSize a (fun w : DerivativeWord2 a => orderedDerivative w (fun y => s y • φ v y) z)) ?_
    (fun i v z => cutoffBracket ϖ z ^ ((q + d) / 2) *
      wordSize (a - i) (fun w : DerivativeWord2 (a - i) => orderedDerivative w (φ v) z)) ?_
  · intro v
    have hc : ContDiff ℝ (a : ℕ∞) (fun y => s y • φ v y) :=
      (hs.smul (hφ v)).of_le (by exact_mod_cast le_top)
    exact ((weight_continuous ϖ q).mul (Real.continuous_sqrt.comp
      (continuous_finsetSum _ fun w _ =>
        ((orderedDerivative_continuous w hc).norm.pow 2)))).aestronglyMeasurable
  · intro v z
    have hbr : 0 < cutoffBracket ϖ z := lt_of_lt_of_le one_pos (cutoffBracket_one_le ϖ z)
    have hw0 : 0 ≤ cutoffBracket ϖ z ^ (q / 2) := Real.rpow_nonneg hbr.le _
    have hWd : ∀ i, 0 ≤ wordSize (a - i)
        (fun w : DerivativeWord2 (a - i) => orderedDerivative w (φ v) z) := fun i =>
      wordSize_nonneg _
    rw [abs_of_nonneg (mul_nonneg hw0 (wordSize_nonneg _))]
    have hM : wordSize a
        (fun w : DerivativeWord2 a => orderedDerivative w (fun y => s y • φ v y) z) ≤
        2 ^ a * ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) *
          (B * ρ ^ i * cutoffBracket ϖ z ^ ((d : ℝ) / 2)) *
            (2 ^ (a - i) * wordSize (a - i)
              (fun w : DerivativeWord2 (a - i) => orderedDerivative w (φ v) z)) := by
      refine wordSize_le_card_mul _ (Finset.sum_nonneg fun i _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hB (pow_nonneg hρ i))
          (Real.rpow_nonneg hbr.le _))) (mul_nonneg (by positivity) (hWd i))) fun w => ?_
      refine (norm_orderedDerivative_smul_le w (hs.of_le (by exact_mod_cast le_top))
        ((hφ v).of_le (by exact_mod_cast le_top)) z).trans ?_
      refine Finset.sum_le_sum fun i hi => ?_
      have hia : i ≤ a := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hsb i hia z) (Nat.cast_nonneg _))
        (mul_nonneg (by positivity) (hWd i))
    calc cutoffBracket ϖ z ^ (q / 2) * wordSize a
          (fun w : DerivativeWord2 a => orderedDerivative w (fun y => s y • φ v y) z)
        ≤ cutoffBracket ϖ z ^ (q / 2) * (2 ^ a * ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) *
          (B * ρ ^ i * cutoffBracket ϖ z ^ ((d : ℝ) / 2)) *
            (2 ^ (a - i) * wordSize (a - i)
              (fun w : DerivativeWord2 (a - i) => orderedDerivative w (φ v) z))) :=
          mul_le_mul_of_nonneg_left hM hw0
      _ = ∑ i ∈ Finset.range (a + 1), (2 ^ a * 2 ^ (a - i) * (a.choose i : ℝ) * B * ρ ^ i) *
            (cutoffBracket ϖ z ^ ((q + d) / 2) * wordSize (a - i)
              (fun w : DerivativeWord2 (a - i) => orderedDerivative w (φ v) z)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show (q + d) / 2 = q / 2 + (d : ℝ) / 2 by ring, Real.rpow_add hbr]
          ring
      _ ≤ ∑ i ∈ Finset.range (a + 1), (4 ^ a * (a.choose i : ℝ) * B * ρ ^ i) *
            (cutoffBracket ϖ z ^ ((q + d) / 2) * wordSize (a - i)
              (fun w : DerivativeWord2 (a - i) => orderedDerivative w (φ v) z)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul_of_nonneg_right ?_
            (mul_nonneg (Real.rpow_nonneg hbr.le _) (hWd i))
          have h2 : (2 : ℝ) ^ a * 2 ^ (a - i) ≤ 4 ^ a := by
            calc (2 : ℝ) ^ a * 2 ^ (a - i) ≤ 2 ^ a * 2 ^ a :=
                  mul_le_mul_of_nonneg_left
                    (pow_le_pow_right₀ (by norm_num) (Nat.sub_le a i)) (by positivity)
              _ = 4 ^ a := by rw [← mul_pow]; norm_num
          have h3 : (0 : ℝ) ≤ (a.choose i : ℝ) * B * ρ ^ i :=
            mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) (pow_nonneg hρ i)
          calc 2 ^ a * 2 ^ (a - i) * (a.choose i : ℝ) * B * ρ ^ i
              = (2 ^ a * 2 ^ (a - i)) * ((a.choose i : ℝ) * B * ρ ^ i) := by ring
            _ ≤ 4 ^ a * ((a.choose i : ℝ) * B * ρ ^ i) := mul_le_mul_of_nonneg_right h2 h3
            _ = 4 ^ a * (a.choose i : ℝ) * B * ρ ^ i := by ring

/-- The constant of the Leibniz estimate. -/
def LeibConst (L : ℕ) : ℝ := (L + 1) * 4 ^ L

theorem LeibConst_pos (L : ℕ) : 0 < LeibConst L := by
  unfold LeibConst
  positivity

/-- **Leibniz for the weighted jet norm.** -/
theorem weightedJetNorm_smul_le (π : ι → ℝ) (q : ℝ) (d L : ℕ) {ϖ r B : ℝ} (hr : 0 < r)
    (hB : 0 ≤ B) {s : Vec 2 → ℝ} (hs : ContDiff ℝ (⊤ : ℕ∞) s)
    (hsb : ∀ i ≤ L, ∀ z, ‖iteratedFDeriv ℝ i s z‖ ≤
      B * r⁻¹ ^ i * cutoffBracket ϖ z ^ ((d : ℝ) / 2))
    (φ : ∀ v, Vec 2 → h v) (hφ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v)) :
    weightedJetNorm π q L ϖ r (fun v _ w z => orderedDerivative w (fun y => s y • φ v y) z) ≤
      ENNReal.ofReal (LeibConst L * B) *
        weightedJetNorm π (q + d) L ϖ r (fun v _ w z => orderedDerivative w (φ v) z) := by
  rw [cutoff_weightedJetNorm_eq_sum π q ϖ r (fun v y => s y • φ v y) L,
    cutoff_weightedJetNorm_eq_sum π (q + d) ϖ r φ L]
  set g : ℕ → ℝ≥0∞ := fun b =>
    ENNReal.ofReal (r ^ b / (b.factorial : ℝ)) * cutoffJetSize π (q + d) ϖ φ b with hg
  set T : ℝ≥0∞ := ∑ b ∈ Finset.range (L + 1), g b with hT
  have hrinv : 0 ≤ r⁻¹ := inv_nonneg.2 hr.le
  have hterm : ∀ a ∈ Finset.range (L + 1),
      ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) *
        cutoffJetSize π q ϖ (fun v y => s y • φ v y) a ≤ ENNReal.ofReal (4 ^ L * B) * T := by
    intro a ha
    have haL : a ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    have h1 := cutoffJetSize_smul_le π q d hrinv hB a hs
      (fun i hi z => hsb i (hi.trans haL) z) φ hφ
    refine (mul_le_mul' le_rfl h1).trans ?_
    rw [Finset.mul_sum]
    have h2 : ∀ i ∈ Finset.range (a + 1),
        ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) *
          (ENNReal.ofReal (4 ^ a * (a.choose i : ℝ) * B * r⁻¹ ^ i) *
            cutoffJetSize π (q + d) ϖ φ (a - i)) ≤ ENNReal.ofReal (4 ^ L * B) * g (a - i) := by
      intro i hi
      have hia : i ≤ a := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [hg, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have hfa : (0 : ℝ) < a.factorial := by exact_mod_cast Nat.factorial_pos a
      have hfi : (1 : ℝ) ≤ i.factorial := by exact_mod_cast Nat.factorial_pos i
      have hfai : (0 : ℝ) < (a - i).factorial := by exact_mod_cast Nat.factorial_pos (a - i)
      have hch : (a.choose i : ℝ) * i.factorial * (a - i).factorial = a.factorial := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hia
      have hpow : r ^ a * r⁻¹ ^ i = r ^ (a - i) := by
        rw [← pow_sub_mul_pow r hia, mul_assoc, ← mul_pow, mul_inv_cancel₀ hr.ne', one_pow,
          mul_one]
      have h4 : (4 : ℝ) ^ a ≤ 4 ^ L := pow_le_pow_right₀ (by norm_num) haL
      have hra : (0 : ℝ) ≤ r ^ (a - i) := pow_nonneg hr.le _
      rw [div_mul_eq_mul_div, div_le_iff₀ hfa, ← hch]
      calc r ^ a * (4 ^ a * (a.choose i : ℝ) * B * r⁻¹ ^ i)
          = 4 ^ a * ((a.choose i : ℝ) * B * r ^ (a - i)) := by rw [← hpow]; ring
        _ ≤ 4 ^ L * ((a.choose i : ℝ) * B * r ^ (a - i)) :=
            mul_le_mul_of_nonneg_right h4
              (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) hra)
        _ = 4 ^ L * B * r ^ (a - i) * (a.choose i : ℝ) * 1 := by ring
        _ ≤ 4 ^ L * B * r ^ (a - i) * (a.choose i : ℝ) * i.factorial :=
            mul_le_mul_of_nonneg_left hfi (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hB)
              hra) (Nat.cast_nonneg _))
        _ = 4 ^ L * B * (r ^ (a - i) / ((a - i).factorial : ℝ)) *
              ((a.choose i : ℝ) * i.factorial * (a - i).factorial) := by
            field_simp
    refine (Finset.sum_le_sum h2).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul' le_rfl ?_
    have hrefl : ∑ i ∈ Finset.range (a + 1), g (a - i) = ∑ b ∈ Finset.range (a + 1), g b := by
      have := Finset.sum_range_reflect g (a + 1)
      simpa only [Nat.add_sub_cancel] using this
    rw [hrefl, hT]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ haL))
  calc ∑ a ∈ Finset.range (L + 1), ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) *
        cutoffJetSize π q ϖ (fun v y => s y • φ v y) a
      ≤ ∑ _a ∈ Finset.range (L + 1), ENNReal.ofReal (4 ^ L * B) * T := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (LeibConst L * B) * T := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
        congr 1
        rw [show ((L + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((L + 1 : ℕ) : ℝ) from
          (ENNReal.ofReal_natCast _).symm, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        unfold LeibConst
        push_cast
        ring

end Family

section Multipliers

/-- The fixed bump: `1` on the sup-ball of radius `1`, `0` outside the sup-ball of radius `2`. -/
def Bump : ContDiffBump (0 : Vec 2) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The spatial cutoff at radius `R`: `1` for `‖z‖ ≤ R`, `0` for `‖z‖ ≥ 2R`. -/
def spatialCutoff (R : ℝ) (z : Vec 2) : ℝ := Bump (R⁻¹ • z)

theorem Bump_contDiff : ContDiff ℝ (⊤ : ℕ∞) (Bump : Vec 2 → ℝ) := Bump.contDiff

theorem Cut_contDiff (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (spatialCutoff R) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec 2 => Bump (R⁻¹ • z))
  exact Bump_contDiff.comp (contDiff_id.const_smul R⁻¹)

theorem Cut_nonneg (R : ℝ) (z : Vec 2) : 0 ≤ spatialCutoff R z := Bump.nonneg

theorem Cut_le_one (R : ℝ) (z : Vec 2) : spatialCutoff R z ≤ 1 := Bump.le_one

theorem Cut_eq_one {R : ℝ} (hR : 0 < R) {z : Vec 2} (hz : ‖z‖ ≤ R) : spatialCutoff R z = 1 := by
  unfold spatialCutoff
  refine Bump.one_of_mem_closedBall ?_
  rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR]
  change R⁻¹ * ‖z‖ ≤ 1
  rw [inv_mul_le_iff₀ hR, mul_one]
  exact hz

theorem Cut_eq_zero {R : ℝ} (hR : 0 < R) {z : Vec 2} (hz : 2 * R ≤ ‖z‖) : spatialCutoff R z = 0 := by
  unfold spatialCutoff
  refine Bump.zero_of_le_dist ?_
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR]
  change 2 ≤ R⁻¹ * ‖z‖
  rw [le_inv_mul_iff₀ hR]
  linarith

theorem Cut_hasCompactSupport {R : ℝ} (hR : 0 < R) : HasCompactSupport (spatialCutoff R) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Vec 2) (2 * R)) fun z hz => ?_
  rw [mem_closedBall_zero_iff]
  by_contra hcon
  exact hz (Cut_eq_zero hR (not_le.1 hcon).le)

/-- A bound of the derivatives of the fixed bump up to order `L`. -/
def CutB (L : ℕ) : ℝ :=
  Classical.choose (exists_iteratedFDeriv_bound Bump_contDiff Bump.hasCompactSupport L)

theorem CutB_nonneg (L : ℕ) : 0 ≤ CutB L :=
  (Classical.choose_spec
    (exists_iteratedFDeriv_bound Bump_contDiff Bump.hasCompactSupport L)).1

/-- The derivatives of the cutoff at radius `R ≥ r` at the scale `r`. -/
theorem Cut_iteratedFDeriv_le (L : ℕ) {R r : ℝ} (ϖ : ℝ) (hr : 0 < r) (hrR : r ≤ R) {i : ℕ}
    (hi : i ≤ L) (z : Vec 2) :
    ‖iteratedFDeriv ℝ i (spatialCutoff R) z‖ ≤
      CutB L * r⁻¹ ^ i * cutoffBracket ϖ z ^ (((0 : ℕ) : ℝ) / 2) := by
  have hb := (Classical.choose_spec
    (exists_iteratedFDeriv_bound Bump_contDiff Bump.hasCompactSupport L)).2 i hi (R⁻¹ • z)
  have hR : 0 < R := hr.trans_le hrR
  have h1 := norm_iteratedFDeriv_scaled_le Bump_contDiff R⁻¹ i z
  rw [Nat.cast_zero, zero_div, Real.rpow_zero, mul_one]
  refine h1.trans ?_
  rw [abs_of_pos (inv_pos.2 hR)]
  exact mul_le_mul hb (pow_le_pow_left₀ (inv_nonneg.2 hR.le) (inv_anti₀ hr hrR) i)
    (by positivity) (CutB_nonneg L)

/-- The scaled coordinate `ϖ z_i` as a continuous linear form. -/
def Coord (ϖ : ℝ) (i : Fin 2) : Vec 2 →L[ℝ] ℝ := ϖ • ContinuousLinearMap.proj i

theorem Coord_apply (ϖ : ℝ) (i : Fin 2) (z : Vec 2) : Coord ϖ i z = ϖ * z i := by
  simp [Coord]

/-- The derivatives of the scaled coordinate, at a scale `r` with `ϖ ≤ r⁻¹`. -/
theorem Coord_iteratedFDeriv_le {ϖ r : ℝ} (hϖ : 0 ≤ ϖ) (hr : 0 < r) (hϖr : ϖ ≤ r⁻¹)
    (i : Fin 2) (j : ℕ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ j (Coord ϖ i) z‖ ≤
      1 * r⁻¹ ^ j * cutoffBracket ϖ z ^ (((1 : ℕ) : ℝ) / 2) := by
  have hbr1 : 1 ≤ cutoffBracket ϖ z ^ (((1 : ℕ) : ℝ) / 2) :=
    Real.one_le_rpow (cutoffBracket_one_le ϖ z) (by norm_num)
  match j with
  | 0 =>
    rw [norm_iteratedFDeriv_zero, pow_zero, mul_one, one_mul, Coord_apply, Real.norm_eq_abs,
      Nat.cast_one, ← Real.sqrt_eq_rpow]
    refine Real.abs_le_sqrt ?_
    unfold cutoffBracket
    have h0 : z i ^ 2 ≤ z 0 ^ 2 + z 1 ^ 2 := by
      fin_cases i
      · exact le_add_of_nonneg_right (sq_nonneg _)
      · exact le_add_of_nonneg_left (sq_nonneg _)
    have h1 := mul_le_mul_of_nonneg_left h0 (sq_nonneg ϖ)
    nlinarith [h1]
  | 1 =>
    rw [norm_iteratedFDeriv_one, (Coord ϖ i).fderiv, pow_one, one_mul]
    have hn : ‖Coord ϖ i‖ ≤ ϖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ hϖ fun y => ?_
      rw [Coord_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hϖ]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm y i) hϖ
    exact (hn.trans hϖr).trans (le_mul_of_one_le_right (inv_nonneg.2 hr.le) hbr1)
  | j + 2 =>
    have hfd : fderiv ℝ (Coord ϖ i) = fun _ => Coord ϖ i := by
      funext y
      exact (Coord ϖ i).fderiv
    rw [← norm_iteratedFDeriv_fderiv, hfd, iteratedFDeriv_succ_const]
    simp only [Pi.zero_apply, norm_zero]
    have : 0 ≤ r⁻¹ := inv_nonneg.2 hr.le
    positivity

end Multipliers

section Tests

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The constant of the spatial cutoff. -/
def CutConst (L : ℕ) : ℝ := LeibConst L * CutB L + 1

theorem CutConst_pos (L : ℕ) : 0 < CutConst L := by
  unfold CutConst
  have := mul_nonneg (LeibConst_pos L).le (CutB_nonneg L)
  linarith

/-- **A spatial cutoff at radius `R ≥ r` is bounded on the weighted jet norm.** -/
theorem weightedJetNorm_cut_le (π : ι → ℝ) (q : ℝ) (L : ℕ) (ϖ : ℝ) {r R : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) (φ : ∀ v, Vec 2 → h v) (hφ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v)) :
    weightedJetNorm π q L ϖ r
        (fun v _ w z => orderedDerivative w (fun y => spatialCutoff R y • φ v y) z) ≤
      ENNReal.ofReal (CutConst L) *
        weightedJetNorm π q L ϖ r (fun v _ w z => orderedDerivative w (φ v) z) := by
  have h := weightedJetNorm_smul_le π q 0 L hr (CutB_nonneg L) (Cut_contDiff R)
    (fun i hi z => Cut_iteratedFDeriv_le L ϖ hr hrR hi z) φ hφ
  rw [Nat.cast_zero, add_zero] at h
  refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  unfold CutConst
  linarith

/-- **A scaled coordinate costs one power of the weight.** -/
theorem weightedJetNorm_coord_le (π : ι → ℝ) (q : ℝ) (L : ℕ) {ϖ r : ℝ} (hϖ : 0 ≤ ϖ)
    (hr : 0 < r) (hϖr : ϖ ≤ r⁻¹) (i : Fin 2) (φ : ∀ v, Vec 2 → h v)
    (hφ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v)) :
    weightedJetNorm π q L ϖ r
        (fun v _ w z => orderedDerivative w (fun y => (ϖ * y i) • φ v y) z) ≤
      ENNReal.ofReal (LeibConst L) *
        weightedJetNorm π (q + 1) L ϖ r (fun v _ w z => orderedDerivative w (φ v) z) := by
  have h := weightedJetNorm_smul_le π q 1 L hr zero_le_one (Coord ϖ i).contDiff
    (fun j _ z => Coord_iteratedFDeriv_le hϖ hr hϖr i j z) φ hφ
  simpa only [Coord_apply, mul_one, Nat.cast_one] using h

/-- **A word monomial `ϖ^j z^w` costs `j` powers of the weight.** -/
theorem weightedJetNorm_monomial_le (π : ι → ℝ) (L : ℕ) {ϖ r : ℝ} (hϖ : 0 ≤ ϖ) (hr : 0 < r)
    (hϖr : ϖ ≤ r⁻¹) : ∀ (j : ℕ) (w : DerivativeWord2 j) (q : ℝ) (φ : ∀ v, Vec 2 → h v),
    (∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v)) →
    weightedJetNorm π q L ϖ r
        (fun v _ u z => orderedDerivative u (fun y => (ϖ ^ j * wordMonomial w y) • φ v y) z) ≤
      ENNReal.ofReal (LeibConst L ^ j) *
        weightedJetNorm π (q + j) L ϖ r (fun v _ u z => orderedDerivative u (φ v) z)
  | 0, w, q, φ, _ => by
    have he : ∀ v, (fun y : Vec 2 => (ϖ ^ 0 * wordMonomial w y) • φ v y) = φ v := by
      intro v
      funext y
      simp [wordMonomial]
    simp only [he]
    rw [pow_zero, ENNReal.ofReal_one, one_mul, Nat.cast_zero, add_zero]
  | j + 1, w, q, φ, hφ => by
    set w' : DerivativeWord2 j := fun i : Fin j => w i.castSucc with hw'
    set ψ : ∀ v, Vec 2 → h v := fun v y => (ϖ ^ j * wordMonomial w' y) • φ v y with hψ
    have hψs : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (ψ v) := fun v =>
      (contDiff_const.mul (wordMonomial_contDiff w')).smul (hφ v)
    have he : ∀ v, (fun y : Vec 2 => (ϖ ^ (j + 1) * wordMonomial w y) • φ v y) =
        fun y => (ϖ * y (w (Fin.last j))) • ψ v y := by
      intro v
      funext y
      rw [hψ, wordMonomial_succ, smul_smul]
      congr 1
      ring
    simp only [he]
    refine (weightedJetNorm_coord_le π q L hϖ hr hϖr (w (Fin.last j)) ψ hψs).trans ?_
    refine (mul_le_mul' le_rfl (weightedJetNorm_monomial_le π L hϖ hr hϖr j w' (q + 1) φ
      hφ)).trans (le_of_eq ?_)
    rw [← mul_assoc, ← ENNReal.ofReal_mul (LeibConst_pos L).le, pow_succ',
      show q + 1 + (j : ℝ) = q + ((j + 1 : ℕ) : ℝ) by push_cast; ring]

omit [∀ i, NormedSpace ℝ (h i)] in
/-- The weighted jet norm of a continuous jet array increases with the weight exponent. -/
theorem weightedJetNorm_weight_mono (π : ι → ℝ) {q q' : ℝ} (hq : q ≤ q') (L : ℕ) (ϖ r : ℝ)
    (J : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v) (hJ : ∀ v a w, Continuous (J v a w)) :
    weightedJetNorm π q L ϖ r J ≤ weightedJetNorm π q' L ϖ r J := by
  unfold weightedJetNorm
  refine Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl ?_
  refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun v _ => mul_le_mul' le_rfl ?_)
    (by norm_num)
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  have hcont : Continuous fun z : Vec 2 => Real.sqrt (∑ w, ‖J v a w z‖ ^ 2) :=
    Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => (hJ v a w).norm.pow 2)
  refine eLpNorm_mono_real ((weight_continuous ϖ q).mul hcont).aestronglyMeasurable fun z => ?_
  have hb : 1 ≤ 1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) :=
    le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
    (Real.sqrt_nonneg _))]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hb (by linarith)) (Real.sqrt_nonneg _)

end Tests

section Negative

end Negative

end AVRegularity.CycleWords.Seam
end
