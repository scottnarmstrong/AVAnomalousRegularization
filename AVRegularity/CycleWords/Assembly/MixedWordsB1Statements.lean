-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.SmoothPullbackDifference
public import AVRegularity.Definitions.CycleWords.ScalarPackage
public import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The retained map of a word block

In the word statement (Lemma 11.12 of the paper), the chronological word `𝒵f` of a block has
a cell-constant retained amplitude `a[f]` and its ordinary Fourier reconstruction `𝒫f`. The map `𝒫`
is defined here once, on plane functions, for `cycle_mixed_words` and for the future kernel
`K₊ = 𝒫₊ ∘ P₀` of `cycle_seam`.

* On a compactly supported datum that starts a chain of `IsPlaneChain` (`wordChainData`, descending
  slots), `𝒫f` is the Fourier cutoff `χ_lo(D/√η)χ_lo(4ξ_*D/π)` of the endpoint `𝒵f(S)`: its
  amplitude is `χ P₀Ẑf(S)`, the cell mean of the low Bloch fibres of the word. The second factor is
  one on the support of the first when `2ξ_*√η ≤ π/4`; it keeps the retained band inside the
  Brillouin zone in every case, so that nothing beyond the package constants is assumed.
* The map is linear, depends only on the a.e. class of its argument, has values smooth of every
  order with Fourier support in `|θ| ≤ 2ξ_*√η`, and is bounded from the moment norm of order `∑K_i`
  into `L²` (`IsRetainedMap`).

These properties determine the map on every measurable datum of finite moment norm of order `∑K_i`,
since compactly supported data are dense there and start chains (`CompactDensityStatement`,
`CompactChainExistenceStatement`). `retainedMap`
is the `Classical.choose` of such a map when one exists and `0` otherwise; the statement's `P` is
`retainedPlaneMap`, its composition with the value of the carrier. -/

/-- The cutoff `χ_lo` of the word statement: smooth, even, one on `|ξ| ≤ ξ_*`, zero on
`|ξ| ≥ 2ξ_*`. -/
structure IsLowCutoff (K : ScalarConstants) (χlo : Vec 2 → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) χlo
  even : ∀ ξ, χlo (-ξ) = χlo ξ
  one : ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ K.ξlo → χlo ξ = 1
  supp : ∀ ξ, 2 * K.ξlo ≤ Real.sqrt (vecDot ξ ξ) → χlo ξ = 0

/-- The retained cutoff in the cell frequency `θ = √η ξ`: `χ_lo(θ/√η) χ_lo(4ξ_*θ/π)`. -/
def retainedCutoff (K : ScalarConstants) (η : ℝ) (χlo : Vec 2 → ℝ) (θ : Vec 2) : ℝ :=
  χlo ((Real.sqrt η)⁻¹ • θ) * χlo ((4 * K.ξlo / Real.pi) • θ)

/-- The premises of a word block of `cycle_mixed_words` after its orders: the maximal order,
contrast and duration, the cell problem (metric below the threshold `g₁`), the letters at fast
reserve `J` and depth `H`, transverse on the orientation regions and fast independent on the quiet
times. The scalar package
is a separate datum. -/
structure IsWordBlock (K : ScalarConstants) (g₁ : ℝ) {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D Nw : ℕ} (H J : ℕ)
    (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D) (η S ηg t₀ ϖ : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ) (reg : BlockRegions) :
    Prop where
  hD : 2 ≤ D
  hπ : ∀ x, 0 < π x
  hη : 0 < η
  hη1 : η ≤ 1
  hS : 1 ≤ S
  hηg : 0 < ηg
  hηg1 : ηg ≤ 1
  hϖ : ϖ = Real.sqrt (η / S)
  hGm : IsCellMetric (fun t _ => G t)
  hv : IsCellDrift v
  hv0 : ∀ t (k : Fin 2), cellMean (fun x => (v t x k : ℂ)) = 0
  hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)
  hvw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw
  hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj j
  hg0 : 0 ≤ g
  hg : g ≤ K.g0
  hg₁ : g ≤ g₁
  hGn : IsMetricNearIdentity (fun t _ => G t) g
  hlet : ∀ i, IsCycleLetter π (letters i) (Set.Icc t₀ (t₀ + S) ×ˢ Set.univ) J H
  htrans : ∀ i, IsTransverseOnPulses (letters i).edge
    (fun p : Fin reg.P => Set.Icc (reg.lo p) (reg.hi p)) reg.orient
  hquiet : ∀ i, IsQuietOn (letters i).edge v reg.quiet
  hmeas : ∀ i x y o, ∀ γ ∈ (letters i).edge x y o, ∀ α X z, Measurable fun t => γ.coeff α t X z

/-- A smaller threshold gives a block of the larger one. -/
theorem IsWordBlock.mono {K : ScalarConstants} {g₁ g₂ : ℝ} {ι : Type*} [Fintype ι]
    {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D Nw H J : ℕ}
    {π : ι → ℝ} {letters : Fin Nw → CycleLetter ι h D} {η S ηg t₀ ϖ : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {g : ℝ} {reg : BlockRegions}
    (hB : IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg) (h12 : g₁ ≤ g₂) :
    IsWordBlock K g₂ H J π letters η S ηg t₀ ϖ G v g reg :=
  { hB with hg₁ := hB.hg₁.trans h12 }

/-- A block is well buffered at rate `c` and power `Q` when the quiet-switching factor
`(1 + B_p) P_e^Q (1 + S)^Q e^{-c D_q}` is at most one. On such blocks the quiet-switching error of
the retained word is absorbed into the constants of the `P_e`-free bounds; on the others the discard
is paid by the full-field bound. -/
def IsWellBuffered (c : ℝ) (Q : ℕ) (η S : ℝ) (reg : BlockRegions) : Prop :=
  (1 + (reg.joins : ℝ)) * peFactor η ^ Q * (1 + S) ^ Q * Real.exp (-c * reg.buffer) ≤ 1

/-- Well-bufferedness at a smaller rate and a larger power implies it at the larger rate and the
smaller power. -/
theorem IsWellBuffered.mono {c c' : ℝ} {Q Q' : ℕ} {η S : ℝ} {reg : BlockRegions}
    (hw : IsWellBuffered c Q η S reg) (hc : c ≤ c') (hQ : Q' ≤ Q) (hS : 0 ≤ S)
    (hbuf : 0 ≤ reg.buffer) : IsWellBuffered c' Q' η S reg := by
  unfold IsWellBuffered at hw ⊢
  have hP : 1 ≤ peFactor η := by
    unfold peFactor
    have := inv_nonneg.2 (Real.sqrt_nonneg η)
    linarith
  have hS1 : (1 : ℝ) ≤ 1 + S := by linarith
  have hj : (0 : ℝ) ≤ 1 + (reg.joins : ℝ) := by positivity
  refine le_trans ?_ hw
  have h1 : peFactor η ^ Q' ≤ peFactor η ^ Q := pow_le_pow_right₀ hP hQ
  have h2 : (1 + S) ^ Q' ≤ (1 + S) ^ Q := pow_le_pow_right₀ hS1 hQ
  have h3 : Real.exp (-c' * reg.buffer) ≤ Real.exp (-c * reg.buffer) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hp0 : 0 ≤ peFactor η ^ Q' := by positivity
  have hs0 : 0 ≤ (1 + S) ^ Q' := by positivity
  calc (1 + (reg.joins : ℝ)) * peFactor η ^ Q' * (1 + S) ^ Q' * Real.exp (-c' * reg.buffer)
      ≤ (1 + (reg.joins : ℝ)) * peFactor η ^ Q * (1 + S) ^ Q * Real.exp (-c * reg.buffer) := by
        gcongr

/-- Descending slots of a word chain: an edge of order `o` of letter `j`, from component `y` of
level `j` to component `x` of level `j + 1`, has `κ_{j+1,x} + o ≤ κ_{j,y} + 2`. -/
def IsWordSlots {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D Nw : ℕ} (letters : Fin Nw → CycleLetter ι h D)
    (κ : Fin (Nw + 1) → ι → ℕ) : Prop :=
  ∀ (j : Fin Nw) x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
    κ j.succ x + o.1 ≤ κ j.castSucc y + 2

/-- The base slots `κ_l = ∑_{i ≥ l} d_i`: descending, and within every reserve of the statement. -/
def wordBaseSlots {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D Nw : ℕ} (letters : Fin Nw → CycleLetter ι h D) :
    Fin (Nw + 1) → ι → ℕ :=
  fun l _ => ∑ i : Fin Nw, if l.val ≤ i.val then (letters i).order else 0

/-- A datum whose components are a.e. equal to smooth compactly supported functions. -/
def IsCompactDatum {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {κ0 : ι → ℕ} (f : ∀ x, PlaneHk Set.univ (κ0 x) (h x)) : Prop :=
  ∀ x, ∃ φ : Vec 2 → h x, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
    planeValue (f x) =ᵐ[volume] φ

/-- Scalar multiples of carrier elements have the expected value almost everywhere. -/
theorem planeValue_smul_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ} (c : ℝ)
    (U : PlaneHk Set.univ K E) :
    planeValue (c • U) =ᵐ[volume] fun z => c • planeValue U z := by
  let R := Weighted.planeJetReadoutOperator (E := E) K ⟨⟨0, Nat.succ_pos K⟩, fun i => Fin.elim0 i⟩
  have hsm := Lp.coeFn_smul c (R U)
  rw [← map_smul] at hsm
  filter_upwards [(planeJetLpReadout_ae (Nat.zero_le K) (c • U) (fun i => Fin.elim0 i)).symm, hsm,
    planeJetLpReadout_ae (Nat.zero_le K) U (fun i => Fin.elim0 i)] with z hz hs hu
  exact hz.trans (hs.trans (congrArg (c • ·) hu))

section Retained

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

/-- `R` is a retained map of the block: linear, a.e. invariant, valued in smooth functions of
Fourier support `|θ| ≤ 2ξ_*√η`, equal to the retained cutoff of the word endpoint on every compactly
supported chain datum (any descending slots), and bounded on measurable functions from the moment
norm of order `∑K_i` into `L²`. Compactly supported data are dense in that moment norm, so these
properties determine `R` on every measurable function of finite moment norm. -/
structure IsRetainedMap (K : ScalarConstants) (χlo : Vec 2 → ℝ) (π : ι → ℝ)
    (letters : Fin Nw → CycleLetter ι h D) (η S ηg t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (X₀ : Vec 2) (R : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x)) :
    Prop where
  band : ∀ g x, (∀ M : ℕ, ContDiff ℝ M (R g x)) ∧
    HasFourierSupportIn (R g x) (2 * K.ξlo * Real.sqrt η)
  congr : ∀ g g' : ∀ x, Vec 2 → h x, (∀ x, g x =ᵐ[volume] g' x) → R g = R g'
  chain : ∀ (κ : Fin (Nw + 1) → ι → ℕ), IsWordSlots letters κ →
    ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
      (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
      (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
      IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
      IsCompactDatum f →
      R (fun x => planeValue (f x)) = fun x =>
        fourierCutoff (retainedCutoff K η χlo) (planeValue (u (Fin.last Nw) x (t₀ + S)))
  bounded : ∃ C : ℝ, 0 < C ∧ ∀ g : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (g x) volume) →
    momentNorm π 0 1 (R g) ≤
      ENNReal.ofReal C * momentNorm π (wordReserveN 0 fun i => (letters i).slow) ϖ g

open Classical in
/-- The retained map of the block: a retained map if one exists, `0` otherwise. -/
def retainedMap (K : ScalarConstants) (χlo : Vec 2 → ℝ) (π : ι → ℝ)
    (letters : Fin Nw → CycleLetter ι h D) (η S ηg t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (X₀ : Vec 2) : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x) :=
  if hR : ∃ R, IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R then hR.choose else 0

theorem retainedMap_spec {K : ScalarConstants} {χlo : Vec 2 → ℝ} {π : ι → ℝ}
    {letters : Fin Nw → CycleLetter ι h D} {η S ηg t₀ ϖ : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {X₀ : Vec 2}
    (hR : ∃ R, IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R) :
    IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀
      (retainedMap K χlo π letters η S ηg t₀ ϖ G v X₀) := by
  unfold retainedMap
  split
  · next h => exact h.choose_spec
  · next h => exact absurd hR h

theorem retainedMap_eq_zero {K : ScalarConstants} {χlo : Vec 2 → ℝ} {π : ι → ℝ}
    {letters : Fin Nw → CycleLetter ι h D} {η S ηg t₀ ϖ : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {X₀ : Vec 2}
    (hR : ¬∃ R, IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R) :
    retainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ = 0 := by
  unfold retainedMap
  split
  · next h => exact absurd h hR
  · rfl

/-- The retained map composed with the value of the carrier, on data with slots `κ0`. -/
def retainedPlaneMap (K : ScalarConstants) (χlo : Vec 2 → ℝ) (π : ι → ℝ)
    (letters : Fin Nw → CycleLetter ι h D) (η S ηg t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (X₀ : Vec 2) (κ0 : ι → ℕ) :
    (∀ x, PlaneHk Set.univ (κ0 x) (h x)) →ₗ[ℝ] (∀ x, Vec 2 → h x) where
  toFun f := retainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ (fun x => planeValue (f x))
  map_add' f f' := by
    by_cases hR : ∃ R, IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R
    · rw [← map_add]
      exact (retainedMap_spec hR).congr _ _ fun x => planeValue_add_ae (f x) (f' x)
    · simp only [retainedMap_eq_zero hR, LinearMap.zero_apply, add_zero]
  map_smul' c f := by
    by_cases hR : ∃ R, IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R
    · rw [RingHom.id_apply, ← map_smul]
      exact (retainedMap_spec hR).congr _ _ fun x => planeValue_smul_ae c (f x)
    · simp only [retainedMap_eq_zero hR, LinearMap.zero_apply, smul_zero]

end Retained

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The statements of `cycle_mixed_words`

Each statement fixes the package constants `K`, then a metric threshold `g₁`, the cutoff, the
orders and the constants, and quantifies over word blocks (`IsWordBlock`, a scalar package, a
fast reserve `J` at least the one the statement needs). The statements about the retained map hold
for every retained map of the block (`IsRetainedMap`).

* `RetainedMapExistsStatement`: every well-buffered block has a retained map.
* `RetainedModelJetsStatement`: the weighted jet bound of the model on well-buffered blocks.
* `ChainDiscardStatement`: the discard bound for the retained map and every chain
  datum with `n` moments.
* `RetainedGaussianStatement`: the Gaussian amplitude bound at every frequency of the
  Brillouin zone, on well-buffered blocks, for data with `n + 2` moments.
* `ChainFullFieldStatement`: the full-field polynomial bound of the endpoint.

On a well-buffered block (`IsWellBuffered`) the quiet-switching error of the retained word is
absorbed into the `P_e`-free constants, and the statement's `P` is the retained map. On the other
blocks `P = 0`: clauses 1, 2 and 4 are trivial, and the full-field bound pays the discard, whose
factor `(1 + B_p) e^{-cD_q} P_e^Q (1+S)^Q` is then at least one.

The reserves are those of the statement: `n = m + ∑K_i`, `K_* = K_f + n + ∑d_i + 2`,
`J_* = 2K_* + max d_i + 2`, `p = 4N_w + 2∑K_i + 2m + 4`. -/

universe u v

/-- **Existence.** Every word block has a retained map. -/
def RetainedMapExistsStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ χlo : Vec 2 → ℝ, IsLowCutoff K χlo →
  ∀ (Nw D H : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (c₁ : ℝ) (Q₁ : ℕ), 0 < c₁ ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D),
    (∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧ (letters i).positive = pos i) →
  ∀ (η S ηg t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions), ScalarPackage K η G v t₀ S ϖ reg →
    IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg →
    wordReserveJstar (wordReserveKstar 0 (wordReserveN 0 Ks) d) d ≤ J →
    IsWellBuffered c₁ Q₁ η S reg →
  ∀ X₀ : Vec 2, ∃ R, IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R

/-- **Model jets**: for every datum with `n` moments,
`∑_{j≤M} ‖⟨z/R⟩^m R^j D^j 𝒫f‖ ≤ C_M Θ_w ‖f‖_{D_n}` in the cell variables. -/
def RetainedModelJetsStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ χlo : Vec 2 → ℝ, IsLowCutoff K χlo →
  ∀ (Nw D H m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (CM : ℕ → ℝ) (c₁ : ℝ) (Q₁ : ℕ), (∀ M, 0 < CM M) ∧ 0 < c₁ ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D),
    (∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧ (letters i).positive = pos i) →
  ∀ (η S ηg t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions), ScalarPackage K η G v t₀ S ϖ reg →
    IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg →
    wordReserveJstar (wordReserveKstar 0 (wordReserveN m Ks) d) d ≤ J →
    IsWellBuffered c₁ Q₁ η S reg →
  ∀ (X₀ : Vec 2) (R : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x)),
    IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R →
  ∀ (M : ℕ) (F : ∀ x, Vec 2 → h x), (∀ x, AEStronglyMeasurable (F x) volume) →
    momentNorm π (wordReserveN m Ks) ϖ F < ⊤ →
    weightedJetNorm π (m : ℝ) M ϖ ϖ⁻¹ (fun x _ wd z => orderedDerivative wd (R F x) z) ≤
      ENNReal.ofReal (CM M * wordTheta ηg letters) * momentNorm π (wordReserveN m Ks) ϖ F

/-- **Discard**: on every chain with a datum of `n` moments, the
endpoint differs from `𝒫f` by `CΘ_w P_e^Q(1+S)^Q[e^{-cS} + (1+B_p)e^{-cD_q}]‖f‖_{D_n}` in the
molecular output norm at scale `ρ_* ≤ C_out e`. -/
def ChainDiscardStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ χlo : Vec 2 → ℝ, IsLowCutoff K χlo →
  ∀ (Nw D H Kf m : ℕ) (Cout : ℝ), 0 < Cout → ∀ (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (C c : ℝ) (Q : ℕ), 0 < C ∧ 0 < c ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D),
    (∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧ (letters i).positive = pos i) →
  ∀ (η S ηg rstar t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions), ScalarPackage K η G v t₀ S ϖ reg →
    IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg →
    wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d ≤ J →
    0 < rstar → rstar ≤ Cout →
  ∀ (X₀ : Vec 2) (R : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x)),
    IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R →
  ∀ κ : Fin (Nw + 1) → ι → ℕ, (∀ x, Kf ≤ κ (Fin.last Nw) x) → IsWordSlots letters κ →
  ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
    momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) < ⊤ →
    IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
    jetOutputNorm π m Kf ϖ rstar
        (fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
          orderedDerivative wd (R (fun x' => planeValue (f x')) x) z) ≤
      ENNReal.ofReal (C * wordTheta ηg letters * peFactor η ^ Q * (1 + S) ^ Q *
          (Real.exp (-c * S) + (1 + reg.joins) * Real.exp (-c * reg.buffer))) *
        momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x))

/-- **Full-field bound.** The molecular output norm of the word endpoint is bounded by
`CΘ_w P_e^Q (1+S)^Q ‖f‖_{D_n}` (the full field of Step 2 of the proof of Lemma 11.12 of the
paper: polynomial propagation in negative and positive spaces, smoothing across a source-free
gap). -/
def ChainFullFieldStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D H Kf m : ℕ) (Cout : ℝ), 0 < Cout → ∀ (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D),
    (∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧ (letters i).positive = pos i) →
  ∀ (η S ηg rstar t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions), ScalarPackage K η G v t₀ S ϖ reg →
    IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg →
    wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d ≤ J →
    0 < rstar → rstar ≤ Cout →
  ∀ (X₀ : Vec 2) (κ : Fin (Nw + 1) → ι → ℕ), (∀ x, Kf ≤ κ (Fin.last Nw) x) →
    IsWordSlots letters κ →
  ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
    momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) < ⊤ →
    IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
    jetOutputNorm π m Kf ϖ rstar
        (fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z) ≤
      ENNReal.ofReal (C * wordTheta ηg letters * peFactor η ^ Q * (1 + S) ^ Q) *
        momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x))

/-- **Gaussian amplitude**: for data with `n + 2` moments the retained
amplitude pair of `𝒫f` is `C^m`, even/odd, and at every `θ` of the Brillouin zone
`∑_{|β|≤m}‖δ^β a‖/β! ≤ CΘ_w(1+x)^p e^{-cx²} ∑_{|α|≤n}‖δ^α(χ_lo f̂)‖/α!`, `x = |θ|/ϖ`. The
retained map is built with the cutoff `χ_lo^{n+1}` (again a low cutoff): each frequency derivative
reaching the datum needs a factor `χ_lo`. -/
def RetainedGaussianStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ χlo : Vec 2 → ℝ, IsLowCutoff K χlo →
  ∀ (Nw D H m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (CGa cGa c₁ : ℝ) (Q₁ : ℕ), 0 < CGa ∧ 0 < cGa ∧ 0 < c₁ ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D),
    (∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧ (letters i).positive = pos i) →
  ∀ (η S ηg t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions), ScalarPackage K η G v t₀ S ϖ reg →
    IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg →
    wordReserveJstar (wordReserveKstar 0 (wordReserveN m Ks) d) d ≤ J →
    IsWellBuffered c₁ Q₁ η S reg →
  ∀ (X₀ : Vec 2) (R : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x)),
    IsRetainedMap K (fun ξ => χlo ξ ^ (wordReserveN m Ks + 1)) π letters η S ηg t₀ ϖ G v X₀ R →
  ∀ F : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (F x) volume) →
    momentNorm π (wordReserveN m Ks + 2) ϖ F < ⊤ →
    ∃ A B : ∀ x, Vec 2 → h x,
      (∀ x, IsRetainedAmplitude (R F x) (2 * K.ξlo * Real.sqrt η) (A x) (B x)) ∧
      (∀ x, ContDiff ℝ m (A x) ∧ ContDiff ℝ m (B x)) ∧
      (∀ x θ, A x (-θ) = A x θ ∧ B x (-θ) = -B x θ) ∧
      ∀ θ : Vec 2, (∀ i, |θ i| ≤ Real.pi) →
        amplitudeJetNorm π m ϖ A B θ ≤
          ENNReal.ofReal (CGa * wordTheta ηg letters *
              (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ wordReserveP m Ks *
              Real.exp (-cGa * (vecDot θ θ / ϖ ^ 2))) *
            ∑ α ∈ momentIndices (wordReserveN m Ks),
              ENNReal.ofReal (ϖ ^ (α.1 + α.2) /
                  ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
                blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α F θ

/-- The fast reserve is monotone in the output orders. -/
theorem wordReserveJstar_le {Nw : ℕ} (Kf Kf' m m' : ℕ) (Ks d : Fin Nw → ℕ) (hK : Kf ≤ Kf')
    (hm : m ≤ m') :
    wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d ≤
      wordReserveJstar (wordReserveKstar Kf' (wordReserveN m' Ks) d) d := by
  unfold wordReserveJstar wordReserveKstar wordReserveN
  omega

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The sub-statements of `ChainDiscardStatement`

`ChainDiscardStatement` is reduced (`chainDiscard_of_compact`) to the discard on compactly
supported smooth data and `ChainFullFieldStatement`, as at the end of Step 3 of the proof of
Lemma 11.12 of the paper, where compactly supported approximants and the full field extend the
bound to general data:

* `CompactDiscardStatement`: for a chain from a smooth compactly supported datum, the endpoint
  minus its retained cutoff (the complementary band of the endpoint) is bounded in the molecular
  output norm by `CΘ_w P_e^Q (1+S)^Q [e^{-cS} + (1+B_p) e^{-c D_q}] ‖f‖_{D_n}`. It does not mention
  the retained map: on compact data the retained map is the retained cutoff of the endpoint
  (`IsRetainedMap.chain`).

The extension: compact approximants of the datum (`CompactDensityStatement`) start chains at the
capped slots of the given chain (the existence statement, `cappedWordSlots`), the differences are
chains (`planeChainFrom_combination`) bounded by `ChainFullFieldStatement`, the retained map
converges with all its
derivatives pointwise (`retainedMap_orderedDerivative_tendsto`), and the molecular output norm is
lower semicontinuous (Fatou). -/

universe u v

/-- **Discard on compact data** (the discarded frequencies of Step 3 of the proof of Lemma 11.12
of the paper, on smooth compactly supported data: the complementary band by marks, `e^{-cS}`, and
the nonconstant endpoint across the terminal quiet stretch, `(1+B_p)e^{-cD_q}`). For a chain at
descending slots (endpoint slots at least `K_f`) from a smooth compactly supported datum, the
endpoint minus its retained cutoff is bounded in the molecular output norm at scale
`ρ_* ≤ C_out` by `CΘ_w P_e^Q (1+S)^Q [e^{-cS} + (1+B_p)e^{-c D_q}] ‖f‖_{D_n}`, `n = m + ∑K_i`.

With no letters (`N_w = 0`) the endpoint is the homogeneous solution `𝒰f`; its
complementary band decays by the marks and its nonconstant part across the terminal quiet buffer,
with `Θ_w = 1`. For `f = 0` the right side is `0`, so the statement includes the uniqueness of
plane chains from zero data (as `ChainDiscardStatement` and `ChainFullFieldStatement` do). For
`S = 1`, `e^{-cS} = e^{-c}`
is a constant and the bound is the full-field bound up to constants (no smoothing across a short
gap is needed). For `D_q = 0` the bound is the full-field bound times `1 + B_p`. The constants
`C, c, Q` depend on `K`, the cutoff, the shape `(N_w, D, H, K_f, m, d, K, pos)` and
`C_out`; not on `η, S, ηg`, the window, the regions or the datum. -/
def CompactDiscardStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ χlo : Vec 2 → ℝ, IsLowCutoff K χlo →
  ∀ (Nw D H Kf m : ℕ) (Cout : ℝ), 0 < Cout → ∀ (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (C c : ℝ) (Q : ℕ), 0 < C ∧ 0 < c ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D),
    (∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧ (letters i).positive = pos i) →
  ∀ (η S ηg rstar t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions), ScalarPackage K η G v t₀ S ϖ reg →
    IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg →
    wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d ≤ J →
    0 < rstar → rstar ≤ Cout →
  ∀ (X₀ : Vec 2) (κ : Fin (Nw + 1) → ι → ℕ), (∀ x, Kf ≤ κ (Fin.last Nw) x) →
    IsWordSlots letters κ →
  ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
    IsCompactDatum f →
    IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
    jetOutputNorm π m Kf ϖ rstar
        (fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
          orderedDerivative wd (fourierCutoff (retainedCutoff K η χlo)
            (planeValue (u (Fin.last Nw) x (t₀ + S)))) z) ≤
      ENNReal.ofReal (C * wordTheta ηg letters * peFactor η ^ Q * (1 + S) ^ Q *
          (Real.exp (-c * S) + (1 + reg.joins) * Real.exp (-c * reg.buffer))) *
        momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x))


/-- The zone factor `b(θ) = χ_lo(4ξ_lo θ/π)` of the retained cutoff: `1` on `|θ| ≤ π/4`, `0` on
`|θ| ≥ π/2`; `retainedCutoff K η χlo = χlo(·/√η) · zoneCutoff K χlo`. -/
def zoneCutoff (K : ScalarConstants) (χlo : Vec 2 → ℝ) (θ : Vec 2) : ℝ :=
  χlo ((4 * K.ξlo / Real.pi) • θ)

/-- **High plane frequencies across the terminal quiet stretch** (the high frequencies in Step 3
of the proof of Lemma 11.12 of the paper: the nonconstant endpoint is bounded by `Ce^{-cD_q}`
times the entrance moments, and the quiet stretch supplies every cell derivative). The window
ends with the quiet
stretch `(t₀ + S - D_q, t₀ + S]` (`cover`, `buffer_inside`), where the drift vanishes and the
letters are fast independent; the part of the endpoint outside the zone factor (plane
frequencies `|θ| ≥ π/4`: every nonconstant cell mode) is at most
`CΘ_w P_e^Q (1+S)^Q e^{-c D_q} ‖f‖_{D_n}` in the molecular output norm.

With no letters the endpoint is the homogeneous solution, whose modes `|θ| ≥ π/4` decay
like `e^{-c|θ|² D_q}` under the space-constant metric of the quiet stretch. For `D_q = 0` the bound
is the full-field bound. For `m = K_f = 0` this is an `L²` statement, and for `f = 0` it reads
`0 ≤ 0`. The constants `C, c, Q` depend on `K`, the cutoff, the shape and `C_out` only. -/
def QuietHighStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ χlo : Vec 2 → ℝ, IsLowCutoff K χlo →
  ∀ (Nw D H Kf m : ℕ) (Cout : ℝ), 0 < Cout → ∀ (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (C c : ℝ) (Q : ℕ), 0 < C ∧ 0 < c ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D),
    (∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧ (letters i).positive = pos i) →
  ∀ (η S ηg rstar t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions), ScalarPackage K η G v t₀ S ϖ reg →
    IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg →
    wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d ≤ J →
    0 < rstar → rstar ≤ Cout →
  ∀ (X₀ : Vec 2) (κ : Fin (Nw + 1) → ι → ℕ), (∀ x, Kf ≤ κ (Fin.last Nw) x) →
    IsWordSlots letters κ →
  ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
    IsCompactDatum f →
    IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
    jetOutputNorm π m Kf ϖ rstar
        (fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
          orderedDerivative wd (fourierCutoff (zoneCutoff K χlo)
            (planeValue (u (Fin.last Nw) x (t₀ + S)))) z) ≤
      ENNReal.ofReal (C * wordTheta ηg letters * peFactor η ^ Q * (1 + S) ^ Q *
          Real.exp (-c * reg.buffer)) *
        momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x))

/-- **The marks band** (the package's `high_marks`, `marks_count`, `marks_sep`, `contraction`).
Between the zone factor and the retained
cutoff lie the plane frequencies `ξ_lo √η ≤ |θ| ≤ π/2`, i.e. the constant Bloch mode at fibre
frequencies `ξ_lo ≤ |ξ|` inside the zone; there every mark of one orientation halves the fibre
`L²` norm, at least `c_adm S/θ_*` marks lie in the window and at most `N_w` meet the insertion
times, so this part of the endpoint is at most `CΘ_w P_e^Q (1+S)^Q e^{-cS} ‖f‖_{D_n}` in the
molecular output norm (frequency jets by holomorphic perturbation on a radius `c/(1+S)` and
Cauchy; differential losses on the short ends of the longest mark gap).

With no letters the homogeneous fibres at `|ξ| ≥ ξ_lo` are halved by each of the
`≥ c_adm S/θ_*` marks of one orientation, so they are `≤ 2^{-c S}`. For `S = 1` the bound is the
full-field bound up to constants. For `ξ_lo √η ≥ π/2` the band is empty and the left side is `0`,
and for `f = 0` the statement reads `0 ≤ 0`. The constants `C, c, Q` depend on `K`, the cutoff, the
shape and `C_out` only. -/
def MarksBandStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ χlo : Vec 2 → ℝ, IsLowCutoff K χlo →
  ∀ (Nw D H Kf m : ℕ) (Cout : ℝ), 0 < Cout → ∀ (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (C c : ℝ) (Q : ℕ), 0 < C ∧ 0 < c ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D),
    (∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧ (letters i).positive = pos i) →
  ∀ (η S ηg rstar t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions), ScalarPackage K η G v t₀ S ϖ reg →
    IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg →
    wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d ≤ J →
    0 < rstar → rstar ≤ Cout →
  ∀ (X₀ : Vec 2) (κ : Fin (Nw + 1) → ι → ℕ), (∀ x, Kf ≤ κ (Fin.last Nw) x) →
    IsWordSlots letters κ →
  ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
    IsCompactDatum f →
    IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
    jetOutputNorm π m Kf ϖ rstar
        (fun x _ wd z => orderedDerivative wd (fourierCutoff (zoneCutoff K χlo)
            (planeValue (u (Fin.last Nw) x (t₀ + S)))) z -
          orderedDerivative wd (fourierCutoff (retainedCutoff K η χlo)
            (planeValue (u (Fin.last Nw) x (t₀ + S)))) z) ≤
      ENNReal.ofReal (C * wordTheta ηg letters * peFactor η ^ Q * (1 + S) ^ Q *
          Real.exp (-c * S)) *
        momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x))

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # Leaf ingredients of `cycle_mixed_words`

Three of the four ingredient statements of `cycle_mixed_words` (`RetainedMapExistsStatement`,
`RetainedModelJetsStatement`, `RetainedGaussianStatement`: existence of the retained map, model
jets, Gaussian amplitude) reduce to the following leaves; the fourth, `ChainDiscardStatement`, is
reduced separately.

* `ChainCombinationStatement`: linear combinations of chains at two descending slot
  assignments are chains at their minimum (truncation and linearity of the weak solution class).
* `CompactChainExistenceStatement`: a compactly supported datum starts a chain at the base
  slots `wordBaseSlots` (from `cycle_mixed_words_exists`).
* `CompactDensityStatement`: smooth compactly supported functions lift to every carrier and
  are dense in every finite moment norm of a measurable field.
* `AmplitudePlancherelStatement`: smoothness, derivative bounds and Plancherel for functions
  with an amplitude pair on a ball.
* `CompactChainGaussianStatement`: the Gaussian amplitude bound for compactly supported chain
  data, with the explicit amplitudes `retainedCosAmplitude`, `retainedSinAmplitude` of the endpoint.
* `GaussianPlancherelStatement`: a pointwise Gaussian amplitude bound gives the weighted jets
  of the reconstruction (Plancherel, the moment identity of the Bloch transform, Gaussian
  absorption).
* `BlochFibreContinuityStatement`: under `n + 2` moments the Bloch fibre derivative norms are
  continuous in the datum, uniformly in the frequency.

For a compactly supported datum the word endpoint has all moments, so its cosine and sine transforms
are Lebesgue integrals, and the amplitudes of its retained cutoff are explicit. -/

section
universe u v

/-- The cosine amplitude of the retained cutoff of `e`: `(2π)⁻² χ(θ) ∫ cos(θ·y) e(y) dy`. -/
def retainedCosAmplitude {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ScalarConstants) (η : ℝ) (χlo : Vec 2 → ℝ) (e : Vec 2 → E) (θ : Vec 2) : E :=
  ((2 * Real.pi)⁻¹ ^ 2 * retainedCutoff K η χlo θ) • ∫ y, Real.cos (vecDot θ y) • e y

/-- The sine amplitude of the retained cutoff of `e`: `(2π)⁻² χ(θ) ∫ sin(θ·y) e(y) dy`. -/
def retainedSinAmplitude {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ScalarConstants) (η : ℝ) (χlo : Vec 2 → ℝ) (e : Vec 2 → E) (θ : Vec 2) : E :=
  ((2 * Real.pi)⁻¹ ^ 2 * retainedCutoff K η χlo θ) • ∫ y, Real.sin (vecDot θ y) • e y

/-- **Band-limited calculus.** A function with an amplitude pair supported in `|θ| ≤ r` is
smooth of every order, its ordered derivatives of order `a` are bounded by `r^a` times the `L¹`
norms of the amplitudes, and for an even/odd pair it is square integrable exactly when the
amplitudes are, with `‖g‖₂ = 2π (‖A‖₂² + ‖B‖₂²)^{1/2}` (Plancherel). -/
def AmplitudePlancherelStatement : Prop :=
  ∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (r : ℝ) (g A B : Vec 2 → E), 0 < r →
    IsRetainedAmplitude g r A B →
    (∀ M : ℕ, ContDiff ℝ M g) ∧
    (∀ (a : ℕ) (wd : DerivativeWord2 a) (z : Vec 2), ‖orderedDerivative wd g z‖ ≤
      r ^ a * ((∫ θ in {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}, ‖A θ‖) +
        ∫ θ in {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}, ‖B θ‖)) ∧
    ((∀ θ, A (-θ) = A θ ∧ B (-θ) = -B θ) →
      (MemLp g 2 volume ↔ MemLp A 2 volume ∧ MemLp B 2 volume) ∧
      (MemLp g 2 volume → eLpNorm g 2 volume =
        ENNReal.ofReal (2 * Real.pi) *
          (eLpNorm A 2 volume ^ 2 + eLpNorm B 2 volume ^ 2) ^ (1 / 2 : ℝ)))

/-- **Chain combination.** Truncation to the minimum of two descending slot assignments and
linear combination of two chains of the same word data give a chain, with the combined datum and
endpoint values almost everywhere. -/
def ChainCombinationStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D Nw : ℕ} (letters : Fin Nw → CycleLetter ι h D) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (X₀ : Vec 2) (δ t₀ t₁ : ℝ) (κ κ' : Fin (Nw + 1) → ι → ℕ),
    2 ≤ D → IsWordSlots letters κ → IsWordSlots letters κ' →
  ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (f' : ∀ x, PlaneHk Set.univ (κ' 0 x) (h x))
    (u' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ' j x) (h x))
    (w' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ' j x + 1) (h x)),
    IsPlaneChain (wordChainData G letters X₀ δ) κ t₀ t₁ v f (fun _ _ _ => 0) u w →
    IsPlaneChain (wordChainData G letters X₀ δ) κ' t₀ t₁ v f' (fun _ _ _ => 0) u' w' →
  ∀ a b : ℝ, ∃ (f'' : ∀ x, PlaneHk Set.univ (min (κ 0 x) (κ' 0 x)) (h x))
    (u'' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (min (κ j x) (κ' j x)) (h x))
    (w'' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
      PlaneHk Set.univ (min (κ j x) (κ' j x) + 1) (h x)),
    IsPlaneChain (wordChainData G letters X₀ δ) (fun j x => min (κ j x) (κ' j x)) t₀ t₁ v f''
      (fun _ _ _ => 0) u'' w'' ∧
    (∀ x, planeValue (f'' x) =ᵐ[volume]
      fun z => a • planeValue (f x) z + b • planeValue (f' x) z) ∧
    ∀ x, planeValue (u'' (Fin.last Nw) x t₁) =ᵐ[volume]
      fun z => a • planeValue (u (Fin.last Nw) x t₁) z + b • planeValue (u' (Fin.last Nw) x t₁) z

/-- **Compact chains.** A compactly supported datum at the base slots starts a chain. -/
def CompactChainExistenceStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D Nw : ℕ} (H J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D)
    (η S ηg t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions), ScalarPackage K η G v t₀ S ϖ reg →
    IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg →
    wordReserveJstar (wordReserveKstar 0 (wordReserveN 0 fun i => (letters i).slow)
      fun i => (letters i).order) (fun i => (letters i).order) ≤ J →
  ∀ (X₀ : Vec 2) (f : ∀ x, PlaneHk Set.univ (wordBaseSlots letters 0 x) (h x)),
    IsCompactDatum f →
  ∃ (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (wordBaseSlots letters j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
      PlaneHk Set.univ (wordBaseSlots letters j x + 1) (h x)),
    IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (wordBaseSlots letters) t₀ (t₀ + S) v f
      (fun _ _ _ => 0) u w

/-- **Compact data.** Smooth compactly supported functions lift to every carrier, and a
measurable field is the limit of smooth compactly supported fields in every moment norm in which
it is finite. -/
def CompactDensityStatement : Prop :=
  (∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] (k : ℕ) (φ : Vec 2 → E),
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∃ f : PlaneHk Set.univ k E, planeValue f =ᵐ[volume] φ) ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (F : ∀ x, Vec 2 → h x), (∀ x, AEStronglyMeasurable (F x) volume) →
  ∃ φs : ℕ → ∀ x, Vec 2 → h x,
    (∀ k x, ContDiff ℝ (⊤ : ℕ∞) (φs k x) ∧ HasCompactSupport (φs k x)) ∧
    ∀ (π : ι → ℝ) (n : ℕ) (s : ℝ), momentNorm π n s F < ⊤ →
      Tendsto (fun k => momentNorm π n s (fun x z => F x z - φs k x z)) atTop (𝓝 0)

/-- **Gaussian amplitude of compact chain data**. On a well-buffered block, for a chain at
descending slots whose datum is a.e. the smooth compactly supported field `φ`, the endpoint is
integrable (it has all moments), the explicit amplitudes of its retained cutoff represent it, are
`C^m`, and satisfy the Gaussian bound at every `θ` of the zone. The retained amplitude of the actual
word is the model of the source (pulse-local transverse graphs, global scalar `e^Ξ`) plus the
quiet-switching error `C B_p Θ_w (1+P_e+S)^C e^{-cD_q}`, which the well-buffered hypothesis
absorbs. -/
def CompactChainGaussianStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ χlo : Vec 2 → ℝ, IsLowCutoff K χlo →
  ∀ (Nw D H m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∀ χr χ₃ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χr → HasCompactSupport χr →
    ContDiff ℝ (⊤ : ℕ∞) χ₃ → (∀ k : ℕ, ∃ B : ℝ, ∀ ξ, ‖iteratedFDeriv ℝ k χ₃ ξ‖ ≤ B) →
    (∀ ξ, χlo ξ = χr ξ ^ (wordReserveN m Ks + 1) * χ₃ ξ) →
  ∃ (CGa cGa c₁ : ℝ) (Q₁ : ℕ), 0 < CGa ∧ 0 < cGa ∧ 0 < c₁ ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D),
    (∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧ (letters i).positive = pos i) →
  ∀ (η S ηg t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions), ScalarPackage K η G v t₀ S ϖ reg →
    IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg →
    wordReserveJstar (wordReserveKstar 0 (wordReserveN m Ks) d) d ≤ J →
    IsWellBuffered c₁ Q₁ η S reg →
  ∀ (X₀ : Vec 2) (κ : Fin (Nw + 1) → ι → ℕ), IsWordSlots letters κ →
  ∀ φ : ∀ x, Vec 2 → h x, (∀ x, ContDiff ℝ (⊤ : ℕ∞) (φ x) ∧ HasCompactSupport (φ x)) →
  ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
    (∀ x, planeValue (f x) =ᵐ[volume] φ x) →
    IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
    (∀ x, Integrable (planeValue (u (Fin.last Nw) x (t₀ + S))) volume) ∧
    (∀ x, IsRetainedAmplitude
      (fourierCutoff (retainedCutoff K η χlo) (planeValue (u (Fin.last Nw) x (t₀ + S))))
      (2 * K.ξlo * Real.sqrt η)
      (retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))))
      (retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))))) ∧
    (∀ x, ContDiff ℝ m (retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S)))) ∧
      ContDiff ℝ m (retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))))) ∧
    ∀ θ : Vec 2, (∀ i, |θ i| ≤ Real.pi) →
      amplitudeJetNorm π m ϖ
          (fun x => retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))))
          (fun x => retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S)))) θ ≤
        ENNReal.ofReal (CGa * wordTheta ηg letters *
            (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ wordReserveP m Ks *
            Real.exp (-cGa * (vecDot θ θ / ϖ ^ 2))) *
          ∑ α ∈ momentIndices (wordReserveN m Ks),
            ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
              blochFibreDerivNorm π (fun θ' => χr ((Real.sqrt η)⁻¹ • θ')) α φ θ

/-- **Plancherel with a Gaussian amplitude.** If the amplitudes of a band-limited family vanish
outside `|θ| < π/2` and obey a pointwise Gaussian bound by the Bloch fibre norms of a smooth
compactly supported field `F` at every `θ` of the zone, then the weighted jets of the family at
scale `ϖ⁻¹` are bounded by the moment norm of `F`. The constant depends on the orders, the Gaussian
rate and the cutoff only. -/
def GaussianPlancherelStatement : Prop :=
  ∀ (m n p M : ℕ) (cGa : ℝ), 0 < cGa →
  ∀ χlo : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χlo → HasCompactSupport χlo →
  ∃ C : ℝ, 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ (η ϖ r CGa : ℝ), 0 < η → 0 < ϖ → ϖ ≤ Real.sqrt η → 0 ≤ CGa →
  ∀ g A B F : ∀ x, Vec 2 → h x,
    (∀ x, ContDiff ℝ (⊤ : ℕ∞) (F x) ∧ HasCompactSupport (F x)) →
    (∀ x, IsRetainedAmplitude (g x) r (A x) (B x)) →
    (∀ x, ContDiff ℝ m (A x) ∧ ContDiff ℝ m (B x)) →
    (∀ x θ, Real.pi / 2 ≤ Real.sqrt (vecDot θ θ) → A x θ = 0 ∧ B x θ = 0) →
    (∀ θ : Vec 2, (∀ i, |θ i| ≤ Real.pi) →
      amplitudeJetNorm π m ϖ A B θ ≤
        ENNReal.ofReal (CGa * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ p *
            Real.exp (-cGa * (vecDot θ θ / ϖ ^ 2))) *
          ∑ α ∈ momentIndices n,
            ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
              blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α F θ) →
    weightedJetNorm π (m : ℝ) M ϖ ϖ⁻¹ (fun x _ wd z => orderedDerivative wd (g x) z) ≤
      ENNReal.ofReal (C * CGa) * momentNorm π n ϖ F

/-- **Continuity of the Bloch fibre norms.** Under `n + 2` moments the fibre derivative norms
of order at most `n` are Lipschitz in the datum, uniformly in the frequency (two more moments give
`H²` in `θ` with values in `L²` of the cell, and `H² ⊂ C⁰` in dimension two). -/
def BlochFibreContinuityStatement : Prop :=
  ∀ (n : ℕ) (χ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
  ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ F F' : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (F x) volume) →
    (∀ x, AEStronglyMeasurable (F' x) volume) →
    momentNorm π (n + 2) s F < ⊤ → momentNorm π (n + 2) s F' < ⊤ →
  ∀ α : ℕ × ℕ, α.1 + α.2 ≤ n → ∀ θ : Vec 2,
    blochFibreDerivNorm π χ α F θ ≤
      blochFibreDerivNorm π χ α F' θ +
        ENNReal.ofReal C * momentNorm π (n + 2) s (fun x z => F x z - F' x z)
end

/-! # Sub-statements of `CompactChainGaussianStatement`, stated for a general block on subintervals

`CompactChainGaussianStatement` is split, following the proof of (ii) of Lemma 11.12 of the paper,
into a factorization with the gauge kept outside and the
complete-window damping of the gauge:

* `RetainedAmplitudeFactorStatement`: on a subinterval `[a, b]` of a `CoreScalarPackage`
  window, for a chain from a plane datum vanishing a.e. outside a ball and a low-disc cutoff, the
  cutoff amplitude of the endpoint is `e^{Ξ(b,a)}` times an amplitude pair whose normalized jets are
  polynomial in `x_ξ = √S|ξ| = |θ|/ϖ`, `P_e`-free up to the quiet-switching factor
  `(1 + B_p) P_e^Q (1 + S)^Q e^{-c D_q}` and the terminal tail `P_e^Q (1 + S)^Q e^{-c D_q'}` (the
  excursion argument stopped before damping).
* `GaugeJetsPieceStatement`: the undamped gauge jets on a piece.
* `GaugeJetsStatement`: on a complete window the normalized jets of `e^{Ξ}` are at most
  `C (1 + x_ξ)^{|β|} e^{-c x_ξ²}` (from `ScalarPackage.gauss` and `phase_jets`).
* The excursion count of one dichotomy path. A letter between
  two slow gaps has a double zero (`S⁻¹` after normalization), between a slow and a fast gap a
  simple zero (`S^{-1/2}`); fast gaps decay exponentially; the terminal gap is slow (the row kills
  the terminal fast part). The integral over the ordered simplex in `[0, L]`, `L ≤ C_H S`, is
  bounded uniformly in `S ≥ 1`: every free position is paid by its zeros.

The fibre frequency of the plane frequency `θ` (radian convention: `cos(θ·y)`, `χ_lo(θ/√η)`) is
`ξ = θ/√η`: the plane mode `e^{iθ·y}p(y)`, `p` periodic, has its periodic factor in the fibre
problem with shift `√ηξ = θ`, and its Fourier amplitude sits at `θ`. The complex amplitude of the
cosine and sine pair is `A - iB` (`∫ e^{-iθ·y}`), so `A - iB = e^{Ξ}(Ã_c - iÃ_s)` reads
`A = Re e^Ξ Ã_c + Im e^Ξ Ã_s`, `B = Re e^Ξ Ã_s - Im e^Ξ Ã_c`. -/

section
universe u v

/-- The fibre frequency `θ/√η` of a plane frequency (radian convention). -/
def planeFibreFrequency (η : ℝ) (θ : Vec 2) : Fin 2 → ℂ := fun i => ((θ i / Real.sqrt η : ℝ) : ℂ)

/-- The gauge `Ξ(b, a) = ∫_a^b λ(ξ)` of a symbol family at the fibre frequency of `θ`. -/
def blockGauge (lam : ℕ × ℕ → ℝ → ℂ) (η a b : ℝ) (θ : Vec 2) : ℂ :=
  ∫ τ in a..b, fibreSeriesC lam (planeFibreFrequency η θ) τ

/-- The normalized derivative norm of an amplitude family,
`∑_{k ≤ m} (ϖ^k/k!) (∑_x π_x⁻¹ (‖D^kA_x(θ)‖² + ‖D^kB_x(θ)‖²))^{1/2}`, with full iterated
derivatives: it bounds `amplitudeJetNorm` and obeys the Leibniz rule without symmetry of
derivatives. -/
def ampDerivNorm {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ) (m : ℕ) (ϖ : ℝ) (A B : ∀ x, Vec 2 → h x)
    (θ : Vec 2) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (m + 1), ENNReal.ofReal (ϖ ^ k / (k.factorial : ℝ)) *
    (∑ x, ENNReal.ofReal ((π x)⁻¹) *
      (ENNReal.ofReal (‖iteratedFDeriv ℝ k (A x) θ‖ ^ 2) +
        ENNReal.ofReal (‖iteratedFDeriv ℝ k (B x) θ‖ ^ 2))) ^ (1 / 2 : ℝ)

/-- The block premises of `IsWordBlock` on a piece `[a, b]`: the letters are cycle letters on
`[a, b]`, the normalization is `ϖ = √(η/S)` with `S ≥ 1` (the duration of the piece is bounded
separately), the regions are those of the package. -/
structure IsWordPiece (K : ScalarConstants) (g₁ : ℝ) {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D Nw : ℕ} (H J : ℕ)
    (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D) (η S ηg ϖ : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ) (reg : BlockRegions)
    (a b : ℝ) : Prop where
  hD : 2 ≤ D
  hπ : ∀ x, 0 < π x
  hη : 0 < η
  hη1 : η ≤ 1
  hS : 1 ≤ S
  hηg : 0 < ηg
  hηg1 : ηg ≤ 1
  hϖ : ϖ = Real.sqrt (η / S)
  hGm : IsCellMetric (fun t _ => G t)
  hv : IsCellDrift v
  hv0 : ∀ t (k : Fin 2), cellMean (fun x => (v t x k : ℂ)) = 0
  hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)
  hvw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw
  hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj j
  hg0 : 0 ≤ g
  hg : g ≤ K.g0
  hg₁ : g ≤ g₁
  hGn : IsMetricNearIdentity (fun t _ => G t) g
  hlet : ∀ i, IsCycleLetter π (letters i) (Set.Icc a b ×ˢ Set.univ) J H
  htrans : ∀ i, IsTransverseOnPulses (letters i).edge
    (fun p : Fin reg.P => Set.Icc (reg.lo p) (reg.hi p)) reg.orient
  hquiet : ∀ i, IsQuietOn (letters i).edge v reg.quiet
  hmeas : ∀ i x y o, ∀ γ ∈ (letters i).edge x y o, ∀ α X z, Measurable fun t => γ.coeff α t X z

/-- A complete block is a piece of itself. -/
theorem IsWordBlock.toPiece {K : ScalarConstants} {g₁ : ℝ} {ι : Type*} [Fintype ι]
    {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D Nw H J : ℕ}
    {π : ι → ℝ} {letters : Fin Nw → CycleLetter ι h D} {η S ηg t₀ ϖ : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {g : ℝ} {reg : BlockRegions}
    (hB : IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg) :
    IsWordPiece K g₁ H J π letters η S ηg ϖ G v g reg t₀ (t₀ + S) :=
  { hB with }

/-- The cosine amplitude of `fourierCutoff mc e`: `(2π)⁻² mc(θ) ∫ cos(θ·y) e(y) dy`. -/
def cutoffCosAmplitude {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (mc : Vec 2 → ℝ)
    (e : Vec 2 → E) (θ : Vec 2) : E :=
  ((2 * Real.pi)⁻¹ ^ 2 * mc θ) • ∫ y, Real.cos (vecDot θ y) • e y

/-- The sine amplitude of `fourierCutoff mc e`: `(2π)⁻² mc(θ) ∫ sin(θ·y) e(y) dy`. -/
def cutoffSinAmplitude {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (mc : Vec 2 → ℝ)
    (e : Vec 2 → E) (θ : Vec 2) : E :=
  ((2 * Real.pi)⁻¹ ^ 2 * mc θ) • ∫ y, Real.sin (vecDot θ y) • e y

/-- The cutoff of a piece: `χ(θ/√η) ψ(θ)`, a low-disc cutoff in the fibre frequency times a fixed
factor with bounded derivatives (`ψ = 1` for the seam, `ψ = χ_lo(4ξ_*·/π)` for the retained
cutoff). -/
def pieceCutoff (χ ψ : Vec 2 → ℝ) (η : ℝ) (θ : Vec 2) : ℝ := χ ((Real.sqrt η)⁻¹ • θ) * ψ θ

/-- **Factorization of the retained amplitude on a piece** (the excursion argument stopped before
the complete-window damping). On a piece `[a, b]` of duration at most `C_H S` (possibly `0`) inside
a `CoreScalarPackage` window, ending with a quiet stretch `(b - D_q, b]`, for a chain at descending
slots from a plane datum `f` whose value vanishes a.e. outside a ball (no smoothness), and a cutoff
`χ(θ/√η)ψ(θ)` with `χ = 0` for `|ξ| ≥ ρ`, `ρ < ξ₀`: the endpoint is integrable, the cutoff
amplitudes represent `fourierCutoff` and are `C^m`, and on the low disc they are `e^{Ξ(b,a)}` times
a `C^m` pair whose normalized derivatives are at most
`CΘ_w (1 + x_ξ)^P (1 + P_e^Q(1+S)^Q ((1 + B_p) e^{-c D_q^{reg}} + e^{-c D_q}))` times the normalized
Bloch jets `J_n` of the datum's plane value, `n = m + ∑K_i`, cut off by `χ_r`, where
`χ = χ_r^{n+1} χ₃`: every frequency derivative reaching the datum (a Taylor monomial or a jet of the
amplitude) needs its own factor of `χ_r`. The quiet-switching and terminal-tail errors sit inside
the gauge (the complete window damps them with it; on pieces `|e^Ξ| ≤ C_g`). The integers `P, Q`
precede `C_H` and the cutoff; `C, c` follow them. The disc lies in the retained disc `ρ ≤ 2ξ_lo`,
which is slow/fast separated (`consts_pos`: `(2 + C_w C_g)(2ξ_lo)² ≤ π²/16`): the slow damping
`-Re λ ≤ (η(1+g) + C_w C_g)|ξ|²` stays below a quarter of the `P_e`-free fast rates (quiet gap
`π²/2`, transverse rate `π²/8`), so gauged fast excursions decay. -/
def RetainedAmplitudeFactorStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D H m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool), ∃ P Q : ℕ,
  ∀ (CH ρ : ℝ) (χ ψ : Vec 2 → ℝ), ρ < K.ξ0 → ρ ≤ 2 * K.ξlo → ContDiff ℝ (⊤ : ℕ∞) χ →
    (∀ ξ, ρ ≤ Real.sqrt (vecDot ξ ξ) → χ ξ = 0) → ContDiff ℝ (⊤ : ℕ∞) ψ →
    (∀ k : ℕ, ∃ B : ℝ, ∀ θ, ‖iteratedFDeriv ℝ k ψ θ‖ ≤ B) →
  ∀ χr χ₃ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χr →
    (∀ k : ℕ, ∃ B : ℝ, ∀ ξ, ‖iteratedFDeriv ℝ k χr ξ‖ ≤ B) → ContDiff ℝ (⊤ : ℕ∞) χ₃ →
    (∀ k : ℕ, ∃ B : ℝ, ∀ ξ, ‖iteratedFDeriv ℝ k χ₃ ξ‖ ≤ B) →
    (∀ ξ, χ ξ = χr ξ ^ (wordReserveN m Ks + 1) * χ₃ ξ) →
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D),
    (∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧ (letters i).positive = pos i) →
  ∀ (η S ηg t₀ Sw ϖ a b Dq : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (g : ℝ) (reg : BlockRegions) (pkg : CoreScalarPackage K η G v t₀ Sw ϖ reg),
    IsWordPiece K g₁ H J π letters η S ηg ϖ G v g reg a b →
    t₀ ≤ a → a ≤ b → b ≤ t₀ + Sw → b - a ≤ CH * S →
    0 ≤ Dq → Set.Ioc (b - Dq) b ⊆ reg.quiet →
    wordReserveJstar (wordReserveKstar 0 (wordReserveN m Ks) d) d ≤ J →
  ∀ (X₀ : Vec 2) (κ : Fin (Nw + 1) → ι → ℕ), IsWordSlots letters κ →
  ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
    (∃ R : ℝ, ∀ x, ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 → planeValue (f x) z = 0) →
    IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ a b v f (fun _ _ _ => 0) u w →
    (∀ x, Integrable (planeValue (u (Fin.last Nw) x b)) volume) ∧
    (∀ r : ℝ, 0 < r → (∀ θ : Vec 2, r ^ 2 < vecDot θ θ → pieceCutoff χ ψ η θ = 0) → ∀ x,
      IsRetainedAmplitude (fourierCutoff (pieceCutoff χ ψ η) (planeValue (u (Fin.last Nw) x b))) r
        (cutoffCosAmplitude (pieceCutoff χ ψ η) (planeValue (u (Fin.last Nw) x b)))
        (cutoffSinAmplitude (pieceCutoff χ ψ η) (planeValue (u (Fin.last Nw) x b)))) ∧
    (∀ x, ContDiff ℝ m (cutoffCosAmplitude (pieceCutoff χ ψ η)
        (planeValue (u (Fin.last Nw) x b))) ∧
      ContDiff ℝ m (cutoffSinAmplitude (pieceCutoff χ ψ η) (planeValue (u (Fin.last Nw) x b)))) ∧
    ∃ Ac As : ∀ x, Vec 2 → h x,
      (∀ x, ContDiff ℝ m (Ac x) ∧ ContDiff ℝ m (As x)) ∧
      (∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) < K.ξ0 → ∀ x,
        cutoffCosAmplitude (pieceCutoff χ ψ η) (planeValue (u (Fin.last Nw) x b)) θ =
            (Complex.exp (blockGauge pkg.actual.lam η a b θ)).re • Ac x θ +
              (Complex.exp (blockGauge pkg.actual.lam η a b θ)).im • As x θ ∧
          cutoffSinAmplitude (pieceCutoff χ ψ η) (planeValue (u (Fin.last Nw) x b)) θ =
            (Complex.exp (blockGauge pkg.actual.lam η a b θ)).re • As x θ -
              (Complex.exp (blockGauge pkg.actual.lam η a b θ)).im • Ac x θ) ∧
      ∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) < K.ξ0 →
        ampDerivNorm π m ϖ Ac As θ ≤
          ENNReal.ofReal (C * wordTheta ηg letters * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ P *
              (1 + peFactor η ^ Q * (1 + S) ^ Q * ((1 + (reg.joins : ℝ)) *
                Real.exp (-c * reg.buffer) + Real.exp (-c * Dq)))) *
            ∑ α ∈ momentIndices (wordReserveN m Ks),
              ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
                blochFibreDerivNorm π (fun θ' => χr ((Real.sqrt η)⁻¹ • θ')) α
                  (fun x => planeValue (f x)) θ

/-- **Gauge jets with complete-window damping** (`ScalarPackage.gauss`, Cauchy estimates,
Faà di Bruno). On a complete window, on the low disc of the retained cutoff, the gauge is smooth
and its normalized derivatives are at most `C (1 + x_ξ)^k e^{-c x_ξ²}`, `x_ξ = |θ|/ϖ`. The metric
and drift premises make the symbol measurable in time and quadratic on the graph disc
(`graph_symbol_aestronglyMeasurable`, `scalarPackageSymbol_quadratic_bound`). -/
def GaugeJetsStatement : Prop :=
  ∀ (K : ScalarConstants) (m : ℕ), ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (η S t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (reg : BlockRegions) (pkg : ScalarPackage K η G v t₀ S ϖ reg),
    0 < η → η ≤ 1 → 1 ≤ S → ϖ = Real.sqrt (η / S) →
    IsCellMetric (fun t _ => G t) → IsCellDrift v →
    (∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw) →
    ContDiffOn ℝ m (fun θ => Complex.exp (blockGauge pkg.actual.lam η t₀ (t₀ + S) θ))
      {θ | fibreNorm (planeFibreFrequency η θ) < K.ξ0} ∧
    ∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) ≤ 2 * K.ξlo → ∀ k ≤ m,
      ϖ ^ k *
          ‖iteratedFDeriv ℝ k
            (fun θ' => Complex.exp (blockGauge pkg.actual.lam η t₀ (t₀ + S) θ')) θ‖ ≤
        C * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ k * Real.exp (-c * (vecDot θ θ / ϖ ^ 2))

/-- **Gauge jets on a piece** (undamped). On a piece `[a, b]` of duration at most
`C_H S` inside a `CoreScalarPackage` window, inside the disc `|ξ| ≤ ρ < ξ₀`, the gauge is smooth and
its normalized derivatives are at most `C (1 + x_ξ)^k` (`real_ratio` for `|e^Ξ| ≤ C_g`; the
quadratic bound of the symbol and Cauchy for `δ_ξ Ξ = O(x_ξ)` and the higher jets; the metric and
drift premises as for `GaugeJetsStatement`). -/
def GaugeJetsPieceStatement : Prop :=
  ∀ (K : ScalarConstants) (m : ℕ) (CH ρ : ℝ), ρ < K.ξ0 → ∃ C : ℝ, 0 < C ∧
  ∀ (η S t₀ Sw ϖ a b : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (reg : BlockRegions) (pkg : CoreScalarPackage K η G v t₀ Sw ϖ reg),
    0 < η → η ≤ 1 → 1 ≤ S → ϖ = Real.sqrt (η / S) →
    IsCellMetric (fun t _ => G t) → IsCellDrift v →
    (∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw) →
    t₀ ≤ a → a ≤ b → b ≤ t₀ + Sw → b - a ≤ CH * S →
    ContDiffOn ℝ m (fun θ => Complex.exp (blockGauge pkg.actual.lam η a b θ))
      {θ | fibreNorm (planeFibreFrequency η θ) < K.ξ0} ∧
    ∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) ≤ ρ → ∀ k ≤ m,
      ϖ ^ k * ‖iteratedFDeriv ℝ k
          (fun θ' => Complex.exp (blockGauge pkg.actual.lam η a b θ')) θ‖ ≤
        C * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ k
end

end AVRegularity.CycleWords.Assembly
end
end
