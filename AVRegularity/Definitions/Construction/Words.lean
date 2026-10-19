-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.LiftCoeff
public import AVRegularity.Definitions.Families.MarkedLedger

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! Definition: the explicit Fourier
Schur norm of the centered positive-degree cell coefficients of a lift, in normalized cell time.

For an operator-valued cell coefficient `c(s, X, z)`, a nonzero cell mode `ξ ∈ ℤ²` and a slow order
`j`, `modeJet` is `‖D_X^j ĉ_cos(s,X,ξ)‖ + ‖D_X^j ĉ_sin(s,X,ξ)‖` with the real Fourier pair
`ĉ_cos = ∫ cos(2πξ·z)c dz`, `ĉ_sin = ∫ sin(2πξ·z)c dz` (equivalent to `|ĉ(ξ)|` up to `√2`;
`|∂_X^β|`, `|β| = j`, is replaced by the `j`-th Fréchet derivative, equivalent up to a constant of
the fixed order). `modeE` is `e_ξ(g;J) = sup_J g + 2π|ξ|(∫_J g²)^{1/2}`. The entry of a block
`v ← u` is `∑_{n=1}^N ∑_{d=1}^n ∑_I ∑_{j≤K} (1/j!) ∑_{ξ≠0} (1+|ξ|)^L sup_X e_ξ(...)`; `layerNorm`
is the Schur norm `Schur_π` of this nonnegative matrix (both weighted sums, `√(π_u/π_v)`).
`entranceNorm` is the single-trace version `𝔍` (evaluation at one time, no time integral). All
values are in `[0, ∞]`, so no supremum or series takes a junk value. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, CompleteSpace (h i)]

/-- The phase `2πξ·z`. -/
def modePhase (ξ : Fin 2 → ℤ) (z : Vec 2) : ℝ := 2 * Real.pi * ∑ i : Fin 2, (ξ i : ℝ) * z i

/-- The Euclidean length `|ξ|`. -/
def modeLen (ξ : Fin 2 → ℤ) : ℝ := Real.sqrt (∑ i : Fin 2, ((ξ i : ℝ)) ^ 2)

/-- `‖D_X^j ĉ_cos(X,ξ)‖ + ‖D_X^j ĉ_sin(X,ξ)‖` for a coefficient `c(X, z)` with values in `E`. -/
def modeJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : Vec 2 → Vec 2 → E) (ξ : Fin 2 → ℤ) (j : ℕ) (X : Vec 2) : ℝ≥0∞ :=
  ‖iteratedFDeriv ℝ j (fun X' => ∫ z in AVenhance.unitCube, Real.cos (modePhase ξ z) • c X' z) X‖ₑ +
    ‖iteratedFDeriv ℝ j (fun X' => ∫ z in AVenhance.unitCube, Real.sin (modePhase ξ z) • c X' z) X‖ₑ

/-- `e_ξ(g;J) = sup_{s∈J} g(s) + 2π|ξ| (∫_J g(s)² ds)^{1/2}`. -/
def modeE (ξ : Fin 2 → ℤ) (g : ℝ → ℝ≥0∞) (J : Set ℝ) : ℝ≥0∞ :=
  (⨆ s ∈ J, g s) + ENNReal.ofReal (2 * Real.pi * modeLen ξ) * (∫⁻ s in J, g s ^ 2) ^ (1 / 2 : ℝ)

/-- The nonzero cell modes. -/
abbrev NZMode : Type := {ξ : Fin 2 → ℤ // ξ ≠ 0}

/-- The `v ← u` entry of for the grade-`hh` coefficients `Cc hh` on the time set `J`
(`trace = some a`: the single trace at `a`, without the time integral). -/
def layerEntry (Cc : ℕ → ℕ → LiftCoeff ι h) (hh N K L : ℕ) (J : Set ℝ) (trace : Option ℝ)
    (v u : ι) : ℝ≥0∞ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 n, ∑ α : DerivativeWord2 d, ∑ j ∈ Finset.range (K + 1),
    ENNReal.ofReal ((j.factorial : ℝ)⁻¹) * ∑' ξ : NZMode,
      ENNReal.ofReal ((1 + modeLen ξ.1) ^ L) * ⨆ X : Vec 2,
        match trace with
        | none => modeE ξ.1 (fun s => modeJet (fun X' z => Cc hh n d α s X' z v u) ξ.1 j X) J
        | some a => modeJet (fun X' z => Cc hh n d α a X' z v u) ξ.1 j X

/-- The Schur norm `max{sup_v ∑_u √(π_u/π_v) M_vu, sup_u ∑_v √(π_u/π_v) M_vu}`. -/
def schurPi (π : ι → ℝ) (M : ι → ι → ℝ≥0∞) : ℝ≥0∞ :=
  max (⨆ v, ∑ u, ENNReal.ofReal (Real.sqrt (π u / π v)) * M v u)
    (⨆ u, ∑ v, ENNReal.ofReal (Real.sqrt (π u / π v)) * M v u)

/-- `𝔈_{h;K,L}(C;J)`. -/
def layerNorm (π : ι → ℝ) (Cc : ℕ → ℕ → LiftCoeff ι h) (hh N K L : ℕ) (J : Set ℝ) : ℝ≥0∞ :=
  schurPi π (layerEntry Cc hh N K L J none)

/-- `𝔍_{h;K,L}(C(a))`: the single-trace version of at the time `a`. -/
def entranceNorm (π : ι → ℝ) (Cc : ℕ → ℕ → LiftCoeff ι h) (hh N K L : ℕ) (a : ℝ) : ℝ≥0∞ :=
  schurPi π (layerEntry Cc hh N K L {a} (some a))

/-- The difference `ΔC = C - C̃` of two coefficient families. -/
def liftDiff (Cc Cc' : ℕ → ℕ → LiftCoeff ι h) : ℕ → ℕ → LiftCoeff ι h :=
  fun hh n d α s X z v u => Cc hh n d α s X z v u - Cc' hh n d α s X z v u

end AVRegularity
end
end

section
@[expose] public section
namespace AVRegularity

/-! The padded alphabet, the words of a passage and the components of the extended and retained
successor families.

* `succAlphabet nMax hMax p npad`: the letter `𝖣`, the templates `𝖬_{n,h}`
  (`3 ≤ n ≤ nMax`, `1 ≤ h ≤ hMax`), `𝖵_{n,h,a,a'}` (`2 ≤ n ≤ nMax`, `1 ≤ h ≤ hMax`,
  `a, a' ≤ p`, `a + a' ≥ 1`), padded by the zero templates `padding k`, `k < npad`. The
  construction fixes `nMax = N + D_H` and `hMax = r̄_H` at the producer menus;
  the successor uses the padded producer menus of its proof; both are parameters here.
* `wordsUpTo A L`: the nonempty words of length at most `L` over `A` (`𝔗` with `L = J + 1`;
  `T_w = #𝔗`).
* `succComp m v t`: the component `(v, 𝔱)` of the passage `m → m-1`: `v` itself for the empty word,
  otherwise the birth event `(m-1, 𝔱)` prepended to the history of `v`
  (`𝖡(v,𝔱) = 𝖡(v) ∪ {m-1}`).
* `compWord m c`: the word of the passage `m → m-1` of a component (empty if its last birth is
  older).
* `succExtComps m A J S`: the extended component set `{(v,𝔱) : v ∈ S, 𝔱 ∈ {∅} ∪ 𝔗}`.
* `IsRetained m H J c`: birth grade at most `H` and word length at most `J` (the projection `Π`). -/

/-- The padded alphabet of a passage. -/
def succAlphabet (nMax hMax p npad : ℕ) : Finset WordLetter :=
  {WordLetter.diag} ∪
    ((Finset.Icc 3 nMax ×ˢ Finset.Icc 1 hMax).image fun x => WordLetter.mean x.1 x.2) ∪
    (((Finset.Icc 2 nMax ×ˢ Finset.Icc 1 hMax) ×ˢ (Finset.range (p + 1) ×ˢ Finset.range (p + 1))).filter
        (fun x => 1 ≤ x.2.1 + x.2.2)).image
      (fun x => WordLetter.covariance x.1.1 x.1.2 x.2.1 x.2.2) ∪
    (Finset.range npad).image WordLetter.padding

/-- The words of length exactly `k` over `A`. -/
def wordsOfLength (A : Finset WordLetter) : ℕ → Finset (List WordLetter)
  | 0 => {[]}
  | k + 1 => (A ×ˢ wordsOfLength A k).image fun x => x.2 ++ [x.1]

/-- The nonempty words of length at most `L` over `A`. -/
def wordsUpTo (A : Finset WordLetter) (L : ℕ) : Finset (List WordLetter) :=
  (Finset.Icc 1 L).biUnion (wordsOfLength A)

/-- The component `(v, 𝔱)` of the passage `m → m-1`. -/
def succComp (m : ℕ) (v : Comp) (t : List WordLetter) : Comp :=
  if ht : t = [] then v else ⟨v.root, ⟨m - 1, t, ht⟩ :: v.births⟩

/-- The word of the passage `m → m-1` of a component. -/
def compWord (m : ℕ) (c : Comp) : List WordLetter :=
  match c.births with
  | e :: _ => if e.scale = m - 1 then e.word else []
  | [] => []

/-- The extended component set of the passage `m → m-1`. -/
def succExtComps (m : ℕ) (A : Finset WordLetter) (J : ℕ) (S : Finset Comp) : Finset Comp :=
  S ∪ (S ×ˢ wordsUpTo A (J + 1)).image fun x => succComp m x.1 x.2

/-- The retained components: birth grade at most `H` and word length at most `J`. -/
def IsRetained (m H J : ℕ) (c : Comp) : Prop :=
  compGrade c ≤ H ∧ (compWord m c).length ≤ J

instance (m H J : ℕ) : DecidablePred (IsRetained m H J) := fun c => by
  unfold IsRetained; infer_instance

end AVRegularity
end
end
