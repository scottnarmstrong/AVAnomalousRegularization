-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ConstituentEdges
public import AVRegularity.Statements.Construction.OcEpsilon
public import AVRegularity.Statements.Intermediate.Families.FamilyDomain

section
@[expose] public section
namespace AVRegularity

/-! The numerical data of the birth masses, readout factors and
markers. One birth event with word `w` at scale `b` multiplies the mass by
`c_H / |𝔚| · ε_b^{η_b}` (for the successor `p_m = c_H E^{η_b}/T_w`; in the weak
construction `c_w E^{η_b}`, with `c_H := c_w`, `|𝔚| := 1`), the readout by
`(ε_b^{η_0})^{|w|}`, and the marker by `ε_b^{-ι}`.
The roots carry given masses and readouts (`1/1` for the finest root; `1/2` and `1` in the
weak construction; arbitrary for a supplied seed). The wavelengths are `ocEpsilon q Λ`, passed
to the definitions. The constraint
`0 < c_H ≤ (1 - 128^{-η_b})/2` is a hypothesis of the statements, not part of the data. -/

/-- The data `(ε, c_H, |𝔚|, η_b, η_0, ι)` and the root masses and readouts of a construction. -/
structure BirthLaw where
  /-- The birth-mass prefactor `c_H`. -/
  cH : ℝ
  cH_pos : 0 < cH
  /-- The number `|𝔚|` of types of a birth (`T_w` in the successor). -/
  wordCount : ℕ
  wordCount_pos : 0 < wordCount
  /-- The mass exponent `η_b`. -/
  etaB : ℝ
  /-- The readout exponent `η_0`. -/
  eta0 : ℝ
  /-- The marker exponent `ι`. -/
  iota : ℝ
  /-- The mass `π_r` of the root `r`. -/
  rootMass : ℕ → ℝ
  rootMass_pos : ∀ r, 0 < rootMass r
  /-- The readout factor `ω_r` of the root `r`. -/
  rootReadout : ℕ → ℝ
  rootReadout_pos : ∀ r, 0 < rootReadout r

end AVRegularity
end
end

section
@[expose] public noncomputable section
namespace AVRegularity

/-! The full (ungraded) ledger, the larger of the two weighted
sums over all rows and columns, `max{ sup_v ∑_u b_{vu}, sup_u ∑_v b_{vu} }`, without the
division into grades. Meaningful for `b ≥ 0`. Empty maxima are zero. -/

/-- `max{ sup_v ∑_u b v u, sup_u ∑_v b v u }`. -/
def fullLedger {ι : Type*} [Fintype ι] (b : ι → ι → ℝ) : ℝ :=
  max (⨆ v : ι, ∑ u, b v u) (⨆ u : ι, ∑ v, b v u)

end AVRegularity
end
end

section
@[expose] public section
namespace AVRegularity

/-! The order-convex hull of a set of times. -/

/-- The order-convex hull of a set of times: all `t` between two of its points. -/
def intervalHull (S : Set ℝ) : Set ℝ :=
  {t | ∃ a ∈ S, ∃ b ∈ S, a ≤ t ∧ t ≤ b}

/-! The letters of the finite word systems that index the new
components born in a passage. `diag` is the diagonal first source `𝖣`, `mean n h` the
remaining means `𝖬_{n,h}` (`n ≥ 3`), `covariance n h a a'` the ordered covariance terms
`𝖵_{n,h,a,a'}`; `eddy n` the weak-level eddy letters `𝔇_{i,n}`;
`padding k` the zero templates that pad the successor alphabet.
Only the identity of a letter matters for the family
(components with different words are different components); the operators they stand for are
defined with the construction. -/

/-- A letter of a birth word. -/
inductive WordLetter : Type
  /-- The diagonal first source `𝖣`. -/
  | diag : WordLetter
  /-- The remaining mean `𝖬_{n,h}`. -/
  | mean (n h : ℕ) : WordLetter
  /-- The ordered covariance term `𝖵_{n,h,a,a'}`. -/
  | covariance (n h a a' : ℕ) : WordLetter
  /-- The weak-level eddy letter `𝔇_{i,n}`. -/
  | eddy (n : ℕ) : WordLetter
  /-- The `k`-th zero padding template of the successor alphabet. -/
  | padding (k : ℕ) : WordLetter
  deriving DecidableEq

/-! One birth event of a component. At the passage whose fine
wavelength is `E = ε_scale` (the passage `i` of the production has `scale = i - 1`; the
successor `m → m - 1` has `scale = m - 1`, `𝖡(v,𝔱) = 𝖡(v) ∪ {m-1}`), a component receives
the children indexed by the nonempty
words over the alphabet. A word is one birth event whatever its length; the empty word is
not an event (it keeps the incoming component). -/

/-- A birth: the scale index `b` of `E = ε_b` and the nonempty word of the new child. -/
structure BirthEvent where
  /-- The scale index `b = i - 1` of the passage, so `E = ε_b`. -/
  scale : ℕ
  /-- The word `𝔱` of the child (a list of letters, in order). -/
  word : List WordLetter
  /-- Empty words are not births. -/
  word_ne_nil : word ≠ []
  deriving DecidableEq

end AVRegularity
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity

/-! The one-piece chart. -/

/-- The one-piece chart: identity material map, all times as output and geometry, anchor `0`. -/
def ChartPiece.trivial : ChartPiece where
  label := 0
  output := Set.univ
  geometry := Set.univ
  output_subset := subset_rfl
  anchor := 0
  anchor_mem := Set.mem_univ _
  material := fun _ => Homeomorph.refl _
  material_smooth := fun _ => contDiff_id
  material_symm_smooth := fun _ => contDiff_id

end AVRegularity
end
end

section
@[expose] public noncomputable section
namespace AVRegularity

/-! The original-order price of a constituent,
`f_γ = max{1, (R_γ/r_γ)^{d^birth_γ - 2}}`. -/

/-- `f_γ = max{1, (R_γ/r_γ)^{d^birth_γ - 2}}`. -/
def constituentPrice (r : ConstituentRecord) : ℝ :=
  max 1 ((r.length / r.width) ^ r.birthExcess)

end AVRegularity
end
end

section
@[expose] public section
namespace AVRegularity

/-! A component of a family, as its birth history, with a root label. A stage of a
construction is a `Finset Comp`; masses, readout weights, grades, birth sets and markers are
computed from the history (a forest of roots and births; the components of a seed have grade
zero and marker `I`). -/

/-- A component: the label of its root (`0` for the finest scalar component `o`; the
components of a supplied seed are further roots) and its births, most recent first. -/
structure Comp where
  /-- The root component the history starts from. -/
  root : ℕ
  /-- The birth events, most recent first. -/
  births : List BirthEvent
  deriving DecidableEq

/-! The birth set `𝖡(v)` of a component, the set of scale
indices of its birth events (the sets count only births since the supplied seed, whose
components have empty birth set). -/

/-- `𝖡(v) = {e.scale : e ∈ births v}`. -/
def compBirthSet (c : Comp) : Finset ℕ :=
  (c.births.map BirthEvent.scale).toFinset

/-! The (birth) grade `g(v)` of a component: every component of a
supplied seed has grade zero and each birth event, however long its word, raises the grade by
one. -/

/-- The grade `g(v)`: the number of birth events in the history. -/
def compGrade (c : Comp) : ℕ :=
  c.births.length

/-! The source graph is acyclic of depth at most `H`: every
directed path `u_0 → u_1 → ⋯ → u_n` of edges has at most `H` edges. A bound on all path lengths
excludes cycles. -/

/-- There is no directed path of `H + 1` edges: for every `p : Fin (H+2) → ι` some consecutive
pair `p k → p (k+1)` is not an edge (all its constituent lists are empty). -/
def HasDepthAtMost {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (edge : ConstituentEdges D h) (H : ℕ) : Prop :=
  ∀ p : Fin (H + 2) → ι, ∃ k : Fin (H + 1), ∀ d, edge (p k.succ) (p k.castSucc) d = []

end AVRegularity
end
end

section
@[expose] public noncomputable section
namespace AVRegularity

/-! The mass `π_v` of a component computed from its history,
`π_v = π_root ∏_{births} (c_H/|𝔚|) ε_b^{η_b}`. -/

/-- `π_v = π_{root v} ∏_{e ∈ births v} (c_H / |𝔚|) ε_{e.scale}^{η_b}`. -/
def compMass (q : ℝ) (Λ : ℕ) (law : BirthLaw) (c : Comp) : ℝ :=
  law.rootMass c.root *
    (c.births.map fun e => law.cH / (law.wordCount : ℝ) * ocEpsilon q Λ e.scale ^ law.etaB).prod

/-! The readout factor `ω_v` of a component computed from its
history, `ω_v = ω_root ∏_{births} (ε_b^{η_0})^{|w|}`. Readout
factors and masses are separate quantities and are never used for one another. -/

/-- `ω_v = ω_{root v} ∏_{e ∈ births v} (ε_{e.scale}^{η_0})^{|e.word|}`. -/
def compReadout (q : ℝ) (Λ : ℕ) (law : BirthLaw) (c : Comp) : ℝ :=
  law.rootReadout c.root *
    (c.births.map fun e => (ocEpsilon q Λ e.scale ^ law.eta0) ^ e.word.length).prod

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! Definition: conjugation of a charted family by a positive diagonal
marker, `A^♯ = d A d^{-1}`: every field of the edge `u → v` is multiplied by `d_v/d_u`; maps,
records, pieces, contexts and weights are unchanged, so the estimates hold for both `A` and
`A^♯ = dAd^{-1}`. The envelopes of the marked family are `IsEnvelope (markerConj marker F) ...`.
Meaningful for `marker > 0`. -/

/-- The family with every field of `u → v` multiplied by `marker v / marker u`. -/
def markerConj {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*} (marker : ι → ℝ)
    (F : ChartedFamily ι h D P Ctx) : ChartedFamily ι h D P Ctx :=
  { F with
    flux := fun p c v u γ d I t X z => (marker v / marker u) • F.flux p c v u γ d I t X z
    flux_periodic := fun p c v u γ d I t X n x => by
      have := F.flux_periodic p c v u γ d I t X n x
      simp only [this]
    flux_zero := fun p c v u γ d I hd => by
      funext t X z
      simp [F.flux_zero p c v u γ d I hd] }

end AVRegularity
end
end

section
@[expose] public noncomputable section
namespace AVRegularity

/-! Definition: the positive edge matrix of a family built from the records,
`b_{vu} = √(π_u/π_v) ∑_γ θ_γ` with the tagged size `θ_γ = ‖C_γ‖ θ^♭_γ` (entry size
`θ_{vu} = ∑_γ θ_γ`). The sum is
over all original identities before any Schur sum (no cancellation); an identity with several
current orders is counted once. -/

/-- `b_{vu} = √(π_u/π_v) ∑_{γ ∈ Γ v u} ‖C_γ‖ θ^♭_γ`: each original identity once, however many
current orders it carries. -/
def recordMajorant {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (π : ι → ℝ) (F : ChartedFamily ι h D P Ctx) (v u : ι) : ℝ :=
  Real.sqrt (π u / π v) * ∑ γ : F.Γ v u, ‖(F.identity v u γ).map‖ * (F.identity v u γ).record.size

end AVRegularity
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity

/-! Definition: the declared domains of the envelopes. For each piece `p` and context
`c`, `dom p c ⊆ ℝ × Vec 2` is the set of required pairs `(t, Y)` of output time and
**dimensional** slow label for the chosen window `W`; all real fast phases are allowed, so the
norm domain is `dom p c × 𝕋²`. Coverage is part of the interface: the domain must contain the
slow Taylor segments `(t, y₀ + s(Y - y₀))`, `0 ≤ s ≤ 1`, from the common center `y₀`,
the retained history evaluations and the images used in chart
compositions; whole-space estimates take `dom = W ×ˢ univ`. -/

namespace ChartedFamily

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The whole-space domain over the time window `W`: `W ×ˢ univ` for every piece and context. -/
def Domain.window (F : ChartedFamily ι h D P Ctx) (W : Set ℝ) : F.Domain :=
  fun _ _ => W ×ˢ Set.univ

end ChartedFamily

end AVRegularity
end
end

section
@[expose] public noncomputable section
namespace AVRegularity

/-! The positive diagonal marker `d_v = ∏_{k ∈ 𝖡(v)} ε_k^{-ι}` (marker `I` when `𝖡(v)` is
empty). -/

/-- `d_v = ∏_{k ∈ 𝖡(v)} ε_k^{-ι}`. -/
def compMarker (q : ℝ) (Λ : ℕ) (law : BirthLaw) (c : Comp) : ℝ :=
  ∏ k ∈ compBirthSet c, ocEpsilon q Λ k ^ (-law.iota)

/-! Definition: the marked and inflated positive edge matrix, the entries of
`d A^♯ d^{-1}` for the record majorant inflated once by the price `f_γ`:
`b^♯_{vu} = (d_v/d_u) √(π_u/π_v) ∑_γ ‖C_γ‖ θ^♭_γ f_γ`: each record is priced once by `f_γ`,
and for a positive marker `d_v` each entry is conjugated by `d_v/d_u`.
The ordinary (unmarked) inflated matrix is the case of the constant marker `1`. -/

/-- `b^♯_{vu} = (d_v/d_u) √(π_u/π_v) ∑_{γ ∈ Γ v u} ‖C_γ‖ θ^♭_γ f_γ` (each identity once, priced
once at its original order). -/
def pricedRecordMajorant {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (π marker : ι → ℝ) (F : ChartedFamily ι h D P Ctx) (v u : ι) : ℝ :=
  marker v / marker u * Real.sqrt (π u / π v) *
    ∑ γ : F.Γ v u, ‖(F.identity v u γ).map‖ * (F.identity v u γ).record.size *
      constituentPrice (F.identity v u γ).record

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! A one-chart edge family as a charted family. -/

namespace ChartedFamily

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- A one-chart edge family as a charted family with the single trivial piece and context: each
constituent of order `d` is an identity of maximal order `d`, with weight `1`. -/
def ofFiber (edge : ConstituentEdges D h) : ChartedFamily ι h D Unit (fun _ => Unit) where
  Γ v u := Σ d : Finset.Icc 2 D, Fin (edge v u d).length
  identity v u γ :=
    { map := ((edge v u γ.1).get γ.2).map
      record := ((edge v u γ.1).get γ.2).record
      maxOrder := γ.1.1
      two_le := (Finset.mem_Icc.1 γ.1.2).1
      le_D := (Finset.mem_Icc.1 γ.1.2).2
      le_birth := ((edge v u γ.1).get γ.2).birthExcess_ge }
  piece _ := ChartPiece.trivial
  flux _ _ v u γ d I :=
    if hd : d = γ.1.1 then ((edge v u γ.1).get γ.2).coeff (by subst hd; exact I)
    else fun _ _ _ => 0
  flux_periodic := by
    intro p c v u γ d I t X
    by_cases hd : d = γ.1.1
    · subst hd
      simpa using ((edge v u γ.1).get γ.2).periodic I t X
    · simp only [hd, dite_false]
      intro n x
      rfl
  flux_zero := by
    intro p c v u γ d I hd
    have : d ≠ γ.1.1 := fun h' => hd ⟨h' ▸ (Finset.mem_Icc.1 γ.1.2).1, h'.le⟩
    simp [this]
  weight _ _ := 1
  weight_nonneg _ _ := zero_le_one
  weight_zero _ t ht := absurd (Set.mem_univ t) ht
  locally_finite a b := Set.toFinite _
  weight_sum t _ := by
    show ∑ᶠ _ : Unit, (1 : ℝ) = 1
    rw [finsum_unique]

end ChartedFamily

end AVRegularity
end
end

section
@[expose] public noncomputable section
namespace AVRegularity

/-! Definition: the marked and inflated ledger `S^♯`, the maximum of the
ordinary and the marked full row and column sums of the inflated positive records. -/

/-- `S^♯ = max{ fullLedger (b^♯ with marker 1), fullLedger (b^♯ with the marker d) }`. -/
def markedLedger {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (π marker : ι → ℝ) (F : ChartedFamily ι h D P Ctx) : ℝ :=
  max (fullLedger (pricedRecordMajorant π (fun _ => 1) F))
    (fullLedger (pricedRecordMajorant π marker F))

end AVRegularity
end
end
