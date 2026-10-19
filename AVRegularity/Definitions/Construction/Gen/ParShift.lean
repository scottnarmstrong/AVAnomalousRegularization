-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Families.MarkedLedger
public import AVRegularity.Statements.Intermediate.CycleReference.StreamFlow
public import AVRegularity.Statements.Intermediate.CycleReference.JacMatrix
public import AVRegularity.Definitions.CycleReference.OcRefCorrector
public import AVRegularity.Statements.Intermediate.CycleOutput.OcPulseWindow
public import AVRegularity.Statements.Intermediate.CycleOutput.OcPulseCellDrift
public import AVRegularity.Statements.Construction.OcA
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCellFieldInverse

section
section
@[expose] public section
namespace AVRegularity

/-! Definition: the inductive syntax `Gen` of generated
coefficients. A generated coefficient is a finite expression, a finite tree whose nodes are
applications of the constructor kinds (K1)–(K6) below to the nodes below them, together with
the transverse primitive and the ordered higher Piola transfer and, for a supplied
seed, finitely many already solved two-dimensional cell inverses, on their original
intervals with their original initial states and real internal phases.

Sorts: a *context function* of level `i` over a slot `𝗉` of
level `i` (`GenSort.ctx`, a function of `(t, 𝔠)`, `𝔠 = (𝒜, ζ_i)`); a *family function* of level
`i-1` over a slot `𝗉` of level `i` (`GenSort.fam`, a function of `(t, 𝒜)`; it is indexed by the
level `i` of its slot); a *cell function* of level `i` over `𝗉` (`GenSort.cell`, a function of
`(t, 𝒜, η)` with real internal phase `η`). The index `(i, p)` of every node is the slot assigned
by the rules: (K2), (K3), (K5) keep the slot of their inputs, (K4) solves on the output
interval of its slot, (K6) passes from `𝗉` to a finer slot `𝗉' ≺ 𝗉` of level `i+1`.

Constructors, by kind:
* (K1) `geo fr L`: an entry of the Jacobian `F_t(0)`, its inverse, the molecular metric
  `𝒢_t(0)` or the strain `∂_uF_u(0)F_u(0)⁻¹` of the family (`fr = own`) or of the child
  appended by (K6) for the finer slot `𝗉'` (`fr = child p'`), at the output time; `drift c`: the
  component `c` of the actual normalized cell drift of the pulse (a sine mode in the internal
  phase with time-only amplitude); `time L`: a time-only function with its original anchor and
  full horizon (time cutoff/partition weight, covariance primitive, flat reference tensor,
  integration constant).
* (K2) `add`, `mul`: sums and products, in their original order.
* (K3) `dOld j` (old-label derivative `∂_{h_j} a(t, 𝔠^{[h]})|_{h=0}`), `dPhase` (derivative in
  the final phase `ζ_{i,q_i}`), `dSlowFam j`, `dSlowCell j` (slow derivatives of family and cell
  functions at fixed internal phase), `dInternal` (`∂_{η_{q_i}}`).
* (K4) `restrict` (a context function at real phases is a cell function) and `cellInv F t₀ ι`:
  the transverse cell inverse of the flux `F` with metric `𝒢_u(0)` of the family, the actual
  drift, original start `t₀` and initial state `ι` (the constructor uses `t₀ = inf J_𝗉` and
  `ι = 0`; a cell-inverse node records its original interval start and initial state,
  ordinary constructor data).
* `transPrim`: the transverse primitive (Fourier multiplier `(2πih)⁻¹`, zero mean).
  
* `solved G v F q t₀ t₁ c sZ ι`: an already solved two-dimensional cell inverse of a supplied
  seed: the original two-dimensional molecular cell equation of the weak levels,
  with metric `G` (family functions), full
  PDE drift `v`, flux `F`, centered scalar source `q`, original interval `[t₀,t₁]` in the cell time
  `t/c`, original initial state `ι`, fast regularity order `sZ`.
* (K5) `mean`: the average over the real internal phase.
* (K2) `famCell c`: a family function read as a cell function independent of the internal phase
  (the mean-times-cell products of the cell recursions).
* (K6) `evalChild p' c`: `ϖ_{𝗉'}(t) c(t, 𝒜^♮)`. The Piola factors `J⁻¹ ⋯ J⁻ᵀ` with
  `J = F^♮_t(0)⁻¹ F_t(0)` and the higher transfer are products (K2) of the letters (K1)
  `geo own` and `geo (child p')` and their old-label derivatives (K3)(a), applied to this node.
Values are scalar: a matrix- or vector-valued coefficient is the array of its scalar entries, and
an ordered matrix product is a sum of ordered scalar products (K2). -/

/-- The three kinds of functions of the generated carrier. -/
inductive GenSort : Type
  /-- Context functions `a(t, (𝒜, ζ_i))`. -/
  | ctx
  /-- Family functions `c(t, 𝒜)`. -/
  | fam
  /-- Cell functions `ω(t, 𝒜, η)`, `η` real. -/
  | cell
  deriving DecidableEq

/-- The time-only letters (K1), with their original anchors and full horizons. -/
inductive TimeLetter : Type
  /-- The partition weight `ϖ_{lev,k}(t)` of the slot `k` of level `lev`. -/
  | partition (lev : ℕ) (k : ℤ)
  /-- The entry `(a,b)` of the covariance primitive `∫_s^t (𝖩_lev - κ_{lev-1} I)` of level `lev`
  with its anchor `s`. -/
  | covPrimitive (lev : ℕ) (s : ℝ) (a b : Fin 2)
  /-- The entry `(a,b)` of the flat reference tensor `𝖩_lev(t)` of level `lev`. -/
  | refFlux (lev : ℕ) (a b : Fin 2)
  /-- A real constant (an integration constant or a numerical factor). -/
  | const (c : ℝ)

/-- The geometric letters (K1) of a family at the output time. -/
inductive GeoLetter : Type
  /-- The entry `(a,b)` of the Jacobian `F_t(0)`. -/
  | jac (a b : Fin 2)
  /-- The entry `(a,b)` of `F_t(0)⁻¹`. -/
  | jacInv (a b : Fin 2)
  /-- The entry `(a,b)` of the molecular metric `𝒢_t(0) = F⁻¹F⁻ᵀ`. -/
  | metric (a b : Fin 2)
  /-- The entry `(a,b)` of the strain `∂_uF_u(0)F_u(0)⁻¹` at `u = t`. -/
  | strain (a b : Fin 2)

/-- The family carrying a geometric letter: the family of the context, or its child appended by
(K6) for the finer slot `p'`. -/
inductive GenFrame : Type
  /-- The family of the context. -/
  | own
  /-- The child `𝒜^♮` appended for the finer slot `p'`. -/
  | child (p' : ℤ)

/-- Generated expressions of sort `s` over the slot `p` of level `i`. -/
inductive Gen : GenSort → ℕ → ℤ → Type
  /-- (K1) A geometric letter. -/
  | geo {i : ℕ} {p : ℤ} (fr : GenFrame) (L : GeoLetter) : Gen .ctx i p
  /-- (K1) The component `c` of the normalized cell drift `w = √η v` of the pulse. -/
  | drift {i : ℕ} {p : ℤ} (c : Fin 2) : Gen .cell i p
  /-- (K1) A time-only letter. -/
  | time {s : GenSort} {i : ℕ} {p : ℤ} (L : TimeLetter) : Gen s i p
  /-- (K2) A sum. -/
  | add {s : GenSort} {i : ℕ} {p : ℤ} : Gen s i p → Gen s i p → Gen s i p
  /-- (K2) A product in the order written. -/
  | mul {s : GenSort} {i : ℕ} {p : ℤ} : Gen s i p → Gen s i p → Gen s i p
  /-- (K3)(a) The old-label derivative in the direction `j`. -/
  | dOld {i : ℕ} {p : ℤ} (j : Fin 2) : Gen .ctx i p → Gen .ctx i p
  /-- (K3)(a) The derivative in the final phase `ζ_{i,q_i}`. -/
  | dPhase {i : ℕ} {p : ℤ} : Gen .ctx i p → Gen .ctx i p
  /-- (K3)(b) The slow derivative of a family function in the direction `j`. -/
  | dSlowFam {i : ℕ} {p : ℤ} (j : Fin 2) : Gen .fam i p → Gen .fam i p
  /-- (K3)(b) The slow derivative of a cell function at fixed internal phase. -/
  | dSlowCell {i : ℕ} {p : ℤ} (j : Fin 2) : Gen .cell i p → Gen .cell i p
  /-- (K3)(c) The derivative `∂_{η_{q_i}}` in the internal phase. -/
  | dInternal {i : ℕ} {p : ℤ} : Gen .cell i p → Gen .cell i p
  /-- (K4) The restriction of a context function to real phases. -/
  | restrict {i : ℕ} {p : ℤ} : Gen .ctx i p → Gen .cell i p
  /-- (K4) The transverse cell inverse of the flux `F`, with original start `t₀` and initial
  state `ι`. -/
  | cellInv {i : ℕ} {p : ℤ} (F : Fin 2 → Gen .cell i p) (t₀ : ℝ) (ι : Gen .cell i p) :
      Gen .cell i p
  /-- The transverse primitive. -/
  | transPrim {i : ℕ} {p : ℤ} : Gen .cell i p → Gen .cell i p
  /-- An already solved two-dimensional cell inverse of a seed (the weak-level molecular cell
  equation `∂_𝗍Z - div_z(G∇_zZ) + v·∇_zZ = div_zF + q`), with metric `G`, full PDE drift `v`
  (`Pe_j v_j` at a weak level), flux `F`, centered scalar source `q`, original interval
  `[t₀, t₁]` in the cell time `t/c` (`c = ε_j²/κ` with the terminal diffusivity `κ` at a weak
  level), fast order `sZ` and original initial state `ι`. -/
  | solved {i : ℕ} {p : ℤ} (G : Fin 2 → Fin 2 → Gen .fam i p) (v F : Fin 2 → Gen .cell i p)
      (q : Gen .cell i p) (t₀ t₁ c : ℝ) (sZ : ℕ) (ι : Gen .cell i p) : Gen .cell i p
  /-- (K5) The mean over the real internal phase. -/
  | mean {i : ℕ} {p : ℤ} : Gen .cell i p → Gen .fam i p
  /-- (K2) A family function of the same slot read as a cell function, independent of the real
  internal phase: the factor of a product of a mean with cell functions on the same family. -/
  | famCell {i : ℕ} {p : ℤ} : Gen .fam i p → Gen .cell i p
  /-- (K6) Evaluation in the coarser chart through the child for the finer slot `p'`. -/
  | evalChild {i : ℕ} {p : ℤ} (p' : ℤ) : Gen .fam (i + 1) p' → Gen .ctx i p

end AVRegularity
end
end

section
/-! Definition: the positive path provenance of a constituent
identity and its structural recursions (birth list, orders, positive witness, length, width,
kernel source).

A constituent identity of a generated family is a finite tree:
* `seed k tag`: the identity `k` of a supplied seed, with its recorded tags (`SeedTag`);
* `dir m γ`: the direct transport at the passage of level `m` of the identity `γ`: the all-slow
  one-edge higher part `ℓ^{-2}η^d P𝐒_d I`, `d ≥ 3` (`𝐄_dir`); a direct term keeps the birth
  level and the birth list of its old constituent, and so does every constituent of order at
  least three obtained from it by the higher transfer; direct transports keep their original
  kernel and tags;
* `quad m path`: the quadratic conversion of the cell-degree-two path summand of the path `path`
  at the passage of level `m` (`𝐄_2`): a quadratic output of a path has no birth level, and its
  birth list is the union of the lists along the path; it receives the kernel, and the length,
  of one of its input constituents of largest width, and its order is two; the input chosen is
  the first input of maximal width along the path. A quadratic output has
no mathematical birth level: the stored `birthLevel` is that of the chosen input and is inert
bookkeeping (the record requires a natural number); no birth occurrence is added, its
`birthExcess` is zero and no fresh-birth factor is inferred from it. The empty-path branch is a
totalization, unreachable for an actual conversion (`Prov.quad_widest_isSome`);
* `letter m l path`: the fresh constituent of the letter `l` of the passage of level `m` along
  `path` (empty for the diagonal letter `𝖣`, which acts as the identity map on each component):
  birth level `m-1`, the union of the lists along its path together with the new letter as its
  birth list, the fresh kernel `S_m` of width `r_m = E^{σ₀}ρ_m` and length `ρ_m`.
A path is the list of its steps `(target, source, identity)` in the order of the path.

The positive witness is the recursion `witness`: the scalar majorants `θ̄^w` multiply a direct
transport by `C`, a quadratic path by `C∏θ̄^w`, and a new letter at `b` by
`w_b C ε_b^{δ-η₀}∏θ̄^w`, with empty product for `𝖣`; the seed
witness is its supplied record size. The order recorded is the maximal current order `D_γ`:
a direct transport keeps it (the higher transfer lowers the order of a term but keeps the
identity); a fresh letter has its present order (`letterOrder`: `𝖬_{n,h}` has order at most
`n`, `𝖵_{n,h,a,a'}` at most `n + 2(a+a')`, the first source at most `N + 1 + 4p`). -/

@[expose] public noncomputable section

namespace AVRegularity

/-- The recorded tags of a seed identity: witness, birth level, original excess, length, width,
birth list and maximal current order. -/
structure SeedTag where
  /-- The positive witness (record size) `θ^♭_γ`. -/
  size : ℝ
  /-- The birth level `b(γ)`. -/
  birthLevel : ℕ
  /-- The original excess `d^birth_γ - 2`. -/
  birthExcess : ℕ
  /-- The original length `R_γ`. -/
  length : ℝ
  /-- The kernel width `r_γ`. -/
  width : ℝ
  /-- The birth list (levels). -/
  births : List ℕ
  /-- The maximal current order `D_γ`. -/
  maxOrder : ℕ

/-- The positive path provenance of a constituent identity. -/
inductive Prov : Type
  /-- The identity `k` of a supplied seed with its tags. -/
  | seed (k : ℕ) (tag : SeedTag)
  /-- The direct transport at the passage of level `m`. -/
  | dir (m : ℕ) (src : Prov)
  /-- The quadratic conversion of a path summand at the passage of level `m`. -/
  | quad (m : ℕ) (path : List (Comp × Comp × Prov))
  /-- The fresh constituent of the letter `l` at the passage of level `m` along a path. -/
  | letter (m : ℕ) (l : WordLetter) (path : List (Comp × Comp × Prov))

/-- The kernel of an identity: a seed kernel (original geometry kept), or the fresh kernel born
at a level. -/
inductive KernelKey : Type
  /-- The original kernel of the seed identity `k`. -/
  | seed (k : ℕ)
  /-- The fresh kernel born at the level `b`. -/
  | fresh (b : ℕ)

/-- The parameters of the tag recursion: the witness constant `C`, the birth inflations `w_b`,
the wavelengths `ε_b`, the exponents `δ, η₀`, the menus `N, p`, and the fresh birth length
`R_b` and width `r_b`. -/
structure ProvParams where
  /-- The witness constant `C`. -/
  C : ℝ
  /-- The inflation `w_b ≥ 1` at a birth of level `b`. -/
  w : ℕ → ℝ
  /-- The wavelengths `ε_b`. -/
  eps : ℕ → ℝ
  /-- The exponent `δ`. -/
  δ : ℝ
  /-- The readout exponent `η₀`. -/
  η0 : ℝ
  /-- The cell cutoff `N`. -/
  N : ℕ
  /-- The covariance degree `p`. -/
  p : ℕ
  /-- The fresh birth length `R_b`. -/
  Rb : ℕ → ℝ
  /-- The fresh birth width `r_b`. -/
  rb : ℕ → ℝ

/-- The recorded tags of an identity. -/
structure ProvTags where
  /-- The maximal current order `D_γ`. -/
  order : ℕ
  /-- The birth level. -/
  birthLevel : ℕ
  /-- The original excess `d^birth - 2`. -/
  birthExcess : ℕ
  /-- The original length. -/
  length : ℝ
  /-- The kernel width. -/
  width : ℝ
  /-- The birth list. -/
  births : List ℕ
  /-- The positive witness. -/
  witness : ℝ
  /-- The kernel. -/
  kernel : KernelKey

/-- The present order of a fresh letter. The first source `𝖣` has order `N + 1 + 4p` (compare
`N_src,e` in display (14.2) of the paper). -/
def letterOrder (N p : ℕ) : WordLetter → ℕ
  | .diag => N + 1 + 4 * p
  | .mean n _ => n
  | .covariance n _ a a' => n + 2 * (a + a')
  | .eddy n => n
  | .padding _ => 2

/-- The first tags of maximal width in a list (`none` for the empty list). -/
def widestTags : List ProvTags → Option ProvTags
  | [] => none
  | t :: ts =>
      match widestTags ts with
      | none => some t
      | some t' => if t.width < t'.width then some t' else some t

mutual
/-- The tags of an identity. -/
def Prov.tags (P : ProvParams) : Prov → ProvTags
  | .seed k tag =>
      { order := tag.maxOrder, birthLevel := tag.birthLevel, birthExcess := tag.birthExcess,
        length := tag.length, width := tag.width, births := tag.births, witness := tag.size,
        kernel := .seed k }
  | .dir _ src =>
      let t := src.tags P
      { t with witness := P.C * t.witness }
  | .quad m path =>
      let ts := Prov.pathTags P path
      match widestTags ts with
      | none =>
          { order := 2, birthLevel := m - 1, birthExcess := 0, length := P.Rb (m - 1),
            width := P.rb (m - 1), births := [], witness := P.C, kernel := .fresh (m - 1) }
      | some tw =>
          { order := 2, birthLevel := tw.birthLevel, birthExcess := 0, length := tw.length,
            width := tw.width, births := (ts.map ProvTags.births).flatten,
            witness := P.C * (ts.map ProvTags.witness).prod, kernel := tw.kernel }
  | .letter m l path =>
      let ts := Prov.pathTags P path
      { order := letterOrder P.N P.p l, birthLevel := m - 1,
        birthExcess := letterOrder P.N P.p l - 2, length := P.Rb (m - 1), width := P.rb (m - 1),
        births := (ts.map ProvTags.births).flatten ++ [m - 1],
        witness := P.w (m - 1) * P.C * P.eps (m - 1) ^ (P.δ - P.η0) *
          (ts.map ProvTags.witness).prod,
        kernel := .fresh (m - 1) }
/-- The tags of the identities of a path, in order. -/
def Prov.pathTags (P : ProvParams) : List (Comp × Comp × Prov) → List ProvTags
  | [] => []
  | (_, _, x) :: rest => x.tags P :: Prov.pathTags P rest
end

theorem widestTags_isSome {l : List ProvTags} (hl : l ≠ []) : (widestTags l).isSome := by
  cases l with
  | nil => exact absurd rfl hl
  | cons t ts =>
      simp only [widestTags]
      split <;> [rfl; split <;> rfl]

theorem Prov.pathTags_length (P : ProvParams) (path : List (Comp × Comp × Prov)) :
    (Prov.pathTags P path).length = path.length := by
  induction path with
  | nil => simp [Prov.pathTags]
  | cons x rest ih =>
      obtain ⟨a, c, y⟩ := x
      simp [Prov.pathTags, ih]

/-- The empty-path totalization of `quad` is unreachable for a nonempty path: an
actual quadratic conversion has a widest input. -/
theorem Prov.quad_widest_isSome (P : ProvParams) {path : List (Comp × Comp × Prov)}
    (hp : path ≠ []) : (widestTags (Prov.pathTags P path)).isSome := by
  apply widestTags_isSome
  intro h
  have := Prov.pathTags_length P path
  rw [h] at this
  exact hp (List.length_eq_zero_iff.mp this.symm)

/-- The constituent record agrees with the tags (size = witness). -/
def ProvTags.Matches (t : ProvTags) (r : ConstituentRecord) : Prop :=
  r.size = t.witness ∧ r.birthLevel = t.birthLevel ∧ r.birthExcess = t.birthExcess ∧
    r.length = t.length ∧ r.width = t.width ∧ r.births = t.births

end AVRegularity
end
end

section
@[expose] public noncomputable section

section
open Homogenization AVenhance
namespace AVRegularity

/-! Definition (`Gen`): the construction data on which generated coefficients are
evaluated, and the scalar helpers of the generated carrier.

* `OCData`: the construction `(α, q, Λ, ζ)`, the stream sequence `Φ` with admissibility at every
  level (so that the flows `X_k = streamFlow (Φ k)` exist), and the diffusivity chain `κ`
  (`κ_i` enters the cell time `ℓ_i² = ε_i²/κ_i` of the transverse inverse).
* `slotAnchor i p = l_{i,p} τ_i''`: the renewal anchor `s_𝗉` of the odd slot `𝗉 = p` of level `i`.
  
* `slotStart i p = (p - 61/48) τ_i`: the original start `inf J_𝗉`.
* `transverseIndex p`: the transverse coordinate `q` of the pulse `p` (the shear of a pulse
  `k ∈ 4ℤ+1` depends on `y₁`, of `k ∈ 4ℤ+3` on `y₂`).
* `relDisp i p u s θ = d_i(u; s, θ)`: the relative displacement of level `i` on the pulse `p`.
  The material equation of the
  unswept relative stream `∑_k p_k ψ_{i,k}` preserves the transverse coordinate, so
  `ε_i d_i(u;s,θ) = (∫_s^u p_p) 𝐮_{i,p}(ε_i θ)` with the pulse `p_p = ocPulse` and shear
  velocity `𝐮_{i,p} = ocShearVel`. -/

/-- The data of the construction used by the generated carrier: `(α, q, Λ, ζ)`, the stream
sequence `Φ` (admissible at every level), the diffusivity chain `κ` and the terminal level. -/
structure OCData where
  /-- The Hölder exponent `α`. -/
  α : ℝ
  /-- The scale ratio exponent `q`. -/
  q : ℝ
  /-- The integer `Λ`. -/
  Λ : ℕ
  /-- The fast profile `ζ`. -/
  ζ : ℝ → ℝ
  /-- The stream sequence `Φ`. -/
  Φ : ℕ → ℝ → Vec 2 → ℝ
  /-- Every stream of the sequence is admissible. -/
  hΦ : ∀ m, IsAdmissibleStream (Φ m)
  /-- The diffusivity chain `κ_m`. -/
  κ : ℕ → ℝ
  /-- The terminal level `M`: at a weak level `j > M` the cell clock of a solved node uses the
  terminal diffusivity `κ_M`, not an extrapolation of the chain.
  Every statement ties it to its terminal level by the premise `D.term = M`. -/
  term : ℕ

namespace OCData

variable (D : OCData)

/-- `ε_k`. -/
def eps (k : ℕ) : ℝ := ocEpsilon D.q D.Λ k

/-- The flow `X_k(t,x,s)` of `b_k = ∇^⊥ Φ_k`. -/
def flowOf (k : ℕ) : ℝ → Vec 2 → ℝ → Vec 2 := streamFlow (D.Φ k) (D.hΦ k)

/-- The renewal anchor `s_𝗉 = l_{i,p} τ_i''` of the slot `p` of level `i`. -/
def slotAnchor (i : ℕ) (p : ℤ) : ℝ := (ocLabel D.α D.q D.Λ i p : ℝ) * ocTauPP D.α D.q D.Λ i

/-- The original start `inf J_𝗉 = (p - 61/48) τ_i` of the slot `p` of level `i`. -/
def slotStart (i : ℕ) (p : ℤ) : ℝ := ((p : ℝ) - 61 / 48) * ocTau D.α D.q D.Λ i

/-- The cell diffusivity of level `i`: `κ_i` for `i ≤ M`, and the terminal `κ_M` at a weak level
`i > M` (the uniform terminal-diffusivity convention). -/
def kap (i : ℕ) : ℝ := D.κ (min i D.term)

/-- The cell time scale `ℓ_i² = ε_i² / κ_{min(i,M)}` (terminal diffusivity at weak levels). -/
def cellScaleSq (i : ℕ) : ℝ := D.eps i ^ 2 / D.kap i

/-- The relative displacement `d_i(u; s, θ)` of level `i` on the pulse `p`:
`ε_i⁻¹ (∫_s^u p_p) 𝐮_{i,p}(ε_i θ)`. -/
def relDisp (i : ℕ) (p : ℤ) (u s : ℝ) (θ : Vec 2) : Vec 2 :=
  (D.eps i)⁻¹ • ((∫ v in s..u, ocPulse D.α D.q D.Λ D.ζ i p v) •
    ocShearVel D.α D.q D.Λ i p (D.eps i • θ))

end OCData

/-- The transverse coordinate `q` of the pulse `p`: `0` for `p ∈ 4ℤ+1`, `1` for `p ∈ 4ℤ+3`. -/
def transverseIndex (p : ℤ) : Fin 2 := if p % 4 = 3 then 1 else 0

end AVRegularity
end

section
open Homogenization
namespace AVRegularity

/-! Definition (`Gen`): real centered chains, the real points of the generated
carrier.

A chain is a base family of level `j'-1` followed by one child at each level `j', …, i-1`. Its
discrete data are the levels and the scheduled slots `𝗉_{j'}, …, 𝗉_i` (the base family has the
anchor `s_{𝗉_{j'}}`, the child of level `k` the anchor `s_{𝗉_{k+1}}`); its parameters are the
base label `Y`, the centers `c_k` and the phases `ζ_k` of the children. Here all parameters are
real. The generated coefficients are defined at real parameters; their holomorphic extension to
the complex domains `𝔇_i(𝗆;𝗉)` is a property, used only by the
analytic sizes, and is never needed to define a coefficient.

At real parameters every family of a chain is the centered map of an *offset flow*:

`𝒜_u(h) = 𝔛(u, x_𝒜 + h, s) - 𝔛(u, x_𝒜, s)`, with `𝔛 = X_{j'-1}` and `x_𝒜 = Y` for the base
family and, for the child with center `c`, anchor `s'` and phase `ζ` of a parent `(𝔛, x_𝒜, s)`,
`γ = ζ - (x_𝒜 + c)/ε'`, `Z_γ(u;r,y) = y + ε' d_k(u; r, y/ε' + γ)`,
`𝔛'(u,x,r) = 𝔛(u, Z_γ(u; r, 𝔛(s,x,r)), s)`, `x_{𝒜'} = 𝔛(s', x_𝒜 + c, s)`
(the inverse `Φ_p(r,·)⁻¹ = 𝔛(s,·,r)` is the group law of the parent flow). This is an explicit
recursion; no inverse function is chosen. The geometric letters are the Jacobian
`F_u(0) = D_x 𝔛(u, x_𝒜, s)`, its inverse, the molecular metric `𝒢 = F⁻¹F⁻ᵀ` and the strain
`∂_u F F⁻¹` (the letters of kind (K1)).

Recentering: a base family with label `Y` becomes the base family
with label `Y + h`; a last child `(c, s', ζ)` becomes the child with center `c + R(h)` and phase
`ζ + R(h)/ε'`, where `R` is the inverse of `𝒜̃_{s'}`; at real parameters
`R(h) = 𝔛(s, x' + h, s') - x_𝒜 - c` with `x' = 𝔛(s', x_𝒜 + c, s)`.

Appending (kind (K6)): the child `𝒜^♮` of the last
family, for a finer slot `𝗉'`, at the output time `t` and final phase `ζ`, has anchor `s_{𝗉'}`,
center `ε_i d_i(s_{𝗉'}; t, ζ)` and phase `ζ + d_i(s_{𝗉'}; t, ζ)`. -/

section
/-- A child of a chain: its center `c` and phase `ζ` (real parameters). -/
structure ChainChild where
  /-- The center `c`. -/
  center : Vec 2
  /-- The phase `ζ`. -/
  phase : Vec 2

/-- A real scheduled chain: the level `j'-1` of the base family, the slots `𝗉_{j'}, …, 𝗉_i`, the
base label `Y` and the children of levels `j', …, i-1`. -/
structure RealChain where
  /-- The level `j'-1` of the base family. -/
  baseLevel : ℕ
  /-- The slots `𝗉_{j'}, …, 𝗉_i` (the slot of level `j'` first). -/
  slots : List ℤ
  /-- The base label `Y`. -/
  base : Vec 2
  /-- The children of levels `j', …, i-1`, in increasing level. -/
  children : List ChainChild

/-- The geometry of a family at real parameters: the offset flow `𝔛(u,x,r)`, the center point
`x_𝒜` and the anchor `s`. -/
abbrev ChainGeom : Type := (ℝ → Vec 2 → ℝ → Vec 2) × Vec 2 × ℝ

namespace OCData

variable (D : OCData)

/-- The geometry of the child of level `k` (pulse `pk`, anchor `s'`, center and phase `c`) of a
family with geometry `g`. -/
def childGeom (k : ℕ) (pk : ℤ) (s' : ℝ) (c : ChainChild) (g : ChainGeom) : ChainGeom :=
  (fun u x r => g.1 u ((g.1 g.2.2 x r) + D.eps k • D.relDisp k pk u r
      ((D.eps k)⁻¹ • (g.1 g.2.2 x r) + (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)))) g.2.2,
    g.1 s' (g.2.1 + c.center) g.2.2, s')

/-- The geometry after the children `cs` of levels `k, k+1, …`, with the slots `𝗉_k, 𝗉_{k+1}, …`. -/
def geomAux : ℕ → List ℤ → List ChainChild → ChainGeom → ChainGeom
  | k, pk :: pk1 :: rest, c :: cs, g =>
      geomAux (k + 1) (pk1 :: rest) cs (D.childGeom k pk (D.slotAnchor (k + 1) pk1) c g)
  | _, _, _, g => g

end OCData

namespace RealChain

variable (D : OCData)

/-- The level `i - 1` of the last family. -/
def lastLevel (ch : RealChain) : ℕ := ch.baseLevel + ch.children.length

/-- The context level `i`. -/
def ctxLevel (ch : RealChain) : ℕ := ch.lastLevel + 1

/-- The slot `𝗉_i` over which the last family lies. -/
def slot (ch : RealChain) : ℤ := ch.slots.getLastD 0

/-- The geometry `(𝔛, x_𝒜, s)` of the last family. -/
def geom (ch : RealChain) : ChainGeom :=
  D.geomAux (ch.baseLevel + 1) ch.slots ch.children
    (D.flowOf ch.baseLevel, ch.base, D.slotAnchor (ch.baseLevel + 1) (ch.slots.headD 0))

/-- The centered map `𝒜_u(h)` of the last family. -/
def famMap (ch : RealChain) (u : ℝ) (h : Vec 2) : Vec 2 :=
  (ch.geom D).1 u ((ch.geom D).2.1 + h) (ch.geom D).2.2 -
    (ch.geom D).1 u (ch.geom D).2.1 (ch.geom D).2.2

/-- The inverse of the centered map, `w ↦ 𝔛(s, 𝔛(u, x_𝒜, s) + w, u) - x_𝒜` (the group law of the
offset flow). -/
def famMapInv (ch : RealChain) (u : ℝ) (w : Vec 2) : Vec 2 :=
  (ch.geom D).1 (ch.geom D).2.2 ((ch.geom D).1 u (ch.geom D).2.1 (ch.geom D).2.2 + w) u -
    (ch.geom D).2.1

/-- The Jacobian `F_u(0)` of the last family. -/
def famJac (ch : RealChain) (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  jacMatrix (fun y => (ch.geom D).1 u y (ch.geom D).2.2) (ch.geom D).2.1

/-- The molecular metric `𝒢_u(0) = F_u(0)⁻¹ F_u(0)⁻ᵀ`. -/
def famMetric (ch : RealChain) (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (ch.famJac D u)⁻¹ * Matrix.transpose (ch.famJac D u)⁻¹

/-- The strain `∂_u F_u(0) F_u(0)⁻¹`. -/
def famStrain (ch : RealChain) (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of (fun a b => deriv (fun u' => ch.famJac D u' a b) u) * (ch.famJac D u)⁻¹

/-- The chain of the parent of the last family (last child and last slot removed). -/
def dropLastChild (ch : RealChain) : RealChain :=
  { ch with slots := ch.slots.dropLast, children := ch.children.dropLast }

/-- The recentered chain `𝒜^{[h]}` (real offset `h`). -/
def recenter (ch : RealChain) (h : Vec 2) : RealChain :=
  match ch.children.getLast? with
  | none => { ch with base := ch.base + h }
  | some c =>
      let g := (ch.dropLastChild).geom D
      let s' := D.slotAnchor (ch.lastLevel + 1) ch.slot
      let x' := g.1 s' (g.2.1 + c.center) g.2.2
      let R := g.1 g.2.2 (x' + h) s' - g.2.1 - c.center
      { ch with children := ch.children.dropLast ++
          [⟨c.center + R, c.phase + (D.eps ch.lastLevel)⁻¹ • R⟩] }

/-- The child `𝒜^♮` appended for the finer slot `p'` at the output time `t` and final phase `ζ`. -/
def appendChild (ch : RealChain) (p' : ℤ) (t : ℝ) (ζ : Vec 2) : RealChain :=
  { ch with
    slots := ch.slots ++ [p']
    children := ch.children ++
      [⟨D.eps ch.ctxLevel • D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) p') t ζ,
        ζ + D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) p') t ζ⟩] }

end RealChain
end

/-! Definition (`Gen`): the scheduling relation and the real points of the graded
generated carrier.

* `IsScheduledIn D i p' p`: the slot `p'` of level `i+1` is scheduled in the slot `p` of level
  `i`, `𝗉' ≺ 𝗉`: the (open) support of `ϖ_{𝗉'}` meets `J_𝗉`.
* `IsCarrierChain D b j₀ i p 𝗆 ch`: `ch` is a real point of `𝔇_i(𝗆;𝗉)`: a scheduled chain over the
  slot `p` of level `i` (odd slots, consecutive slots scheduled, base level at least `j₀ - 1`)
  whose child centers satisfy `|c_k|₁ < λ_𝗆 ε_k`, `λ_𝗆 = (1+𝗆)b/4`. At real points the strip
  conditions on the base label and on the phases are
  vacuous. The recorded construction (anchors, intervals, starts, initial states, primitive
  anchors) is part of the discrete data and of the expression, never a parameter of the chain.
* `IsAdmissibleChain = IsCarrierChain … 2`: the outer definition domain (`λ_2 = 3b/4`). -/

/-- `𝗉' ≺ 𝗉`: the slot `p'` of level `i+1` is scheduled in the slot `p` of level `i`. -/
def IsScheduledIn (D : OCData) (i : ℕ) (p' p : ℤ) : Prop :=
  (Function.support (ocCutoff D.α D.q D.Λ (i + 1) p') ∩ ocPulseWindow D.α D.q D.Λ i p).Nonempty

/-- `ch` is a real point of the carrier `𝔇_i(𝗆;𝗉)` over the slot `p` of level `i`. -/
def IsCarrierChain (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (mres : ℝ) (ch : RealChain) : Prop :=
  ch.ctxLevel = i ∧ j₀ ≤ ch.baseLevel + 1 ∧ ch.slots.length = ch.children.length + 1 ∧
    ch.slot = p ∧ (∀ q ∈ ch.slots, Odd q) ∧
    (∀ k : ℕ, ∀ hk : k + 1 < ch.slots.length,
      IsScheduledIn D (ch.baseLevel + 1 + k) (ch.slots[k + 1]) (ch.slots[k])) ∧
    ∀ k : ℕ, ∀ hk : k < ch.children.length,
      ∑ a : Fin 2, |(ch.children[k]).center a| < (1 + mres) * b / 4 * D.eps (ch.baseLevel + 1 + k)

/-- The outer definition domain: real points of `𝔇_i(2;𝗉)`. -/
def IsAdmissibleChain (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (ch : RealChain) : Prop :=
  IsCarrierChain D b j₀ i p 2 ch

end AVRegularity
end

section
open Homogenization MeasureTheory
namespace AVRegularity

/-! Definition (`Gen`): the semantic values of the three sorts at real parameters
and the explicit operations of the constructors.

* `GenSort.Sem`: a context function is `(t, chain, ζ_i) ↦ a`, a family function `(t, chain) ↦ c`,
  a cell function `(t, chain, η) ↦ ω` with real internal phase `η`.
* `TimeLetter.eval`: the partition weight `ϖ_{lev,k} = ocCutoff`, the covariance primitive
  `ocCovariance` of level `lev` with diffusivities `(κ_lev, κ_{lev-1})` and its anchor, the flat
  reference tensor `ocRefFlux` of level `lev` at `κ_lev`, a constant.
* `GeoLetter.eval`: the entries of `F_t(0)`, `F_t(0)⁻¹`, `𝒢_t(0)` and the normalized strain of the
  last family of the chain (frame `own`) or of the chain with the (K6) child appended (frame
  `child`). The strain of a family of level `k` is divided by its strain rate
  `a_k = ocA … k` (`k = ch.lastLevel`), and expressions carry the factor `a_k` as an exact `.const`
  time letter; in the child frame, `jac`, `jacInv` and `metric` take their identity
  values where the cutoff `ϖ_{i+1,𝗉'}` of the finer slot vanishes, while the strain keeps its value
  at all times.
* `phaseCoeff q f h = ∫₀¹ f(s e_q) e^{-2πihs} ds`: the Fourier coefficient in the transverse phase
  of a transverse function (it does not depend on `η_p`).
* `transverseInverseSem`: the transverse mode inverse,
  in physical time `t = ℓ_i² t̃`, with an original start `t₀`
  and initial state `ι`:
  `ω̂_h(t) = k_h(t,t₀) ι̂_h(t₀) + (2πih/ℓ²) ∫_{t₀}^t k_h(t,s) F̂_{q,h}(s) ds`,
  `k_h(t,s) = exp(-(4π²h²/ℓ²) ∫_s^t 𝒢_qq(u) du)`, `ω = Re ∑_h ω̂_h e^{2πihη_q}`; the constructor
  has `ι = 0` (and then `ω̂_0 = 0`).
* `transversePrimitiveSem`: `Re ∑_{h≠0} (2πih)⁻¹ f̂_h e^{2πihη_q}`.
* `cellMeanSem`: the average over the unit cell (K5).
The infinite sums are `tsum`s: where a series does not converge the value is the junk value of
`tsum`; the generated class asserts convergence through `Gen.Denotes` only when the semantics is
used in an estimate (the series converge absolutely for generated functions). -/

/-- The semantic values of the three sorts at real parameters. -/
abbrev GenSort.Sem : GenSort → Type
  | .ctx => ℝ → RealChain → Vec 2 → ℝ
  | .fam => ℝ → RealChain → ℝ
  | .cell => ℝ → RealChain → Vec 2 → ℝ

/-- A time-only function as a function of each sort. -/
def GenSort.ofTime : (s : GenSort) → (ℝ → ℝ) → s.Sem
  | .ctx, f => fun t _ _ => f t
  | .fam, f => fun t _ => f t
  | .cell, f => fun t _ _ => f t

/-- The pointwise sum. -/
def GenSort.add : (s : GenSort) → s.Sem → s.Sem → s.Sem
  | .ctx, a, b => fun t c z => a t c z + b t c z
  | .fam, a, b => fun t c => a t c + b t c
  | .cell, a, b => fun t c z => a t c z + b t c z

/-- The pointwise product, in the order written. -/
def GenSort.mul : (s : GenSort) → s.Sem → s.Sem → s.Sem
  | .ctx, a, b => fun t c z => a t c z * b t c z
  | .fam, a, b => fun t c => a t c * b t c
  | .cell, a, b => fun t c z => a t c z * b t c z

/-- The value of a time-only letter at time `t` (with the terminal-diffusivity convention
`OCData.kap` at weak levels). -/
def TimeLetter.eval (D : OCData) : TimeLetter → ℝ → ℝ
  | .partition lev k, t => ocCutoff D.α D.q D.Λ lev k t
  | .covPrimitive lev s a b, t =>
      ocCovariance D.α D.q D.Λ D.ζ lev (D.kap lev) (D.kap (lev - 1)) s t a b
  | .refFlux lev a b, t => ocRefFlux D.α D.q D.Λ D.ζ lev (D.kap lev) t a b
  | .const c, _ => c

/-- The value of a geometric letter for the last family of `ch` at time `u`; the strain is
normalized by the strain rate `a_k = ocA … k` of the level `k = ch.lastLevel` of the family. -/
def GeoLetter.evalAt (D : OCData) (ch : RealChain) (u : ℝ) : GeoLetter → ℝ
  | .jac a b => ch.famJac D u a b
  | .jacInv a b => (ch.famJac D u)⁻¹ a b
  | .metric a b => ch.famMetric D u a b
  | .strain a b => (ocA D.α D.q D.Λ ch.lastLevel)⁻¹ * ch.famStrain D u a b

/-- The strain letters (not gated by the cutoff in the child frame). -/
def GeoLetter.isStrain : GeoLetter → Bool
  | .strain _ _ => true
  | _ => false

/-- The value of a letter at the identity Jacobian: `δ_ab` for `jac`, `jacInv`, `metric`, and `0`
for the strain. -/
def GeoLetter.idVal : GeoLetter → ℝ
  | .jac a b => if a = b then 1 else 0
  | .jacInv a b => if a = b then 1 else 0
  | .metric a b => if a = b then 1 else 0
  | .strain _ _ => 0

/-- The context function of a geometric letter in the frame `fr` over a slot of level `i`. In the
child frame (the child appended for the finer slot `p'`), the letters other than the strain take
their identity values where `ϖ_{i+1,p'}(t) = 0`. -/
def GeoLetter.eval (D : OCData) (i : ℕ) (fr : GenFrame) (L : GeoLetter) : GenSort.Sem .ctx :=
  match fr with
  | .own => fun t ch _ => L.evalAt D ch t
  | .child p' => fun t ch ζ =>
      if L.isStrain = true ∨ ocCutoff D.α D.q D.Λ (i + 1) p' t ≠ 0 then
        L.evalAt D (ch.appendChild D p' t ζ) t
      else L.idVal

/-- The component `c` of the normalized cell drift `w = √η v`, `η = κ_i/κ_{i-1}` (with the terminal
diffusivity at weak levels, `OCData.kap`), of the pulse
`p` of level `i`, at the cell time `t/ℓ_i²` (the (K1) letter is `w`; the cell PDE keeps
the unnormalized `v = ocPulseCellDrift`). -/
def driftSem (D : OCData) (i : ℕ) (p : ℤ) (c : Fin 2) : GenSort.Sem .cell :=
  fun t _ η => Real.sqrt (D.kap i / D.kap (i - 1)) *
    ocPulseCellDrift D.α D.q D.Λ D.ζ i (D.kap i) p (t / D.cellScaleSq i) η c

/-- The Fourier coefficient `∫₀¹ f(s e_q) e^{-2πihs} ds` in the transverse phase. This samples `f`
along `s e_q`: it is the transverse Fourier coefficient only for an input invariant along the
parallel direction. A non-transverse input is projected, not rejected; the
transversality of every generated input of `cellInv`/`transPrim` is part of
`successor_context_certified` (generated coefficients are transverse on pulses,
`IsStageInvariant`), not of the syntax. -/
def phaseCoeff (q : Fin 2) (f : Vec 2 → ℝ) (h : ℤ) : ℂ :=
  ∫ s in (0 : ℝ)..1, ((f (s • basisVec q) : ℝ) : ℂ) *
    Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ) * (s : ℂ)))

/-- The heat kernel `k_h(t,s) = exp(-(4π²h²/ℓ²) ∫_s^t 𝒢_qq)` of the mode `h`. -/
def modeKernel (D : OCData) (i : ℕ) (q : Fin 2) (ch : RealChain) (h : ℤ) (t s : ℝ) : ℂ :=
  ((Real.exp (-(4 * Real.pi ^ 2 * (h : ℝ) ^ 2 / D.cellScaleSq i) *
    ∫ u in s..t, ch.famMetric D u q q) : ℝ) : ℂ)

/-- The transverse cell inverse (K4) of the flux `F` over the slot `p` of level `i`, with
original start `t₀` and initial state `ι`. -/
def transverseInverseSem (D : OCData) (i : ℕ) (p : ℤ) (F : Fin 2 → GenSort.Sem .cell) (t₀ : ℝ)
    (ι : GenSort.Sem .cell) : GenSort.Sem .cell :=
  fun t ch η =>
    (∑' h : ℤ,
      (modeKernel D i (transverseIndex p) ch h t t₀ * phaseCoeff (transverseIndex p) (ι t₀ ch) h +
        (2 * Real.pi * Complex.I * (h : ℂ) / (D.cellScaleSq i : ℂ)) *
          ∫ s in t₀..t, modeKernel D i (transverseIndex p) ch h t s *
            phaseCoeff (transverseIndex p) (F (transverseIndex p) s ch) h) *
      Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * (η (transverseIndex p) : ℂ))).re

/-- The transverse primitive: Fourier multiplier `(2πih)⁻¹` for `h ≠ 0`, zero mean. -/
def transversePrimitiveSem (p : ℤ) (f : GenSort.Sem .cell) : GenSort.Sem .cell :=
  fun t ch η =>
    (∑' h : ℤ, (if h = 0 then 0 else
        (2 * Real.pi * Complex.I * (h : ℂ))⁻¹ * phaseCoeff (transverseIndex p) (f t ch) h) *
      Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * (η (transverseIndex p) : ℂ))).re

/-- The mean (K5) over the real internal phase. -/
def cellMeanSem (ω : GenSort.Sem .cell) : GenSort.Sem .fam :=
  fun t ch => ∫ η in AVenhance.unitCube, ω t ch η

/-! Definition: the evaluation relation `Gen.Denotes D bw j₀ e f`
(the expression `e` denotes the function `f` at real parameters), by structural induction on
the expression, one clause per constructor of `Gen`.

Every clause is functional except `solved`: an already solved two-dimensional cell inverse of a
seed is characterized by its equation, as the finite-past cell inverse
`IsCellFieldInverse` (built on the cell evolution `IsCellSolution`) on its original interval
in its cell time `t/c`, with its original initial state and the scalar source `div_zF + q`.
The relation is required only on the admissible chains of the outer carrier of
its slot (`IsAdmissibleChain D bw j₀ i p`; the construction does not assert the equation on
arbitrary unscheduled chains), which is why `Denotes` carries the carrier width `b` and the
starting level
`j₀`. The node must have a nondegenerate interval `t₀ < t₁` and a positive scale `c > 0`, and its
value is pinned to zero outside the physical interval `[c t₀, c t₁]` and off the admissible chains
(an empty interval or `c = 0` would let the node denote anything); on the
interval and the admissible chains the cell equation holds on the whole interval, so the uniqueness
of the finite-past inverse pins the value.
Uniqueness of that inverse makes `Denotes` functional (not used here).

The derivative clauses (K3) use `fderiv` at real points: the old-label derivative moves the chain
by the recentering `RealChain.recenter` and the final phase by `h/ε_i`
(`𝔠^{[h]} = (𝒜^{[h]}, ζ_i + h/ε_i)`); the slow derivatives of family and
cell functions move only the family, at fixed internal phase; `dPhase` and `dInternal`
differentiate along `e_{q}` with `q = transverseIndex p`. -/

/-- `Gen.Denotes D bw j₀ e f`: the generated expression `e` denotes the function `f` at real
parameters of the construction `D`. -/
inductive Gen.Denotes (D : OCData) (bw : ℝ) (j₀ : ℕ) : {s : GenSort} → {i : ℕ} → {p : ℤ} → Gen s i p → s.Sem → Prop
  | geo {i : ℕ} {p : ℤ} (fr : GenFrame) (L : GeoLetter) :
      Gen.Denotes D bw j₀ (Gen.geo (i := i) (p := p) fr L) (L.eval D i fr)
  | drift {i : ℕ} {p : ℤ} (c : Fin 2) :
      Gen.Denotes D bw j₀ (Gen.drift (i := i) (p := p) c) (driftSem D i p c)
  | time {s : GenSort} {i : ℕ} {p : ℤ} (L : TimeLetter) :
      Gen.Denotes D bw j₀ (Gen.time (s := s) (i := i) (p := p) L) (s.ofTime (L.eval D))
  | add {s : GenSort} {i : ℕ} {p : ℤ} {a b : Gen s i p} {fa fb : s.Sem} :
      Gen.Denotes D bw j₀ a fa → Gen.Denotes D bw j₀ b fb → Gen.Denotes D bw j₀ (Gen.add a b) (s.add fa fb)
  | mul {s : GenSort} {i : ℕ} {p : ℤ} {a b : Gen s i p} {fa fb : s.Sem} :
      Gen.Denotes D bw j₀ a fa → Gen.Denotes D bw j₀ b fb → Gen.Denotes D bw j₀ (Gen.mul a b) (s.mul fa fb)
  | dOld {i : ℕ} {p : ℤ} (j : Fin 2) {a : Gen .ctx i p} {fa : GenSort.Sem .ctx} :
      Gen.Denotes D bw j₀ a fa →
        Gen.Denotes D bw j₀ (Gen.dOld j a)
          (fun t ch ζ => fderiv ℝ (fun h : Vec 2 =>
            fa t (ch.recenter D h) (ζ + (D.eps i)⁻¹ • h)) 0 (basisVec j))
  | dPhase {i : ℕ} {p : ℤ} {a : Gen .ctx i p} {fa : GenSort.Sem .ctx} :
      Gen.Denotes D bw j₀ a fa →
        Gen.Denotes D bw j₀ (Gen.dPhase a)
          (fun t ch ζ => fderiv ℝ (fa t ch) ζ (basisVec (transverseIndex p)))
  | dSlowFam {i : ℕ} {p : ℤ} (j : Fin 2) {c : Gen .fam i p} {fc : GenSort.Sem .fam} :
      Gen.Denotes D bw j₀ c fc →
        Gen.Denotes D bw j₀ (Gen.dSlowFam j c)
          (fun t ch => fderiv ℝ (fun h : Vec 2 => fc t (ch.recenter D h)) 0 (basisVec j))
  | dSlowCell {i : ℕ} {p : ℤ} (j : Fin 2) {w : Gen .cell i p} {fw : GenSort.Sem .cell} :
      Gen.Denotes D bw j₀ w fw →
        Gen.Denotes D bw j₀ (Gen.dSlowCell j w)
          (fun t ch η => fderiv ℝ (fun h : Vec 2 => fw t (ch.recenter D h) η) 0 (basisVec j))
  | dInternal {i : ℕ} {p : ℤ} {w : Gen .cell i p} {fw : GenSort.Sem .cell} :
      Gen.Denotes D bw j₀ w fw →
        Gen.Denotes D bw j₀ (Gen.dInternal w)
          (fun t ch η => fderiv ℝ (fw t ch) η (basisVec (transverseIndex p)))
  | restrict {i : ℕ} {p : ℤ} {a : Gen .ctx i p} {fa : GenSort.Sem .ctx} :
      Gen.Denotes D bw j₀ a fa → Gen.Denotes D bw j₀ (Gen.restrict a) fa
  | cellInv {i : ℕ} {p : ℤ} {F : Fin 2 → Gen .cell i p} (t₀ : ℝ) {ι : Gen .cell i p}
      {fF : Fin 2 → GenSort.Sem .cell} {fι : GenSort.Sem .cell} :
      (∀ k, Gen.Denotes D bw j₀ (F k) (fF k)) → Gen.Denotes D bw j₀ ι fι →
        Gen.Denotes D bw j₀ (Gen.cellInv F t₀ ι) (transverseInverseSem D i p fF t₀ fι)
  | transPrim {i : ℕ} {p : ℤ} {w : Gen .cell i p} {fw : GenSort.Sem .cell} :
      Gen.Denotes D bw j₀ w fw → Gen.Denotes D bw j₀ (Gen.transPrim w) (transversePrimitiveSem p fw)
  | solved {i : ℕ} {p : ℤ} {G : Fin 2 → Fin 2 → Gen .fam i p} {v F : Fin 2 → Gen .cell i p}
      {q : Gen .cell i p} (t₀ t₁ c : ℝ) (sZ : ℕ) {ι : Gen .cell i p}
      {fG : Fin 2 → Fin 2 → GenSort.Sem .fam} {fv fF : Fin 2 → GenSort.Sem .cell}
      {fq fι ω : GenSort.Sem .cell} :
      t₀ < t₁ → 0 < c →
      (∀ a b, Gen.Denotes D bw j₀ (G a b) (fG a b)) → (∀ k, Gen.Denotes D bw j₀ (v k) (fv k)) →
        (∀ k, Gen.Denotes D bw j₀ (F k) (fF k)) → Gen.Denotes D bw j₀ q fq →
        Gen.Denotes D bw j₀ ι fι →
        (∀ ch : RealChain, IsAdmissibleChain D bw j₀ i p ch →
          IsCellFieldInverse (E := ℝ) (fun s => Matrix.of fun a b => fG a b (c * s) ch)
            (fun s η => fun k => fv k (c * s) ch η) sZ t₀ t₁ (fι (c * t₀) ch)
            (fun s η => ∑ k : Fin 2, fderiv ℝ (fF k (c * s) ch) η (basisVec k) + fq (c * s) ch η)
            (fun s η => ω (c * s) ch η)) →
        (∀ (t : ℝ) (ch : RealChain) (η : Vec 2),
          (t ∉ Set.Icc (c * t₀) (c * t₁) ∨ ¬ IsAdmissibleChain D bw j₀ i p ch) → ω t ch η = 0) →
        Gen.Denotes D bw j₀ (Gen.solved G v F q t₀ t₁ c sZ ι) ω
  | mean {i : ℕ} {p : ℤ} {w : Gen .cell i p} {fw : GenSort.Sem .cell} :
      Gen.Denotes D bw j₀ w fw → Gen.Denotes D bw j₀ (Gen.mean w) (cellMeanSem fw)
  | famCell {i : ℕ} {p : ℤ} {c : Gen .fam i p} {fc : GenSort.Sem .fam} :
      Gen.Denotes D bw j₀ c fc → Gen.Denotes D bw j₀ (Gen.famCell c) (fun t ch _ => fc t ch)
  | evalChild {i : ℕ} {p : ℤ} (p' : ℤ) {c : Gen .fam (i + 1) p'} {fc : GenSort.Sem .fam} :
      Gen.Denotes D bw j₀ c fc →
        Gen.Denotes D bw j₀ (Gen.evalChild (i := i) (p := p) p' c)
          (fun t ch ζ => ocCutoff D.α D.q D.Λ (i + 1) p' t * fc t (ch.appendChild D p' t ζ))

end AVRegularity
end

section
open Homogenization
namespace AVRegularity

/-! Definition (`Gen`): scheduled expressions and generated functions.

* `Gen.IsScheduled D e`: every occurrence of `e` carries the slot and times prescribed by the
  construction: an evaluation in the coarser chart (K6) and every letter of an appended
  child pass to a slot scheduled in the current one, and every transverse inverse (K4) is solved
  from the original start `inf J_𝗉` of its own slot with zero initial state. Solved seed nodes run on
  the pinned clock `c = ε_i²/κ_{min(i,M)}` of their level (terminal diffusivity at a weak
  level) over the original interval `J_𝗉` of their
  slot, `[t₀, t₁] = J_𝗉/c`, and keep their initial states. A
  covariance-primitive letter has its original anchor `0`.
  A coarser-chart evaluation (K6) passes only to an odd finer slot (the slots are the
  odd pulses), so its appended child can be admissible.
* A context function `f` over the slot `p` of level `i` is generated with the schedule when it is
  given by a scheduled finite expression (`IsGeneratedCtxFrom` below adds the seed provenance). -/

/-- Every occurrence of the expression carries the slot and times assigned by the construction. -/
inductive Gen.IsScheduled (D : OCData) : {s : GenSort} → {i : ℕ} → {p : ℤ} → Gen s i p → Prop
  | geoOwn {i : ℕ} {p : ℤ} (L : GeoLetter) :
      Gen.IsScheduled D (Gen.geo (i := i) (p := p) .own L)
  | geoChild {i : ℕ} {p : ℤ} (p' : ℤ) (L : GeoLetter) :
      IsScheduledIn D i p' p → Gen.IsScheduled D (Gen.geo (i := i) (p := p) (.child p') L)
  | drift {i : ℕ} {p : ℤ} (c : Fin 2) : Gen.IsScheduled D (Gen.drift (i := i) (p := p) c)
  | timePartition {s : GenSort} {i : ℕ} {p : ℤ} (lev : ℕ) (k : ℤ) :
      Gen.IsScheduled D (Gen.time (s := s) (i := i) (p := p) (.partition lev k))
  | timeCov {s : GenSort} {i : ℕ} {p : ℤ} (lev : ℕ) (a b : Fin 2) :
      Gen.IsScheduled D (Gen.time (s := s) (i := i) (p := p) (.covPrimitive lev 0 a b))
  | timeRef {s : GenSort} {i : ℕ} {p : ℤ} (lev : ℕ) (a b : Fin 2) :
      Gen.IsScheduled D (Gen.time (s := s) (i := i) (p := p) (.refFlux lev a b))
  | timeConst {s : GenSort} {i : ℕ} {p : ℤ} (c : ℝ) :
      Gen.IsScheduled D (Gen.time (s := s) (i := i) (p := p) (.const c))
  | add {s : GenSort} {i : ℕ} {p : ℤ} {a b : Gen s i p} :
      Gen.IsScheduled D a → Gen.IsScheduled D b → Gen.IsScheduled D (Gen.add a b)
  | mul {s : GenSort} {i : ℕ} {p : ℤ} {a b : Gen s i p} :
      Gen.IsScheduled D a → Gen.IsScheduled D b → Gen.IsScheduled D (Gen.mul a b)
  | dOld {i : ℕ} {p : ℤ} (j : Fin 2) {a : Gen .ctx i p} :
      Gen.IsScheduled D a → Gen.IsScheduled D (Gen.dOld j a)
  | dPhase {i : ℕ} {p : ℤ} {a : Gen .ctx i p} :
      Gen.IsScheduled D a → Gen.IsScheduled D (Gen.dPhase a)
  | dSlowFam {i : ℕ} {p : ℤ} (j : Fin 2) {c : Gen .fam i p} :
      Gen.IsScheduled D c → Gen.IsScheduled D (Gen.dSlowFam j c)
  | dSlowCell {i : ℕ} {p : ℤ} (j : Fin 2) {w : Gen .cell i p} :
      Gen.IsScheduled D w → Gen.IsScheduled D (Gen.dSlowCell j w)
  | dInternal {i : ℕ} {p : ℤ} {w : Gen .cell i p} :
      Gen.IsScheduled D w → Gen.IsScheduled D (Gen.dInternal w)
  | restrict {i : ℕ} {p : ℤ} {a : Gen .ctx i p} :
      Gen.IsScheduled D a → Gen.IsScheduled D (Gen.restrict a)
  | cellInv {i : ℕ} {p : ℤ} {F : Fin 2 → Gen .cell i p} :
      (∀ k, Gen.IsScheduled D (F k)) →
        Gen.IsScheduled D (Gen.cellInv F (D.slotStart i p) (Gen.time (.const 0)))
  | transPrim {i : ℕ} {p : ℤ} {w : Gen .cell i p} :
      Gen.IsScheduled D w → Gen.IsScheduled D (Gen.transPrim w)
  | solved {i : ℕ} {p : ℤ} {G : Fin 2 → Fin 2 → Gen .fam i p} {v F : Fin 2 → Gen .cell i p}
      {q : Gen .cell i p} (t₀ t₁ c : ℝ) (sZ : ℕ) {ι : Gen .cell i p} :
      t₀ < t₁ → 0 < c → c = D.cellScaleSq i → t₀ = D.slotStart i p / c →
      t₁ = (((p : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i) / c →
      (∀ a b, Gen.IsScheduled D (G a b)) → (∀ k, Gen.IsScheduled D (v k)) →
        (∀ k, Gen.IsScheduled D (F k)) → Gen.IsScheduled D q → Gen.IsScheduled D ι →
        Gen.IsScheduled D (Gen.solved G v F q t₀ t₁ c sZ ι)
  | mean {i : ℕ} {p : ℤ} {w : Gen .cell i p} :
      Gen.IsScheduled D w → Gen.IsScheduled D (Gen.mean w)
  | famCell {i : ℕ} {p : ℤ} {c : Gen .fam i p} :
      Gen.IsScheduled D c → Gen.IsScheduled D (Gen.famCell c)
  | evalChild {i : ℕ} {p : ℤ} (p' : ℤ) {c : Gen .fam (i + 1) p'} :
      Odd p' → IsScheduledIn D i p' p → Gen.IsScheduled D c →
        Gen.IsScheduled D (Gen.evalChild (i := i) (p := p) p' c)

end AVRegularity
end

section
open Homogenization
open scoped ENNReal
namespace AVRegularity

/-! Definition: the complex-domain
certificate of a generated context function.

The stored semantics is real (`GenSort.Sem`). The certificate asserts, for fixed discrete chain
data, a holomorphic extension to the actual graded complex carrier `𝔇_i(2;𝗉)` that restricts to the
real semantics at real parameters, is measurable in output time, and whose context size at an
inner reserve `𝗆 < 2` is bounded by a prescribed positive witness.

* `ChainData`: the discrete data (base level, slots) of a chain.
* `ChainParamsC n`: the complex parameters (base label, `n` child centers and phases, final
  phase); `RealChain.paramsC`: the real parameters of a real chain and a final phase.
* `carrierC D b dd n 𝗆`: the parameters of `𝔇_i(𝗆;𝗉)` with the discrete data `dd`:
  base label in the strip `S_{(1+𝗆/4) r ε_{j'-1}}`
  (`r = 1/100`), child centers `|c_k|₁ < λ_𝗆 ε_k`, child phases `|Im ζ_{q_k}| < w_𝗆 + b/64`, final
  phase `|Im ζ_{i,q_i}| < w_𝗆`, `λ_𝗆 = (1+𝗆)b/4`, `w_𝗆 = (3+𝗆/4)b`.
* `IsHolExtension D b j₀ i p f F`: on the output domain `J_𝗉 = ocPulseWindow i p` of the slot
  (the construction does not assert or continue these functions outside their output
  intervals), `F dd n t` is holomorphic on `carrierC … 2`, measurable in time, and equals the real
  semantics `f` at the real parameters of every admissible chain with these discrete data. Two
  more clauses are bundled with the measurability clause:
  - (a) on `carrierC … 2`, `F` is invariant under the real translations of the final phase and of
    each child phase (`ChainParamsC.shiftFinal`, `ChainParamsC.shiftChild`) by a vector whose
    transverse component (for the last slot, resp. the slot of the child) is an integer. The
    phases are torus variables, and a context depends on them through the relative displacement,
    a function of the transverse phase;
  - (b) `F` is locally bounded on `carrierC … 2` uniformly in the output time.
* `ctxSize D b j₀ i F 𝗆 L`: the context size `q_{𝗆,L}` of a
  slot-indexed family of extensions:
  `∑_h e^{3πb|h|}(1+|h|)^L sup_𝗉 sup_{t ∈ J_𝗉, families in 𝔉_{i-1}(𝗆;𝗉)} |F̂_{𝗉,h}|`, the
  Fourier coefficient taken in the final transverse phase over a real period (families have a real
  final phase), all slot, data and time suprema inside the mode sum (`ctxModeSup`). -/

/-- The discrete data of a chain: base level and slots. -/
structure ChainData where
  /-- The base level `j' - 1`. -/
  baseLevel : ℕ
  /-- The slots `𝗉_{j'}, …, 𝗉_i`. -/
  slots : List ℤ

/-- The complex parameters of a chain with `n` children and a final phase. -/
abbrev ChainParamsC (n : ℕ) : Type :=
  (Fin 2 → ℂ) × (Fin n → (Fin 2 → ℂ) × (Fin 2 → ℂ)) × (Fin 2 → ℂ)

/-- The discrete data of a real chain. -/
def RealChain.data (ch : RealChain) : ChainData := ⟨ch.baseLevel, ch.slots⟩

/-- The (real) parameters of a real chain and a final phase, as complex parameters. -/
def RealChain.paramsC (ch : RealChain) (ζ : Vec 2) : ChainParamsC ch.children.length :=
  (fun a => (ch.base a : ℂ),
    fun k => (fun a => ((ch.children.get k).center a : ℂ), fun a => ((ch.children.get k).phase a : ℂ)),
    fun a => (ζ a : ℂ))

/-- The parameters of `𝔇_i(𝗆;𝗉)` with the discrete data `dd` and `n` children. -/
def carrierC (D : OCData) (b : ℝ) (dd : ChainData) (n : ℕ) (mres : ℝ) : Set (ChainParamsC n) :=
  {x | (∑ a : Fin 2, |(x.1 a).im|) < (1 + mres / 4) * (1 / 100) * D.eps dd.baseLevel ∧
    (∀ k : Fin n, (∑ a : Fin 2, ‖(x.2.1 k).1 a‖) < (1 + mres) * b / 4 * D.eps (dd.baseLevel + 1 + k) ∧
      |((x.2.1 k).2 (transverseIndex (dd.slots.getD k 0))).im| < (3 + mres / 4) * b + b / 64) ∧
    |(x.2.2 (transverseIndex (dd.slots.getLastD 0))).im| < (3 + mres / 4) * b}

/-- The real translation of the final phase by `v`. -/
def ChainParamsC.shiftFinal {n : ℕ} (x : ChainParamsC n) (v : Vec 2) : ChainParamsC n :=
  (x.1, x.2.1, x.2.2 + fun a => (v a : ℂ))

/-- The real translation of the phase of the child `k` by `v`. -/
def ChainParamsC.shiftChild {n : ℕ} (x : ChainParamsC n) (k : Fin n) (v : Vec 2) :
    ChainParamsC n :=
  (x.1, Function.update x.2.1 k ((x.2.1 k).1, (x.2.1 k).2 + fun a => (v a : ℂ)), x.2.2)

/-- `F` is a holomorphic, time-measurable extension of the real context function `f` over the
slot `p` of level `i` on the outer carrier, invariant under the real translations of the final
phase and of the child phases with integer transverse component, and locally bounded uniformly
in the output time (these two clauses are bundled with the measurability clause). -/
def IsHolExtension (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (f : GenSort.Sem .ctx)
    (F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ) : Prop :=
  (∀ dd n, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p,
      DifferentiableOn ℂ (F dd n t) (carrierC D b dd n 2)) ∧
    ((∀ dd n x, Measurable fun t : ocPulseWindow D.α D.q D.Λ i p => F dd n t x) ∧
      (∀ dd n, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ x ∈ carrierC D b dd n 2,
        (∀ v : Vec 2, (∃ m : ℤ, v (transverseIndex (dd.slots.getLastD 0)) = m) →
          F dd n t (x.shiftFinal v) = F dd n t x) ∧
        ∀ (k : Fin n) (v : Vec 2), (∃ m : ℤ, v (transverseIndex (dd.slots.getD k 0)) = m) →
          F dd n t (x.shiftChild k v) = F dd n t x) ∧
      (∀ dd n, ∀ x ∈ carrierC D b dd n 2, ∃ U ∈ nhds x, ∃ M : ℝ,
        ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ y ∈ U, ‖F dd n t y‖ ≤ M)) ∧
    ∀ (ch : RealChain), ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ (ζ : Vec 2),
      IsAdmissibleChain D b j₀ i p ch →
        F ch.data ch.children.length t (ch.paramsC ζ) = (f t ch ζ : ℂ)

/-- The Fourier coefficient of order `h` of `F` in the final transverse phase at the family
parameters of `x` (final phase moved along `e_q` over a real period). -/
def finalPhaseCoeff {n : ℕ} (q : Fin 2) (G : ChainParamsC n → ℂ) (x : ChainParamsC n) (h : ℤ) : ℂ :=
  ∫ s in (0 : ℝ)..1, G (x.1, x.2.1, x.2.2 + fun a => if a = q then (s : ℂ) else 0) *
    Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ) * (s : ℂ)))

/-- The supremum of the mode `h` of `F` over the scheduled discrete data over the slot `p` of
level `i`, the output times `t ∈ J_𝗉`, and the families of `𝔉_{i-1}(𝗆;𝗉)` (real final phase). -/
def ctxModeSup (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ)
    (F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ) (mres : ℝ) (h : ℤ) : ℝ≥0∞ :=
  ⨆ (dd : ChainData) (n : ℕ)
    (_ : ∃ ch : RealChain, IsAdmissibleChain D b j₀ i p ch ∧ ch.data = dd ∧ ch.children.length = n)
    (t : ℝ) (_ : t ∈ ocPulseWindow D.α D.q D.Λ i p)
    (x : ChainParamsC n) (_ : x ∈ carrierC D b dd n mres) (_ : ∀ a, (x.2.2 a).im = 0),
    ‖finalPhaseCoeff (transverseIndex p) (F dd n t) x h‖ₑ

/-- The context size `q_{𝗆,L}` of a slot-indexed family of extensions over the odd slots of
level `i`: `∑_h e^{3πb|h|}(1+|h|)^L sup_𝗉 sup_{t,𝒜} |F̂_{𝗉,h}(t,𝒜)|`, all slot and time suprema
inside each mode sum: the analytic norm of display (10.9) of the paper, for the two-scale forms
of display (10.2). -/
def ctxSize (D : OCData) (b : ℝ) (j₀ i : ℕ)
    (F : {k : ℤ // Odd k} → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ) (mres : ℝ) (L : ℕ) :
    ℝ≥0∞ :=
  ∑' h : ℤ, ENNReal.ofReal (Real.exp (3 * Real.pi * b * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ L) *
    ⨆ p : {k : ℤ // Odd k}, ctxModeSup D b j₀ i p.1 (F p) mres h

end AVRegularity
end

section
open Homogenization
namespace AVRegularity

/-! Definition: seed provenance of solved
nodes and the slotwise structural transversality of generated functions.

* `SeedExports`: a registry of the certified context exports of the supplied seed, each with its
  full occurrence tree; the two-dimensional inverses (`solved` nodes) occur only
  inside these trees.
* `Gen.FromSeed 𝒮 e`: the source-generation judgement `𝒮 ⊢ e`: context
  exports, and the ordinary constructors (K1)-(K6) with the transverse primitive, with **no fresh
  `solved` rule** outside the exports.
* `IsGeneratedCtxFrom D b j₀ 𝒮 i p f`: `f` is denoted by a scheduled expression with seed
  provenance.
* `slotParallel p`: the parallel coordinate `p_i` of the slot `p` (complementary to
  `transverseIndex p`).
* `IsSlotTransverseCtx D i p f`: the slotwise structural transversality of a context
  function: on the scheduled output domain `J_𝗉` (`ocPulseWindow`), on the admissible chains over
  `𝗉`, invariance under parallel shifts of the final phase. -/

/-- A registry of certified context exports of the supplied seed. -/
abbrev SeedExports : Type := ∀ {i : ℕ} {p : ℤ}, Gen .ctx i p → Prop

/-- The source-generation judgement `𝒮 ⊢ e`: no fresh `solved` node outside the exports. -/
inductive Gen.FromSeed (𝒮 : SeedExports) : {s : GenSort} → {i : ℕ} → {p : ℤ} → Gen s i p → Prop
  | export {i : ℕ} {p : ℤ} {e : Gen .ctx i p} : 𝒮 e → Gen.FromSeed 𝒮 e
  | geo {i : ℕ} {p : ℤ} (fr : GenFrame) (L : GeoLetter) :
      Gen.FromSeed 𝒮 (Gen.geo (i := i) (p := p) fr L)
  | drift {i : ℕ} {p : ℤ} (c : Fin 2) : Gen.FromSeed 𝒮 (Gen.drift (i := i) (p := p) c)
  | time {s : GenSort} {i : ℕ} {p : ℤ} (L : TimeLetter) :
      Gen.FromSeed 𝒮 (Gen.time (s := s) (i := i) (p := p) L)
  | add {s : GenSort} {i : ℕ} {p : ℤ} {a b : Gen s i p} :
      Gen.FromSeed 𝒮 a → Gen.FromSeed 𝒮 b → Gen.FromSeed 𝒮 (Gen.add a b)
  | mul {s : GenSort} {i : ℕ} {p : ℤ} {a b : Gen s i p} :
      Gen.FromSeed 𝒮 a → Gen.FromSeed 𝒮 b → Gen.FromSeed 𝒮 (Gen.mul a b)
  | dOld {i : ℕ} {p : ℤ} (j : Fin 2) {a : Gen .ctx i p} :
      Gen.FromSeed 𝒮 a → Gen.FromSeed 𝒮 (Gen.dOld j a)
  | dPhase {i : ℕ} {p : ℤ} {a : Gen .ctx i p} : Gen.FromSeed 𝒮 a → Gen.FromSeed 𝒮 (Gen.dPhase a)
  | dSlowFam {i : ℕ} {p : ℤ} (j : Fin 2) {c : Gen .fam i p} :
      Gen.FromSeed 𝒮 c → Gen.FromSeed 𝒮 (Gen.dSlowFam j c)
  | dSlowCell {i : ℕ} {p : ℤ} (j : Fin 2) {w : Gen .cell i p} :
      Gen.FromSeed 𝒮 w → Gen.FromSeed 𝒮 (Gen.dSlowCell j w)
  | dInternal {i : ℕ} {p : ℤ} {w : Gen .cell i p} :
      Gen.FromSeed 𝒮 w → Gen.FromSeed 𝒮 (Gen.dInternal w)
  | restrict {i : ℕ} {p : ℤ} {a : Gen .ctx i p} :
      Gen.FromSeed 𝒮 a → Gen.FromSeed 𝒮 (Gen.restrict a)
  | cellInv {i : ℕ} {p : ℤ} {F : Fin 2 → Gen .cell i p} (t₀ : ℝ) {ι : Gen .cell i p} :
      (∀ k, Gen.FromSeed 𝒮 (F k)) → Gen.FromSeed 𝒮 ι → Gen.FromSeed 𝒮 (Gen.cellInv F t₀ ι)
  | transPrim {i : ℕ} {p : ℤ} {w : Gen .cell i p} :
      Gen.FromSeed 𝒮 w → Gen.FromSeed 𝒮 (Gen.transPrim w)
  | mean {i : ℕ} {p : ℤ} {w : Gen .cell i p} : Gen.FromSeed 𝒮 w → Gen.FromSeed 𝒮 (Gen.mean w)
  | famCell {i : ℕ} {p : ℤ} {c : Gen .fam i p} :
      Gen.FromSeed 𝒮 c → Gen.FromSeed 𝒮 (Gen.famCell c)
  | evalChild {i : ℕ} {p : ℤ} (p' : ℤ) {c : Gen .fam (i + 1) p'} :
      Gen.FromSeed 𝒮 c → Gen.FromSeed 𝒮 (Gen.evalChild (i := i) (p := p) p' c)

/-- Well-formedness of a seed registry: every export root lies at or above the seed
level `n` (constructors keep their input level except the coarser-chart evaluation, so levels do
not decrease from a seed root to its descendants). Metadata, not provenance. -/
def SeedExports.Above (𝒮 : SeedExports) (n : ℕ) : Prop :=
  ∀ {i : ℕ} {p : ℤ} (e : Gen .ctx i p), 𝒮 e → n ≤ i

/-- The context function `f` is denoted by a scheduled expression with seed provenance. -/
def IsGeneratedCtxFrom (D : OCData) (b : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (i : ℕ) (p : ℤ)
    (f : GenSort.Sem .ctx) : Prop :=
  ∃ e : Gen .ctx i p, Gen.IsScheduled D e ∧ Gen.FromSeed 𝒮 e ∧ Gen.Denotes D b j₀ e f

/-- The parallel coordinate `p_i` of the slot `p` (complementary to `transverseIndex p`). -/
def slotParallel (p : ℤ) : Fin 2 := if p % 4 = 3 then 0 else 1

/-- Slotwise structural transversality of a context function over the slot `p` of level
`i`: on the output domain `J_𝗉` and the admissible chains, invariance under parallel shifts of the
final phase. -/
def IsSlotTransverseCtx (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (f : GenSort.Sem .ctx) : Prop :=
  ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ (ch : RealChain), IsAdmissibleChain D b j₀ i p ch →
    ∀ (ζ : Vec 2) (s : ℝ), f t ch (ζ + s • basisVec (slotParallel p)) = f t ch ζ

/-! Definition (next to `IsSlotTransverseCtx`): the
slotwise structural parallel invariance of the certified seed exports.

* `RealChain.IsParShift ch ch'`: `ch'` is `ch` with the phase of each child shifted along the
  parallel direction of the pulse it follows (`ChainChild.IsParStep`, `ChainChild.IsParRel`); the
  base level, slots, base label and child centres are unchanged (every family of a chain is
  unchanged under such shifts).
* `IsSlotParInvCtx D b j₀ i p f`: on the output domain `J_𝗉` and the admissible chains over `𝗉`,
  invariance under these child-phase shifts and (the clause of `IsSlotTransverseCtx`) under
  parallel shifts of the final phase. -/

/-- A child `c'` is the child `c` with its phase shifted along the parallel direction of the
pulse `p`. -/
def ChainChild.IsParStep (p : ℤ) (c c' : ChainChild) : Prop :=
  c'.center = c.center ∧ ∃ s : ℝ, c'.phase = c.phase + s • basisVec (slotParallel p)

/-- The children `cs'` are the children `cs` with each phase shifted along the parallel direction
of the pulse `f j` of the `j`-th child. -/
def ChainChild.IsParRel : (ℕ → ℤ) → List ChainChild → List ChainChild → Prop
  | _, [], [] => True
  | f, c :: cs, c' :: cs' =>
      ChainChild.IsParStep (f 0) c c' ∧ ChainChild.IsParRel (fun j => f (j + 1)) cs cs'
  | _, _, _ => False

/-- The chain `ch'` is `ch` with each child phase shifted along the parallel direction of the
pulse it follows: the same base level, slots, base label and child centres.
-/
def RealChain.IsParShift (ch ch' : RealChain) : Prop :=
  ch'.baseLevel = ch.baseLevel ∧ ch'.slots = ch.slots ∧ ch'.base = ch.base ∧
    ChainChild.IsParRel (fun j => ch.slots.getD j 0) ch.children ch'.children

/-- Slotwise structural parallel invariance of a context function over the slot `p` of level `i`:
on the output domain
`J_𝗉` and the admissible chains, invariance under parallel shifts of the child phases and of the
final phase (the latter is `IsSlotTransverseCtx`). -/
def IsSlotParInvCtx (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (f : GenSort.Sem .ctx) : Prop :=
  ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ (ch : RealChain), IsAdmissibleChain D b j₀ i p ch →
    (∀ (ch' : RealChain) (ζ : Vec 2), ch.IsParShift ch' → f t ch' ζ = f t ch ζ) ∧
    ∀ (ζ : Vec 2) (s : ℝ), f t ch (ζ + s • basisVec (slotParallel p)) = f t ch ζ

end AVRegularity
end
end
end
