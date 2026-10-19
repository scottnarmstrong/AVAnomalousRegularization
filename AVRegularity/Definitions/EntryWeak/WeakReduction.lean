-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Entry.TerminalResidualClauses
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
namespace AVRegularity

/-! Definition: the scales and weights of the weak levels.


At a weak level `M < i ≤ M + J_w` the diffusivity is the terminal one, `ν_i = B_i = κ_M`
(`OCData.kap i = κ_{min(i,M)}` with `D.term = M`), so `η_i = 1`, `e = ε_i`, `E = ε_{i-1}`,
`ℓ_i² = e²/κ_M` and `Pe_i = e^β/κ_M` (`β = 1 + α`). The weak exponents are `a_* = (q+2)γ`, the
mass and readout exponents `0 < η₀ ≤ δ/8`, `η_b = η₀/2`, the mass factor `c_w = (4N_wJ_w)⁻¹`, and
`χ_w = 2a_* - η₀ - η_b/2 > 0`. -/

namespace OCData

variable (D : OCData)

/-- The Péclet number `Pe_i = ε_i^β / κ_M` of a weak level (terminal diffusivity). -/
def weakPe (i : ℕ) : ℝ := D.eps i ^ (1 + D.α) / D.kap i

end OCData

/-- `a_* = (q+2)γ`. -/
def weakAStar (α q : ℝ) : ℝ := (q + 2) * ocGamma α q

/-- `χ_w = 2a_* - η₀ - η_b/2`, `η_b = η₀/2`. -/
def weakChi (α q η₀ : ℝ) : ℝ := 2 * weakAStar α q - η₀ - η₀ / 4

/-- The weak mass factor `c_w = (4N_wJ_w)⁻¹`. -/
def weakCw (N J : ℕ) : ℝ := ((4 * N * J : ℕ) : ℝ)⁻¹

/-- `χ_w > 0`: `δ ≤ (q-1)/4`, `a_* = (q+2)γ ≥ q - 1` since
`γ ≥ (q-1)/(q+1)` and `q + 1 < 3`, so `χ_w ≥ 2(q-1) - (5/4)(q-1)/32 > 0`. -/
theorem weakChi_pos {α q η₀ : ℝ} (hα : 0 < α) (hq₁ : 1 < q) (hq₂ : q < 17 / 16)
    (hη : η₀ ≤ ocDelta α q / 8) : 0 < weakChi α q η₀ := by
  have hX : 0 ≤ (2 * q + 1) * (1 + α) / (2 * q + 2) := by positivity
  have hδ : ocDelta α q ≤ (q - 1) / 4 := by
    unfold ocDelta
    have : 0 ≤ (q - 1) / 4 := by linarith
    nlinarith
  have hγ : q - 1 ≤ (q + 2) * ocGamma α q := by
    unfold ocGamma
    rw [← mul_div_assoc, le_div_iff₀ (by linarith)]
    have h1 : q + 1 ≤ (q + 2) * (1 + α) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ q - 1)
    linarith [show (q + 2) * ((q - 1) * (1 + α)) = (q - 1) * ((q + 2) * (1 + α)) by ring]
  unfold weakChi weakAStar
  linarith

end AVRegularity
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! Definition: the sources of one weak passage.

At a weak passage of level `i` (output level `i-1`):
* the **eddy letters** `𝔇_{i,n}`, `2 ≤ n ≤ N_w + 1` (`WordLetter.eddy n`): the new diagonal eddy
  means, `M^e_2 = div_X⟨wT_1·⟩`, `M^e_n = M_n` (`n ≥ 3`), with the molecular Laplacian left in
  `𝓛_{i-1}`; a letter edge `(v,w) → (v,wn)`, `|w| < R_w`, carries `-M^e_n` with the readout factor
  `λ_i⁻¹ = E^{-η₀}`;
* the **inherited means**: for every word `w` of length `≤ R_w` and every directed path `π` of
  `h ≥ 1` edges of the incoming family, the path mean `+𝐄^{(h)}_{n,π}`, `2 ≤ n ≤ N_w + D_i`, on the
  edge `(π.src, w) → (π.tgt, w)` (the inherited operator `𝔈_i` copied into every word).

`weakEddyFlux` is the eddy mean flux on the scalar grade-zero lift: the cell mean of the drift
term `√η v·C_{n-1}` of `liftFluxX` (the slow term `-ηG∇_XC_{n-2}` has zero mean for `n ≥ 3`, and at
`n = 2` it is the molecular term left in `𝓛_{i-1}`). The tags of a new constituent are a seed tag
(`weakTag`): the birth list of weak eddy births
(inherited: the concatenated birth lists of the path, eddy: `[i]`), the **stored** positive witness
`Θ̂ = (ω_u/ω_v)Θ` bounding the stored conjugated coefficients (inherited: the product of the
incoming stored witnesses, no new factor; eddy: `λ_i⁻¹Pe_i² = E^{-η₀}Pe_i²`), the creation level
`i`, the degree as excess and maximal order, the width `r_w = x^{1+σ_w}` of the weak
kernel `S_w` that every weak constituent carries after the single regularization (recorded from
birth, so that the record is positive), and the length `ε_i` (the coefficients are
`A_{γ,d} = κ ε_{i}^{n-2}ε_{i-1}^{d-n}Θ_γ a_γ` at output level `i-1`). -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The eddy letters `{𝔇_n : 2 ≤ n ≤ N + 1}`. -/
def weakAlphabet (N : ℕ) : Finset WordLetter := (Finset.Icc 2 (N + 1)).image WordLetter.eddy

/-- The extended components `{(v,w) : v ∈ S, |w| ≤ R}` of a weak passage at level `m`. -/
def weakExtComps (m N R : ℕ) (S : Finset Comp) : Finset Comp :=
  S ∪ (S ×ˢ wordsUpTo (weakAlphabet N) R).image fun x => succComp m x.1 x.2

/-- A source of the weak passage from the incoming stage `G`. -/
inductive WeakSource (G : GenStage D hr Dm b j₀) : Type
  /-- The inherited path mean of degree `n` along `π`, copied into the word `w`. -/
  | inherited (w : List WordLetter) (h : ℕ) (π : StagePath G h) (n : ℕ)
  /-- The eddy letter of degree `n` from `(v,w)` to `(v,w𝔇_n)`. -/
  | eddy (v : CompIn G.comps) (w : List WordLetter) (n : ℕ)

namespace WeakSource

variable {G : GenStage D hr Dm b j₀}

/-- The source component at the passage of level `m`. -/
def srcComp (m : ℕ) : WeakSource G → Comp
  | .inherited w _ π _ => succComp m π.src w
  | .eddy v w _ => succComp m v.1 w

/-- The target component at the passage of level `m`. -/
def tgtComp (m : ℕ) : WeakSource G → Comp
  | .inherited w _ π _ => succComp m π.tgt w
  | .eddy v w n => succComp m v.1 (w ++ [.eddy n])

/-- Validity: words over the eddy alphabet, `h ≥ 1` and `2 ≤ n ≤ N + D_i` for inherited means,
`|w| < R` and `2 ≤ n ≤ N + 1` for eddy letters. -/
def Valid (N R Din : ℕ) : WeakSource G → Prop
  | .inherited w h _ n => (w = [] ∨ w ∈ wordsUpTo (weakAlphabet N) R) ∧ 1 ≤ h ∧ 2 ≤ n ∧ n ≤ N + Din
  | .eddy _ w n => (w = [] ∨ w ∈ wordsUpTo (weakAlphabet N) R) ∧ w.length < R ∧ 2 ≤ n ∧ n ≤ N + 1

/-- The number of source edges of the path. -/
def pathLen : WeakSource G → ℕ
  | .inherited _ h _ _ => h
  | .eddy .. => 0

/-- The readout factor of the source: `E^{-η₀}` for a letter, `1` for an inherited mean. -/
def lam (m : ℕ) (η₀ : ℝ) : WeakSource G → ℝ
  | .inherited .. => 1
  | .eddy .. => D.eps (m - 1) ^ (-η₀)

/-- The degree of the source. -/
def degree : WeakSource G → ℕ
  | .inherited _ _ _ n => n
  | .eddy _ _ n => n

/-- The seed tag of the new constituent (passage at level `m`; tags of the incoming identities
read with `P`; kernel width `rW`). -/
def weakTag (P : ProvParams) (m : ℕ) (rW η₀ : ℝ) : WeakSource G → SeedTag
  | .inherited _ _ π n =>
      { size := ((π.provList.map fun x => (x.2.2.tags P).witness)).prod
        birthLevel := m
        birthExcess := n - 2
        length := D.eps m
        width := rW
        births := (π.provList.map fun x => (x.2.2.tags P).births).flatten
        maxOrder := n }
  | .eddy _ _ n =>
      { size := D.eps (m - 1) ^ (-η₀) * D.weakPe m ^ 2
        birthLevel := m
        birthExcess := n - 2
        length := D.eps m
        width := rW
        births := [m]
        maxOrder := n }

end WeakSource

/-- The eddy letter flux `J^eddy_n = -ℓ^{-2}ε_c^nρ⟨√η v C_{n-1}⟩` on the scalar grade-zero lift
(the flux of `𝔇_{i,n} = -M^e_n`), in the label variables of
the chart, at time `t`. -/
def weakEddyFlux (D : OCData) (m : ℕ) (ρ : ℝ) (Q : LiftOperatorData (Fin 1) (fun _ => ℝ) Dm)
    (Cc0 : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (n : ℕ) (t : ℝ) :
    (Vec 2 → ℝ) → Vec 2 → Vec 2 :=
  fun f y k =>
    -((D.cellScaleSq m)⁻¹ * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ) *
      fieldCellMean (fun z =>
        (Real.sqrt Q.η * Q.v ((D.cellScaleSq m)⁻¹ * t) z k) •
          liftApply (n - 1) (Cc0 0 (n - 1)) (fun _ X => Pi.single (0 : Fin 1) (f (ρ • X)))
            ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z) 0

namespace WeakSource

variable {G : GenStage D hr Dm b j₀}

open scoped Classical in
/-- The finer output of a weak source on the family `A` over the slot `k` (level `m = G.level`):
the path mean of the source's path family, or the eddy mean of the grade-zero lift; the slow
length is `ρ`. -/
def fluxOp (ρ : ℝ) (s : WeakSource G)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) : FamFluxOp :=
  fun k t A =>
    if hA : IsAdmissibleChain D b j₀ G.level k A ∧ Odd k then
      match s, Cc with
      | .inherited _ _ π n, Cc =>
          pathMeanFlux D G.level ρ
            (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩)) (Cc k A) n t
      | .eddy _ _ n, _ =>
          weakEddyFlux D G.level ρ
            (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k A ρ (fun _ _ _ => []))
            (Cc0 k A) n t
    else fun _ _ => 0

/-- The path lift sequences of an inherited source on every admissible family of every odd slot,
from the original start, at the slow length `ρ`, with cell order `N` and the path grade.
Box smoothness and cell inversion hold on the admissible recentering carrier. -/
def IsLiftFamily (sX sZ N : ℕ) (ρ : ℝ) (s : WeakSource G)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)) : Prop :=
  match s, Cc with
  | .inherited _ h π _, Cc =>
      ∀ (k : ℤ) (A : RealChain) (hA : IsAdmissibleChain D b j₀ G.level k A ∧ Odd k),
        IsLiftSequenceOn (ladderOmega D b j₀ G.level k A ρ)
          (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩))
          sX sZ (D.slotStart G.level k / D.cellScaleSq G.level)
          ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
          N h (Cc k A)
  | .eddy .., _ => True

end WeakSource
end

/-! Definition: **the actual weak construction**.

* `WeakMenu`: the weak orders `N_w, R_w`, the lift reserves `sX, sZ`, the readout exponent `η₀`,
  the finest level `M + J_w` (the naturality level of the pieces).
* `IsWeakPassage D P Mn G G'`: `G'` (level `i-1`) is the weak passage of `G` (level `i > M`):
  components `V_i × W_{R_w}` (all words of length `≤ R_w` over the eddy letters; no grade or length
  frontier is discarded), natural pieces, scalar identity maps, and a bijection of the identities
  with the valid weak sources. Each identity is a seed identity with the tag `weakTag`, and its
  chart coefficients are pinned by the transfer (`transferAt`, Piola lowering to every order
  `2 ≤ d' ≤ n`) of the source's finer output (`WeakSource.fluxOp`), with the readout factor, and
  to zero off the carrier. The lifts are the actual lift sequences (`IsLiftSequence`) on every
  admissible family from the original starts, with the two-dimensional cell inverse with drift
  `Pe_iv_𝗉` and `η = 1` (`IsCellFieldInverse` with the lift data `familyLiftData`, which
  uses `OCData.kap`), slow length `E = ε_{i-1}`, cell order `N_w`.
* `IsWeakRoot`: the finest family (level `M + J_w`): one root component, no identity.
* `weakMass`, `weakReadoutWeight`: `π_{(v,wn)} = π_{(v,w)}c_wE^{η_b}`,
  `ω_{(v,wn)} = ω_{(v,w)}E^{η₀}` per letter, root `π = 1/2`, `ω = 1`.
* `IsWeakConstruction`: the stages `stage i`, `M ≤ i ≤ M + J_w`, from the root by weak
  passages, with the incoming order bound `D_i = 1 + (M + J_w - i)N_w` (inherited degrees `≤ N_w + D_i`; the output bounds are
  `D_M ≤ 1 + J_wN_w`, depth `≤ J_wR_w`). The readout factor of a letter is the conjugation
  `ω_u/ω_v = λ_i⁻¹`; inherited sources get no additional factor (the incoming stored coefficients
  already carry `ω_u/ω_v`, which telescopes along the path). -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The menus of the weak passages. -/
structure WeakMenu where
  /-- The cell order `N_w`. -/
  N : ℕ
  /-- The response depth `R_w`. -/
  R : ℕ
  /-- The slow reserve of the lifts. -/
  sX : ℕ
  /-- The fast reserve of the lifts. -/
  sZ : ℕ
  /-- The readout exponent `η₀`. -/
  η0 : ℝ
  /-- The finest level `M + J_w`. -/
  Mtop : ℕ

/-- The largest order of the identities of a stage (`D_i`). -/
def GenStage.maxOrderBound (G : GenStage D hr Dm b j₀) (Din : ℕ) : Prop :=
  ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).maxOrder ≤ Din

open scoped Classical in
/-- `G'` is the weak passage of `G` by the actual weak construction. -/
def IsWeakPassage (D : OCData) (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (G G' : GenStage D hr Dm b j₀) : Prop :=
  D.term < G.level ∧ G'.level = G.level - 1 ∧ G.maxOrderBound Din ∧
    G'.comps = weakExtComps G.level Mn.N Mn.R G.comps ∧ G'.IsNatural Mn.Mtop ∧
    ∃ (e : ∀ v' u', G'.fam.Γ v' u' ≃ {s : WeakSource G //
          s.Valid Mn.N Mn.R Din ∧ s.srcComp G.level = u'.1 ∧ s.tgtComp G.level = v'.1})
      (idx : ∀ v' u', G'.fam.Γ v' u' → ℕ)
      (Cc : ∀ s : WeakSource G, ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
      (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)),
      (∀ s : WeakSource G, s.IsLiftFamily Mn.sX Mn.sZ Mn.N (D.eps (G.level - 1)) (Cc s)) ∧
      (∀ (k : ℤ) (A : RealChain), Odd k → IsAdmissibleChain D b j₀ G.level k A →
        IsLiftSequence (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k A
            (D.eps (G.level - 1)) (fun _ _ _ => []))
          Mn.sX Mn.sZ (D.slotStart G.level k / D.cellScaleSq G.level)
          ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Mn.N 0
          (Cc0 k A)) ∧
      (∀ v' u' (γ' : G'.fam.Γ v' u') v'' u'' (γ'' : G'.fam.Γ v'' u''),
        idx v' u' γ' = idx v'' u'' γ'' → v' = v'' ∧ u' = u'' ∧ HEq γ' γ'') ∧
      ∀ v' u' (γ' : G'.fam.Γ v' u'),
        G'.prov v' u' γ' = .seed (idx v' u' γ') ((e v' u' γ').1.weakTag P G.level rW Mn.η0) ∧
        (G'.fam.identity v' u' γ').map = rootPathMap hr u'.1.root [] v'.1.root ∧
        ∀ (p : OddSlot) (c : StageCtx D b j₀ G'.level p) (d : ℕ) (I : DerivativeWord2 (d - 1))
          (t : ℝ) (X z : Vec 2), 2 ≤ d →
          G'.fam.flux p c v' u' γ' d I t X z =
            if IsAdmissibleChain D b j₀ G'.level p.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
            then transferAt D G.level p.1 ((e v' u' γ').1.lam G.level Mn.η0)
              (e v' u' γ').1.degree
              ((e v' u' γ').1.fluxOp (D.eps (G.level - 1)) (Cc (e v' u' γ').1) Cc0) t
              (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
            else 0

/-- The finest weak family: one root component `⟨r, []⟩`, no identity, natural pieces. -/
def IsWeakRoot (Mtop r : ℕ) (G : GenStage D hr Dm b j₀) : Prop :=
  G.level = Mtop ∧ G.comps = {⟨r, []⟩} ∧ (∀ v u, IsEmpty (G.fam.Γ v u)) ∧ G.IsNatural Mtop

/-- The weak masses `π_{(v,wn)} = π_{(v,w)}c_wE^{η_b}` per letter, root mass `1/2`. -/
def weakMass (D : OCData) (N J : ℕ) (η₀ : ℝ) (c : Comp) : ℝ :=
  (1 / 2) * (c.births.map fun e =>
    (weakCw N J * D.eps e.scale ^ (η₀ / 2)) ^ e.word.length).prod

/-- The weak readout weights `ω_{(v,wn)} = ω_{(v,w)}E^{η₀}` per letter, root weight `1`. -/
def weakReadoutWeight (D : OCData) (η₀ : ℝ) (c : Comp) : ℝ :=
  (c.births.map fun e => (D.eps e.scale ^ η₀) ^ e.word.length).prod

/-- The actual weak construction from the root (level `M + J_w`) to the terminal level `M`. -/
def IsWeakConstruction (D : OCData) (P : ProvParams) (Mn : WeakMenu) (M J : ℕ) (rW : ℝ)
    (r : ℕ) (stage : ℕ → GenStage D hr Dm b j₀) : Prop :=
  Mn.Mtop = M + J ∧ IsWeakRoot (M + J) r (stage (M + J)) ∧
    ∀ i, M < i → i ≤ M + J →
      IsWeakPassage D P Mn rW (1 + (M + J - i) * Mn.N) (stage i) (stage (i - 1)) ∧
      (stage (i - 1)).HasTags P
end

end AVRegularity
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! Definition: the composed weak readout `𝒲_w`.

At a weak passage of level `i`:
* `weakReadoutStep`: the readout `𝓡_i` from the family of level `i-1` to the components of
  level `i`, summing the words at each old component with the weights `λ_i^{|w|} = E^{η₀|w|}`;
* `weakGluedLift`: the glued lift `Λ_i g = ∑_𝗉 ϖ_𝗉 T_𝗉 g` on classical fields, with the lift
  coefficients `CcR` of the full fiber of the level-`i` family at the native charts, from the
  original starts (`IsLiftSequence`, two-dimensional cell inverse, `η = 1`), slow length
  `E = ε_{i-1}`;
* `IsWeakReadoutChain`: the composed readouts `𝒲_{M+J} = ` the value at the root,
  `𝒲_{i-1} = 𝒲_iΛ_i𝓡_i`; the complete weak readout is `𝒲_w = 𝒲_M`, of readout order
  `L_w ≤ J_wN_w`. The readout acts on stored (readout-conjugated) components. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- `𝓡_i`: from classical fields on the components of `G'` (level `i-1`) to the components of `G`
(level `i`). -/
def weakReadoutStep (i : ℕ) (η₀ : ℝ) (G G' : GenStage D ScalarH Dm b j₀)
    (g : CompIn G'.comps → Vec 2 → ℝ) : CompIn G.comps → Vec 2 → ℝ :=
  fun v x => ∑ v' : CompIn G'.comps,
    if compParent i v'.1 = v.1 then (D.eps (i - 1) ^ η₀) ^ (compWord i v'.1).length * g v' x else 0

/-- The glued weak lift `Λ_i` of level `i` on a classical field at time `t`. -/
def weakGluedLift (i N depth : ℕ) (G : GenStage D ScalarH Dm b j₀)
    (CcR : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)) (t : ℝ)
    (g : CompIn G.comps → Vec 2 → ℝ) : CompIn G.comps → Vec 2 → ℝ :=
  fun v x => gluedLift (ocObsPulses D.α D.q D.Λ i t t) (fun k => ocCutoff D.α D.q D.Λ i k)
    (D.cellScaleSq i) (D.eps (i - 1)) (D.eps i) (D.eps i / D.eps (i - 1)) N depth CcR
    (fun k s' y => D.flowOf (i - 1) s' y (D.slotAnchor i k))
    (fun k s' y => D.flowOf (i - 1) (D.slotAnchor i k) y s') (fun _ y w => g w y) t x v

/-- The lift coefficients of the level-`i` family used by `Λ_i`. -/
def IsWeakReadoutLifts (i N depth sX sZ : ℕ) (G : GenStage D ScalarH Dm b j₀)
    (CcR : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)) : Prop :=
  ∀ (k : ℤ) (hk : Odd k),
    IsLiftSequence (familyLiftData D i k (nativeChain i k) (D.eps (i - 1))
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
      sX sZ (D.slotStart i k / D.cellScaleSq i)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i) / D.cellScaleSq i) N depth (CcR k)

/-- The composed weak readouts `𝒲_i` of the construction (`𝒲_{M+J}` the root value,
`𝒲_{i-1} = 𝒲_iΛ_i𝓡_i`). -/
def IsWeakReadoutChain (M J N r : ℕ) (η₀ : ℝ) (depth : ℕ → ℕ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
    (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ) : Prop :=
  (∀ t g x (hr : (⟨r, []⟩ : Comp) ∈ (stage (M + J)).comps), W (M + J) t g x = g ⟨_, hr⟩ x) ∧
    ∀ i, M < i → i ≤ M + J → ∀ t g,
      W (i - 1) t g = W i t (weakGluedLift i N (depth i) (stage i) (CcR i) t
        (weakReadoutStep i η₀ (stage i) (stage (i - 1)) g))
end

/-! Definition: the weak output stage as seen by terminal entry.
The level-`M` weak family `G` (components with
weak word births) is **re-rooted**: a bijection `ι` onto root components (`births = []`), with root
masses `π = weakMass` and root readouts `ω = weakReadoutWeight`, identities relabeled injectively as
seed identities keeping their weak tags with a common factor `Cθ ≥ 1` on tag and record size
(birth list, length, the weak kernel
width `r_w`, excess, order), maps, the other record fields, pieces, weights, actual chains and chart coefficients.
The regularization assigns every identity the kernel `S_w` (`isoPairedKernel r_w`); the record
width is `r_w` from birth (`weakTag`), so stored and recorded widths agree. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The re-rooting of the level-`M` weak family `G` as the weak output stage `Gw`. -/
def IsWeakEncoding (N J : ℕ) (η₀ : ℝ) (rootM rootR : ℕ → ℝ)
    (G Gw : GenStage D ScalarH Dm b j₀) (ι : CompIn G.comps ≃ CompIn Gw.comps) : Prop :=
  Gw.level = G.level ∧ (∀ v, (ι v).1.births = []) ∧
    (∀ v, rootM (ι v).1.root = weakMass D N J η₀ v.1 ∧
      rootR (ι v).1.root = weakReadoutWeight D η₀ v.1) ∧
    (∀ p, (Gw.actual p).1 = (G.actual p).1) ∧ (∀ p, Gw.fam.piece p = G.fam.piece p) ∧
    (∀ p t, Gw.fam.weight p t = G.fam.weight p t) ∧
    ∃ (Cθ : ℝ) (e : ∀ v u, G.fam.Γ v u ≃ Gw.fam.Γ (ι v) (ι u)) (idx : ∀ v u, G.fam.Γ v u → ℕ),
      1 ≤ Cθ ∧
      (∀ v u (γ : G.fam.Γ v u) v' u' (γ' : G.fam.Γ v' u'),
        idx v u γ = idx v' u' γ' → v = v' ∧ u = u' ∧ HEq γ γ') ∧
      ∀ v u (γ : G.fam.Γ v u),
        (∃ tag, G.prov v u γ = .seed (idx v u γ) tag ∧ Gw.prov (ι v) (ι u) (e v u γ) =
          .seed (idx v u γ) { tag with size := Cθ * tag.size }) ∧
        (Gw.fam.identity (ι v) (ι u) (e v u γ)).map = (G.fam.identity v u γ).map ∧
        (Gw.fam.identity (ι v) (ι u) (e v u γ)).record.size =
          Cθ * (G.fam.identity v u γ).record.size ∧
        (Gw.fam.identity (ι v) (ι u) (e v u γ)).record.birthLevel =
          (G.fam.identity v u γ).record.birthLevel ∧
        (Gw.fam.identity (ι v) (ι u) (e v u γ)).record.birthExcess =
          (G.fam.identity v u γ).record.birthExcess ∧
        (Gw.fam.identity (ι v) (ι u) (e v u γ)).record.length =
          (G.fam.identity v u γ).record.length ∧
        (Gw.fam.identity (ι v) (ι u) (e v u γ)).record.width =
          (G.fam.identity v u γ).record.width ∧
        (Gw.fam.identity (ι v) (ι u) (e v u γ)).record.births =
          (G.fam.identity v u γ).record.births ∧
        (Gw.fam.identity (ι v) (ι u) (e v u γ)).maxOrder = (G.fam.identity v u γ).maxOrder ∧
        ∀ (p : OddSlot) (c : StageCtx D b j₀ Gw.level p) (c' : StageCtx D b j₀ G.level p),
          c.1 = c'.1 → ∀ (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2),
          Gw.fam.flux p c (ι v) (ι u) (e v u γ) d I t X z = G.fam.flux p c' v u γ d I t X z
end

end AVRegularity
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity

/-! Definition: **the weak reduction**.
**the weak reduction**.

* `IsWeakPassageSolution`: from the family `U^{(i)}` on the components of level `i`, at the quiet
  time `t_i`, the genuinely solved coarse family `Ū = U^{(i-1)}` on the components of level `i-1` on
  `[t_i, T]` (the copied equations `(𝓛_{i-1} - 𝔈̂_i)Ū_∅ = 0`,
  `(𝓛_{i-1} - 𝔈̂_i)Ū_{wn} = λ_i⁻¹𝔇_{i,n}Ū_w`: the whole system of the weak family of level `i-1`,
  unregularized, at the diffusivity `κ_M` and drift `𝐛_{i-1}`), with the trace `U^{(i)}(t_i)` on
  every old component (no forced row reset) and zero on new words.
* `IsWeakReduction`: the finest family `U^{(M+J)}` is the scalar solution `θ` from the first
  interior time `a₊ ≥ a`; for `M < i ≤ M + J` the passage time `t_i` is **pinned**: `t_i = (l + 1/2)τ''_i` is the midpoint of the first slow renewal quiet margin
  `[(l + 1/2)τ''_i - τ'_i, (l + 1/2)τ''_i + τ'_i]` whose left endpoint follows `a_i = t_{i+1}`, so
  `t_{i+1} + τ'_i ≤ t_i < t_{i+1} + τ''_i + τ'_i ≤ t_{i+1} + 2τ''_i` and `t_i` is quiet (every level-`i`
  slow envelope vanishes there); `a_{M+J} = a₊`. The passage solution `U^{(i-1)}` starts from
  `U^{(i)}(t_i)`. The output is `U = U^{(M)}` on `[a_M, T]`, `a_M = t_{M+1}`, with trace
  `U₀ = U^{(M)}(a_M)`.
* `rerootFamily`: transport of a scalar family along a re-rooting. -/

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The passage solution `Ū` of level `i-1` from the family `U` of level `i` at the time `ti`. -/
def IsWeakPassageSolution (P : ProvParams) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (n : ℕ+)
    (K : ℕ) (G G' : GenStage D ScalarH Dm b j₀) (ti T : ℝ)
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk K (ScalarH v.1.root))
    (Ub : ∀ v : CompIn G'.comps, ℝ → TorusHk K (ScalarH v.1.root))
    (Ubw : ∀ v : CompIn G'.comps, ℝ → TorusHk (K + 1) (ScalarH v.1.root))
    (Ubk : ∀ v u (_ : G'.fam.Γ v u), ℝ → TorusHk (K + Dm - 1) (ScalarH u.1.root)) : Prop :=
  ∃ Ub₀ : ∀ v : CompIn G'.comps, TorusHk K (ScalarH v.1.root),
    IsTerminalTrace G G' (fun v => U v ti) Ub₀ ∧
    G'.IsRegSolution P (fun _ => isoPairedKernel 0 n) (fun _ => isoPairedKernel 0 n) φ₀ hφ₀
      (D.kap G'.level) (streamVel (D.Φ G'.level)) K ti T Ub₀ (fun _ _ => 0) (fun _ _ => 0)
      Ub Ubw Ubk

/-- The weak reduction from the scalar solution `θ` to the level-`M` family.
The passage time `t_i` is pinned to the source choice: the
midpoint `(l + 1/2)τ''_i` of the **first** slow renewal quiet margin
`[(l + 1/2)τ''_i - τ'_i, (l + 1/2)τ''_i + τ'_i]` whose left endpoint follows the previous time
`t_{i+1}`. On that quiet margin every level-`i` slow envelope vanishes, so `t_i` is quiet, and
`t_i - t_{i+1} ≥ τ'_i > 0` leaves a smoothing time. The final
quiet time is bounded by `T`, keeping the reduction inside the solution window. -/
def IsWeakReduction (P : ProvParams) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (n : ℕ+)
    (M J K r : ℕ) (a T : ℝ) (θ : ℝ → Vec 2 → ℝ) (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (tq : ℕ → ℝ) (U : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk K (ScalarH v.1.root))
    (Uw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (K + 1) (ScalarH v.1.root))
    (Uk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ → TorusHk (K + Dm - 1) (ScalarH u.1.root)) :
    Prop :=
  a ≤ tq (M + J + 1) ∧ tq (M + 1) ≤ T ∧
    (∀ (hr : (⟨r, []⟩ : Comp) ∈ (stage (M + J)).comps), ∀ t ∈ Set.Icc (tq (M + J + 1)) T,
      (U (M + J) ⟨_, hr⟩ t).toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
        θ t) ∧
    ∀ i, M < i → i ≤ M + J →
      (∃ l : ℤ, tq i = ((l : ℝ) + 1 / 2) * ocTauPP D.α D.q D.Λ i) ∧
      tq (i + 1) + ocTauP D.α D.q D.Λ i ≤ tq i ∧
      tq i < tq (i + 1) + ocTauPP D.α D.q D.Λ i + ocTauP D.α D.q D.Λ i ∧
      tq i ≤ tq (i + 1) + 2 * ocTauPP D.α D.q D.Λ i ∧
      tq i ∈ ocQuietTimes D.α D.q D.Λ D.ζ i ∧
      IsWeakPassageSolution P φ₀ hφ₀ n K (stage i) (stage (i - 1)) (tq i) T (U i) (U (i - 1))
        (Uw (i - 1)) (Uk (i - 1))

/-- Transport of a scalar family along a re-rooting `ι : G ≃ G'`: the family on `G'`
whose component `v` is the component `ι⁻¹ v` of `F` (scalar components are real for every
root). -/
def rerootFamily {k : ℕ} {G G' : GenStage D ScalarH Dm b j₀} (ι : CompIn G.comps ≃ CompIn G'.comps)
    (F : ∀ v : CompIn G.comps, ℝ → TorusHk k (ScalarH v.1.root)) :
    ∀ v : CompIn G'.comps, ℝ → TorusHk k (ScalarH v.1.root) :=
  fun v t => F (ι.symm v) t

end AVRegularity
end
