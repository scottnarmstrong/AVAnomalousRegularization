-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.LiftGen.Main
public import AVRegularity.Proofs.GenSem.Finer.CovLetterArr
import AVRegularity.Proofs.GenSem.Op.FamChart

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **The slow-flux array is uniformly represented.** `URepArr.fluxXArr`: under the
hypotheses of `URepArr.srcArr`, the array `fluxXArr` of the slow flux of the test field is
time-uniformly represented, entry by entry. -/

namespace UEnv

variable {V : UEnv (RealChain × ℝ)} {ι : Type} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

omit [DecidableEq ι] in
/-- **The slow-flux array `fluxXArr` is uniformly represented.** The hypotheses are those of
`URepArr.srcArr` (here for the one test index `w`, the component `v`, the direction `κ`). -/
theorem URepArr.fluxXArr (hV : V.Ok) (Q : RealChain → LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) {hh n : ℕ} (hn : 1 ≤ n) {η : ℝ}
    (hη : ∀ l ∈ V.W, (Q l.1).η = η)
    (hGr : ∀ i j, V.IsURep (fun l X _ => (Q l.1).G l.2 X i j))
    (hvr : ∀ k, V.IsURep (fun l _ z => (Q l.1).v l.2 z k))
    (hed : V.EdgeURep Q)
    (hC : V.CoeffRepBelow Cc hh n)
    (hreg : ∀ l ∈ V.W, LiftRegular (Q l.1) (Cc l.1) w l.2 hh n (n + Dm + 2)) (v : ι) (κ : Fin 2) :
    V.URepArr (fun l => GenSem.fluxXArr (Q l.1) (Cc l.1) w hh n l.2 v κ) := by
  have hsm : ∀ l ∈ V.W, ∀ hh' k, hh' ≤ hh → k ≤ n → ∀ u,
      ArrSmooth (n + Dm + 2) (GenSem.entryArr (Cc l.1 hh' k) k w l.2 u) := fun l hl hh' k h1 h2 u =>
    arrSmooth_entryArr _ _ _ _ _ ((hreg l hl).coeff hh' h1 k h2 · · u)
  have hent : ∀ hh' k, (hh' < hh ∨ (hh' = hh ∧ k < n)) → ∀ u,
      V.URepArr (fun l => GenSem.entryArr (Cc l.1 hh' k) k w l.2 u) := fun hh' k hk u =>
    urepArr_entryArr (hC hh' k hk) w u
  have hB1 := hent hh (n - 1) (Or.inr ⟨rfl, by omega⟩) v
  unfold GenSem.fluxXArr
  refine URepArr.sub (URepArr.add (URepArr.sub ?_ ?_) ?_) ?_
  · -- fluxXA
    refine (URepArr.mulArr ((hvr κ).smul (Real.sqrt η)) hB1).congr fun l hl => ?_
    simp only [GenSem.fluxXA, hη l hl]
  · -- fluxXB
    refine (URepArr.smul (URepArr.sum Finset.univ fun j _ =>
      URepArr.mulArr (hGr κ j) (hB1.fastArr j)) (Real.sqrt η)).congr fun l hl => ?_
    simp only [GenSem.fluxXB, hη l hl]
  · -- fluxXC
    by_cases h2 : 2 ≤ n
    · have hB2 := hent hh (n - 2) (Or.inr ⟨rfl, by omega⟩) v
      refine (URepArr.neg (URepArr.smul (URepArr.sum Finset.univ fun j _ =>
        URepArr.mulArr (hGr κ j) (hB2.slowArr hV.hζ hV.hρ hV.hU (fun l hl =>
          ((hsm l hl hh (n - 2) le_rfl (by omega) v).mono (by omega : 1 ≤ n + Dm + 2)).slow) j))
        η)).congr fun l hl => ?_
      simp only [GenSem.fluxXC, h2, ite_true, hη l hl]
    · refine (urepArr_zero V).congr fun l hl => ?_
      simp [GenSem.fluxXC, h2]
  · -- fluxXD
    by_cases h0 : hh = 0
    · refine (urepArr_zero V).congr fun l hl => ?_
      simp [GenSem.fluxXD, h0]
    · refine (URepArr.sum (Finset.Icc 1 (min Dm n)) fun j hj => (URepG.fluxG hV (fun A => (Q A).edge) (Real.sqrt η) κ
        (A := fun u l => GenSem.entryArr (Cc l.1 (hh - 1) (n - j)) (n - j) w l.2 u)
        (fun u => hent (hh - 1) (n - j) (Or.inl (by omega)) u)
        (fun l hl u => (hsm l hl (hh - 1) (n - j) (by omega) (by omega) u).mono (by omega))
        hed v (j - 1)).smul (Real.sqrt η)).congr fun l hl => ?_
      simp only [GenSem.fluxXD, h0, ite_false, hη l hl]

end UEnv

end AVRegularity.Providers.GenSem
end

section
open Homogenization AVRegularity AVRegularity.Sobolev Set
namespace AVRegularity.Providers.GenSem

/-! **The lifted source edges of a generated stage are uniformly represented.**
`pathEdgesAt G π p A` is the scalar path family `pathEdges G π p ⟨A, _⟩` of an admissible context
`A` (and no edge elsewhere). `edgeURep_of_generated`: if `G` is generated and slotwise
transverse, then the aggregate of the lifted edge coefficients (`liftEdges`, via
`familyLiftData`) is uniformly represented over the lift environment (`EdgeURep`): an edge of the
path family is either empty or the single old flux `a♭_{γ,d}` (constant map the identity), and the old flux
at the lifted offset `X` is the generated context function at the recentered context
`A^{[ρ X]}` (as `ε_{m-1} (ρ/ε_{m-1}) = ρ`). -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- The scalar path family at the base chain `A`: `pathEdges` at the context `⟨A, _⟩` when `A` is
admissible over the slot `p` of the level of `G`, and no edges otherwise. -/
def pathEdgesAt (G : GenStage D hr Dm b j₀) {h : ℕ} (π : StagePath G h) (p : OddSlot)
    (A : RealChain) : ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ) :=
  if hA : IsAdmissibleChain D b j₀ G.level p.1 A then pathEdges G π p ⟨A, hA⟩
  else fun _ _ _ => []

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- **The lifted source edges of a generated, slotwise transverse stage are uniformly
represented.** The old stage `G` has level `m` and the slot `p = k`; `U A` consists of offsets
whose recentering `A^{[ρ X]}` is admissible over `k`, the base chains `A ∈ 𝒜` are themselves
admissible, `ε_{m-1} ≠ 0`, and the lift times `τ ∈ [t₀, t₁]` map into the output window `J_k`
(`ℓ_m² τ ∈ ocPulseWindow`). -/
theorem edgeURep_of_generated (G : GenStage D hr Dm b j₀) (hG : G.IsGenerated)
    (hT : G.IsSlotTransverse) {h : ℕ} (π : StagePath G h) (p : OddSlot) {m : ℕ} {k : ℤ}
    (hm : G.level = m) (hk : p.1 = k) {ρ : ℝ} (hε : D.eps (m - 1) ≠ 0) (𝒜 : Set RealChain)
    (U : RealChain → Set (Vec 2)) (t₀ t₁ : ℝ)
    (hA𝒜 : ∀ A ∈ 𝒜, IsAdmissibleChain D b j₀ m k A)
    (hU : ∀ A ∈ 𝒜, ∀ X ∈ U A, IsAdmissibleChain D b j₀ m k (A.recenter D (ρ • X)))
    (ht : ∀ τ ∈ Icc t₀ t₁, D.cellScaleSq m * τ ∈ ocPulseWindow D.α D.q D.Λ m k) :
    (liftEnv D b j₀ G.exports m k ρ 𝒜 U t₀ t₁).EdgeURep
      (fun A => familyLiftData D m k A ρ (pathEdgesAt G π p A)) := by
  subst hm
  subst hk
  intro v u d α κ'
  by_cases hvu : (v : ℕ) = u + 1 ∧ (u : ℕ) < h
  swap
  · refine UEnv.isURep_const _ 0 |>.congr fun l hl X _ z => ?_
    by_cases hA : IsAdmissibleChain D b j₀ G.level p.1 l.1 <;>
      simp [familyLiftData, liftEdges, pathEdgesAt, pathEdges, hvu, hA]
  by_cases hd : d.1 ≤ (G.fam.identity _ _ (π.step ⟨u, hvu.2⟩).2.2).maxOrder
  swap
  · refine UEnv.isURep_const _ 0 |>.congr fun l hl X _ z => ?_
    by_cases hA : IsAdmissibleChain D b j₀ G.level p.1 l.1 <;>
      simp [familyLiftData, liftEdges, pathEdgesAt, pathEdges, hvu, hd, hA]
  obtain ⟨f, ⟨e, hs, hf, hden⟩, hfl⟩ := hG p _ _ (π.step ⟨u, hvu.2⟩).2.2 d.1 α κ'
  have hagg : ∀ (l : RealChain × ℝ)
      (hl : l ∈ (liftEnv D b j₀ G.exports G.level p.1 ρ 𝒜 U t₀ t₁).W), ∀ X z,
      ((((familyLiftData D G.level p.1 l.1 ρ (pathEdgesAt G π p l.1)).edge v u d).map
        fun γ => γ.map 1 * γ.coeff α l.2 X z κ').sum) =
      G.fam.flux p ⟨l.1, hA𝒜 l.1 hl.1⟩ _ _ (π.step ⟨u, hvu.2⟩).2.2 d.1 α
        (D.cellScaleSq G.level * l.2) ((ρ / D.eps (G.level - 1)) • X) z κ' := by
    intro l hl X z
    simp [familyLiftData, liftEdges, pathEdgesAt, pathEdges, hvu, hd, hA𝒜 l.1 hl.1]
  refine ⟨Gen.restrict e, UEnv.urep_restrict hs hf hden ?_ ?_⟩
  · intro l hl X hX z
    rw [hagg l hl X z, hfl ⟨l.1, hA𝒜 l.1 hl.1⟩ _ (ht l.2 hl.2) _ z,
      smul_smul, mul_div_cancel₀ _ hε]
    simp only [hU l.1 hl.1 X hX, ↓reduceIte]
    rfl
  · intro l hl X hX z s
    rw [hagg l hl X _, hagg l hl X z]
    exact congrFun (hT p ⟨l.1, hA𝒜 l.1 hl.1⟩ _ _ (π.step ⟨u, hvu.2⟩).2.2 d.1 α _
      (ht l.2 hl.2) _ z s) κ'

end AVRegularity.Providers.GenSem
end

section
open Homogenization AVRegularity AVRegularity.Sobolev MeasureTheory Set
namespace AVRegularity.Providers.GenSem

/-! **Covariant jets of the path mean array.** On the lift setup, the entry of `pmArr` at the
label `y` of the base chain `A` and the physical time `t` is the family denotation
`C · ⟨f⟩(t, A^{[y]})` of the represented slow-flux array `fluxXArr`, for every label `y` with
`ρ⁻¹ y ∈ U A` (by covariance, `A^{[ρ (ρ⁻¹ y)]} = A^{[y]}`). Hence its jets of every order at the
label `0` are represented (`jetRep_covariant_on`), over the family index set `liftFamW` of
physical times `ℓ_m² τ`, `τ ∈ [t₀, t₁]`, and base chains `A ∈ 𝒜`. -/

/-- The family index set of the lift window: the physical times `ℓ_m² τ`, `τ ∈ [t₀, t₁]`, and the
base chains of `𝒜`. -/
def liftFamW (D : OCData) (m : ℕ) (𝒜 : Set RealChain) (t₀ t₁ : ℝ) : Set (ℝ × RealChain) :=
  {q | q.2 ∈ 𝒜 ∧ (D.cellScaleSq m)⁻¹ * q.1 ∈ Icc t₀ t₁}

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {𝒜 : Set RealChain}
  {ρ : ℝ} {h Dm : ℕ} {edge : RealChain → ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ)}
  {U : RealChain → Set (Vec 2)} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
  {Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)}

namespace LiftGenSetup

/-- **Covariant jets of the path mean array**, for every degree `n ≥ 1`, given the regularity of
the lift data at the degree `n`. Every entry of `pmArr` has represented jets of every order at the
label `0`, over `liftFamW`. -/
theorem jetRep_pmArr' (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc)
    (h0 : ∀ A ∈ 𝒜, (0 : Vec 2) ∈ U A) (hhH : h ≤ H) {n : ℕ} (hn1 : 1 ≤ n)
    (hregn : ∀ A ∈ 𝒜, ∀ τ ∈ Icc t₀ t₁,
      LiftRegular (familyLiftData D m k A ρ (edge A)) (Cc A) 0 τ h n (n + Dm + 2))
    (κ : Fin 2) (j : ℕ) (α : DerivativeWord2 j) (r : ℕ) :
    JetRep D bw j₀ 𝒮 m k (liftFamW D m 𝒜 t₀ t₁) r (fun t A y =>
      pmArr D m ρ (familyLiftData D m k A ρ (edge A)) (Cc A) n t κ j α y 0) := by
  set V := liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁ with hV
  have hok : V.Ok := hS.ok
  have hbelow : V.CoeffRepBelow Cc h n := fun hh' k' hk m'' α' v' u' =>
    hS.coeffRep hh' (by omega) k' m'' α' v' u'
  have hrep : V.URepArr (fun l =>
      GenSem.fluxXArr (familyLiftData D m k l.1 ρ (edge l.1)) (Cc l.1) 0 h n l.2 (Fin.last h) κ) :=
    UEnv.URepArr.fluxXArr hok (fun A => familyLiftData D m k A ρ (edge A)) Cc 0 hn1
      (η := D.kap m / D.kap (m - 1)) (fun _ _ => rfl) hS.metric_rep hS.drift_rep hS.edges hbelow
      (fun l hl => hregn l.1 hl.1 l.2 hl.2) (Fin.last h) κ
  obtain ⟨e, hs, hf, f, hd, hv, -⟩ := hrep j α
  set C := -((D.cellScaleSq m)⁻¹ * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ) *
    ρ ^ j with hC
  refine jetRep_covariant_on hS.hζ r
    (c := Gen.mul (Gen.time (s := .fam) (i := m) (p := k) (.const C)) (Gen.mean e))
    (fc := GenSort.mul .fam (GenSort.ofTime .fam (TimeLetter.eval D (.const C))) (cellMeanSem f))
    (U := fun _ A => {w | ρ⁻¹ • w ∈ U A})
    (fun q hq => (hS.hU q.2 hq.1).preimage (continuous_const_smul _))
    (fun q hq => by simpa using h0 q.2 hq.1)
    (.mul (.timeConst C) (.mean hs)) (.mul (.time _) (.mean hf)) (.mul (.time _) (.mean hd))
    fun q hq w hw => ?_
  obtain ⟨t, A⟩ := q
  have hl : ((A, (D.cellScaleSq m)⁻¹ * t) : RealChain × ℝ) ∈ V.W := ⟨hq.1, hq.2⟩
  have htime : D.cellScaleSq m * ((D.cellScaleSq m)⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ hS.hc.ne', one_mul]
  have hval : ∀ z, GenSem.fluxXArr (familyLiftData D m k A ρ (edge A)) (Cc A) 0 h n
      ((D.cellScaleSq m)⁻¹ * t) (Fin.last h) κ j α (ρ⁻¹ • w) z = f t (A.recenter D w) z := by
    intro z
    have := hv _ hl _ hw z
    simp only [hV, liftEnv] at this
    rw [this, htime, smul_smul, mul_inv_cancel₀ hS.hρ, one_smul]
  simp only [pmArr, hval]
  rfl

end LiftGenSetup

end AVRegularity.Providers.GenSem
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **The coefficients of the path mean flux are family-represented.**
`pathMeanFlux_famRep'`: for a `LiftGenSetup` of a scalar path family (components `Fin (h + 1)`),
the family function
`λ = (A, τ) ↦ fluxCoeff (pathMeanFlux D m ρ (familyLiftData D m k A ρ (edge A)) (Cc A) n (ℓ_m² τ)) d I 0 κ`
is represented by one scheduled, seed-provenanced family expression, uniformly over the base
chains `A ∈ 𝒜` and the lift times `τ ∈ [t₀, t₁]`. -/

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {𝒜 : Set RealChain}
  {ρ : ℝ} {h Dm : ℕ} {edge : RealChain → ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ)}
  {U : RealChain → Set (Vec 2)} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
  {Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)}

namespace LiftGenSetup

/-- **The coefficient array of the path mean flux is family-represented.** The hypotheses are those
of the lift setup, `0 ∈ U A` for `A ∈ 𝒜`, and the grade `h ≤ H` and degree `1 ≤ n ≤ N`. No
restriction on `d` or `I` is needed. -/
theorem pathMeanFlux_famRep' (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc)
    (h0 : ∀ A ∈ 𝒜, (0 : Vec 2) ∈ U A) (hhH : h ≤ H) {n : ℕ} (hn1 : 1 ≤ n)
    (hregn : ∀ A ∈ 𝒜, ∀ τ ∈ Set.Icc t₀ t₁,
      LiftRegular (familyLiftData D m k A ρ (edge A)) (Cc A) 0 τ h n (n + Dm + 2))
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (κ : Fin 2) :
    ∃ c : Gen .fam m k, (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).FamURep (fun l =>
      fluxCoeff (pathMeanFlux D m ρ (familyLiftData D m k l.1 ρ (edge l.1)) (Cc l.1) n
        (D.cellScaleSq m * l.2)) d I 0 κ) c := by
  set V := liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁ with hV
  have hok : V.Ok := hS.ok
  have hbelow : V.CoeffRepBelow Cc h n := fun hh' k' hk m'' α' v' u' =>
    hS.coeffRep hh' (by omega) k' m'' α' v' u'
  have hrep : ∀ σ : Equiv.Perm (Fin (d - 1)), V.URepArr (fun l =>
      GenSem.fluxXArr (familyLiftData D m k l.1 ρ (edge l.1)) (Cc l.1) 0 h n l.2 (Fin.last h) κ) :=
    fun σ => UEnv.URepArr.fluxXArr hok (fun A => familyLiftData D m k A ρ (edge A)) Cc 0 hn1
      (η := D.kap m / D.kap (m - 1)) (fun _ _ => rfl) hS.metric_rep hS.drift_rep hS.edges hbelow
      (fun l hl => hregn l.1 hl.1 l.2 hl.2) (Fin.last h) κ
  have hsum : V.IsURep (fun l X z => ∑ σ : Equiv.Perm (Fin (d - 1)),
      GenSem.fluxXArr (familyLiftData D m k l.1 ρ (edge l.1)) (Cc l.1) 0 h n l.2 (Fin.last h) κ
        (d - 1) (I ∘ σ) X z) :=
    UEnv.IsURep.sum _ fun σ _ => hrep σ (d - 1) (I ∘ σ)
  obtain ⟨e, he⟩ := hsum
  have hm := UEnv.URep.mean0 hS.hζ he (fun l hl => h0 l.1 hl.1)
  have hc := (UEnv.famURep_const V (-((D.cellScaleSq m)⁻¹ *
      (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ) * ρ ^ (d - 1) *
      ((d - 1).factorial : ℝ)⁻¹)).mul hm
  refine ⟨_, hc.congr fun l hl => ?_⟩
  have hreg : LiftRegular (familyLiftData D m k l.1 ρ (edge l.1)) (Cc l.1) (0 : Fin (h + 1))
      ((D.cellScaleSq m)⁻¹ * (D.cellScaleSq m * l.2)) h n (Dm + 2) := by
    rw [← mul_assoc, inv_mul_cancel₀ hS.hc.ne', one_mul]
    exact (hregn l.1 hl.1 l.2 hl.2).mono le_rfl le_rfl (by omega)
  rw [fluxCoeff_pathMeanFlux D m _ _ n _ hreg d I κ, ← mul_assoc, inv_mul_cancel₀ hS.hc.ne']
  ring_nf

end LiftGenSetup

end AVRegularity.Providers.GenSem
end

section
open Homogenization AVRegularity AVRegularity.Sobolev Set
namespace AVRegularity.Providers.GenSem

/-! **The covariance letter is family-represented.** On the lift setup, every coefficient
`fluxCoeff (covLetterFlux …) d I 0 c` of the covariance letter `𝖵_{n,h,a,a'}` is one family
expression, uniformly over the base chains and the lift window (`covLetter_famRep`).

The array chain of `covLetterFlux_applyArr` carries represented jets (`ArrJetG` over the family
algebra on `liftFamW`): the path mean arrays by covariance (`jetRep_pmArr'`), the push and pull by
the chart pair, the constant covariance arrays by the time letters `covPrimitive`, and the
compositions. Additional hypotheses, beyond the lift setup:
* the covariance primitive at any anchor `s₀` is the scheduled time letter (anchor `0`)
  minus a time constant (`ocCovariance_anchor`; the terminal anchor `t_p`);
* the terminal-diffusivity convention agrees with `κ` at the levels `m`, `m - 1` (cascade levels);
* the lift data are `C^{2a + Dm + 2}` (the outer `𝒞^a` differentiates the push-forward
  coefficients `2a` times; `reg` of the setup gives `C^{n + Dm + 2}`). -/

section
variable {Λ : Type*} {R : (Λ → ℝ) → Prop}

theorem arrJetG_smul (hR : RepAlg R) {r : ℕ} (c : ℝ) {B : Λ → CArr} (hB : ArrJetG R r B) :
    ArrJetG R r (fun l => c • B l) := fun m α =>
  ⟨(JetRepG.mul hR (fun _ => contDiff_const) (hB m α).2 (jetRepG_const hR r c) (hB m α).1).congr_germ
      fun _ => Filter.Eventually.of_forall fun _ => rfl,
    fun l => contDiff_const.mul ((hB m α).2 l)⟩

end

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {𝒜 : Set RealChain}
  {ρ : ℝ} {h Dm : ℕ} {edge : RealChain → ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ)}
  {U : RealChain → Set (Vec 2)} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
  {Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)}

/-- The covariance matrix entries at the anchor `0` are the time letters `covPrimitive`. -/
theorem famAlg_covMat_zero {W : Set (ℝ × RealChain)} (hκ : D.kap m = D.κ m)
    (hκ' : D.kap (m - 1) = D.κ (m - 1)) (i j : Fin 2) :
    famAlg D bw j₀ 𝒮 m k W (fun q : W => covMat D m 0 q.1.1 i j) :=
  ⟨fun t _ => covMat D m 0 t i j, fun _ => rfl, Gen.time (.covPrimitive m 0 i j),
    .timeCov m i j, .time _, _, .time _, fun q _ => by
      simp only [covMat, GenSort.ofTime, TimeLetter.eval, hκ, hκ']⟩

/-- The covariance matrix entries at any anchor `s₀` are represented: the time letters
`covPrimitive` minus the time constant at `s₀` (`ocCovariance_anchor`). -/
theorem famAlg_covMat {W : Set (ℝ × RealChain)} {s₀ : ℝ} (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (hν : 0 < D.κ m) (hκ : D.kap m = D.κ m)
    (hκ' : D.kap (m - 1) = D.κ (m - 1)) (i j : Fin 2) :
    famAlg D bw j₀ 𝒮 m k W (fun q : W => covMat D m s₀ q.1.1 i j) := by
  have hR := repAlg_famAlg D bw j₀ 𝒮 m k W
  have h := hR.add (famAlg_covMat_zero (W := W) hκ hκ' i j) (hR.const (-covMat D m 0 s₀ i j))
  have heq : (fun q : W => covMat D m s₀ q.1.1 i j) =
      fun q : W => covMat D m 0 q.1.1 i j + -covMat D m 0 s₀ i j :=
    funext fun q => (ocCovariance_anchor D hΛ hζ m hν _ s₀ q.1.1 i j).trans (sub_eq_add_neg _ _)
  rw [heq]
  exact h

namespace LiftGenSetup

/-- A family function represented on `liftFamW` is family-represented over the lift window. -/
theorem famURep_of_famRepOn (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc)
    {G : ℝ → RealChain → ℝ} (hG : IsFamRepOn D bw j₀ 𝒮 m k (liftFamW D m 𝒜 t₀ t₁) G) :
    ∃ c : Gen .fam m k,
      (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).FamURep (fun l => G (D.cellScaleSq m * l.2) l.1) c := by
  obtain ⟨c, hs, hf, fc, hd, hv⟩ := hG
  refine ⟨c, hs, hf, fc, hd, fun l hl => hv (D.cellScaleSq m * l.2, l.1) ⟨hl.1, ?_⟩⟩
  show (D.cellScaleSq m)⁻¹ * (D.cellScaleSq m * l.2) ∈ Icc t₀ t₁
  rw [inv_mul_cancel_left₀ hS.hc.ne']
  exact hl.2

/-- The path mean arrays have represented jets of order `r` over `liftFamW`. -/
theorem arrJetG_pmArr (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc)
    (h0 : ∀ A ∈ 𝒜, (0 : Vec 2) ∈ U A) (hhH : h ≤ H) {n : ℕ} (hn1 : 1 ≤ n)
    (hregn : ∀ A ∈ 𝒜, ∀ τ ∈ Icc t₀ t₁,
      LiftRegular (familyLiftData D m k A ρ (edge A)) (Cc A) 0 τ h n (n + Dm + 2))
    (r : ℕ) (hregR : ∀ A ∈ 𝒜, ∀ τ ∈ Icc t₀ t₁,
      LiftRegular (familyLiftData D m k A ρ (edge A)) (Cc A) 0 τ h n (r + Dm + 2)) (κ : Fin 2) :
    ArrJetG (famAlg D bw j₀ 𝒮 m k (liftFamW D m 𝒜 t₀ t₁)) r (fun q =>
      pmArr D m ρ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n q.1.1 κ) := fun j α =>
  ⟨jetRep_toG (hS.jetRep_pmArr' h0 hhH hn1 hregn κ j α r), fun q =>
    contDiff_pmArr D m ρ _ _ n q.1.1 κ (hregR q.1.2 q.2.1 _ q.2.2) j α⟩

/-- **The coefficients of the covariance letter are family-represented** over the lift window. -/
theorem covLetter_famRep (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc)
    (h0 : ∀ A ∈ 𝒜, (0 : Vec 2) ∈ U A) (hhH : h ≤ H) {n : ℕ} (hn1 : 1 ≤ n)
    (hregn : ∀ A ∈ 𝒜, ∀ τ ∈ Icc t₀ t₁,
      LiftRegular (familyLiftData D m k A ρ (edge A)) (Cc A) 0 τ h n (n + Dm + 2))
    (a a' : ℕ) {s₀ : ℝ} (hΛ : 1 ≤ D.Λ) (hκ : D.kap m = D.κ m)
    (hκ' : D.kap (m - 1) = D.κ (m - 1))
    (hreg2 : ∀ A ∈ 𝒜, ∀ τ ∈ Icc t₀ t₁,
      LiftRegular (familyLiftData D m k A ρ (edge A)) (Cc A) 0 τ h n (2 * a + Dm + 2))
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) :
    ∃ e : Gen .fam m k, (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).FamURep (fun l =>
      fluxCoeff (covLetterFlux D m ρ s₀ (familyLiftData D m k l.1 ρ (edge l.1)) (Cc l.1) n a a'
        (D.cellScaleSq m * l.2) l.1) d I 0 c) e := by
  set W := liftFamW D m 𝒜 t₀ t₁ with hW
  have hR := repAlg_famAlg D bw j₀ 𝒮 m k W
  have hWS : ∀ q ∈ W, q.2.WellSlotted := fun q hq => (hS.hA q.2 hq.1).1
  set K := 2 * a + (n + 2 * a') with hK
  set K' := max K (d - 1) with hK'
  have hP : ∀ κ, ArrJetG (famAlg D bw j₀ 𝒮 m k W) (2 * a) (fun q =>
      pmArr D m ρ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n q.1.1 κ) :=
    hS.arrJetG_pmArr h0 hhH hn1 hregn (2 * a) hreg2
  have hH : ∀ i j, famAlg D bw j₀ 𝒮 m k W (fun q : W => covMat D m s₀ q.1.1 i j) :=
    famAlg_covMat hΛ hS.hζ (hκ ▸ kap_pos_of_cellScaleSq_pos D hS.hc) hκ hκ'
  have hB1 : ∀ c', ArrJetG (famAlg D bw j₀ 𝒮 m k W) (2 * a) (fun q : W =>
      covB1 D m ρ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n q.1.1 q.1.2 c') :=
    fun c' => arrJetG_push_famMap hS.hζ hWS hP c'
  have hB2 : ∀ c', ArrJetG (famAlg D bw j₀ 𝒮 m k W) (0 + 2 * a) (fun q : W =>
      covB2 D m ρ s₀ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n a' q.1.1 q.1.2 c') :=
    fun c' => by
      rw [zero_add]
      exact arrJetG_compArr hR n (hB1 c')
        (arrJetG_covArrPow hR (H := fun q : W => covMat D m s₀ q.1.1) hH a' (2 * a + n))
  have hB4 : ∀ c', ArrJetG (famAlg D bw j₀ 𝒮 m k W) 0 (fun q : W =>
      covB4 D m ρ s₀ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n a a' q.1.1 q.1.2 c') :=
    fun c' => arrJetG_smul hR _ (arrJetG_compArr hR (2 * a)
      (arrJetG_covArrPow hR (H := fun q : W => covMat D m s₀ q.1.1) hH a 0) (hB2 c'))
  have hF : ∀ c', ArrJetG (famAlg D bw j₀ 𝒮 m k W) 0 (fun q : W => covFin D m ρ s₀
      (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n a a' q.1.1 q.1.2 c') :=
    fun c' => arrJetG_pull_famMap hS.hζ hWS hB4 c'
  -- the value at the label `0`
  have hval := rep_fluxCoeff_applyArr hR (K := K') (A := fun q : W => covFin D m ρ s₀
      (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n a a' q.1.1 q.1.2) d I
    (le_max_right _ _) c (fun m' α => (hF c m' α).1.value)
  obtain ⟨G, hG, hGr⟩ := hval
  obtain ⟨e, he⟩ := hS.famURep_of_famRepOn hGr
  refine ⟨e, he.congr fun l hl => ?_⟩
  have hq : ((D.cellScaleSq m * l.2, l.1) : ℝ × RealChain) ∈ W := ⟨hl.1, by
    show (D.cellScaleSq m)⁻¹ * (D.cellScaleSq m * l.2) ∈ Icc t₀ t₁
    rw [inv_mul_cancel_left₀ hS.hc.ne']; exact hl.2⟩
  -- the identity of the letter with its array operator
  have hτ : (D.cellScaleSq m)⁻¹ * (D.cellScaleSq m * l.2) = l.2 :=
    inv_mul_cancel_left₀ hS.hc.ne' l.2
  have hreg : LiftRegular (familyLiftData D m k l.1 ρ (edge l.1)) (Cc l.1) 0
      ((D.cellScaleSq m)⁻¹ * (D.cellScaleSq m * l.2)) h n (2 * a + Dm + 2) := by
    rw [hτ]; exact hreg2 l.1 hl.1 l.2 hl.2
  have hmono : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) :=
    (contDiff_mono (0 : Vec 2) I).of_le le_top
  have hvec : covLetterFlux D m ρ s₀ (familyLiftData D m k l.1 ρ (edge l.1)) (Cc l.1) n a a'
      (D.cellScaleSq m * l.2) l.1 (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) 0 =
      fun c' => applyArr K' (covFin D m ρ s₀ (familyLiftData D m k l.1 ρ (edge l.1)) (Cc l.1) n a
        a' (D.cellScaleSq m * l.2) l.1 c') (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) 0 0 := by
    refine funext fun c' => ?_
    rw [covLetterFlux_applyArr hS.hζ hS.hρ l.1 hreg hmono 0 c',
      applyArr_eq_of_supp (le_max_left K (d - 1)) (arrSupp_covFin _ _ _ _ _ _ _ _ _ _ _ c')]
  have key : fluxCoeff (covLetterFlux D m ρ s₀ (familyLiftData D m k l.1 ρ (edge l.1)) (Cc l.1) n
      a a' (D.cellScaleSq m * l.2) l.1) d I 0 c =
      fluxCoeff (fun g y κ => applyArr K' (covFin D m ρ s₀ (familyLiftData D m k l.1 ρ (edge l.1))
        (Cc l.1) n a a' (D.cellScaleSq m * l.2) l.1 κ) g y 0) d I 0 c := by
    unfold fluxCoeff
    rw [hvec]
  exact key.trans (hG ⟨_, hq⟩)

end LiftGenSetup

end AVRegularity.Providers.GenSem
end
