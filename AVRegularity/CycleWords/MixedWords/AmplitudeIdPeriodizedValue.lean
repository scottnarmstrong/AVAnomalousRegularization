-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.CompactChainExistence
public import AVRegularity.CycleWords.MixedWords.B1WSourceL2
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import AVRegularity.Proofs.Intermediate.Weighted.CycleMixedWordsExists
public import AVRegularity.CycleWords.MixedWords.SlowDamping
import AVRegularity.CycleWords.FibreGraphNativeSeries
import AVRegularity.Weighted.WordNativeSolutionPack
import AVRegularity.Weighted.ScalarChainClippedFactorialENNReal

section
@[expose] public section
section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # `ChainDiscardStatement` from the discard on compact data

`chainDiscard_of_compact : CompactDiscardStatement → ChainFullFieldStatement →
ChainDiscardStatement`: smooth approximation in the input moment norm extends the endpoint to
rough data. The given chain is capped at the slots `cappedWordSlots κ K_f d` (its endpoint keeps
the jets of order `≤ K_f`); compact approximants `φ_k` of the datum (`CompactDensityStatement`)
start chains at the same capped slots (the existence statement); the difference of the two chains
is a chain from `f - φ_k` (`planeChainFrom_combination`), bounded by `ChainFullFieldStatement`; on
the compact chains the retained map is the retained cutoff of the endpoint, so
`CompactDiscardStatement` bounds them; the retained map converges with every derivative pointwise
(`retainedMap_orderedDerivative_tendsto`); Fatou (`jetOutputNorm_le_liminf`) closes. -/

section
universe u v

section Helpers

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem momentNorm_congr_ae' (π : ι → ℝ) (n : ℕ) (s : ℝ) {F G : ∀ x, Vec 2 → h x}
    (hFG : ∀ x, F x =ᵐ[volume] G x) : momentNorm π n s F = momentNorm π n s G := by
  have key : ∀ (β : ℕ × ℕ) x, eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • F x z)
      2 volume = eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • G x z) 2 volume := by
    intro β x
    refine eLpNorm_congr_ae ?_
    filter_upwards [hFG x] with z hz
    rw [hz]
  simp only [momentNorm, key]

variable {D Nw : ℕ}

/-- The capped slots descend along every letter edge. -/
theorem cappedWordSlots_isWordSlots {π : ι → ℝ} {dom : Set (ℝ × Vec 2)} {J H : ℕ}
    {letters : Fin Nw → CycleLetter ι h D} (hlet : ∀ i, IsCycleLetter π (letters i) dom J H)
    {d : Fin Nw → ℕ} (hd : ∀ i, (letters i).order = d i) {κ : Fin (Nw + 1) → ι → ℕ}
    (hκ : IsWordSlots letters κ) (Kf : ℕ) : IsWordSlots letters (cappedWordSlots κ Kf d) := by
  intro j x y o hne
  have ho2 : 2 ≤ o.1 := (Finset.mem_Icc.1 o.2).1
  have hod : o.1 ≤ d j := by
    rw [← hd j]
    by_contra hlt
    exact hne ((hlet j).edge_order x y o (not_le.1 hlt))
  exact cappedWordSlots_edge_compatible κ Kf d j x y o.1 ho2 hod (hκ j x y o hne)

omit [Fintype ι] in
/-- The capped slots stay below the fast reserve of the statement. -/
theorem cappedWordSlots_le_reserve (κ : Fin (Nw + 1) → ι → ℕ) (Kf m : ℕ) (d Ks : Fin Nw → ℕ)
    (j : Fin (Nw + 1)) (x : ι) :
    cappedWordSlots κ Kf d j x ≤
      wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d := by
  refine (cappedWordSlots_le_fixed κ Kf d j x).trans ?_
  unfold wordReserveJstar wordReserveKstar wordReserveN
  omega

end Helpers

section Jets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- The jets of `1 • trunc U + (-1) • V` are those of `U` minus those of `V`. -/
theorem planeJetOrder_trunc_sub_ae {K L : ℕ} (hKL : K ≤ L) (U : PlaneHk Set.univ L E)
    (V : PlaneHk Set.univ K E) {a : ℕ} (ha : a ≤ K) (wd : DerivativeWord2 a) :
    planeJetOrder ((1 : ℝ) • truncatePlaneHk hKL U + (-1 : ℝ) • V) a wd =ᵐ[volume]
      fun z => planeJetOrder U a wd z - planeJetOrder V a wd z := by
  have heq : (1 : ℝ) • truncatePlaneHk hKL U + (-1 : ℝ) • V = truncatePlaneHk hKL U - V := by
    rw [one_smul, neg_one_smul, ← sub_eq_add_neg]
  rw [heq]
  filter_upwards [planeJetOrder_sub_ae ha (truncatePlaneHk hKL U) V wd] with z hz
  rw [hz, planeJetOrder_truncate hKL ha U wd]

end Jets

section Chains

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {N : ℕ}

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The level data of the difference of a truncated chain and a chain. -/
theorem chainDatum_trunc_sub (κ κ' : Fin (N + 1) → ι → ℕ) (hle : ∀ j x, κ' j x ≤ κ j x)
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x)) (f' : ∀ x, PlaneHk Set.univ (κ' 0 x) (h x)) :
    (fun j x => (1 : ℝ) • truncatePlaneHk (hle j x) (chainDatum κ f j x) +
        (-1 : ℝ) • chainDatum κ' f' j x) =
      chainDatum κ' (fun x => (1 : ℝ) • truncatePlaneHk (hle 0 x) (f x) + (-1 : ℝ) • f' x) := by
  funext j x
  by_cases hj : j = 0
  · subst hj
    simp [chainDatum]
  · simp [chainDatum, hj]

/-- **The difference chain.** A word chain at slots `κ` minus a word chain at smaller descending
slots `κ'` is, after truncation, a word chain at `κ'` from the truncated difference of the data. -/
theorem isPlaneChain_trunc_sub {D : ℕ} (hD : 2 ≤ D) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (letters : Fin N → CycleLetter ι h D) (X₀ : Vec 2) (δ a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (κ κ' : Fin (N + 1) → ι → ℕ) (hle : ∀ j x, κ' j x ≤ κ j x)
    (hc : IsWordSlots letters κ) (hc' : IsWordSlots letters κ')
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (f' : ∀ x, PlaneHk Set.univ (κ' 0 x) (h x))
    (u' : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ' j x) (h x))
    (w' : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ' j x + 1) (h x))
    (hs : IsPlaneChain (wordChainData G letters X₀ δ) κ a b v f (fun _ _ _ => 0) u w)
    (hs' : IsPlaneChain (wordChainData G letters X₀ δ) κ' a b v f' (fun _ _ _ => 0) u' w') :
    IsPlaneChain (wordChainData G letters X₀ δ) κ' a b v
      (fun x => (1 : ℝ) • truncatePlaneHk (hle 0 x) (f x) + (-1 : ℝ) • f' x) (fun _ _ _ => 0)
      (fun j x s => (1 : ℝ) • truncatePlaneHk (hle j x) (u j x s) + (-1 : ℝ) • u' j x s)
      (fun j x s => (1 : ℝ) • truncatePlaneHk (Nat.succ_le_succ (hle j x)) (w j x s) +
        (-1 : ℝ) • w' j x s) := by
  have ht := wordChainFrom_truncate hD G letters κ κ' hle hc hc' X₀ δ a b v (chainDatum κ f)
    (fun _ _ _ => 0) u w ((isPlaneChain_iff_from _ κ a b v f _ u w).1 hs)
  have hc2 := planeChainFrom_combination ht ((isPlaneChain_iff_from _ κ' a b v f' _ u' w').1 hs')
    1 (-1)
  refine (isPlaneChain_iff_from _ κ' a b v _ _ _ _).2 (IsPlaneChainFrom.congr_data hc2 ?_ ?_)
  · exact chainDatum_trunc_sub κ κ' hle f f'
  · funext j x s
    simp

end Chains
end

/-! # The extension of the discard to rough data

`chainDiscard_of_compact : CompactDiscardStatement → ChainFullFieldStatement →
ChainDiscardStatement`: the compact chains at capped slots (`exists_compactChain_capped`, the
existence statement), the bound for one approximant (`discard_step_le`) and the limit. -/

section
universe u v

section Step

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **One approximant.** If the compact endpoint minus `R_k` is bounded by `X` and the difference
chain's endpoint by `Y`, the actual endpoint minus `R_k` is bounded by `X + Y`. -/
theorem discard_step_le (π : ι → ℝ) (m Kf : ℕ) (s r : ℝ) {L L' : ι → ℕ} (hle : ∀ x, L' x ≤ L x)
    (hKf : ∀ x, L' x = Kf) (uN : ∀ x, PlaneHk Set.univ (L x) (h x))
    (ukN : ∀ x, PlaneHk Set.univ (L' x) (h x)) (Rk : ∀ x, Vec 2 → h x)
    (hRk : ∀ x (M : ℕ), ContDiff ℝ M (Rk x)) {X Y : ℝ≥0∞}
    (hA : jetOutputNorm π m Kf s r
      (fun x a wd z => planeJetOrder (ukN x) a wd z - orderedDerivative wd (Rk x) z) ≤ X)
    (hD : jetOutputNorm π m Kf s r (fun x a wd z =>
      planeJetOrder ((1 : ℝ) • truncatePlaneHk (hle x) (uN x) + (-1 : ℝ) • ukN x) a wd z) ≤ Y) :
    jetOutputNorm π m Kf s r
      (fun x a wd z => planeJetOrder (uN x) a wd z - orderedDerivative wd (Rk x) z) ≤ X + Y := by
  have hsplit : (fun x a (wd : DerivativeWord2 a) z =>
      planeJetOrder (uN x) a wd z - orderedDerivative wd (Rk x) z) =
      fun x a wd z => (planeJetOrder (ukN x) a wd z - orderedDerivative wd (Rk x) z) +
        (planeJetOrder (uN x) a wd z - planeJetOrder (ukN x) a wd z) := by
    funext x a wd z
    abel
  have hmR : ∀ x a (wd : DerivativeWord2 a), AEStronglyMeasurable
      (orderedDerivative wd (Rk x)) volume :=
    fun x a wd => (orderedDerivative_continuous wd (hRk x a)).aestronglyMeasurable
  have hmA : ∀ x a (wd : DerivativeWord2 a), AEStronglyMeasurable
      (fun z => planeJetOrder (ukN x) a wd z - orderedDerivative wd (Rk x) z) volume :=
    fun x a wd => (planeJetOrder_aestronglyMeasurable (ukN x) a wd).sub (hmR x a wd)
  have hmB : ∀ x a (wd : DerivativeWord2 a), AEStronglyMeasurable
      (fun z => planeJetOrder (uN x) a wd z - planeJetOrder (ukN x) a wd z) volume :=
    fun x a wd => (planeJetOrder_aestronglyMeasurable (uN x) a wd).sub
      (planeJetOrder_aestronglyMeasurable (ukN x) a wd)
  have hcongr : jetOutputNorm π m Kf s r (fun x a wd z =>
      planeJetOrder (uN x) a wd z - planeJetOrder (ukN x) a wd z) =
      jetOutputNorm π m Kf s r (fun x a wd z =>
        planeJetOrder ((1 : ℝ) • truncatePlaneHk (hle x) (uN x) + (-1 : ℝ) • ukN x) a wd z) := by
    refine jetOutputNorm_congr_ae π m Kf s r fun x a wd ha => ?_
    exact (planeJetOrder_trunc_sub_ae (hle x) (uN x) (ukN x) ((hKf x).symm ▸ ha) wd).symm
  rw [hsplit]
  refine (jetOutputNorm_add_le π m Kf s r _ _ hmA hmB).trans (add_le_add hA ?_)
  rw [hcongr]
  exact hD

end Step

section Capped

/-- **Compact chains at the capped slots** (the existence statement). -/
theorem exists_compactChain_capped {K : ScalarConstants} {g₁ : ℝ} (hg₁ : g₁ ≤ 1 / 4)
    {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D Nw H J Kf m : ℕ} {d Ks : Fin Nw → ℕ} {pos : Fin Nw → Bool} {π : ι → ℝ}
    {letters : Fin Nw → CycleLetter ι h D}
    (hletters : ∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧
      (letters i).positive = pos i)
    {η S ηg t₀ ϖ : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {g : ℝ}
    {reg : BlockRegions} (pkg : ScalarPackage K η G v t₀ S ϖ reg)
    (hB : IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg)
    (hJ : wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d ≤ J) (X₀ : Vec 2)
    {κ : Fin (Nw + 1) → ι → ℕ} (hκf : ∀ x, Kf ≤ κ (Fin.last Nw) x)
    (hκ : IsWordSlots letters κ)
    (fk : ∀ x, PlaneHk Set.univ (cappedWordSlots κ Kf d 0 x) (h x)) (hfk : IsCompactDatum fk) :
    ∃ (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (cappedWordSlots κ Kf d j x) (h x))
      (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κ Kf d j x + 1) (h x)),
      IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κ Kf d) t₀ (t₀ + S) v
        fk (fun _ _ _ => 0) uk wk := by
  have hcapW := cappedWordSlots_isWordSlots hB.hlet (fun i => (hletters i).1) hκ Kf
  refine AVRegularity.Providers.cycle_mixed_words_exists K Nw D H Kf m hB.hD d Ks pos π hB.hπ
    letters hletters η S ηg t₀ ϖ hB.hη hB.hη1 hB.hS hB.hηg hB.hηg1 hB.hϖ G v g hB.hGm hB.hv
    hB.hvs hB.hv0 hB.hvw hB.hvj hB.hg0 (hB.hg₁.trans hg₁) hB.hg hB.hGn reg pkg
    (fun i => isCycleLetter_reserve_mono (hB.hlet i) hJ) hB.hmeas X₀ (cappedWordSlots κ Kf d)
    (fun x => (cappedWordSlots_last κ Kf d x (hκf x)).ge) hcapW
    (fun j x => cappedWordSlots_le_reserve κ Kf m d Ks j.succ x) fk ?_
  refine lt_top_iff_ne_top.2 (AVRegularity.Weighted.geometryDataNorm_ne_top_of_components
    π _ _ ϖ 0 1 fk fun x => ?_)
  obtain ⟨φ, -, hφc, hφ⟩ := hfk x
  refine weightedFactorialNormSq_compact_value_ne_top _ ϖ 0 1 (fk x) hφc.isCompact ?_
  have he : (fk x).toFunction.jet (valueIndex2 (cappedWordSlots κ Kf d 0 x)) =
      planeValue (fk x) := (planeValue_eq_stored (fk x)).symm
  rw [he]
  filter_upwards [hφ] with z hz hzA
  rw [hz]
  exact image_eq_zero_of_notMem_tsupport hzA

end Capped

section Core

/-- **The extension**, with the compact discard bound `B` and the full-field factor `C_F` at the
capped slots as hypotheses. -/
theorem chainDiscard_core {K : ScalarConstants} {g₁ : ℝ} (hg₁ : g₁ ≤ 1 / 4) {χlo : Vec 2 → ℝ}
    {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D Nw H J Kf m : ℕ} {d Ks : Fin Nw → ℕ} {pos : Fin Nw → Bool} {π : ι → ℝ}
    {letters : Fin Nw → CycleLetter ι h D}
    (hletters : ∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧
      (letters i).positive = pos i)
    {η S ηg rstar t₀ ϖ : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {g : ℝ}
    {reg : BlockRegions} (pkg : ScalarPackage K η G v t₀ S ϖ reg)
    (hB : IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg)
    (hJ : wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d ≤ J) (X₀ : Vec 2)
    {R : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x)}
    (hR : IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R)
    {κ : Fin (Nw + 1) → ι → ℕ} (hκf : ∀ x, Kf ≤ κ (Fin.last Nw) x) (hκ : IsWordSlots letters κ)
    {f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x)}
    {u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x)}
    {w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)}
    (hfin : momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) < ⊤)
    (hch : IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f
      (fun _ _ _ => 0) u w)
    {B CFF : ℝ≥0∞} (hBtop : B ≠ ⊤) (hCFtop : CFF ≠ ⊤)
    (hCDb : ∀ (fk : ∀ x, PlaneHk Set.univ (cappedWordSlots κ Kf d 0 x) (h x))
      (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κ Kf d j x) (h x))
      (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κ Kf d j x + 1) (h x)),
      IsCompactDatum fk →
      IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κ Kf d) t₀ (t₀ + S) v
        fk (fun _ _ _ => 0) uk wk →
      jetOutputNorm π m Kf ϖ rstar
          (fun x a wd z => planeJetOrder (uk (Fin.last Nw) x (t₀ + S)) a wd z -
            orderedDerivative wd (fourierCutoff (retainedCutoff K η χlo)
              (planeValue (uk (Fin.last Nw) x (t₀ + S)))) z) ≤
        B * momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (fk x)))
    (hFFb : ∀ (f' : ∀ x, PlaneHk Set.univ (cappedWordSlots κ Kf d 0 x) (h x))
      (u' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κ Kf d j x) (h x))
      (w' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κ Kf d j x + 1) (h x)),
      momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f' x)) < ⊤ →
      IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κ Kf d) t₀ (t₀ + S) v
        f' (fun _ _ _ => 0) u' w' →
      jetOutputNorm π m Kf ϖ rstar
          (fun x a wd z => planeJetOrder (u' (Fin.last Nw) x (t₀ + S)) a wd z) ≤
        CFF * momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f' x))) :
    jetOutputNorm π m Kf ϖ rstar
        (fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
          orderedDerivative wd (R (fun x' => planeValue (f x')) x) z) ≤
      B * momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) := by
  set F : ∀ x, Vec 2 → h x := fun x => planeValue (f x) with hFdef
  have hd : ∀ i, (letters i).order = d i := fun i => (hletters i).1
  have hle : ∀ j x, cappedWordSlots κ Kf d j x ≤ κ j x := cappedWordSlots_le_original κ Kf d
  have hW' : IsWordSlots letters (cappedWordSlots κ Kf d) :=
    cappedWordSlots_isWordSlots hB.hlet hd hκ Kf
  have hlast : ∀ x, cappedWordSlots κ Kf d (Fin.last Nw) x = Kf :=
    fun x => cappedWordSlots_last κ Kf d x (hκf x)
  have hFm : ∀ x, AEStronglyMeasurable (F x) volume :=
    fun x => planeJetOrder_aestronglyMeasurable (f x) 0 _
  -- compact approximants and their chains
  obtain ⟨φs, hφs, hconv⟩ := compactDensity.{u, v}.2 F hFm
  have hconvN := hconv π (wordReserveN m Ks) ϖ hfin
  have hlift : ∀ k x, ∃ fk : PlaneHk Set.univ (cappedWordSlots κ Kf d 0 x) (h x),
      planeValue fk =ᵐ[volume] φs k x :=
    fun k x => compactDensity.{u, v}.1 _ (φs k x) (hφs k x).1 (hφs k x).2
  choose fk hfk using hlift
  have hcd : ∀ k, IsCompactDatum (fk k) := fun k x => ⟨φs k x, (hφs k x).1, (hφs k x).2, hfk k x⟩
  have hex := fun k => exists_compactChain_capped hg₁ hletters pkg hB hJ X₀ hκf hκ (fk k) (hcd k)
  choose uk wk huk using hex
  have hdiffm : ∀ k, momentNorm π (wordReserveN m Ks) ϖ
      (fun x z => F x z - planeValue (fk k x) z) =
      momentNorm π (wordReserveN m Ks) ϖ (fun x z => F x z - φs k x z) := by
    intro k
    refine momentNorm_congr_ae' _ _ _ fun x => ?_
    filter_upwards [hfk k x] with z hz
    rw [hz]
  have hfkm : ∀ k, momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (fk k x)) =
      momentNorm π (wordReserveN m Ks) ϖ (φs k) :=
    fun k => momentNorm_congr_ae' _ _ _ fun x => hfk k x
  -- the retained map along the approximants
  have hslow : (fun i => (letters i).slow) = Ks := funext fun i => (hletters i).2.1
  have hr : 0 < 2 * K.ξlo * Real.sqrt η := by
    have h1 := pkg.consts_pos.2.1
    have h2 := Real.sqrt_pos.2 hB.hη
    positivity
  have hlim0 : Tendsto (fun k => momentNorm π (wordReserveN 0 fun i => (letters i).slow) ϖ
      (fun x z => F x z - planeValue (fk k x) z)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconvN
      (fun k => zero_le) (fun k => ?_)
    rw [← hdiffm k, hslow]
    exact momentNorm_mono (by unfold wordReserveN; omega) _ _ _
  have hRlim : ∀ x a (wd : DerivativeWord2 a) z,
      Tendsto (fun k => orderedDerivative wd (R (fun x' => planeValue (fk k x')) x) z) atTop
        (𝓝 (orderedDerivative wd (R F x) z)) :=
    fun x a wd z => retainedMap_orderedDerivative_tendsto amplitudePlancherel hR hr hB.hπ F
      (fun k x => planeValue (fk k x)) hFm
      (fun k x => planeJetOrder_aestronglyMeasurable (fk k x) 0 _) hlim0 x a wd z
  -- Fatou
  have hfatou := jetOutputNorm_le_liminf π m Kf ϖ rstar
    (fun k x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
      orderedDerivative wd (R (fun x' => planeValue (fk k x')) x) z)
    (fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
      orderedDerivative wd (R F x) z)
    (fun k x a wd => (planeJetOrder_aestronglyMeasurable _ a wd).sub
      (orderedDerivative_continuous wd ((hR.band _ x).1 a)).aestronglyMeasurable)
    (fun x a wd => (planeJetOrder_aestronglyMeasurable _ a wd).sub
      (orderedDerivative_continuous wd ((hR.band _ x).1 a)).aestronglyMeasurable)
    (fun x a wd z => tendsto_const_nhds.sub (hRlim x a wd z))
  -- one approximant
  have hstep : ∀ᶠ k in atTop, jetOutputNorm π m Kf ϖ rstar
      (fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
        orderedDerivative wd (R (fun x' => planeValue (fk k x')) x) z) ≤
      B * momentNorm π (wordReserveN m Ks) ϖ (φs k) +
        CFF * momentNorm π (wordReserveN m Ks) ϖ (fun x z => F x z - φs k x z) := by
    filter_upwards [hconvN.eventually (gt_mem_nhds zero_lt_one)] with k hk
    have hchain := hR.chain _ hW' (fk k) (uk k) (wk k) (huk k) (hcd k)
    have hA := hCDb (fk k) (uk k) (wk k) (hcd k) (huk k)
    have hRk : (fun x a (wd : DerivativeWord2 a) z =>
        planeJetOrder (uk k (Fin.last Nw) x (t₀ + S)) a wd z -
          orderedDerivative wd (R (fun x' => planeValue (fk k x')) x) z) =
        fun x a wd z => planeJetOrder (uk k (Fin.last Nw) x (t₀ + S)) a wd z -
          orderedDerivative wd (fourierCutoff (retainedCutoff K η χlo)
            (planeValue (uk k (Fin.last Nw) x (t₀ + S)))) z := by
      funext x a wd z
      rw [congrFun hchain x]
    rw [← hRk, hfkm k] at hA
    have hdiff := isPlaneChain_trunc_sub hB.hD G letters X₀ (ϖ * ηg) t₀ (t₀ + S) v κ
      (cappedWordSlots κ Kf d) hle hκ hW' f u w (fk k) (uk k) (wk k) hch (huk k)
    have hval : ∀ x, planeValue ((1 : ℝ) • truncatePlaneHk (hle 0 x) (f x) + (-1 : ℝ) • fk k x)
        =ᵐ[volume] fun z => F x z - planeValue (fk k x) z :=
      fun x => planeJetOrder_trunc_sub_ae (hle 0 x) (f x) (fk k x) (Nat.zero_le _) _
    have hm'' : momentNorm π (wordReserveN m Ks) ϖ (fun x =>
        planeValue ((1 : ℝ) • truncatePlaneHk (hle 0 x) (f x) + (-1 : ℝ) • fk k x)) =
        momentNorm π (wordReserveN m Ks) ϖ (fun x z => F x z - φs k x z) := by
      rw [momentNorm_congr_ae' _ _ _ hval, hdiffm k]
    have hD := hFFb _ _ _ (by rw [hm'']; exact hk.trans ENNReal.one_lt_top) hdiff
    rw [hm''] at hD
    exact discard_step_le π m Kf ϖ rstar (hle (Fin.last Nw)) hlast
      (fun x => u (Fin.last Nw) x (t₀ + S)) (fun x => uk k (Fin.last Nw) x (t₀ + S))
      (fun x => R (fun x' => planeValue (fk k x')) x) (fun x M => (hR.band _ x).1 M) hA hD
  -- the limit
  have hb : Tendsto (fun k => B * momentNorm π (wordReserveN m Ks) ϖ (φs k) +
      CFF * momentNorm π (wordReserveN m Ks) ϖ (fun x z => F x z - φs k x z)) atTop
      (𝓝 (B * momentNorm π (wordReserveN m Ks) ϖ F)) := by
    have h1 := ENNReal.Tendsto.const_mul (momentNorm_tendsto π _ ϖ F φs hfin hconvN)
      (Or.inr hBtop)
    have h2 := ENNReal.Tendsto.const_mul hconvN (Or.inr hCFtop)
    simpa using h1.add h2
  calc _ ≤ _ := hfatou
    _ ≤ liminf (fun k => B * momentNorm π (wordReserveN m Ks) ϖ (φs k) +
          CFF * momentNorm π (wordReserveN m Ks) ϖ (fun x z => F x z - φs k x z)) atTop :=
        liminf_le_liminf hstep
    _ = B * momentNorm π (wordReserveN m Ks) ϖ F := hb.liminf_eq

end Core

/-- **`ChainDiscardStatement` from the discard on compact data and the full-field bound.** -/
theorem chainDiscard_of_compact (hCD : CompactDiscardStatement.{u, v})
    (hFF : ChainFullFieldStatement.{u, v}) : ChainDiscardStatement.{u, v} := by
  intro K
  obtain ⟨g₁C, hg₁C, hCDK⟩ := hCD K
  obtain ⟨g₁F, hg₁F, hFFK⟩ := hFF K
  refine ⟨min (min g₁C g₁F) (1 / 4), lt_min (lt_min hg₁C hg₁F) (by norm_num), ?_⟩
  intro χlo hχ Nw D H Kf m Cout hCout d Ks pos
  obtain ⟨C, c, Q, hC, hc, hCDs⟩ := hCDK χlo hχ Nw D H Kf m Cout hCout d Ks pos
  obtain ⟨CF, QF, hCF, hFFs⟩ := hFFK Nw D H Kf m Cout hCout d Ks pos
  refine ⟨C, c, Q, hC, hc, ?_⟩
  intro ι _ h _ _ _ _ _ _ J π letters hletters η S ηg rstar t₀ ϖ G v g reg pkg hB hJ hrstar
    hrstarC X₀ R hR κ hκf hκ f u w hfin hch
  have hcapW := cappedWordSlots_isWordSlots hB.hlet (fun i => (hletters i).1) hκ Kf
  have hcapf : ∀ x, Kf ≤ cappedWordSlots κ Kf d (Fin.last Nw) x :=
    fun x => (cappedWordSlots_last κ Kf d x (hκf x)).ge
  exact chainDiscard_core (min_le_right _ _) hletters pkg hB hJ X₀ hR hκf hκ hfin hch
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    (fun fk uk wk hcd hchk => hCDs J π letters hletters η S ηg rstar t₀ ϖ G v g reg pkg
      (hB.mono ((min_le_left _ _).trans (min_le_left _ _))) hJ hrstar hrstarC X₀ _ hcapf hcapW
      fk uk wk hcd hchk)
    (fun f' u' w' hfin' hchk => hFFs J π letters hletters η S ηg rstar t₀ ϖ G v g reg pkg
      (hB.mono ((min_le_left _ _).trans (min_le_right _ _))) hJ hrstar hrstarC X₀ _ hcapf hcapW
      f' u' w' hfin' hchk)
end

end AVRegularity.CycleWords.Assembly
end
end
end

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! All polynomial moments of the given compact-data word chain. -/

universe u v
variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ} {K : ScalarConstants} {g₁ : ℝ}

/-- The zeroth summand of the factorial energy controls the weighted value. -/
theorem amplitudeId_weighted_value_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {k : ℕ} (U : PlaneHk Set.univ k E) (n : ℕ) (ϖ r : ℝ) :
    (∫⁻ y, ENNReal.ofReal ((1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) ^ n * ‖planeValue U y‖ ^ 2)) ≤
      weightedFactorialNormSq n ϖ 0 r k U := by
  have he := Finset.single_le_sum (s := Finset.range (k + 1))
    (f := fun j => ENNReal.ofReal (r ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
      ∫⁻ y, ENNReal.ofReal ((1 + ϖ ^ 2 * ((y 0 - (0 : Vec 2) 0) ^ 2 +
        (y 1 - (0 : Vec 2) 1) ^ 2)) ^ n *
        ∑ w : DerivativeWord2 j, ‖planeJetOrder U j w y‖ ^ 2))
    (fun _ _ => by positivity) (by simp : 0 ∈ Finset.range (k + 1))
  simp only [Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow,
    div_one, ENNReal.ofReal_one, one_mul, Pi.zero_apply, sub_zero,
    Fintype.sum_unique] at he
  convert he using 1
  · congr 1
  · simp only [weightedFactorialNormSq, Pi.zero_apply, sub_zero]

/-- One positive radius controls all polynomial energy budgets of the genuine chain. -/
theorem amplitudeId_polynomial_energy (F : AmplitudeIdFrame (ι := ι) (h := h)
    (D := D) (Nw := Nw) K g₁) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ ∀ n j x,
      ((⨆ t ∈ Icc F.a F.b, weightedFactorialNormSq
        (wordMomentSlot n (fun l => (F.letters l).slow) j) F.ϖ 0 r (F.κ j x) (F.u j x t)) +
       ∫⁻ t in Icc F.a F.b, weightedGradFactorialNormSq
        (wordMomentSlot n (fun l => (F.letters l).slow) j) F.ϖ 0 r (F.κ j x) (F.w j x t)) ≠ ⊤ := by
  classical
  obtain ⟨strain, ha, hjets⟩ := finite_drift_jet_envelope F.J F.η F.piece.hη F.v
    F.piece.hvs K.Cvj F.piece.hvj
  obtain ⟨r, hr, hrh, hsmall⟩ := exists_finite_drift_radius strain ha
  have hϖ : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
  have hs (p : Fin (Nw + 1) × ι) : ∀ᵐ y ∂volume, y ∉ tsupport (F.φ p.2) →
      planeValue (wordLevelDatum F.κ F.f p.1 p.2) y = 0 := by
    rcases p with ⟨l, z⟩
    by_cases hl : l = 0
    · subst l
      rw [wordLevelDatum_zero]
      filter_upwards [F.datum z] with y hy hout
      rw [hy]
      exact image_eq_zero_of_notMem_tsupport hout
    · have he : wordLevelDatum F.κ F.f l z = 0 := by simp only [wordLevelDatum, dite_eq_right hl]
      rw [he]
      exact (planeValue_zero_ae (E := h z) (F.κ l z)).mono (fun y hy _ => hy)
  refine ⟨r, hr, hrh, ?_⟩
  intro n j x
  exact wordChainFrom_compact_polynomial_energy F.piece.hD F.π F.piece.hπ F.letters
    F.J F.H F.a F.b F.ordered F.piece.hlet F.κ F.J F.cap (fun l z => F.cap l.succ z)
    F.X₀ (F.ϖ * F.ηg)
    (fun l z z' o k wd X y => F.piece.hmeas l z z' o _ (List.get_mem _ _) wd X y)
    F.v F.piece.hv F.piece.hvs strain r F.ϖ ha hr hϖ hrh hsmall hjets F.G F.piece.hGm
    F.t₀ F.Sw K.Cwt F.pkg.weights F.left F.right n
    (fun p => wordLevelDatum F.κ F.f p.1 p.2) (fun p => F.u p.1 p.2)
    (fun p => F.w p.1 p.2) F.solution (fun p => tsupport (F.φ p.2))
    (fun p => (F.compact p.2).2) hs j x

/-- A common radius gives uniform trace moments and integrated full-lift moments. -/
theorem amplitudeId_full_polynomial_budgets (F : AmplitudeIdFrame (ι := ι) (h := h)
    (D := D) (Nw := Nw) K g₁) :
    ∃ r : ℝ, 0 < r ∧ ∀ n j x,
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc F.a F.b,
        weightedFactorialNormSq n F.ϖ 0 r (F.κ j x) (F.u j x t) ≤ ENNReal.ofReal C) ∧
      (∫⁻ t in Icc F.a F.b,
        weightedFactorialNormSq n F.ϖ 0 r (F.κ j x + 1) (F.w j x t)) ≠ ⊤ := by
  obtain ⟨r, hr, hrh, he⟩ := amplitudeId_polynomial_energy F
  refine ⟨r, hr, ?_⟩
  intro n j x
  let E := (⨆ t ∈ Icc F.a F.b, weightedFactorialNormSq
      (wordMomentSlot n (fun l => (F.letters l).slow) j) F.ϖ 0 r (F.κ j x) (F.u j x t)) +
    ∫⁻ t in Icc F.a F.b, weightedGradFactorialNormSq
      (wordMomentSlot n (fun l => (F.letters l).slow) j) F.ϖ 0 r (F.κ j x) (F.w j x t)
  have hE : E ≠ ⊤ := he n j x
  have hb (t : ℝ) (ht : t ∈ Icc F.a F.b) :
      weightedFactorialNormSq n F.ϖ 0 r (F.κ j x) (F.u j x t) ≤ ENNReal.ofReal E.toReal := by
    rw [ENNReal.ofReal_toReal hE]
    apply (weightedFactorialNormSq_moment_mono
      (show n ≤ wordMomentSlot n (fun l => (F.letters l).slow) j from Nat.le_add_right _ _)
      F.ϖ 0 r (F.κ j x) (F.u j x t)).trans
    have hsup : weightedFactorialNormSq (wordMomentSlot n (fun l => (F.letters l).slow) j)
        F.ϖ 0 r (F.κ j x) (F.u j x t) ≤
        ⨆ s ∈ Icc F.a F.b, weightedFactorialNormSq (wordMomentSlot n (fun l => (F.letters l).slow) j)
          F.ϖ 0 r (F.κ j x) (F.u j x s) := le_iSup₂_of_le t ht le_rfl
    exact hsup.trans (le_add_right le_rfl)
  refine ⟨⟨E.toReal, ENNReal.toReal_nonneg, hb⟩, ?_⟩
  apply CycleJointProofs.weightedFactorialNormSq_lift_time_ne_top n F.ϖ 0 r F.a F.b hr
    (hrh.trans (by norm_num)) (F.u j x) (F.w j x) (F.solution.2.2.1 (j, x)) E.toReal hb
  apply ne_top_of_le_ne_top hE
  apply le_trans _ (le_add_left le_rfl)
  exact lintegral_mono (fun t => weightedGradFactorialNormSq_moment_mono
    (show n ≤ wordMomentSlot n (fun l => (F.letters l).slow) j from Nat.le_add_right _ _)
    F.ϖ 0 r (F.κ j x) (F.w j x t))

/-- The genuine chain has a finite weighted L2 value budget at every level and time. -/
theorem amplitudeId_weighted_value_finite (F : AmplitudeIdFrame (ι := ι) (h := h)
    (D := D) (Nw := Nw) K g₁) (j : Fin (Nw + 1)) (x : ι)
    (t : ℝ) (ht : t ∈ Icc F.a F.b) (n : ℕ) :
    (∫⁻ y, ENNReal.ofReal ((1 + F.ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) ^ n *
      ‖planeValue (F.u j x t) y‖ ^ 2)) < ⊤ := by
  obtain ⟨r, _, _, henergy⟩ := amplitudeId_polynomial_energy F
  have he := henergy n j x
  apply lt_of_le_of_lt (amplitudeId_weighted_value_le (F.u j x t) n F.ϖ r)
  apply lt_of_le_of_lt (weightedFactorialNormSq_moment_mono
    (show n ≤ wordMomentSlot n (fun l => (F.letters l).slow) j from Nat.le_add_right _ _)
    F.ϖ 0 r (F.κ j x) (F.u j x t))
  have hsup : weightedFactorialNormSq (wordMomentSlot n (fun l => (F.letters l).slow) j)
      F.ϖ 0 r (F.κ j x) (F.u j x t) ≤
      ⨆ s ∈ Icc F.a F.b, weightedFactorialNormSq (wordMomentSlot n (fun l => (F.letters l).slow) j)
        F.ϖ 0 r (F.κ j x) (F.u j x s) := le_iSup₂_of_le t ht le_rfl
  apply lt_of_le_of_lt hsup
  exact lt_of_le_of_lt (le_add_right le_rfl) (lt_top_iff_ne_top.mpr he)

/-- Closed moment ingredient, with no additional reserve or smallness premise. -/
theorem amplitudeIdMoments : AmplitudeIdMomentsStatement.{u, v} := by
  intro K g₁ ι _ h _ _ _ _ _ _ D Nw F j x t ht n β _
  apply amplitudeId_integrable_of_all_monomial_memLp
  intro γ
  apply amplitudeId_monomial_memLp_of_weighted _
    (planeJetOrder_memLp (Nat.zero_le _) (F.u j x t) (fun i => i.elim0)).aestronglyMeasurable F.ϖ
  · rw [F.piece.hϖ]
    exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
  · exact amplitudeId_weighted_value_finite F j x t ht

end AVRegularity.CycleWords.Assembly
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! The literal preceding word flux has a single native time curve retaining every moment. -/

universe u v
variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ} {K : ScalarConstants} {g₁ : ℝ}

/-- Every component flux has all its polynomial time-energy budgets, at one common radius. -/
theorem amplitudeId_flux_moments (F : AmplitudeIdFrame (ι := ι) (h := h)
    (D := D) (Nw := Nw) K g₁) :
    ∃ r : ℝ, 0 < r ∧ ∀ j x, ∃ V : ℝ → PlaneHk Set.univ (F.κ j x) (PiLp 2 (fun _ : Fin 2 => h x)),
      MemLp V 2 (volume.restrict (Icc F.a F.b)) ∧
      (∀ n, (∫⁻ t in Icc F.a F.b, weightedFactorialNormSq n F.ϖ 0 r (F.κ j x) (V t)) ≠ ⊤) ∧
      ∀ᵐ t ∂volume.restrict (Icc F.a F.b), planeValue (V t) =ᵐ[volume]
        fun y => wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ
          (fun p => F.w p.1 p.2 t) (j, x) t y := by
  classical
  obtain ⟨r, hr, _, he⟩ := amplitudeId_polynomial_energy F
  have hϖ : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
  have hgrad (n : ℕ) (j : Fin (Nw + 1)) (x : ι) :
      (∫⁻ t in Icc F.a F.b, weightedGradFactorialNormSq n F.ϖ 0 r (F.κ j x) (F.w j x t)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (he n j x)
    apply le_trans _ (le_add_left le_rfl)
    exact lintegral_mono (fun t => weightedGradFactorialNormSq_moment_mono
      (show n ≤ wordMomentSlot n (fun l => (F.letters l).slow) j from Nat.le_add_right _ _)
      F.ϖ 0 r (F.κ j x) (F.w j x t))
  refine ⟨r, hr, ?_⟩
  intro j
  refine Fin.cases ?_ (fun l => ?_) j
  · intro x
    let V : ℝ → PlaneHk Set.univ (F.κ 0 x) (PiLp 2 (fun _ : Fin 2 => h x)) := fun _ => 0
    have hV : MemLp V 2 (volume.restrict (Icc F.a F.b)) :=
      planeHk_zero_time_memLp (E := PiLp 2 (fun _ : Fin 2 => h x))
        (F.κ 0 x) (volume.restrict (Icc F.a F.b))
    refine ⟨V, hV, ?_, ?_⟩
    · intro n
      dsimp only [V]
      simp only [weightedFactorialNormSq_zero_carrier, lintegral_zero, ne_eq,
        ENNReal.zero_ne_top, not_false_eq_true]
    · exact Filter.Eventually.of_forall (fun t => (planeValue_zero_ae (E := PiLp 2 (fun _ : Fin 2 => h x))
        (F.κ 0 x)).mono (fun y hy => by
          change planeValue (0 : PlaneHk Set.univ (F.κ 0 x)
            (PiLp 2 (fun _ : Fin 2 => h x))) y = _
          dsimp only
          rw [hy, wordChainPreviousFlux_initial]))
  · intro x
    apply CycleJointProofs.planeForcing_exists_every_moment F.ϖ r 0 (volume.restrict (Icc F.a F.b))
    intro n
    obtain ⟨V, hV, hVe, hVr⟩ := exists_admissible_letter_flux_time F.π F.piece.hπ
      (F.letters l) F.a F.b F.J F.H (F.piece.hlet l)
      (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) (l.succ, x) (fun z => (l.castSucc, z)) x
      (F.cap l.succ x) (if (F.letters l).positive then 1 else 0) n F.X₀ (F.ϖ * F.ηg)
      (fun z o k wd X y => F.piece.hmeas l x z o _ (List.get_mem _ _) wd X y)
      F.ϖ hϖ r hr (fun z => F.w l.castSucc z) (fun z => F.solution.2.1 (l.castSucc, z))
      (fun z => hgrad (n + (F.letters l).slow) l.castSucc z)
    refine ⟨V, hV, hVe, ?_⟩
    filter_upwards [hVr] with t ht
    have hrval : planeValue (V t) =ᵐ[volume] planeJetReadoutOperator (F.κ l.succ x)
        (valueIndex2 (F.κ l.succ x)) (V t) := by
      rw [planeValue_eq_stored, planeJetReadoutOperator_apply]
      exact (univToPlane_ae _).symm
    apply hrval.trans
    filter_upwards [ht] with y hy
    rw [hy, wordChainPreviousFlux_succ]
    rfl

end AVRegularity.CycleWords.Assembly
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! The literal monomial derivatives and phase-weighted weak product used in the fibre equation. -/

/-- Monomial weights have derivatives of every order. -/
theorem amplitudeId_moment_contDiff (β : ℕ × ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (momentWeight β) := by
  unfold momentWeight
  fun_prop

/-- The literal gradient is the actual derivative of its monomial. -/
theorem amplitudeId_moment_fderiv (β : ℕ × ℕ) (y : Vec 2) (i : Fin 2) :
    fderiv ℝ (momentWeight β) y (basisVec i) = momentWeightGrad β y i := by
  have h₀ : DifferentiableAt ℝ (fun z : Vec 2 => z 0) y := by fun_prop
  have h₁ : DifferentiableAt ℝ (fun z : Vec 2 => z 1) y := by fun_prop
  have hp₀ : DifferentiableAt ℝ (fun z : Vec 2 => z 0 ^ β.1) y := by fun_prop
  have hp₁ : DifferentiableAt ℝ (fun z : Vec 2 => z 1 ^ β.2) y := by fun_prop
  unfold momentWeight
  rw [fderiv_fun_mul hp₀ hp₁, fderiv_fun_pow β.1 h₀, fderiv_fun_pow β.2 h₁]
  have hc (k : Fin 2) : fderiv ℝ (fun z : Vec 2 => z k) y = ContinuousLinearMap.proj k :=
    (ContinuousLinearMap.proj k : Vec 2 →L[ℝ] ℝ).hasFDerivAt.fderiv
  rw [hc 0, hc 1]
  fin_cases i <;> simp [momentWeightGrad, basisVec] <;> ring

/-- The contracted derivative of the literal gradient is the statement's metric Laplacian. -/
theorem amplitudeId_moment_laplacian (β : ℕ × ℕ)
    (G : Matrix (Fin 2) (Fin 2) ℝ) (y : Vec 2) :
    (∑ i : Fin 2, ∑ k : Fin 2, G i k *
      fderiv ℝ (fun z => momentWeightGrad β z i) y (basisVec k)) = momentWeightLap G β y := by
  have h₀ : (fun z => momentWeightGrad β z 0) =
      (fun z => (β.1 : ℝ) * momentWeight (β.1 - 1, β.2) z) := by
    funext z
    simp only [momentWeightGrad, Matrix.cons_val_zero, momentWeight]
    ring
  have h₁ : (fun z => momentWeightGrad β z 1) =
      (fun z => (β.2 : ℝ) * momentWeight (β.1, β.2 - 1) z) := by
    funext z
    simp only [momentWeightGrad, Matrix.cons_val_one, Matrix.cons_val_zero, momentWeight]
    ring
  simp only [Fin.sum_univ_two, h₀, h₁]
  rw [fderiv_const_mul ((amplitudeId_moment_contDiff (β.1 - 1, β.2)).differentiable (by simp)).differentiableAt,
    fderiv_const_mul ((amplitudeId_moment_contDiff (β.1, β.2 - 1)).differentiable (by simp)).differentiableAt]
  simp only [smul_apply, smul_eq_mul, amplitudeId_moment_fderiv, momentWeightGrad,
    Matrix.cons_val_zero, Matrix.cons_val_one, momentWeightLap]
  rcases β with ⟨m, n⟩
  cases m <;> cases n <;> simp [Nat.cast_add, Nat.succ_sub_succ_eq_sub] <;> ring_nf <;> simp

/-- The Fourier phase has all real derivatives. -/
theorem amplitudeId_phase_contDiff (θ : Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => Complex.exp (-(Complex.I * (vecDot θ y : ℂ)))) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (vecDot θ) := by unfold vecDot; fun_prop
  exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hd) |>.neg)

/-- The actual phase gradient has the radian shift used by the fibre coefficients. -/
theorem amplitudeId_phase_fderiv (θ y : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun z : Vec 2 => Complex.exp (-(Complex.I * (vecDot θ z : ℂ)))) y (basisVec i) =
      -(Complex.I * (θ i : ℂ)) * Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) := by
  let L : Vec 2 →L[ℝ] ℝ := ∑ k : Fin 2, θ k • ContinuousLinearMap.proj k
  have hL : (fun z => vecDot θ z) = L := by
    funext z
    simp only [L, vecDot, sum_apply, smul_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul]
  have hd := ((Complex.ofRealCLM.hasFDerivAt.comp y L.hasFDerivAt).const_mul Complex.I).neg.cexp
  simp only [Pi.neg_apply, Function.comp_apply] at hd
  have hLp (z : Vec 2) : vecDot θ z = L z := congrFun hL z
  simp_rw [hLp]
  change fderiv ℝ (fun z => Complex.exp (-(Complex.I * Complex.ofRealCLM (L z)))) y (basisVec i) = _
  rw [hd.fderiv]
  simp only [smul_apply, neg_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, L,
    smul_eq_mul, basisVec, Fin.sum_univ_two]
  fin_cases i <;> simp <;> ring

/-- The phase-weighted coordinate is a genuine smooth operator coefficient. -/
def amplitudeId_momentCoefficient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (θ : Vec 2) (β : ℕ × ℕ) (e : E) (y : Vec 2) : E →L[ℝ] ℂ :=
  (Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (momentWeight β y : ℂ)) •
    (Complex.ofRealCLM.comp (innerSL ℝ e))

/-- Smoothness of the coefficient includes the polynomial growth; no global bound is assumed. -/
theorem amplitudeId_momentCoefficient_contDiff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (θ : Vec 2) (β : ℕ × ℕ) (e : E) :
    ContDiff ℝ (⊤ : ℕ∞) (amplitudeId_momentCoefficient θ β e) := by
  exact ((amplitudeId_phase_contDiff θ).mul
    (Complex.ofRealCLM.contDiff.comp (amplitudeId_moment_contDiff β))).smul contDiff_const

/-- Differentiating the coefficient gives the monomial gradient and the phase shift. -/
theorem amplitudeId_momentCoefficient_fderiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (θ : Vec 2) (β : ℕ × ℕ) (e z : E) (y : Vec 2) (i : Fin 2) :
    fderiv ℝ (amplitudeId_momentCoefficient θ β e) y (basisVec i) z =
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        ((momentWeightGrad β y i * inner ℝ e z : ℝ) : ℂ) -
      Complex.I * (θ i : ℂ) * Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        ((momentWeight β y * inner ℝ e z : ℝ) : ℂ) := by
  have hc := (amplitudeId_momentCoefficient_contDiff θ β e).differentiable (by simp)
  have he := fderiv_clm_apply (hc y) (differentiableAt_const (c := z))
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add] at he
  have hfun : (fun x => amplitudeId_momentCoefficient θ β e x z) =
      (fun x => Complex.exp (-(Complex.I * (vecDot θ x : ℂ))) *
        ((momentWeight β x * inner ℝ e z : ℝ) : ℂ)) := by
    funext x
    simp only [amplitudeId_momentCoefficient, smul_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc]
  have hd : DifferentiableAt ℝ (fun x => ((momentWeight β x * inner ℝ e z : ℝ) : ℂ)) y := by
    exact (Complex.ofRealCLM.differentiableAt.comp y
      (((amplitudeId_moment_contDiff β).differentiable (by simp) y).mul_const _))
  have hm := Complex.ofRealCLM.hasFDerivAt.comp y
    (((amplitudeId_moment_contDiff β).differentiable (by simp) y).hasFDerivAt.mul_const (inner ℝ e z))
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at hm
  rw [hfun, fderiv_fun_mul ((amplitudeId_phase_contDiff θ).differentiable (by simp) y) hd,
    hm.fderiv] at he
  have hev := congrArg (fun A : Vec 2 →L[ℝ] ℂ => A (basisVec i)) he
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, ContinuousLinearMap.flip_apply, amplitudeId_moment_fderiv,
    amplitudeId_phase_fderiv] at hev
  rw [← hev]
  push_cast
  ring

/-- The first product jet is the covariant gradient of the moment-weighted value. -/
theorem amplitudeId_moment_jet_first {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (U : PlaneHk Set.univ 1 E) (θ : Vec 2) (β : ℕ × ℕ) (e : E) (y : Vec 2) (i : Fin 2) :
    multiplicationRawJet (amplitudeId_momentCoefficient θ β e) U.toFunction.jet
        ⟨⟨1, by decide⟩, fun _ => i⟩ y =
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        ((momentWeight β y * inner ℝ e (planeJetOrder U 1 (fun _ => i) y) +
          momentWeightGrad β y i * inner ℝ e (planeValue U y) : ℝ) : ℂ) -
        Complex.I * (θ i : ℂ) * Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
          ((momentWeight β y * inner ℝ e (planeValue U y) : ℝ) : ℂ) := by
  rw [CycleJointProofs.multiplicationRawJet_first, amplitudeId_momentCoefficient_fderiv]
  have hv : U.toFunction.jet (valueIndex2 1) y = planeValue U y := by
    rw [planeValue_eq_stored]
    rfl
  have hg : U.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y = planeJetOrder U 1 (fun _ => i) y := by
    rw [planeJetOrder_eq_stored le_rfl]
  rw [hv, hg]
  simp only [amplitudeId_momentCoefficient, smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_add,
    Complex.ofReal_mul]
  ring

/-- Applying the polynomial phase to an actual plane field preserves its weak derivative identities. -/
theorem amplitudeId_moment_weakJet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {k : ℕ} (U : PlaneHk Set.univ k E) (θ : Vec 2) (β : ℕ × ℕ) (e : E) :
    HasOrderedWeakJetOn Set.univ
      (multiplicationRawJet (amplitudeId_momentCoefficient θ β e) U.toFunction.jet) := by
  apply multiplicationRawJet_hasOrderedWeakJetOn
    ((amplitudeId_momentCoefficient_contDiff θ β e).of_le (by simp)) U.toFunction.hasWeakJet
  exact jet_scalar_locallyIntegrable U.toFunction.memL2

/-- Its order-zero jet is exactly the summand in the radian Bloch periodization. -/
theorem amplitudeId_moment_jet_value {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {k : ℕ}
    (U : PlaneHk Set.univ k E) (θ : Vec 2) (β : ℕ × ℕ) (e : E) (y : Vec 2) :
    multiplicationRawJet (amplitudeId_momentCoefficient θ β e) U.toFunction.jet
        (valueIndex2 k) y = Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
          ((momentWeight β y * inner ℝ e (planeValue U y) : ℝ) : ℂ) := by
  rw [multiplicationRawJet_value]
  have hv : U.toFunction.jet (valueIndex2 k) y = planeValue U y := by
    rw [planeValue_eq_stored]
    rfl
  rw [hv]
  simp only [amplitudeId_momentCoefficient, smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, Complex.ofRealCLM_apply,
    smul_eq_mul, Complex.ofReal_mul, mul_assoc]

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords.Assembly

/-! # The capped frame and the stage curves

A word piece (`IsWordPiece`) has descending slots `κ` with no cap. Its chain, truncated to the
capped slots `cappedWordSlots κ 0 d` (at most `J` by the reserve hypothesis of the word fibre facts
`WordFibreFactsStatement`), is again a word chain (`isPlaneChain_truncate`) with the same plane
values (`planeValue_truncate`). This gives the frame of the amplitude identification
`AmplitudeIdentificationStatement` (`b1wCappedFrame`).

A cell solution whose source and flux components are in `L²([a,b] × cell)` is a Hilbert curve
with the dual derivative of the word fibre facts (`cellSolution_to_Hilbert`). With
`AmplitudeIdFibresMeasStatement` this gives the stage curves of the word fibre facts, one per
`(level, component, vector, frequency, moment)`. -/

universe u v

section Chains

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {N : ℕ}

/-- Truncation keeps the plane value. -/
theorem planeValue_truncate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K L : ℕ} (hKL : K ≤ L)
    (U : PlaneHk Set.univ L E) : planeValue (truncatePlaneHk hKL U) = planeValue U :=
  planeJetOrder_truncate hKL (Nat.zero_le K) U _

/-- **A word chain truncated to smaller descending slots is a word chain.** -/
theorem isPlaneChain_truncate {D : ℕ} (hD : 2 ≤ D) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (letters : Fin N → CycleLetter ι h D) (X₀ : Vec 2) (δ a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (κ κ' : Fin (N + 1) → ι → ℕ) (hle : ∀ j x, κ' j x ≤ κ j x)
    (hc : IsWordSlots letters κ) (hc' : IsWordSlots letters κ')
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hs : IsPlaneChain (wordChainData G letters X₀ δ) κ a b v f (fun _ _ _ => 0) u w) :
    IsPlaneChain (wordChainData G letters X₀ δ) κ' a b v
      (fun x => truncatePlaneHk (hle 0 x) (f x)) (fun _ _ _ => 0)
      (fun j x t => truncatePlaneHk (hle j x) (u j x t))
      (fun j x t => truncatePlaneHk (Nat.succ_le_succ (hle j x)) (w j x t)) := by
  have ht := wordChainFrom_truncate hD G letters κ κ' hle hc hc' X₀ δ a b v (chainDatum κ f)
    (fun _ _ _ => 0) u w ((isPlaneChain_iff_from _ κ a b v f _ u w).1 hs)
  refine (isPlaneChain_iff_from _ κ' a b v _ _ _ _).2 (IsPlaneChainFrom.congr_data ht ?_ ?_)
  · funext j x
    by_cases hj : j = 0
    · subst hj
      simp [chainDatum]
    · simp [chainDatum, hj]
  · funext j x t
    exact map_zero _

end Chains

/-- **The capped frame of a word piece**: the frame of the amplitude identification at the slots
`cappedWordSlots κ 0 d`, with the truncated chain. -/
def b1wCappedFrame (K : ScalarConstants) (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D Nw : ℕ} (H J : ℕ) (π : ι → ℝ)
    (letters : Fin Nw → CycleLetter ι h D) (d : Fin Nw → ℕ)
    (hd : ∀ i, (letters i).order = d i)
    (η S ηg t₀ Sw ϖ a b : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (g : ℝ) (reg : BlockRegions) (pkg : CoreScalarPackage K η G v t₀ Sw ϖ reg)
    (piece : IsWordPiece K g₁ H J π letters η S ηg ϖ G v g reg a b)
    (ha : t₀ ≤ a) (hab : a ≤ b) (hb : b ≤ t₀ + Sw) (X₀ : Vec 2)
    (κ : Fin (Nw + 1) → ι → ℕ) (hκ : IsWordSlots letters κ)
    (hcap : ∀ j x, cappedWordSlots κ 0 d j x ≤ J)
    (φ : ∀ x, Vec 2 → h x) (hφ : ∀ x, StronglyMeasurable (φ x) ∧ HasCompactSupport (φ x))
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hdatum : ∀ x, planeValue (f x) =ᵐ[volume] φ x)
    (hsol : IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ a b v f (fun _ _ _ => 0) u w) :
    AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁ where
  H := H
  J := J
  π := π
  letters := letters
  η := η
  S := S
  ηg := ηg
  t₀ := t₀
  Sw := Sw
  ϖ := ϖ
  a := a
  b := b
  G := G
  v := v
  g := g
  reg := reg
  pkg := pkg
  piece := piece
  left := ha
  ordered := hab
  right := hb
  X₀ := X₀
  κ := cappedWordSlots κ 0 d
  slots := cappedWordSlots_isWordSlots piece.hlet hd hκ 0
  cap := hcap
  φ := φ
  compact := hφ
  f := fun x => truncatePlaneHk (cappedWordSlots_le_original κ 0 d 0 x) (f x)
  u := fun j x t => truncatePlaneHk (cappedWordSlots_le_original κ 0 d j x) (u j x t)
  w := fun j x t => truncatePlaneHk (Nat.succ_le_succ (cappedWordSlots_le_original κ 0 d j x))
    (w j x t)
  datum := fun x => by rw [planeValue_truncate]; exact hdatum x
  solution := isPlaneChain_truncate piece.hD G letters X₀ (ϖ * ηg) a b v κ
    (cappedWordSlots κ 0 d) (cappedWordSlots_le_original κ 0 d) hκ
    (cappedWordSlots_isWordSlots piece.hlet hd hκ 0) f u w hsol

end AVRegularity.CycleWords.Assembly
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! Literal moment Bloch sums are periodic L2 values at every time and every frequency. -/

/-- The radial weight is controlled by the same quadratic polynomial as the energy. -/
theorem amplitudeId_radial_weight_bound (ϖ : ℝ) (hϖ : 0 < ϖ) (y : Vec 2) :
    1 + ‖y‖ ≤ (2 + (ϖ ^ 2)⁻¹) * (1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) := by
  have hnorm : ‖y‖ ≤ (1 + (ϖ ^ 2)⁻¹) * (1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i
    · change |y 0| ≤ _
      exact amplitudeId_coordinate_weight_bound ϖ hϖ (y 0) (y 1)
    · change |y 1| ≤ _
      convert amplitudeId_coordinate_weight_bound ϖ hϖ (y 1) (y 0) using 1
      ring
  calc
    _ ≤ 1 + (1 + (ϖ ^ 2)⁻¹) * (1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) := add_le_add le_rfl hnorm
    _ ≤ (1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) +
        (1 + (ϖ ^ 2)⁻¹) * (1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) :=
      add_le_add (le_add_of_nonneg_right (by positivity)) le_rfl
    _ = _ := by ring

/-- Every ordinary moment has the fourth radial L2 moment needed for absolute periodization. -/
theorem amplitudeId_radial_monomial_memLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Vec 2 → E) (hu : AEStronglyMeasurable u volume) (ϖ : ℝ) (hϖ : 0 < ϖ)
    (h : ∀ n : ℕ, (∫⁻ y, ENNReal.ofReal
      ((1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) ^ n * ‖u y‖ ^ 2)) < ⊤)
    (β : ℕ × ℕ) :
    MemLp (fun y => (1 + ‖y‖) ^ 4 • ((y 0 ^ β.1 * y 1 ^ β.2) • u y)) 2 volume := by
  let n := β.1 + β.2
  let A := 1 + (ϖ ^ 2)⁻¹
  let B := 2 + (ϖ ^ 2)⁻¹
  let W := fun y : Vec 2 => 1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)
  have hw := amplitudeId_quadratic_memLp u hu ϖ (n + 4) (h (2 * (n + 4)))
  apply (hw.const_smul (B ^ 4 * A ^ n)).of_le
    ((by fun_prop : Continuous (fun y : Vec 2 => (1 + ‖y‖) ^ 4)).aestronglyMeasurable.smul
      ((by fun_prop : Continuous (fun y : Vec 2 => y 0 ^ β.1 * y 1 ^ β.2)).aestronglyMeasurable.smul hu))
  apply Filter.Eventually.of_forall
  intro y
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hW : 0 ≤ W y := by dsimp [W]; positivity
  have hx := amplitudeId_coordinate_weight_bound ϖ hϖ (y 0) (y 1)
  have hy : |y 1| ≤ A * W y := by
    convert amplitudeId_coordinate_weight_bound ϖ hϖ (y 1) (y 0) using 1
    ring
  have hm := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx β.1)
    (pow_le_pow_left₀ (abs_nonneg _) hy β.2) (by positivity) (by positivity)
  have hm' : |y 0| ^ β.1 * |y 1| ^ β.2 ≤ A ^ n * W y ^ n := by
    convert hm using 1
    dsimp only [n]
    rw [← pow_add, mul_pow]
  have hr := pow_le_pow_left₀ (by positivity) (amplitudeId_radial_weight_bound ϖ hϖ y) 4
  have hb := mul_le_mul hr hm' (by positivity) (by positivity)
  have hb' : (1 + ‖y‖) ^ 4 * (|y 0| ^ β.1 * |y 1| ^ β.2) ≤
      (B ^ 4 * A ^ n) * W y ^ (n + 4) := by
    convert hb using 1
    simp only [mul_pow, pow_add]
    ring
  change ‖(1 + ‖y‖) ^ 4 • ((y 0 ^ β.1 * y 1 ^ β.2) • u y)‖ ≤
    ‖(B ^ 4 * A ^ n) • ((W y) ^ (n + 4) • u y)‖
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 + ‖y‖) ^ 4),
    abs_mul, abs_pow, abs_of_nonneg hA, abs_of_nonneg hB, abs_of_nonneg hW]
  convert mul_le_mul_of_nonneg_right hb' (norm_nonneg (u y)) using 1 <;> ring

/-- Multiplication by the real-frequency complex phase preserves an L2 bound. -/
theorem amplitudeId_phase_memLp {μ : Measure (Vec 2)} (θ : Vec 2) {g : Vec 2 → ℝ}
    (hg : MemLp g 2 μ) :
    MemLp (fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (g y : ℂ)) 2 μ := by
  have hc : MemLp (fun y => (g y : ℂ)) 2 μ := hg.ofReal
  apply hc.of_le ((planePhase_continuous θ).aestronglyMeasurable.mul hc.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro y
  change ‖Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (g y : ℂ)‖ ≤ ‖(g y : ℂ)‖
  rw [norm_mul, norm_planePhase, one_mul]

end AVRegularity.CycleWords.Assembly
end
end
end
