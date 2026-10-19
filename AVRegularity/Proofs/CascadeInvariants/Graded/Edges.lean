-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.CascadeInvariants.CopyDirNorm

/-! **Ledger: the graded source edges.** The quantitative form of `edgeURep_of_generated`. The
context of the graded calculus over the certified old coefficients (`oldCtx`, for a certificate
`G.OldCert 𝒮o μo Lo Co`) has the leaf map `oldLeaf`, the inner rate `3π b` and the fast-weight
budget `Lo`. The lifted source edge of the
step `u → u+1` of a path of the old stage is the restriction to real phases of the wrapped
certified coefficient of its identity, a certified leaf: its structural norm is the weighted sum of
its certified profile, at most the ledger entry `θ_old`, whenever the reserve is at most that of
the target of the step (`μo`) and the fast weight at most `Lo`. So the edge aggregates have the sizes
`pathTheta` (the sum of the ledger entries of the identity of the step over its orders, words and
components), with no reserve and no fast weight. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal

namespace AVRegularity.Providers.CascadeInvariants

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

/-- The expression is a sum node. -/
def isAddNode : {s : GenSort} → {i : ℕ} → {p : ℤ} → Gen s i p → Bool
  | _, _, _, .add _ _ => true
  | _, _, _, _ => false

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {𝒮o : SeedExports} {μo : Comp → ℝ} {Lo : ℕ} {Co : ℝ}
  {G : GenStage D hr Dm b j₀}

/-- Only sum nodes are leaves of the old-coefficient leaf map. -/
theorem oldLeaf_eq_none_of_not_add (hcert : G.OldCert 𝒮o μo Lo Co) {s : GenSort} {i : ℕ}
    {p : ℤ} (e : Gen s i p) (he : isAddNode e = false) : oldLeaf hcert e = none := by
  classical
  simp only [oldLeaf]
  split_ifs with h
  · obtain ⟨x, hx⟩ := h
    have h1 := congrArg
      (fun σ : Σ (s : GenSort) (i : ℕ) (p : ℤ), Gen s i p => isAddNode σ.2.2.2) hx
    have h2 : isAddNode (oldWrap hcert x) = true := rfl
    have h3 : isAddNode (oldWrap hcert x) = isAddNode e := h1
    rw [h2, he] at h3
    cases h3
  · rfl

/-- The wrapped certified expression of an old coefficient is scheduled, from the seed, and
denotes the certified function. -/
theorem oldWrap_spec (hcert : G.OldCert 𝒮o μo Lo Co) (x : OldIdx G) :
    Gen.IsScheduled D (oldWrap hcert x) ∧ Gen.FromSeed 𝒮o (oldWrap hcert x) ∧
      ∃ f : GenSort.Sem .ctx, Gen.Denotes D b j₀ (oldWrap hcert x) f ∧
        ∀ t ch z, f t ch z = oldFun hcert x t ch z := by
  obtain ⟨hs, hf, hden⟩ := oldExpr_spec hcert x
  refine ⟨.add (.mul (.timeConst 1) hs) (.mul (.timeConst 0) (.timeConst _)),
    .add (.mul (.time _) hf) (.mul (.time _) (.time _)), _,
    .add (.mul (.time _) hden) (.mul (.time _) (.time _)), fun t ch z => ?_⟩
  show TimeLetter.eval D (.const 1) t * _ + TimeLetter.eval D (.const 0) t * _ = _
  simp [TimeLetter.eval]

/-- **The context of the graded calculus over the certified old coefficients.** -/
def oldCtx (hcert : G.OldCert 𝒮o μo Lo Co) (κ : MajConsts) (Δ μ₀ : ℝ) (S Kg Kd : ℝ≥0) :
    GCtx where
  κ := κ
  Δ := Δ
  a₀ := 3 * Real.pi * b
  leaf := oldLeaf hcert
  μ₀ := μ₀
  L₀ := Lo
  T := Set.univ
  S := S
  Kg := Kg
  Kd := Kd

theorem oldCtx_ok (hcert : G.OldCert 𝒮o μo Lo Co) (κ : MajConsts) {Δ μ₀ : ℝ} (hΔ : 0 ≤ Δ)
    (hμ : μ₀ ≤ 2) {S Kg Kd : ℝ≥0}
    (hKg : ∀ L, L ≤ Lo → geoW κ (3 * Real.pi * b) L ≤ Kg)
    (hKd : ∀ (k : Fin 2) (L : ℕ), L ≤ Lo → wsum (3 * Real.pi * b) L (κ.drift k) ≤ Kd) :
    (oldCtx hcert κ Δ μ₀ S Kg Kd).Ok where
  hΔ := hΔ
  hμ := hμ
  hleaf := fun _ _ _ e hs => oldLeaf_eq_none_of_ne_ctx hcert e hs
  hgeo := fun _ _ _ => oldLeaf_eq_none_of_not_add hcert _ rfl
  hKg := hKg
  hKd := hKd
  hT := fun _ => trivial

/-- The size of an old identity as a source edge: the sum of its certified ledger entries over
its orders, words and components. -/
def edgeTheta (hcert : G.OldCert 𝒮o μo Lo Co) (v u : CompIn G.comps) (γ : G.fam.Γ v u) : ℝ≥0 :=
  ∑ d ∈ Finset.Icc 2 (G.fam.identity v u γ).maxOrder, ∑ α : DerivativeWord2 (d - 1),
    ∑ c : Fin 2, Real.toNNReal (oldTheta hcert v u γ d α c)

theorem toNNReal_oldTheta_le_edgeTheta (hcert : G.OldCert 𝒮o μo Lo Co) (v u : CompIn G.comps)
    (γ : G.fam.Γ v u) {d : ℕ} (hd2 : 2 ≤ d) (hd : d ≤ (G.fam.identity v u γ).maxOrder)
    (α : DerivativeWord2 (d - 1)) (c : Fin 2) :
    Real.toNNReal (oldTheta hcert v u γ d α c) ≤ edgeTheta hcert v u γ := by
  unfold edgeTheta
  have h1 : Real.toNNReal (oldTheta hcert v u γ d α c) ≤
      ∑ c' : Fin 2, Real.toNNReal (oldTheta hcert v u γ d α c') :=
    Finset.single_le_sum (f := fun c' => Real.toNNReal (oldTheta hcert v u γ d α c'))
      (fun _ _ => zero_le) (Finset.mem_univ c)
  have h2 : ∑ c' : Fin 2, Real.toNNReal (oldTheta hcert v u γ d α c') ≤
      ∑ α' : DerivativeWord2 (d - 1), ∑ c' : Fin 2,
        Real.toNNReal (oldTheta hcert v u γ d α' c') :=
    Finset.single_le_sum (f := fun α' => ∑ c' : Fin 2,
      Real.toNNReal (oldTheta hcert v u γ d α' c')) (fun _ _ => zero_le) (Finset.mem_univ α)
  have h3 := Finset.single_le_sum (f := fun d' => ∑ α' : DerivativeWord2 (d' - 1),
      ∑ c' : Fin 2, Real.toNNReal (oldTheta hcert v u γ d' α' c')) (fun _ _ => zero_le)
      (Finset.mem_Icc.mpr ⟨hd2, hd⟩)
  exact h1.trans (h2.trans h3)

/-- The sizes of the source edges of a path of the old stage. -/
def pathTheta (hcert : G.OldCert 𝒮o μo Lo Co) {h : ℕ} (π : StagePath G h)
    (v u : Fin (h + 1)) : ℝ≥0 :=
  if hvu : (v : ℕ) = u + 1 ∧ (u : ℕ) < h then
    edgeTheta hcert (π.step ⟨u, hvu.2⟩).1 (π.step ⟨u, hvu.2⟩).2.1 (π.step ⟨u, hvu.2⟩).2.2
  else 0

/-- **The lifted source edges of a certified, slotwise transverse stage are graded**, with the
sizes `pathTheta`, no reserve and no fast weight. -/
theorem edgeURepP_of_certified (hb : 0 ≤ b) (hεn : ∀ k, 0 ≤ D.eps k)
    (hcert : G.OldCert 𝒮o μo Lo Co) (hT : G.IsSlotTransverse) {h : ℕ} (π : StagePath G h)
    (p : OddSlot) {m : ℕ} {k : ℤ} (hm : G.level = m) (hk : p.1 = k) {ρ : ℝ}
    (hε : D.eps (m - 1) ≠ 0) (𝒜 : Set RealChain) (U : RealChain → Set (Vec 2)) (t₀ t₁ : ℝ)
    (hA𝒜 : ∀ A ∈ 𝒜, IsAdmissibleChain D b j₀ m k A)
    (hU : ∀ A ∈ 𝒜, ∀ Y ∈ U A, IsAdmissibleChain D b j₀ m k (A.recenter D (ρ • Y)))
    (ht : ∀ τ ∈ Set.Icc t₀ t₁, D.cellScaleSq m * τ ∈ ocPulseWindow D.α D.q D.Λ m k)
    (κ : MajConsts) {Δ μ₀ : ℝ} {S Kg Kd : ℝ≥0} (hXok : (oldCtx hcert κ Δ μ₀ S Kg Kd).Ok)
    (hμ : ∀ j : Fin h, μ₀ ≤ μo (π.step j).1.1)
    (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1)) (κ' : Fin 2) :
    (liftEnv D b j₀ 𝒮o m k ρ 𝒜 U t₀ t₁).IsURepP (oldCtx hcert κ Δ μ₀ S Kg Kd)
      (fun l Y z => (((familyLiftData D m k l.1 ρ (pathEdgesAt G π p l.1)).edge v u d).map
        fun γ => γ.map 1 * γ.coeff α l.2 Y z κ').sum) 0 0 (pathTheta hcert π v u) := by
  subst hm
  subst hk
  by_cases hvu : (v : ℕ) = u + 1 ∧ (u : ℕ) < h
  swap
  · refine ((UEnv.isURepP_zero hXok _ 0 0).mono hXok le_rfl le_rfl zero_le).congr
      fun l hl Y _ z => ?_
    by_cases hA : IsAdmissibleChain D b j₀ G.level p.1 l.1 <;>
      simp [familyLiftData, liftEdges, pathEdgesAt, pathEdges, hvu, hA]
  by_cases hd : d.1 ≤ (G.fam.identity _ _ (π.step ⟨u, hvu.2⟩).2.2).maxOrder
  swap
  · refine ((UEnv.isURepP_zero hXok _ 0 0).mono hXok le_rfl le_rfl zero_le).congr
      fun l hl Y _ z => ?_
    by_cases hA : IsAdmissibleChain D b j₀ G.level p.1 l.1 <;>
      simp [familyLiftData, liftEdges, pathEdgesAt, pathEdges, hvu, hd, hA]
  set x : OldIdx G := ⟨(π.step ⟨u, hvu.2⟩).1, (π.step ⟨u, hvu.2⟩).2.1, (π.step ⟨u, hvu.2⟩).2.2,
    d.1, α, κ', p⟩ with hx
  obtain ⟨hs, hf, f, hden, hval⟩ := oldWrap_spec hcert x
  have hagg : ∀ (l : RealChain × ℝ)
      (hl : l ∈ (liftEnv D b j₀ 𝒮o G.level p.1 ρ 𝒜 U t₀ t₁).W), ∀ Y z,
      ((((familyLiftData D G.level p.1 l.1 ρ (pathEdgesAt G π p l.1)).edge v u d).map
        fun γ => γ.map 1 * γ.coeff α l.2 Y z κ').sum) =
      G.fam.flux p ⟨l.1, hA𝒜 l.1 hl.1⟩ _ _ (π.step ⟨u, hvu.2⟩).2.2 d.1 α
        (D.cellScaleSq G.level * l.2) ((ρ / D.eps (G.level - 1)) • Y) z κ' := by
    intro l hl Y z
    simp [familyLiftData, liftEdges, pathEdgesAt, pathEdges, hvu, hd, hA𝒜 l.1 hl.1]
  refine ⟨Gen.restrict (oldWrap hcert x), UEnv.urep_restrict hs hf hden ?_ ?_,
    Or.inr (solvedFree_oldWrap hcert x), fun t _ mres L hmres hL => ?_⟩
  · intro l hl Y hY z
    rw [hagg l hl Y z, oldFun_flux hcert x ⟨l.1, hA𝒜 l.1 hl.1⟩ _ (ht l.2 hl.2) _ z,
      smul_smul, mul_div_cancel₀ _ hε]
    have hadm : IsAdmissibleChain D b j₀ G.level x.p.1 (l.1.recenter D (ρ • Y)) :=
      hU l.1 hl.1 Y hY
    simp only [hadm, ↓reduceIte]
    exact (hval _ _ _).symm
  · intro l hl Y hY z s
    rw [hagg l hl Y _, hagg l hl Y z]
    exact congrFun (hT p ⟨l.1, hA𝒜 l.1 hl.1⟩ _ _ (π.step ⟨u, hvu.2⟩).2.2 d.1 α _
      (ht l.2 hl.2) _ z s) κ'
  · show genNorm D κ Δ (3 * Real.pi * b) (oldLeaf hcert) (Gen.restrict (oldWrap hcert x))
      (3 * Real.pi * b) mres L t ≤ _
    rw [genNorm_restrict_eq _ _ _ _ _ (oldLeaf_eq_none_of_ne_ctx hcert _ GCtx.cell_ne_ctx),
      genNorm_oldWrap_eq]
    have hmr : mres ≤ μo x.v.1 := by
      have h1 : mres + ((0 : ℕ) : ℝ) * Δ ≤ μ₀ := hmres
      have h2 := hμ ⟨u, hvu.2⟩
      simp only [Nat.cast_zero, zero_mul, add_zero] at h1
      exact h1.trans h2
    have hLs : L ≤ Lo := by
      have : L + 0 ≤ Lo := hL
      omega
    refine (wsum_oldProfile_le hcert hb hεn x hmr le_rfl hLs).trans ?_
    have hd2 := (Finset.mem_Icc.mp d.2).1
    have := toNNReal_oldTheta_le_edgeTheta hcert _ _ (π.step ⟨u, hvu.2⟩).2.2 hd2 hd α κ'
    simp only [pathTheta, hvu, and_self, ↓reduceDIte]
    exact ENNReal.coe_le_coe.mpr this

end AVRegularity.Providers.CascadeInvariants
