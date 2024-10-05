/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Triangularizable linear endomorphisms

This file contains basic results relevant to the triangularizability of linear endomorphisms.

## Main definitions / results

 * `Module.End.exists_eigenvalue`: in finite dimensions, over an algebraically closed field, every
   linear endomorphism has an eigenvalue.
 * `Module.End.iSup_genEigenspace_eq_top`: in finite dimensions, over an algebraically
   closed field, the generalized eigenspaces of any linear endomorphism span the whole space.
 * `Module.End.iSup_genEigenspace_restrict_eq_top`: in finite dimensions, if the
   generalized eigenspaces of a linear endomorphism span the whole space then the same is true of
   its restriction to any invariant submodule.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2015]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## TODO

Define triangularizable endomorphisms (e.g., as existence of a maximal chain of invariant subspaces)
and prove that in finite dimensions over a field, this is equivalent to the property that the
generalized eigenspaces span the whole space.

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/

open Set Function Module Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
   {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Module.End

theorem exists_hasEigenvalue_of_iSup_genEigenspace_eq_top [Nontrivial M] {f : End R M}
    (hf : ⨆ μ, ⨆ k, f.genEigenspace μ k = ⊤) :
    ∃ μ, f.HasEigenvalue μ := by
  by_contra! contra
  suffices ∀ μ, ⨆ k, f.genEigenspace μ k = ⊥ by simp [this] at hf
  intro μ
  replace contra : ∀ k, f.genEigenspace μ k = ⊥ := fun k ↦ by
    have hk : ¬ f.HasGenEigenvalue μ k := fun hk ↦ contra μ (f.hasEigenvalue_of_hasGenEigenvalue hk)
    rwa [hasGenEigenvalue_iff, not_not] at hk
  simp [contra]

-- This is Lemma 5.21 of [axler2015], although we are no longer following that proof.
/-- In finite dimensions, over an algebraically closed field, every linear endomorphism has an
eigenvalue. -/
theorem exists_eigenvalue [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) :
    ∃ c : K, f.HasEigenvalue c := by
  simp_rw [hasEigenvalue_iff_mem_spectrum]
  exact spectrum.nonempty_of_isAlgClosed_of_finiteDimensional K f

noncomputable instance [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) :
    Inhabited f.Eigenvalues :=
  ⟨⟨f.exists_eigenvalue.choose, f.exists_eigenvalue.choose_spec⟩⟩

-- Lemma 8.21 of [axler2015]
/-- In finite dimensions, over an algebraically closed field, the generalized eigenspaces of any
linear endomorphism span the whole space. -/
theorem iSup_genEigenspace_eq_top [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ⨆ (μ : K) (k : ℕ), f.genEigenspace μ k = ⊤ := by
  -- We prove the claim by strong induction on the dimension of the vector space.
  induction' h_dim : finrank K V using Nat.strong_induction_on with n ih generalizing V
  cases' n with n
  -- If the vector space is 0-dimensional, the result is trivial.
  · rw [← top_le_iff]
    simp only [Submodule.finrank_eq_zero.1 (Eq.trans (finrank_top _ _) h_dim), bot_le]
  -- Otherwise the vector space is nontrivial.
  · haveI : Nontrivial V := finrank_pos_iff.1 (by rw [h_dim]; apply Nat.zero_lt_succ)
    -- Hence, `f` has an eigenvalue `μ₀`.
    obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, f.HasEigenvalue μ₀ := exists_eigenvalue f
    -- We define `ES` to be the generalized eigenspace
    let ES := f.genEigenspace μ₀ (finrank K V)
    -- and `ER` to be the generalized eigenrange.
    let ER := f.genEigenrange μ₀ (finrank K V)
    -- `f` maps `ER` into itself.
    have h_f_ER : ∀ x : V, x ∈ ER → f x ∈ ER := fun x hx =>
      map_genEigenrange_le (Submodule.mem_map_of_mem hx)
    -- Therefore, we can define the restriction `f'` of `f` to `ER`.
    let f' : End K ER := f.restrict h_f_ER
    -- The dimension of `ES` is positive
    have h_dim_ES_pos : 0 < finrank K ES := by
      dsimp only [ES]
      rw [h_dim]
      apply pos_finrank_genEigenspace_of_hasEigenvalue hμ₀ (Nat.zero_lt_succ n)
    -- and the dimensions of `ES` and `ER` add up to `finrank K V`.
    have h_dim_add : finrank K ER + finrank K ES = finrank K V := by
      dsimp only [ER, ES]
      rw [Module.End.genEigenspace_def, Module.End.genEigenrange_def]
      apply LinearMap.finrank_range_add_finrank_ker
    -- Therefore the dimension `ER` mus be smaller than `finrank K V`.
    have h_dim_ER : finrank K ER < n.succ := by linarith
    -- This allows us to apply the induction hypothesis on `ER`:
    have ih_ER : ⨆ (μ : K) (k : ℕ), f'.genEigenspace μ k = ⊤ :=
      ih (finrank K ER) h_dim_ER f' rfl
    -- The induction hypothesis gives us a statement about subspaces of `ER`. We can transfer this
    -- to a statement about subspaces of `V` via `Submodule.subtype`:
    have ih_ER' : ⨆ (μ : K) (k : ℕ), (f'.genEigenspace μ k).map ER.subtype = ER := by
      simp only [(Submodule.map_iSup _ _).symm, ih_ER, Submodule.map_subtype_top ER]
    -- Moreover, every generalized eigenspace of `f'` is contained in the corresponding generalized
    -- eigenspace of `f`.
    have hff' :
      ∀ μ k, (f'.genEigenspace μ k).map ER.subtype ≤ f.genEigenspace μ k := by
      intros
      rw [genEigenspace_restrict]
      apply Submodule.map_comap_le
    -- It follows that `ER` is contained in the span of all generalized eigenvectors.
    have hER : ER ≤ ⨆ (μ : K) (k : ℕ), f.genEigenspace μ k := by
      rw [← ih_ER']
      exact iSup₂_mono hff'
    -- `ES` is contained in this span by definition.
    have hES : ES ≤ ⨆ (μ : K) (k : ℕ), f.genEigenspace μ k :=
      le_trans (le_iSup (fun k => f.genEigenspace μ₀ k) (finrank K V))
        (le_iSup (fun μ : K => ⨆ k : ℕ, f.genEigenspace μ k) μ₀)
    -- Moreover, we know that `ER` and `ES` are disjoint.
    have h_disjoint : Disjoint ER ES := generalized_eigenvec_disjoint_range_ker f μ₀
    -- Since the dimensions of `ER` and `ES` add up to the dimension of `V`, it follows that the
    -- span of all generalized eigenvectors is all of `V`.
    show ⨆ (μ : K) (k : ℕ), f.genEigenspace μ k = ⊤
    rw [← top_le_iff, ← Submodule.eq_top_of_disjoint ER ES h_dim_add h_disjoint]
    apply sup_le hER hES

end Module.End

namespace Submodule

variable {p : Submodule K V} {f : Module.End K V}

theorem inf_iSup_genEigenspace [FiniteDimensional K V] (h : ∀ x ∈ p, f x ∈ p) :
    p ⊓ ⨆ μ, ⨆ k, f.genEigenspace μ k = ⨆ μ, ⨆ k, p ⊓ f.genEigenspace μ k := by
  simp_rw [← (f.genEigenspace _).mono.directed_le.inf_iSup_eq]
  refine le_antisymm (fun m hm ↦ ?_)
    (le_inf_iff.mpr ⟨iSup_le fun μ ↦ inf_le_left, iSup_mono fun μ ↦ inf_le_right⟩)
  classical
  obtain ⟨hm₀ : m ∈ p, hm₁ : m ∈ ⨆ μ, ⨆ k, f.genEigenspace μ k⟩ := hm
  obtain ⟨m, hm₂, rfl⟩ := (mem_iSup_iff_exists_finsupp _ _).mp hm₁
  suffices ∀ μ, (m μ : V) ∈ p by
    exact (mem_iSup_iff_exists_finsupp _ _).mpr ⟨m, fun μ ↦ mem_inf.mp ⟨this μ, hm₂ μ⟩, rfl⟩
  intro μ
  by_cases hμ : μ ∈ m.support; swap
  · simp only [Finsupp.not_mem_support_iff.mp hμ, p.zero_mem]
  have h_comm : ∀ (μ₁ μ₂ : K),
    Commute ((f - algebraMap K (End K V) μ₁) ^ finrank K V)
            ((f - algebraMap K (End K V) μ₂) ^ finrank K V) := fun μ₁ μ₂ ↦
    ((Commute.sub_right rfl <| Algebra.commute_algebraMap_right _ _).sub_left
      (Algebra.commute_algebraMap_left _ _)).pow_pow _ _
  let g : End K V := (m.support.erase μ).noncommProd _ fun μ₁ _ μ₂ _ _ ↦ h_comm μ₁ μ₂
  have hfg : Commute f g := Finset.noncommProd_commute _ _ _ _ fun μ' _ ↦
    (Commute.sub_right rfl <| Algebra.commute_algebraMap_right _ _).pow_right _
  have hg₀ : g (m.sum fun _μ mμ ↦ mμ) = g (m μ) := by
    suffices ∀ μ' ∈ m.support, g (m μ') = if μ' = μ then g (m μ) else 0 by
      rw [map_finsupp_sum, Finsupp.sum_congr (g2 := fun μ' _ ↦ if μ' = μ then g (m μ) else 0) this,
        Finsupp.sum_ite_eq', if_pos hμ]
    rintro μ' hμ'
    split_ifs with hμμ'
    · rw [hμμ']
    replace hm₂ : ((f - algebraMap K (End K V) μ') ^ finrank K V) (m μ') = 0 := by
      obtain ⟨k, hk⟩ := (mem_iSup_of_chain _ _).mp (hm₂ μ')
      simpa only [End.mem_genEigenspace] using
        Module.End.genEigenspace_le_genEigenspace_finrank _ _ k hk
    have : _ = g := (m.support.erase μ).noncommProd_erase_mul (Finset.mem_erase.mpr ⟨hμμ', hμ'⟩)
      (fun μ ↦ (f - algebraMap K (End K V) μ) ^ finrank K V) (fun μ₁ _ μ₂ _ _ ↦ h_comm μ₁ μ₂)
    rw [← this, LinearMap.mul_apply, hm₂, _root_.map_zero]
  have hg₁ : MapsTo g p p := Finset.noncommProd_induction _ _ _ (fun g' : End K V ↦ MapsTo g' p p)
      (fun f₁ f₂ ↦ MapsTo.comp) (mapsTo_id _) fun μ' _ ↦ by
    suffices MapsTo (f - algebraMap K (End K V) μ') p p by
      simp only [LinearMap.coe_pow]; exact this.iterate (finrank K V)
    intro x hx
    rw [LinearMap.sub_apply, algebraMap_end_apply]
    exact p.sub_mem (h _ hx) (smul_mem p μ' hx)
  have hg₂ : MapsTo g ↑(⨆ k, f.genEigenspace μ k) ↑(⨆ k, f.genEigenspace μ k) :=
    f.mapsTo_iSup_genEigenspace_of_comm hfg μ
  have hg₃ : InjOn g ↑(⨆ k, f.genEigenspace μ k) := by
    apply LinearMap.injOn_of_disjoint_ker (subset_refl _)
    have this := f.independent_genEigenspace
    simp_rw [f.iSup_genEigenspace_eq_genEigenspace_finrank] at this ⊢
    rw [LinearMap.ker_noncommProd_eq_of_supIndep_ker, ← Finset.sup_eq_iSup]
    · simpa only [End.genEigenspace_def] using
        Finset.supIndep_iff_disjoint_erase.mp (this.supIndep' m.support) μ hμ
    · simpa only [End.genEigenspace_def] using this.supIndep' (m.support.erase μ)
  have hg₄ : SurjOn g
      ↑(p ⊓ ⨆ k, f.genEigenspace μ k) ↑(p ⊓ ⨆ k, f.genEigenspace μ k) := by
    have : MapsTo g
        ↑(p ⊓ ⨆ k, f.genEigenspace μ k) ↑(p ⊓ ⨆ k, f.genEigenspace μ k) :=
      hg₁.inter_inter hg₂
    rw [← LinearMap.injOn_iff_surjOn this]
    exact hg₃.mono inter_subset_right
  specialize hm₂ μ
  obtain ⟨y, ⟨hy₀ : y ∈ p, hy₁ : y ∈ ⨆ k, f.genEigenspace μ k⟩, hy₂ : g y = g (m μ)⟩ :=
    hg₄ ⟨(hg₀ ▸ hg₁ hm₀), hg₂ hm₂⟩
  rwa [← hg₃ hy₁ hm₂ hy₂]

theorem eq_iSup_inf_genEigenspace [FiniteDimensional K V]
    (h : ∀ x ∈ p, f x ∈ p) (h' : ⨆ μ, ⨆ k, f.genEigenspace μ k = ⊤) :
    p = ⨆ μ, ⨆ k, p ⊓ f.genEigenspace μ k := by
  rw [← inf_iSup_genEigenspace h, h', inf_top_eq]

end Submodule

/-- In finite dimensions, if the generalized eigenspaces of a linear endomorphism span the whole
space then the same is true of its restriction to any invariant submodule. -/
theorem Module.End.iSup_genEigenspace_restrict_eq_top
    {p : Submodule K V} {f : Module.End K V} [FiniteDimensional K V]
    (h : ∀ x ∈ p, f x ∈ p) (h' : ⨆ μ, ⨆ k, f.genEigenspace μ k = ⊤) :
    ⨆ μ, ⨆ k, Module.End.genEigenspace (LinearMap.restrict f h) μ k = ⊤ := by
  have := congr_arg (Submodule.comap p.subtype) (Submodule.eq_iSup_inf_genEigenspace h h')
  have h_inj : Function.Injective p.subtype := Subtype.coe_injective
  simp_rw [Submodule.inf_genEigenspace f p h, Submodule.comap_subtype_self,
    ← Submodule.map_iSup, Submodule.comap_map_eq_of_injective h_inj] at this
  exact this.symm

/-- Given a family of endomorphisms `i ↦ f i` which are compatible in the sense that every maximal
generalised eigenspace of `f i` is invariant wrt `f j`, if each `f i` is triangularizable, the
family is simultaneously triangularizable. -/
lemma Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo
    {ι : Type*} [FiniteDimensional K V]
    (f : ι → End K V)
    (h : ∀ i j φ, MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ))
    (h' : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) :
    ⨆ χ : ι → K, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by
  generalize h_dim : finrank K V = n
  induction n using Nat.strongRecOn generalizing V with | ind n ih => ?_
  obtain this | ⟨i : ι, hy : ¬ ∃ φ, (f i).maxGenEigenspace φ = ⊤⟩ :=
    forall_or_exists_not (fun j : ι ↦ ∃ φ : K, (f j).maxGenEigenspace φ = ⊤)
  · choose χ hχ using this
    replace hχ : ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by simpa
    simp_rw [eq_top_iff] at hχ ⊢
    exact le_trans hχ <| le_iSup (fun χ : ι → K ↦ ⨅ i, (f i).maxGenEigenspace (χ i)) χ
  · replace hy : ∀ φ, finrank K ((f i).maxGenEigenspace φ) < n := fun φ ↦ by
      simp_rw [not_exists, ← lt_top_iff_ne_top] at hy; exact h_dim ▸ Submodule.finrank_lt (hy φ)
    have hi (j : ι) (φ : K) :
        MapsTo (f j) ((f i).maxGenEigenspace φ) ((f i).maxGenEigenspace φ) := by
      exact h j i φ
    replace ih (φ : K) :
        ⨆ χ : ι → K, ⨅ j, maxGenEigenspace ((f j).restrict (hi j φ)) (χ j) = ⊤ := by
      apply ih _ (hy φ)
      · intro j k μ
        exact mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo (f j) (f k) _ _ (h j k μ)
      · exact fun j ↦ Module.End.iSup_genEigenspace_restrict_eq_top _ (h' j)
      · rfl
    replace ih (φ : K) :
        ⨆ (χ : ι → K) (_ : χ i = φ), ⨅ j, maxGenEigenspace ((f j).restrict (hi j φ)) (χ j) = ⊤ := by
      suffices ∀ χ : ι → K, χ i ≠ φ → ⨅ j, maxGenEigenspace ((f j).restrict (hi j φ)) (χ j) = ⊥ by
        specialize ih φ; rw [iSup_split, biSup_congr this] at ih; simpa using ih
      intro χ hχ
      rw [eq_bot_iff, ← ((f i).maxGenEigenspace φ).ker_subtype, LinearMap.ker,
        ← Submodule.map_le_iff_le_comap, ← Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo,
        ← disjoint_iff_inf_le]
      exact ((f i).disjoint_iSup_genEigenspace hχ.symm).mono_right (iInf_le _ i)
    replace ih (φ : K) :
        ⨆ (χ : ι → K) (_ : χ i = φ), ⨅ j, maxGenEigenspace (f j) (χ j) =
        maxGenEigenspace (f i) φ := by
      have (χ : ι → K) (hχ : χ i = φ) : ⨅ j, maxGenEigenspace (f j) (χ j) =
          (⨅ j, maxGenEigenspace ((f j).restrict (hi j φ)) (χ j)).map
            ((f i).maxGenEigenspace φ).subtype := by
        rw [← hχ, iInf_maxGenEigenspace_restrict_map_subtype_eq]
      simp_rw [biSup_congr this, ← Submodule.map_iSup, ih, Submodule.map_top,
        Submodule.range_subtype]
    simpa only [← ih, iSup_comm (ι := K), iSup_iSup_eq_right] using h' i
