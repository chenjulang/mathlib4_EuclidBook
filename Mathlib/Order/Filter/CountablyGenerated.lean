/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Data.Set.Countable
import Mathlib.Order.Filter.Bases

open Set

namespace Filter

variable {α β γ ι : Type*} {ι' : Sort*}

/-- `IsCountablyGenerated f` means `f = generate s` for some countable `s`. -/
class IsCountablyGenerated (f : Filter α) : Prop where
  /-- There exists a countable set that generates the filter. -/
  out : ∃ s : Set (Set α), s.Countable ∧ f = generate s

/-- `IsCountableBasis p s` means the image of `s` bounded by `p` is a countable filter basis. -/
structure IsCountableBasis (p : ι → Prop) (s : ι → Set α) extends IsBasis p s : Prop where
  /-- The set of `i` that satisfy the predicate `p` is countable. -/
  countable : (setOf p).Countable

/-- We say that a filter `l` has a countable basis `s : ι → Set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`, and the set
defined by `p` is countable. -/
structure HasCountableBasis (l : Filter α) (p : ι → Prop) (s : ι → Set α)
    extends HasBasis l p s : Prop where
  /-- The set of `i` that satisfy the predicate `p` is countable. -/
  countable : (setOf p).Countable

/-- A countable filter basis `B` on a type `α` is a nonempty countable collection of sets of `α`
such that the intersection of two elements of this collection contains some element
of the collection. -/
structure CountableFilterBasis (α : Type*) extends FilterBasis α where
  /-- The set of sets of the filter basis is countable. -/
  countable : sets.Countable

-- For illustration purposes, the countable filter basis defining `(atTop : Filter ℕ)`
instance Nat.inhabitedCountableFilterBasis : Inhabited (CountableFilterBasis ℕ) :=
  ⟨⟨default, countable_range fun n => Ici n⟩⟩

theorem HasCountableBasis.isCountablyGenerated {f : Filter α} {p : ι → Prop} {s : ι → Set α}
    (h : f.HasCountableBasis p s) : f.IsCountablyGenerated :=
  ⟨⟨{ t | ∃ i, p i ∧ s i = t }, h.countable.image s, h.toHasBasis.eq_generate⟩⟩

theorem HasBasis.isCountablyGenerated [Countable ι] {f : Filter α} {p : ι → Prop} {s : ι → Set α}
    (h : f.HasBasis p s) : f.IsCountablyGenerated :=
  HasCountableBasis.isCountablyGenerated ⟨h, to_countable _⟩

theorem antitone_seq_of_seq (s : ℕ → Set α) :
    ∃ t : ℕ → Set α, Antitone t ∧ ⨅ i, 𝓟 (s i) = ⨅ i, 𝓟 (t i) := by
  use fun n => ⋂ m ≤ n, s m; constructor
  · exact fun i j hij => biInter_mono (Iic_subset_Iic.2 hij) fun n _ => Subset.rfl
  apply le_antisymm <;> rw [le_iInf_iff] <;> intro i
  · rw [le_principal_iff]
    refine (biInter_mem (finite_le_nat _)).2 fun j _ => ?_
    exact mem_iInf_of_mem j (mem_principal_self _)
  · refine iInf_le_of_le i (principal_mono.2 <| iInter₂_subset i ?_)
    rfl

theorem countable_biInf_eq_iInf_seq [CompleteLattice α] {B : Set ι} (Bcbl : B.Countable)
    (Bne : B.Nonempty) (f : ι → α) : ∃ x : ℕ → ι, ⨅ t ∈ B, f t = ⨅ i, f (x i) :=
  let ⟨g, hg⟩ := Bcbl.exists_eq_range Bne
  ⟨g, hg.symm ▸ iInf_range⟩

theorem countable_biInf_eq_iInf_seq' [CompleteLattice α] {B : Set ι} (Bcbl : B.Countable)
    (f : ι → α) {i₀ : ι} (h : f i₀ = ⊤) : ∃ x : ℕ → ι, ⨅ t ∈ B, f t = ⨅ i, f (x i) := by
  rcases B.eq_empty_or_nonempty with hB | Bnonempty
  · rw [hB, iInf_emptyset]
    use fun _ => i₀
    simp [h]
  · exact countable_biInf_eq_iInf_seq Bcbl Bnonempty f

theorem countable_biInf_principal_eq_seq_iInf {B : Set (Set α)} (Bcbl : B.Countable) :
    ∃ x : ℕ → Set α, ⨅ t ∈ B, 𝓟 t = ⨅ i, 𝓟 (x i) :=
  countable_biInf_eq_iInf_seq' Bcbl 𝓟 principal_univ

section IsCountablyGenerated

protected theorem HasAntitoneBasis.mem_iff [Preorder ι] {l : Filter α} {s : ι → Set α}
    (hs : l.HasAntitoneBasis s) {t : Set α} : t ∈ l ↔ ∃ i, s i ⊆ t :=
  hs.toHasBasis.mem_iff.trans <| by simp only [exists_prop, true_and]

protected theorem HasAntitoneBasis.mem [Preorder ι] {l : Filter α} {s : ι → Set α}
    (hs : l.HasAntitoneBasis s) (i : ι) : s i ∈ l :=
  hs.toHasBasis.mem_of_mem trivial

theorem HasAntitoneBasis.hasBasis_ge [Preorder ι] [IsDirected ι (· ≤ ·)] {l : Filter α}
    {s : ι → Set α} (hs : l.HasAntitoneBasis s) (i : ι) : l.HasBasis (fun j => i ≤ j) s :=
  hs.1.to_hasBasis (fun j _ => (exists_ge_ge i j).imp fun _k hk => ⟨hk.1, hs.2 hk.2⟩) fun j _ =>
    ⟨j, trivial, Subset.rfl⟩

/-- If `f` is countably generated and `f.HasBasis p s`, then `f` admits a decreasing basis
enumerated by natural numbers such that all sets have the form `s i`. More precisely, there is a
sequence `i n` such that `p (i n)` for all `n` and `s (i n)` is a decreasing sequence of sets which
forms a basis of `f`-/
theorem HasBasis.exists_antitone_subbasis {f : Filter α} [h : f.IsCountablyGenerated]
    {p : ι' → Prop} {s : ι' → Set α} (hs : f.HasBasis p s) :
    ∃ x : ℕ → ι', (∀ i, p (x i)) ∧ f.HasAntitoneBasis fun i => s (x i) := by
  obtain ⟨x', hx'⟩ : ∃ x : ℕ → Set α, f = ⨅ i, 𝓟 (x i) := by
    rcases h with ⟨s, hsc, rfl⟩
    rw [generate_eq_biInf]
    exact countable_biInf_principal_eq_seq_iInf hsc
  have : ∀ i, x' i ∈ f := fun i => hx'.symm ▸ (iInf_le (fun i => 𝓟 (x' i)) i) (mem_principal_self _)
  let x : ℕ → { i : ι' // p i } := fun n =>
    Nat.recOn n (hs.index _ <| this 0) fun n xn =>
      hs.index _ <| inter_mem (this <| n + 1) (hs.mem_of_mem xn.2)
  have x_anti : Antitone fun i => s (x i).1 :=
    antitone_nat_of_succ_le fun i => (hs.set_index_subset _).trans inter_subset_right
  have x_subset : ∀ i, s (x i).1 ⊆ x' i := by
    rintro (_ | i)
    exacts [hs.set_index_subset _, (hs.set_index_subset _).trans inter_subset_left]
  refine ⟨fun i => (x i).1, fun i => (x i).2, ?_⟩
  have : (⨅ i, 𝓟 (s (x i).1)).HasAntitoneBasis fun i => s (x i).1 := .iInf_principal x_anti
  convert this
  exact
    le_antisymm (le_iInf fun i => le_principal_iff.2 <| by cases i <;> apply hs.set_index_mem)
      (hx'.symm ▸
        le_iInf fun i => le_principal_iff.2 <| this.1.mem_iff.2 ⟨i, trivial, x_subset i⟩)

/-- A countably generated filter admits a basis formed by an antitone sequence of sets. -/
theorem exists_antitone_basis (f : Filter α) [f.IsCountablyGenerated] :
    ∃ x : ℕ → Set α, f.HasAntitoneBasis x :=
  let ⟨x, _, hx⟩ := f.basis_sets.exists_antitone_subbasis
  ⟨x, hx⟩

theorem exists_antitone_seq (f : Filter α) [f.IsCountablyGenerated] :
    ∃ x : ℕ → Set α, Antitone x ∧ ∀ {s}, s ∈ f ↔ ∃ i, x i ⊆ s :=
  let ⟨x, hx⟩ := f.exists_antitone_basis
  ⟨x, hx.antitone, by simp [hx.1.mem_iff]⟩

instance Inf.isCountablyGenerated (f g : Filter α) [IsCountablyGenerated f]
    [IsCountablyGenerated g] : IsCountablyGenerated (f ⊓ g) := by
  rcases f.exists_antitone_basis with ⟨s, hs⟩
  rcases g.exists_antitone_basis with ⟨t, ht⟩
  exact HasCountableBasis.isCountablyGenerated ⟨hs.1.inf ht.1, Set.to_countable _⟩

instance map.isCountablyGenerated (l : Filter α) [l.IsCountablyGenerated] (f : α → β) :
    (map f l).IsCountablyGenerated :=
  let ⟨_x, hxl⟩ := l.exists_antitone_basis
  (hxl.map _).isCountablyGenerated

instance comap.isCountablyGenerated (l : Filter β) [l.IsCountablyGenerated] (f : α → β) :
    (comap f l).IsCountablyGenerated :=
  let ⟨_x, hxl⟩ := l.exists_antitone_basis
  (hxl.comap _).isCountablyGenerated

instance Sup.isCountablyGenerated (f g : Filter α) [IsCountablyGenerated f]
    [IsCountablyGenerated g] : IsCountablyGenerated (f ⊔ g) := by
  rcases f.exists_antitone_basis with ⟨s, hs⟩
  rcases g.exists_antitone_basis with ⟨t, ht⟩
  exact HasCountableBasis.isCountablyGenerated ⟨hs.1.sup ht.1, Set.to_countable _⟩

instance prod.isCountablyGenerated (la : Filter α) (lb : Filter β) [IsCountablyGenerated la]
    [IsCountablyGenerated lb] : IsCountablyGenerated (la ×ˢ lb) :=
  Filter.Inf.isCountablyGenerated _ _

instance coprod.isCountablyGenerated (la : Filter α) (lb : Filter β) [IsCountablyGenerated la]
    [IsCountablyGenerated lb] : IsCountablyGenerated (la.coprod lb) :=
  Filter.Sup.isCountablyGenerated _ _

end IsCountablyGenerated

theorem isCountablyGenerated_seq [Countable ι'] (x : ι' → Set α) :
    IsCountablyGenerated (⨅ i, 𝓟 (x i)) := by
  use range x, countable_range x
  rw [generate_eq_biInf, iInf_range]

theorem isCountablyGenerated_of_seq {f : Filter α} (h : ∃ x : ℕ → Set α, f = ⨅ i, 𝓟 (x i)) :
    f.IsCountablyGenerated := by
  rcases h with ⟨x, rfl⟩
  apply isCountablyGenerated_seq

theorem isCountablyGenerated_biInf_principal {B : Set (Set α)} (h : B.Countable) :
    IsCountablyGenerated (⨅ s ∈ B, 𝓟 s) :=
  isCountablyGenerated_of_seq (countable_biInf_principal_eq_seq_iInf h)

theorem isCountablyGenerated_iff_exists_antitone_basis {f : Filter α} :
    IsCountablyGenerated f ↔ ∃ x : ℕ → Set α, f.HasAntitoneBasis x := by
  constructor
  · intro h
    exact f.exists_antitone_basis
  · rintro ⟨x, h⟩
    rw [h.1.eq_iInf]
    exact isCountablyGenerated_seq x

@[instance]
theorem isCountablyGenerated_principal (s : Set α) : IsCountablyGenerated (𝓟 s) :=
  isCountablyGenerated_of_seq ⟨fun _ => s, iInf_const.symm⟩

@[instance]
theorem isCountablyGenerated_pure (a : α) : IsCountablyGenerated (pure a) := by
  rw [← principal_singleton]
  exact isCountablyGenerated_principal _

@[instance]
theorem isCountablyGenerated_bot : IsCountablyGenerated (⊥ : Filter α) :=
  @principal_empty α ▸ isCountablyGenerated_principal _

@[instance]
theorem isCountablyGenerated_top : IsCountablyGenerated (⊤ : Filter α) :=
  @principal_univ α ▸ isCountablyGenerated_principal _

-- Porting note: without explicit `Sort u` and `Type v`, Lean 4 uses `ι : Prop`
universe u v

instance iInf.isCountablyGenerated {ι : Sort u} {α : Type v} [Countable ι] (f : ι → Filter α)
    [∀ i, IsCountablyGenerated (f i)] : IsCountablyGenerated (⨅ i, f i) := by
  choose s hs using fun i => exists_antitone_basis (f i)
  rw [← PLift.down_surjective.iInf_comp]
  refine HasCountableBasis.isCountablyGenerated ⟨hasBasis_iInf fun n => (hs _).1, ?_⟩
  refine (countable_range <| Sigma.map ((↑) : Finset (PLift ι) → Set (PLift ι)) fun _ => id).mono ?_
  rintro ⟨I, f⟩ ⟨hI, -⟩
  lift I to Finset (PLift ι) using hI
  exact ⟨⟨I, f⟩, rfl⟩

instance pi.isCountablyGenerated {ι : Type*} {α : ι → Type*} [Countable ι]
    (f : ∀ i, Filter (α i)) [∀ i, IsCountablyGenerated (f i)] : IsCountablyGenerated (pi f) :=
  iInf.isCountablyGenerated _

end Filter