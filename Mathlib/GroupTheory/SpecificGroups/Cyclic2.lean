import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Squarefree

universe u

theorem isCyclic_of_card_eq_mul_primes {G : Type u} [Group G] {p q : ℕ} [hp : Fact p.Prime]
    [hq : Fact q.Prime] (hpq : ¬(p ∣ (q - 1))) (hcard : Nat.card G = p * q) : IsCyclic G := by
  have : Finite G := Nat.finite_of_card_ne_zero (hcard ▸ Nat.mul_ne_zero hp.1.ne_zero hq.1.ne_zero)
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime p (show p^1 ∣ Nat.card G by simp [hcard])
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime q (show q^1 ∣ Nat.card G by simp [hcard])
  have disj : (P : Set G) ∩  (Q : Set G) = {1} := by sorry
  have card_eq := Set.ncard_union_add_ncard_inter (P : Set G) (Q : Set G)
  have : ((P : Set G) ∩ ↑Q).ncard = 1 := by
    rw [disj]
    simp only [Set.ncard_singleton]
  rw [this] at card_eq
  have : Set.ncard ((P : Set G) ∪ (Q : Set G)) = p + q - 1 := by sorry
  have : (P : Set G) ∪ (Q : Set G) < ⊤ := by sorry
  sorry

theorem gcd_totient_eq_one_iff (n : ℕ) (hne : n ≠ 0):
    Nat.gcd n n.totient = 1 ↔ Squarefree n ∧
    (∀ p q : ℕ, p ∈ n.primeFactors → q ∈ n.primeFactors → p < q → ¬(p ∣ q - 1)) := by
  constructor <;> intro h
  · have hsq : Squarefree n := by
      by_contra hsq
      rw [Nat.squarefree_iff_prime_squarefree] at hsq
      push_neg at hsq
      rcases hsq with ⟨p, hp, hdvd⟩
      have hpn : p ∣ n := dvd_of_mul_right_dvd hdvd
      have hpt : p ∣ n.totient := by
        rw [Nat.totient_eq_prod_factorization hne]
        refine (Prime.dvd_finsupp_prod_iff (Nat.Prime.prime hp)).mpr ?_
        refine ⟨p, ?_, ?_⟩
        · simp [hpn, hp, hne]
        · refine (Nat.Prime.dvd_mul hp).2 <| Or.inl ?_
          refine (Nat.dvd_prime_pow hp).mpr ⟨1, ?_, by simp⟩
          suffices h : 2 ≤ n.factorization p by omega
          rwa [← Nat.Prime.pow_dvd_iff_le_factorization hp hne, Nat.pow_two _]
      have : p ∣ n.gcd n.totient := dvd_gcd hpn hpt
      rw [h] at this
      exact Nat.Prime.not_dvd_one hp this
    constructor
    · exact hsq
    · intro p q hp hq _
      intro hdvd
      have hpn : p ∣ n := by exact Nat.dvd_of_mem_primeFactors hp
      have hpt : p ∣ n.totient := by
        rw [Nat.totient_eq_div_primeFactors_mul n, Nat.prod_primeFactors_of_squarefree hsq]
        rw [Nat.div_self (Nat.pos_of_ne_zero hne), one_mul, Prime.dvd_finset_prod_iff]
        · refine ⟨q, hq, hdvd⟩
        · exact Nat.prime_iff.mp (Nat.prime_of_mem_primeFactors hp)
      have : p ∣ n.gcd n.totient := dvd_gcd hpn hpt
      rw [h] at this
      exact Nat.Prime.not_dvd_one ((Nat.prime_of_mem_primeFactors hp)) this
  · rcases h with ⟨hsq, hpq⟩
    rw [Nat.totient_eq_div_primeFactors_mul n, Nat.prod_primeFactors_of_squarefree hsq]
    rw [Nat.div_self (Nat.pos_of_ne_zero hne), one_mul]
    refine Nat.Coprime.prod_right fun p hp ↦ ?_
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    refine Nat.Coprime.prod_left fun q hq ↦ ?_
    have hp' : Nat.Prime p := ((@Nat.mem_primeFactors_of_ne_zero _ p hne).1 hp).1
    have hq' : Nat.Prime q := ((@Nat.mem_primeFactors_of_ne_zero _ q hne).1 hq).1
    by_cases hlt : p < q
    · refine (Nat.Prime.coprime_iff_not_dvd hq').2 <| Nat.not_dvd_of_pos_of_lt ?_ ?_
      · simp only [tsub_pos_iff_lt, Nat.Prime.one_lt hp']
      · apply  tsub_lt_of_lt hlt
    · apply (Nat.Prime.coprime_iff_not_dvd hq').2
      push_neg at hlt
      rcases (le_iff_eq_or_lt.1 hlt) with rfl | hlt
      · apply Nat.not_dvd_of_pos_of_lt ?_ (Nat.sub_one_lt (Nat.Prime.ne_zero hq'))
        · simp only [tsub_pos_iff_lt, Nat.Prime.one_lt hq']
      · exact hpq q p hq hp hlt
