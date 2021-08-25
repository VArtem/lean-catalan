import data.finset
import data.finset.nat_antidiagonal
import algebra.big_operators.nat_antidiagonal
import tactic

open_locale big_operators

open finset

@[derive decidable_eq]
inductive Tree
| Leaf : Tree
| Branch : Tree → Tree → Tree

namespace Tree

def internal : Tree → ℕ
| Leaf := 0
| (Branch l r) := (internal l) + (internal r) + 1

@[simp] def internal_Leaf : internal Leaf = 0 := rfl
@[simp] def internal_Branch (l r : Tree) : internal (Branch l r) = internal l + internal r + 1 := rfl

def TreeN (n : ℕ) := {t : Tree // internal t = n}

def leaf0 : TreeN 0 := ⟨Leaf, internal_Leaf⟩ 
def combineTrees {n m : ℕ} (l : TreeN n) (r : TreeN m) : 
  TreeN (n + m).succ := ⟨Branch l.1 r.1, by rw [internal_Branch, l.2, r.2]⟩

def all : Π (n : ℕ), finset (TreeN n)
| 0 := {leaf0}
| (n + 1) := 
  finset.bUnion (finset.nat.antidiagonal n) $
  λ i, if h : i.1 < n.succ ∧ i.2 < n.succ ∧ i.1 + i.2 = n then
    let h₁ := and.left h in
    let h₂ := and.left (and.right h) in
    let h₃ := and.right (and.right h) in
      finset.image 
      (λ p : TreeN i.1 × TreeN i.2, by {rw ←h₃, exact combineTrees p.1 p.2})
      (finset.product (all i.1) (all i.2))
    else ∅


instance {n : ℕ} : fintype (TreeN n) :=
  ⟨all n, 
  begin
    apply nat.strong_induction_on n,
    clear n,
    rintro n ih ⟨t, h⟩,
    cases n, {
      rw [all, mem_singleton, leaf0, internal_Leaf],
      cases t with a b l r,
      { simp only [subtype.mk_eq_mk] },
      { rw internal at h,
        exfalso,
        linarith },
    }, {
      cases t with a b l r,
      { simpa only using h},
      simp [all, internal] at h ⊢,
      rw nat.add_one at h,
      replace h := nat.succ_inj'.1 h,
      subst h,

      have a_lt : a.internal < (a.internal + b.internal).succ := by {rw nat.succ_eq_add_one, linarith},
      have b_lt : b.internal < (a.internal + b.internal).succ := by {rw nat.succ_eq_add_one, linarith},
      use [a.internal, b.internal],
      simp only [true_and, dite_eq_ite, and_true, add_left_inj, eq_self_iff_true, nat.mem_antidiagonal, subtype.coe_eta, set_coe_cast,
  eq_mpr_eq_cast, subtype.val_eq_coe],
      rw if_pos,
      simp only [mem_image, exists_prop, prod.exists, mem_product],
      {
        use [a, b],
        refine ⟨⟨ih _ a_lt ⟨a, _⟩, ih _ b_lt ⟨b, _⟩⟩, rfl⟩,
      },
      exact ⟨a_lt, b_lt⟩,
    }
  end⟩

end Tree

open Tree

def catalan : ℕ → ℕ
| 0 := 1
| (n + 1) := ∑ p in finset.nat.antidiagonal n, 
  if h : p.1 < n.succ ∧ p.2 < n.succ ∧ p.1 + p.2 = n then
    let h₁ := and.left h in 
    let h₂ := and.left (and.right h) in
    let h₃ := and.right (and.right h) in
    catalan p.1 * catalan p.2
  else 0

lemma catalan_eq_TreeN_card {n} : catalan n = (all n).card :=
begin
  apply nat.strong_induction_on n,
  rintro n ih,
  cases n, {
    simp only [catalan, univ, fintype.elems, all, card_singleton],
  }, {
    simp only [all, catalan, eq_mpr_eq_cast],
    rw [card_bUnion], { 
      congr',
      ext,
      split_ifs, {
        rw [card_image_of_injective, card_product],
        rw [ih, ih],
        exact h.2.1,
        exact h.1,
        
        rintro a b,
        simp only [cast_inj],
        rintro h2,
        rw [combineTrees, combineTrees] at h2,
        simp only [subtype.mk_eq_mk, subtype.val_eq_coe] at h2,
        ext,
        exact h2.1,
        exact h2.2,
      }, {
        simp only [card_empty],
      }
    }, {
      rintro x hx y hy hneq k hk,
      simp at hk,
      rw [nat.mem_antidiagonal] at hx hy,
      split_ifs at hk, {
        simp at hk,
        rcases hk with ⟨⟨a1, b1, ha1, hc1⟩, ⟨a2, b2, ha2, hc2⟩⟩,
        rcases k with ⟨(_ | ⟨kleft, kright⟩), kint⟩,
        simpa using kint,
        simp only [combineTrees, subtype.val_eq_coe] at hc1 hc2,
        simp only [*, subtype.mk_eq_mk, bot_eq_empty, ne.def, set_coe_cast, not_mem_empty] at *,
        rcases hc2 with ⟨hc21, hc22⟩,
        substs hc21 hc22,
        apply hneq,
        repeat {rw ←subtype.val_eq_coe at hc1},
        rw prod.eq_iff_fst_eq_snd_eq,
        rw [←a1.property, ←a2.property, ←b1.property, ←b2.property],
        rw [hc1.1, hc1.2],
        exact ⟨rfl, rfl⟩,
      }, 
      all_goals { simpa using hk },
    }
  }
end